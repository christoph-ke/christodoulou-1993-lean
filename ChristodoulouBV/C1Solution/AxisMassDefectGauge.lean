module

public import ChristodoulouBV.C1Solution.AxisMassDefect
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Conformal gauge on the initial characteristic

The canonical conformal factor already satisfies the algebraic Einstein
relation. This file checks the additional initial-coordinate normalization
used in the source paper.
-/

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- A relative `C¹` jet along the initial edge gives an ordinary vertical
derivative at each interior edge point. -/
theorem vertical_hasDerivAt_initial_edge {b : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 b))
    {v : ℝ} (hv : v ∈ Ioo 0 b) :
    HasDerivAt (fun t => f (0, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (0, v)) (0, 1)) v := by
  have hp : (0, v) ∈ closedCoordTriangle 0 b :=
    ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 b)
      (closedCoordTriangle 0 b) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpath : HasDerivWithinAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1)
      (Icc 0 b) v :=
    ((hasDerivAt_const v (0 : ℝ)).prodMk (hasDerivAt_id' v)).hasDerivWithinAt
  have hfield := (hf.differentiableOn (by norm_num) (0, v) hp).hasFDerivWithinAt
  have h := hfield.comp_hasDerivWithinAt v hpath hmap
  exact h.hasDerivAt (Icc_mem_nhds hv.1 hv.2)

/-- The alternative initial gauge prescribes `r(0,v)=v/2` on the entire
initial edge, including both endpoints. -/
theorem Box.radius_initial_gauge {b M : ℝ} {hEdge : ℝ → ℝ}
    (x : Box 0 b M (fun _ => 1 / 2) hEdge)
    {v : ℝ} (hv : v ∈ Icc 0 b) :
    x.1.toTriple.radius (0, v) = v / 2 := by
  have hint : (∫ s in (0 : ℝ)..v, x.1.toTriple.lam (0, s)) =
      ∫ _s in (0 : ℝ)..v, (1 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc 0 b := by
      have hsv : s ∈ Icc 0 v := by simpa only [uIcc_of_le hv.1] using hs
      exact ⟨hsv.1, hsv.2.trans hv.2⟩
    change x.1.1.extendValue (0, s) = 1 / 2
    exact x.lam_edge ⟨s, hs'⟩
  change (∫ s in (0 : ℝ)..v, x.1.toTriple.lam (0, s)) = v / 2
  rw [hint]
  simp
  ring

/-- The reconstructed conformal factor is one at the initial axis point
for the alternative initial gauge. -/
theorem Box.conformal_initial_gauge {b M : ℝ} {hEdge : ℝ → ℝ}
    (x : Box 0 b M (fun _ => 1 / 2) hEdge) (hb : 0 < b)
    (hM : 1 ≤ M)
    (hsmall : b ≤ (numericalLedger M).lifetime M) :
    x.1.toTriple.conformal (0, 0) = 1 := by
  apply x.conformal_initial_axis hb hM (by simpa using hsmall)
  · intro v hv
    norm_num
  · norm_num

/-- The logarithmic conformal derivative follows algebraically from the
outgoing mass equation and the two geometric derivatives when `λ` is
constant along the characteristic. This lemma keeps the calculus separate
from the source-specific initial-edge data. -/
theorem log_conformal_hasDerivAt_of_const_lam
    {lam nu mu : ℝ → ℝ} {v r theta : ℝ}
    (hlampos : 0 < lam v) (hnuneg : nu v < 0)
    (hcomp : 0 < 1 - mu v) (hr : r ≠ 0)
    (hlam : HasDerivAt lam 0 v)
    (hnu : HasDerivAt nu
      (mu v * lam v * nu v / ((1 - mu v) * r)) v)
    (hmu : HasDerivAt mu
      ((1 - mu v) * theta ^ 2 / (lam v * r) - mu v * lam v / r) v) :
    HasDerivAt
      (fun t => Real.log (Real.sqrt (-4 * lam t * nu t / (1 - mu t))))
      (theta ^ 2 / (2 * lam v * r)) v := by
  let S : ℝ → ℝ := fun t => -4 * lam t * nu t / (1 - mu t)
  have hden : 1 - mu v ≠ 0 := ne_of_gt hcomp
  have hnum : 0 < -4 * lam v * nu v := by
    nlinarith only [mul_pos hlampos (neg_pos.mpr hnuneg)]
  have hSpos : 0 < S v := div_pos hnum hcomp
  have hS := ((hlam.const_mul (-4)).mul hnu).div
    ((hasDerivAt_const v (1 : ℝ)).sub hmu) hden
  change HasDerivAt S _ v at hS
  have hnear : ∀ᶠ t in 𝓝 v, 0 ≤ S t := by
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (S v) := isOpen_Ioi.mem_nhds hSpos
    exact (hS.continuousAt.eventually hmem).mono (fun _ ht => ht.le)
  have hEq : (fun t => Real.log (Real.sqrt (S t))) =ᶠ[𝓝 v]
      (fun t => Real.log (S t) / 2) := by
    filter_upwards [hnear] with t ht
    exact Real.log_sqrt ht
  have hlog := (Real.hasDerivAt_log hSpos.ne').comp v hS
  have hhalf := hlog.div_const 2
  have hresult := hhalf.congr_of_eventuallyEq hEq
  change HasDerivAt
    (fun t => Real.log (Real.sqrt (S t)))
    (theta ^ 2 / (2 * lam v * r)) v
  convert hresult using 1
  dsimp [S]
  field_simp [ne_of_gt hlampos, hden, hr, ne_of_lt hnuneg]
  ring

/-- Along the interior of the initial edge, the mass ratio derivative is
the quotient derivative of `2m/r` with the proved outgoing mass equation
substituted. -/
theorem Box.massRatio_hasDerivAt_initial_gauge
    {b M : ℝ} {hEdge : ℝ → ℝ}
    (x : Box 0 b M (fun _ => 1 / 2) hEdge) (hb : 0 < b)
    {v : ℝ} (hv : v ∈ Ioo 0 b) :
    HasDerivAt (fun t => x.1.toTriple.massRatio (0, t))
      ((1 - x.1.toTriple.massRatio (0, v)) *
          x.1.toTriple.theta (0, v) ^ 2 /
            (x.1.toTriple.lam (0, v) * x.1.toTriple.radius (0, v)) -
        x.1.toTriple.massRatio (0, v) * x.1.toTriple.lam (0, v) /
          x.1.toTriple.radius (0, v)) v := by
  have hp : (0, v) ∈ closedCoordTriangle 0 b :=
    ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hr : x.1.toTriple.radius (0, v) ≠ 0 :=
    (x.radius_pos hp hv.1).ne'
  have hmass := vertical_hasDerivAt_initial_edge (x.mass_c1 hb) hv
  rw [x.mass_v_eq_outgoing_density hb hp hv.1] at hmass
  have hrad := vertical_hasDerivAt_initial_edge (x.radius_c1 hb) hv
  rw [x.radius_v hb hp] at hrad
  have hquot := (hmass.const_mul 2).div hrad hr
  have hEq : (fun t => x.1.toTriple.massRatio (0, t)) =ᶠ[𝓝 v]
      (fun t => 2 * x.1.toTriple.mass (0, t) /
        x.1.toTriple.radius (0, t)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
    exact x.massRatio_off_axis (p := (0, t)) ht.1
  have h := hquot.congr_of_eventuallyEq hEq
  have hμ := x.massRatio_off_axis (p := (0, v)) hv.1
  have hl : x.1.toTriple.lam (0, v) ≠ 0 := ne_of_gt (by
    linarith [x.lam_ge_quarter hp])
  convert h using 1
  rw [hμ]
  field_simp [hr, hl]

/-- The logarithmic conformal derivative on the alternative initial gauge
is the scalar energy density appearing in the paper's equation (1.10). -/
theorem Box.log_conformal_hasDerivAt_initial_gauge
    {b M : ℝ} {hEdge : ℝ → ℝ}
    (x : Box 0 b M (fun _ => 1 / 2) hEdge) (hb : 0 < b)
    (hM : 1 ≤ M)
    (hsmall : b ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {v : ℝ} (hv : v ∈ Ioo 0 b) :
    HasDerivAt (fun t => Real.log (x.1.toTriple.conformal (0, t)))
      (v * ((fderivWithin ℝ x.1.toTriple.phi
        (closedCoordTriangle 0 b) (0, v)) (0, 1)) ^ 2 / 2) v := by
  have hp : (0, v) ∈ closedCoordTriangle 0 b :=
    ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hg : ∀ t ∈ Icc 0 b, (3 / 8 : ℝ) ≤ (fun _ : ℝ => 1 / 2) t := by
    intro t ht
    norm_num
  have hlpos : 0 < x.1.toTriple.lam (0, v) := by
    linarith [x.lam_ge_quarter hp]
  have hnneg : x.1.toTriple.nu (0, v) < 0 := by
    linarith [(x.nu_signs hb hM (by simpa using hsmall) hg hp).2]
  have hcomp : 0 < 1 - x.1.toTriple.massRatio (0, v) := by
    linarith [(x.massRatio_bounds hb hM (by simpa using hsmall) hp).2]
  have hr : x.1.toTriple.radius (0, v) ≠ 0 :=
    (x.radius_pos hp hv.1).ne'
  have hlamEq : (fun t => x.1.toTriple.lam (0, t)) =ᶠ[𝓝 v]
      (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
    change x.1.1.extendValue (0, t) = 1 / 2
    exact x.lam_edge ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
  have hlam : HasDerivAt (fun t => x.1.toTriple.lam (0, t)) 0 v :=
    (hasDerivAt_const v (1 / 2 : ℝ)).congr_of_eventuallyEq hlamEq
  have hnu := vertical_hasDerivAt_initial_edge x.nu_c1 hv
  have hnu' : HasDerivAt (fun t => x.1.toTriple.nu (0, t))
      (x.1.toTriple.massRatio (0, v) * x.1.toTriple.lam (0, v) *
        x.1.toTriple.nu (0, v) /
          ((1 - x.1.toTriple.massRatio (0, v)) *
            x.1.toTriple.radius (0, v))) v := by
    change HasDerivAt (fun t => x.1.toTriple.nu (0, t))
      ((fderivWithin ℝ x.1.toTriple.nu
        (closedCoordTriangle 0 b) (0, v)) (0, 1)) v at hnu
    rwa [x.nu_v_equation hb hM (by simpa using hsmall) hfixed hp hv.1] at hnu
  have hmu := x.massRatio_hasDerivAt_initial_gauge hb hv
  have hlog := log_conformal_hasDerivAt_of_const_lam
    (lam := fun t => x.1.toTriple.lam (0, t))
    (nu := fun t => x.1.toTriple.nu (0, t))
    (mu := fun t => x.1.toTriple.massRatio (0, t))
    (v := v) (r := x.1.toTriple.radius (0, v))
    (theta := x.1.toTriple.theta (0, v))
    hlpos hnneg hcomp hr hlam hnu' hmu
  change HasDerivAt
    (fun t => Real.log (x.1.toTriple.conformal (0, t)))
    (x.1.toTriple.theta (0, v) ^ 2 /
      (2 * x.1.toTriple.lam (0, v) * x.1.toTriple.radius (0, v))) v at hlog
  have hradius := x.radius_initial_gauge (v := v) ⟨hv.1.le, hv.2.le⟩
  have hlamval : x.1.toTriple.lam (0, v) = 1 / 2 := by
    change x.1.1.extendValue (0, v) = 1 / 2
    exact x.lam_edge ⟨v, ⟨hv.1.le, hv.2.le⟩⟩
  have htheta := x.theta_eq_radius_mul_phi_v hb hp
  have hcoef : x.1.toTriple.theta (0, v) ^ 2 /
      (2 * x.1.toTriple.lam (0, v) * x.1.toTriple.radius (0, v)) =
      v * ((fderivWithin ℝ x.1.toTriple.phi
        (closedCoordTriangle 0 b) (0, v)) (0, 1)) ^ 2 / 2 := by
    rw [htheta, hradius, hlamval]
    have hvne : v ≠ 0 := ne_of_gt hv.1
    field_simp [hvne]
  rwa [hcoef] at hlog

/-- The initial conformal gauge is exactly Christodoulou's exponential
integral formula (1.10), including the axis endpoint. -/
theorem Box.conformal_initial_gauge_eq_exp_integral
    {b M : ℝ} {hEdge : ℝ → ℝ}
    (x : Box 0 b M (fun _ => 1 / 2) hEdge) (hb : 0 < b)
    (hM : 1 ≤ M)
    (hsmall : b ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {v : ℝ} (hv : v ∈ Icc 0 b) :
    x.1.toTriple.conformal (0, v) =
      Real.exp (∫ s in (0 : ℝ)..v,
        s * ((fderivWithin ℝ x.1.toTriple.phi
          (closedCoordTriangle 0 b) (0, s)) (0, 1)) ^ 2 / 2) := by
  let K := closedCoordTriangle 0 b
  let Ω : ℝ → ℝ := fun t => x.1.toTriple.conformal (0, t)
  let q : ℝ → ℝ := fun t =>
    t * ((fderivWithin ℝ x.1.toTriple.phi K (0, t)) (0, 1)) ^ 2 / 2
  have hg : ∀ t ∈ Icc 0 b, (3 / 8 : ℝ) ≤ (fun _ : ℝ => 1 / 2) t := by
    intro t ht
    norm_num
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hb)
  have hφjet : ContinuousOn
      (fun p => (fderivWithin ℝ x.1.toTriple.phi K p) (0, 1)) K :=
    ((x.phi_c1 hb).continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 b) K := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hline : Continuous (fun t : ℝ => ((0 : ℝ), t)) :=
    continuous_const.prodMk continuous_id
  have hq : ContinuousOn q (Icc 0 b) := by
    dsimp [q]
    exact (continuousOn_id.mul
      ((hφjet.comp hline.continuousOn hmap).pow 2)).div_const 2
  have hμ : ContinuousOn x.1.toTriple.massRatio K :=
    (x.massRatio_c1 hb hM (by simpa using hsmall)).continuousOn
  have hlamcont : ContinuousOn x.1.toTriple.lam K := x.lam_c1.continuousOn
  have hnucont : ContinuousOn x.1.toTriple.nu K := x.nu_c1.continuousOn
  have hden : ∀ p ∈ K, 1 - x.1.toTriple.massRatio p ≠ 0 := by
    intro p hp
    have hμb := (x.massRatio_bounds hb hM (by simpa using hsmall) hp).2
    exact ne_of_gt (by linarith only [hμb])
  have harg : ContinuousOn
      (fun p => -4 * x.1.toTriple.lam p * x.1.toTriple.nu p /
        (1 - x.1.toTriple.massRatio p)) K :=
    ((continuousOn_const.mul hlamcont).mul hnucont).div
      (continuousOn_const.sub hμ) hden
  have hΩK : ContinuousOn x.1.toTriple.conformal K := by
    change ContinuousOn
      (fun p => Real.sqrt (-4 * x.1.toTriple.lam p * x.1.toTriple.nu p /
        (1 - x.1.toTriple.massRatio p))) K
    exact Real.continuous_sqrt.comp_continuousOn harg
  have hΩ : ContinuousOn Ω (Icc 0 b) :=
    hΩK.comp hline.continuousOn hmap
  have hΩpos : ∀ t ∈ Icc 0 b, 0 < Ω t := by
    intro t ht
    exact (x.conformal_relation hb hM (by simpa using hsmall) hg
      (hmap ht)).1
  have hlog : ContinuousOn (fun t => Real.log (Ω t)) (Icc 0 b) :=
    hΩ.log (fun t ht => ne_of_gt (hΩpos t ht))
  have hderiv : ∀ t ∈ Ioo 0 v,
      HasDerivAt (fun s => Real.log (Ω s)) (q t) t := by
    intro t ht
    exact x.log_conformal_hasDerivAt_initial_gauge hb hM hsmall hfixed
      ⟨ht.1, ht.2.trans_le hv.2⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
    hv.1 (hlog.mono (Icc_subset_Icc le_rfl hv.2))
    (hq.mono (Icc_subset_Icc le_rfl hv.2)) hderiv
  have hΩzero : Ω 0 = 1 := x.conformal_initial_gauge hb hM hsmall
  have hlogeq : Real.log (Ω v) = ∫ t in (0 : ℝ)..v, q t := by
    rw [hΩzero, Real.log_one, sub_zero] at hFTC
    exact hFTC.symm
  have hΩv : 0 < Ω v := hΩpos v hv
  calc
    Ω v = Real.exp (Real.log (Ω v)) := (Real.exp_log hΩv).symm
    _ = Real.exp (∫ t in (0 : ℝ)..v, q t) := by rw [hlogeq]

end ChristodoulouBV.AxisPicard

end
