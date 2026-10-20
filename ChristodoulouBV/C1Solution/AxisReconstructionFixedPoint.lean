module

public import ChristodoulouBV.C1Solution.AxisReconstruction
public import ChristodoulouBV.C1Solution.AxisTriangleFixedPoint
public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPrimitiveJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Differential consequences of the axis Picard fixed point

The Picard integral equations yield the three evolution derivatives on the
closed triangle. Boundary values, including both vertices, follow by
continuity of the relative first jets.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- A horizontal slice derivative on the interior determines the relative
horizontal first jet everywhere on the closed coordinate triangle. -/
theorem horizontal_jet_of_interior_slices {a b : ℝ} (hab : a < b)
    {f G : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hslice : ∀ u v, a < u → u < v → v < b →
      HasDerivAt (fun t => f (t, v)) (G (u, v)) u)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ f (closedCoordTriangle a b) p) (1, 0) = G p := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjet : ContinuousOn
      (fun q => (fderivWithin ℝ f K q) (1, 0)) K :=
    (hf.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hopen : EqOn (fun q => (fderivWithin ℝ f K q) (1, 0)) G
      (openCoordTriangle a b) := by
    rintro ⟨u, v⟩ hq
    have hparts : a < u ∧ u < v ∧ v < b := hq
    have hqi : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hq
    have hKn : K ∈ 𝓝 (u, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hqi) interior_subset
    have hfAt : DifferentiableAt ℝ f (u, v) :=
      (hf.differentiableOn (by norm_num) (u, v) (interior_subset hqi))
        |>.differentiableAt hKn
    have hpath : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    have hcomp : HasDerivAt (fun t => f (t, v))
        (fderiv ℝ f (u, v) (1, 0)) u := by
      simpa only [Function.comp_def] using
        hfAt.hasFDerivAt.comp_hasDerivAt u hpath
    have hordinary := hcomp.unique (hslice u v hparts.1 hparts.2.1 hparts.2.2)
    change (fderivWithin ℝ f K (u, v)) (1, 0) = G (u, v)
    rw [fderivWithin_of_mem_nhds hKn]
    exact hordinary
  have hclosed : EqOn (fun q => (fderivWithin ℝ f K q) (1, 0)) G K :=
    hopen.of_subset_closure hjet hG
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hab])
  exact hclosed hp

/-- A vertical slice derivative on the interior determines the relative
vertical first jet everywhere on the closed coordinate triangle. -/
theorem vertical_jet_of_interior_slices {a b : ℝ} (hab : a < b)
    {f G : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hslice : ∀ u v, a < u → u < v → v < b →
      HasDerivAt (fun t => f (u, t)) (G (u, v)) v)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ f (closedCoordTriangle a b) p) (0, 1) = G p := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjet : ContinuousOn
      (fun q => (fderivWithin ℝ f K q) (0, 1)) K :=
    (hf.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hopen : EqOn (fun q => (fderivWithin ℝ f K q) (0, 1)) G
      (openCoordTriangle a b) := by
    rintro ⟨u, v⟩ hq
    have hparts : a < u ∧ u < v ∧ v < b := hq
    have hqi : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hq
    have hKn : K ∈ 𝓝 (u, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hqi) interior_subset
    have hfAt : DifferentiableAt ℝ f (u, v) :=
      (hf.differentiableOn (by norm_num) (u, v) (interior_subset hqi))
        |>.differentiableAt hKn
    have hpath : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hcomp : HasDerivAt (fun t => f (u, t))
        (fderiv ℝ f (u, v) (0, 1)) v := by
      simpa only [Function.comp_def] using
        hfAt.hasFDerivAt.comp_hasDerivAt v hpath
    have hordinary := hcomp.unique (hslice u v hparts.1 hparts.2.1 hparts.2.2)
    change (fderivWithin ℝ f K (u, v)) (0, 1) = G (u, v)
    rw [fderivWithin_of_mem_nhds hKn]
    exact hordinary
  have hclosed : EqOn (fun q => (fderivWithin ℝ f K q) (0, 1)) G K :=
    hopen.of_subset_closure hjet hG
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hab])
  exact hclosed hp

/-- The outgoing expansion obeys `λ_u=K_g` on the closed axis triangle. -/
theorem Box.lam_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.lam
      (closedCoordTriangle a b) p) (1, 0) =
      x.1.toTriple.gravitational p := by
  apply horizontal_jet_of_interior_slices hab x.lam_c1
    (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn
    (fun u v hau huv hvb => ?_) hp
  have h := x.picard_lam_horizontal_deriv hab hM hsmall
    hau.le huv.le hvb.le
  have hEq : (fun t => (x.1.toTriple.picard a g hEdge).lam (t, v)) =ᶠ[𝓝 u]
      (fun t => x.1.toTriple.lam (t, v)) := by
    filter_upwards [Ioo_mem_nhds hau huv] with t ht
    exact hfixed.1 ⟨ht.1.le, ht.2.le, hvb.le⟩
  exact (h.hasDerivAt (Icc_mem_nhds hau huv)).congr_of_eventuallyEq hEq.symm

/-- The normalized scalar field obeys the Picard source equation `h_u=Q`
on the entire closed axis triangle. -/
theorem Box.h_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.h
      (closedCoordTriangle a b) p) (1, 0) =
      x.1.toTriple.scalarSource p := by
  apply horizontal_jet_of_interior_slices hab x.h_c1
    (x.picard_coefficients_c1 hab hM hsmall).2.continuousOn
    (fun u v hau huv hvb => ?_) hp
  have h := x.picard_h_horizontal_deriv hab hM hsmall
    hau.le huv.le hvb.le
  have hEq : (fun t => (x.1.toTriple.picard a g hEdge).h (t, v)) =ᶠ[𝓝 u]
      (fun t => x.1.toTriple.h (t, v)) := by
    filter_upwards [Ioo_mem_nhds hau huv] with t ht
    exact hfixed.2.2 ⟨ht.1.le, ht.2.le, hvb.le⟩
  exact (h.hasDerivAt (Icc_mem_nhds hau huv)).congr_of_eventuallyEq hEq.symm

/-- The incoming expansion obeys `ν_v=K_g` on the closed axis triangle. -/
theorem Box.nu_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.nu
      (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.gravitational p := by
  apply vertical_jet_of_interior_slices hab x.nu_c1
    (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn
    (fun u v hau huv hvb => ?_) hp
  have h := x.picard_nu_vertical_deriv hab hM hsmall
    hau.le huv.le hvb.le
  have hEq : (fun t => (x.1.toTriple.picard a g hEdge).nu (u, t)) =ᶠ[𝓝 v]
      (fun t => x.1.toTriple.nu (u, t)) := by
    filter_upwards [Ioo_mem_nhds huv hvb] with t ht
    exact hfixed.2.1 ⟨hau.le, ht.1.le, ht.2.le⟩
  exact (h.hasDerivAt (Icc_mem_nhds huv hvb)).congr_of_eventuallyEq hEq.symm

/-- The gravitational and scalar Picard sources vanish on the regular
axis, forcing the corresponding evolution jets to vanish there. -/
theorem Box.picard_axis_evolution_jets {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.lam (closedCoordTriangle a b) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ x.1.toTriple.nu (closedCoordTriangle a b) (u, u)) (0, 1) = 0 ∧
    (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (1, 0) = 0 := by
  have hpoint : (u, u) ∈ closedCoordTriangle a b := by
    change a ≤ u ∧ u ≤ u ∧ u ≤ b
    exact ⟨hu.1, le_rfl, hu.2⟩
  simp [x.lam_u hab hM hsmall hfixed hpoint,
    x.nu_v hab hM hsmall hfixed hpoint,
    x.h_u hab hM hsmall hfixed hpoint]

/-- The scalar Picard source is `-K_g(h-φ)/λ` on the closed triangle. -/
theorem Triple.scalarSource_eq (x : Triple) (p : ℝ × ℝ) :
    x.scalarSource p =
      x.gravitational p * (-(x.h p - x.phi p) / x.lam p) := by
  rfl

/-- The outgoing scalar derivative satisfies `α_u=K_g φ` on the entire
closed axis triangle. -/
theorem Box.alpha_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.alpha
      (closedCoordTriangle a b) p) (1, 0) =
      x.1.toTriple.gravitational p * x.1.toTriple.phi p := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hldiff := (x.lam_c1).differentiableOn (by norm_num) p hp
  have hhdiff := (x.h_c1).differentiableOn (by norm_num) p hp
  change (fderivWithin ℝ (x.1.1.extendValue * x.1.2.2.extendValue) K p) (1, 0) = _
  rw [fderivWithin_mul hunique hldiff hhdiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hlu := x.lam_u hab hM hsmall hfixed hp
  have hhu := x.h_u hab hM hsmall hfixed hp
  change (fderivWithin ℝ x.1.1.extendValue K p) (1, 0) =
    x.1.toTriple.gravitational p at hlu
  change (fderivWithin ℝ x.1.2.2.extendValue K p) (1, 0) =
    x.1.toTriple.scalarSource p at hhu
  rw [hlu, hhu, x.1.toTriple.scalarSource_eq p]
  change x.1.toTriple.lam p *
      (x.1.toTriple.gravitational p *
        (-(x.1.toTriple.h p - x.1.toTriple.phi p) / x.1.toTriple.lam p)) +
      x.1.toTriple.h p * x.1.toTriple.gravitational p =
      x.1.toTriple.gravitational p * x.1.toTriple.phi p
  have hlam : x.1.toTriple.lam p ≠ 0 :=
    ne_of_gt (by linarith only [x.lam_ge_quarter hp])
  field_simp [hlam]
  ring_nf

/-- The radial incoming first jet equals the Picard incoming expansion,
including on the regular axis and at both vertices. -/
theorem Box.radius_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.radius
      (closedCoordTriangle a b) p) (1, 0) =
      x.1.toTriple.nu p := by
  have hR := intervalIntegral.radius_horizontal_jet_of_contDiffOn
    hab x.lam_c1 hp
  change (fderivWithin ℝ
    (intervalIntegral.weightedDiagonalRadius x.1.1.extendValue)
      (closedCoordTriangle a b) p) (1, 0) = x.1.toTriple.nu p
  rw [hR]
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hint : (∫ s in p.1..p.2,
      (fderivWithin ℝ x.1.1.extendValue
        (closedCoordTriangle a b) (p.1, s)) (1, 0)) =
      ∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc p.1 p.2 := by
      simpa only [uIcc_of_le hcoord.2.1] using hs
    exact x.lam_u hab hM hsmall hfixed
      ⟨hcoord.1, hs'.1, hs'.2.trans hcoord.2.2⟩
  rw [hint]
  have hnu := hfixed.2.1 hp
  have hdiag := hfixed.1 (show (p.1, p.1) ∈ closedCoordTriangle a b from
    ⟨hcoord.1, le_refl _, hcoord.2.1.trans hcoord.2.2⟩)
  change -(x.1.toTriple.picard a g hEdge).lam (p.1, p.1) +
      (∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s)) =
      x.1.toTriple.nu p at hnu
  rw [hdiag] at hnu
  exact hnu

/-- The scalar-radius incoming first jet equals the integral formula for
`β` on the entire closed triangle. -/
theorem Box.scalarRadius_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.scalarRadius
      (closedCoordTriangle a b) p) (1, 0) =
      x.1.toTriple.beta p := by
  have hΨ := intervalIntegral.radius_horizontal_jet_of_contDiffOn
    hab x.alpha_c1 hp
  change (fderivWithin ℝ
    (intervalIntegral.weightedDiagonalRadius x.1.toTriple.alpha)
      (closedCoordTriangle a b) p) (1, 0) = x.1.toTriple.beta p
  rw [hΨ]
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hint : (∫ s in p.1..p.2,
      (fderivWithin ℝ x.1.toTriple.alpha
        (closedCoordTriangle a b) (p.1, s)) (1, 0)) =
      ∫ s in p.1..p.2,
        x.1.toTriple.gravitational (p.1, s) * x.1.toTriple.phi (p.1, s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc p.1 p.2 := by
      simpa only [uIcc_of_le hcoord.2.1] using hs
    exact x.alpha_u hab hM hsmall hfixed
      ⟨hcoord.1, hs'.1, hs'.2.trans hcoord.2.2⟩
  rw [hint]
  rfl

/-- The incoming scalar derivative satisfies `β_v=K_g φ` on the entire
closed axis triangle. -/
theorem Box.beta_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.beta
      (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.gravitational p * x.1.toTriple.phi p := by
  have hsource := (x.picard_coefficients_c1 hab hM hsmall).1.mul (x.phi_c1 hab)
  apply vertical_jet_of_interior_slices hab (x.beta_c1 hab hM hsmall)
    hsource.continuousOn (fun u v hau huv hvb => ?_) hp
  have h := intervalIntegral.hasDerivWithinAt_integral_upper_of_triangle_continuous
    hsource.continuousOn hau.le (le_refl u) huv.le hvb.le
  have hconst : HasDerivAt
      (fun t : ℝ => -x.1.toTriple.alpha (u, u)) 0 v :=
    hasDerivAt_const v _
  have hsum := (hconst.hasDerivWithinAt).add h
  have hfun : (fun t => x.1.toTriple.beta (u, t)) =
      ((fun t : ℝ => -x.1.toTriple.alpha (u, u)) +
        fun t => ∫ s in u..t,
          x.1.toTriple.gravitational (u, s) * x.1.toTriple.phi (u, s)) := by
    funext t
    simp only [Triple.beta, Pi.add_apply]
  have hbeta : HasDerivWithinAt
      (fun t => x.1.toTriple.beta (u, t))
      (x.1.toTriple.gravitational (u, v) * x.1.toTriple.phi (u, v))
      (Icc u b) v := by
    rw [hfun]
    simpa only [zero_add] using hsum
  exact hbeta.hasDerivAt (Icc_mem_nhds huv hvb)

end ChristodoulouBV.AxisPicard

end
