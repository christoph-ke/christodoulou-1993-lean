module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
public import ChristodoulouBV.C1Solution.ExtractionMass
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FunProp
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The initial-edge mass-gap equation

The outgoing mass primitive differentiates at a positive point of the initial
edge. This supplies the ODE used to bound the initial quotient uniformly over
the compatible family.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The outgoing mass equation at a positive point of the initial edge. The
derivative is classical because the point is interior to the edge interval. -/
theorem initial_mass_hasDerivAt_v_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (S.m 0)
      ((1 - 2 * S.m 0 v / S.r 0 v) * S.theta 0 v ^ 2 /
        (2 * S.lam 0 v)) v := by
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hv.1, hv.2]
  have hBb : B < b := by dsimp [B]; linarith [hv.2]
  have hvB : v < B := by dsimp [B]; linarith [hv.2]
  let a := v / 2
  let c := (v + B) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hv.1]
  have hav : a < v := by dsimp [a]; linarith [hv.1]
  have hvc : v < c := by dsimp [c]; linarith [hvB]
  have hcB : c < B := by dsimp [c]; linarith [hvB]
  let g : ℝ → ℝ := fun s =>
    (1 - 2 * S.m 0 s / S.r 0 s) * S.theta 0 s ^ 2 /
      (2 * S.lam 0 s)
  have hmap (s : ℝ) (hs : s ∈ Icc a c) :
      (0, s) ∈ closedCoordTriangle 0 B := by
    change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ s ∧ s ≤ B
    exact ⟨le_refl 0, ha.le.trans hs.1, hs.2.trans hcB.le⟩
  have hmem (s : ℝ) (hs : s ∈ Icc a c) :
      (0, s) ∈ developmentWithInitialEdge b :=
    ⟨le_refl 0, ha.trans_le hs.1, (hs.2.trans_lt hcB).trans hBb⟩
  have hg : ContinuousOn g (Icc a c) := by
    have hcanon : ContinuousOn
        (fun s => C1Solution.canonicalMassOutgoingDensity b S (0, s))
        (Icc a c) :=
      (C1Solution.canonicalMass_densities_continuousOn hB hBb H).1.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    apply hcanon.congr
    intro s hs
    dsimp [g, C1Solution.canonicalMassOutgoingDensity]
    rw [C1Solution.canonicalMassRatio_eq_mass_ratio H (hmem s hs)]
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (S.m 0) g a t := by
    have htU : (0, t) ∈ developmentWithInitialEdge b :=
      hmem t ⟨ht.1.le, ht.2.le⟩
    have hseg : outSeg 0 a t ⊆ developmentWithInitialEdge b :=
      H.solution.development.out_seg_subset htU ha ht.1.le le_rfl
    exact H.solution.mass_out 0 a t ht.1.le hseg
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hav hvc hg hprim

/-- On the initial edge the mass-gap derivative is the linear mass-source
term plus a nonnegative mass term. -/
theorem initial_mass_gap_hasDerivAt_v_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (fun w => 1 - 2 * S.m 0 w / S.r 0 w)
      (-(1 - 2 * S.m 0 v / S.r 0 v) * S.theta 0 v ^ 2 /
          (S.r 0 v * S.lam 0 v) +
        (2 * S.m 0 v / S.r 0 v) * S.lam 0 v / S.r 0 v) v := by
  have hrad : HasDerivAt (S.r 0) (S.lam 0 v) v := by
    have heq : S.r 0 =ᶠ[𝓝 v] (fun w => w / 2) := by
      filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
      exact hr w hw
    have hder : HasDerivAt (fun w : ℝ => w / 2) (1 / 2) v := by
      simpa only [id_eq, div_eq_mul_inv, one_mul] using
        (hasDerivAt_id v).mul_const (1 / 2 : ℝ)
    rw [initial_lam_eq_of_gauge H hr hv]
    exact hder.congr_of_eventuallyEq heq
  have hm := initial_mass_hasDerivAt_v_of_c1 H hv
  have hr0 : S.r 0 v ≠ 0 :=
    ne_of_gt (H.solution.radius_pos (0, v) ⟨le_refl 0, hv.1, hv.2⟩)
  have h := ((hasDerivAt_const v (1 : ℝ)).sub
    ((hm.const_mul 2).div hrad hr0))
  convert h using 1
  field_simp [hr0]
  ring

/-- Bounded scalar-radius data bound the initial outgoing scalar amplitude.
The factor two comes from the initial radius gauge and the scalar primitive
from the regular axis. -/
theorem initial_theta_abs_le_of_alpha_bound {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2)
    {v A : ℝ} (hv : v ∈ Ioo (0 : ℝ) b)
    (hα : ∀ w ∈ Ioo (0 : ℝ) b, |S.alpha 0 w| ≤ A) :
    |S.theta 0 v| ≤ 2 * A := by
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hv.1, hv.2]
  have hBb : B < b := by dsimp [B]; linarith [hv.2]
  have hvB : v ≤ B := by dsimp [B]; linarith [hv.2]
  have hp : (0, v) ∈ closedCoordTriangle 0 B :=
    ⟨le_refl 0, hv.1.le, hvB⟩
  have hψ := C1Solution.canonicalScalarRadius_eq_canonicalRadius_mul_phi
    hB hBb H hp
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H (le_refl 0) hv.1 hvB,
    hr v hv] at hψ
  have hψ' : (∫ w in (0 : ℝ)..v, S.alpha 0 w) =
      (v / 2) * S.phi 0 v := by
    simpa only [C1Solution.canonicalScalarRadius,
      intervalIntegral.weightedDiagonalRadius] using hψ
  have hInt : |∫ w in (0 : ℝ)..v, S.alpha 0 w| ≤ A * v := by
    have hbnd : ∀ w ∈ Set.uIoc (0 : ℝ) v, ‖S.alpha 0 w‖ ≤ A := by
      intro w hw
      have hw' : w ∈ Ioc (0 : ℝ) v := by simpa only [uIoc_of_le hv.1.le] using hw
      simpa only [Real.norm_eq_abs] using hα w ⟨hw'.1, hw'.2.trans_lt hv.2⟩
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    simpa only [Real.norm_eq_abs, abs_of_pos hv.1, sub_zero] using hh
  have hlam : S.lam 0 v = 1 / 2 := initial_lam_eq_of_gauge H hr hv
  have hφ : |S.lam 0 v * S.phi 0 v| ≤ A := by
    rw [hlam]
    have heq : (1 / 2 : ℝ) * S.phi 0 v =
        (∫ w in (0 : ℝ)..v, S.alpha 0 w) / v := by
      apply (eq_div_iff (ne_of_gt hv.1)).2
      rw [hψ']
      ring
    rw [heq, abs_div, abs_of_pos hv.1]
    exact (div_le_iff₀ hv.1).2 (by simpa only [mul_comm] using hInt)
  change |S.alpha 0 v - S.lam 0 v * S.phi 0 v| ≤ 2 * A
  calc
    _ ≤ |S.alpha 0 v| + |S.lam 0 v * S.phi 0 v| := abs_sub _ _
    _ ≤ A + A := add_le_add (hα v hv) hφ
    _ = 2 * A := by ring

/-- A linear differential lower bound preserves a positive gap over a
finite outgoing interval. This version accommodates the favorable positive
mass term in the initial-edge gap equation. -/
theorem initial_gap_lower_of_deriv_ge
    {a b C : ℝ} {q : ℝ → ℝ}
    (hab : a ≤ b)
    (hqcont : ContinuousOn q (Icc a b))
    (hqdiff : DifferentiableOn ℝ q (Ioo a b))
    (hderiv : ∀ v ∈ Ioo a b, -(C * q v) ≤ deriv q v) :
    ∀ v ∈ Icc a b,
      q a * Real.exp (-(C * (v - a))) ≤ q v := by
  let F : ℝ → ℝ := fun v => q v * Real.exp (C * (v - a))
  have hEcont : Continuous (fun v : ℝ => Real.exp (C * (v - a))) := by
    fun_prop
  have hFcont : ContinuousOn F (Icc a b) :=
    hqcont.mul hEcont.continuousOn
  have hFderiv (v : ℝ) (hv : v ∈ Ioo a b) :
      HasDerivAt F
        (Real.exp (C * (v - a)) * (deriv q v + C * q v)) v := by
    have hq : HasDerivAt q (deriv q v) v :=
      ((hqdiff v hv).differentiableAt (isOpen_Ioo.mem_nhds hv)).hasDerivAt
    have hinner : HasDerivAt (fun t : ℝ => C * (t - a)) C v := by
      simpa only [smul_eq_mul, mul_one, id_eq] using
        (HasDerivAt.const_mul C ((hasDerivAt_id v).sub_const a))
    have hExp : HasDerivAt (fun t : ℝ => Real.exp (C * (t - a)))
        (Real.exp (C * (v - a)) * C) v := hinner.exp
    convert hq.mul hExp using 1
    ring
  have hFdiff : DifferentiableOn ℝ F (interior (Icc a b)) := by
    intro v hv
    have hv' : v ∈ Ioo a b := by simpa only [interior_Icc] using hv
    exact (hFderiv v hv').differentiableAt.differentiableWithinAt
  have hFnonneg : ∀ v ∈ interior (Icc a b), 0 ≤ deriv F v := by
    intro v hv
    have hv' : v ∈ Ioo a b := by simpa only [interior_Icc] using hv
    rw [(hFderiv v hv').deriv]
    exact mul_nonneg (Real.exp_nonneg _) (by linarith [hderiv v hv'])
  have hFmono := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    hFcont hFdiff hFnonneg
  intro v hv
  have hFa : F a ≤ F v := hFmono ⟨le_rfl, hab⟩ hv hv.1
  have hFa' : q a ≤ q v * Real.exp (C * (v - a)) := by
    simpa only [F, sub_self, mul_zero, Real.exp_zero, mul_one] using hFa
  calc
    q a * Real.exp (-(C * (v - a))) ≤
        (q v * Real.exp (C * (v - a))) * Real.exp (-(C * (v - a))) :=
      mul_le_mul_of_nonneg_right hFa' (Real.exp_nonneg _)
    _ = q v := by rw [mul_assoc, ← Real.exp_add]; simp

/-- The positive initial mass gap has a differential lower bound on an
off-axis part of the initial edge. The coefficient uses only a bound for
`θ` and the lower endpoint `vBar`. -/
theorem initial_mass_gap_deriv_ge_of_theta_bound
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2)
    {vBar v T : ℝ} (hvBar : 0 < vBar) (hvBarv : vBar ≤ v)
    (hv : v ∈ Ioo (0 : ℝ) b) (hT : 0 ≤ T)
    (hθ : |S.theta 0 v| ≤ T) :
    -(4 * T ^ 2 / vBar *
        (1 - 2 * S.m 0 v / S.r 0 v)) ≤
      deriv (fun w => 1 - 2 * S.m 0 w / S.r 0 w) v := by
  let μ := 2 * S.m 0 v / S.r 0 v
  let q := 1 - μ
  let g := S.theta 0 v ^ 2 / (S.r 0 v * S.lam 0 v)
  let C := 4 * T ^ 2 / vBar
  have hθsq : S.theta 0 v ^ 2 ≤ T ^ 2 := by
    rcases le_total 0 (S.theta 0 v) with h | h
    · rw [abs_of_nonneg h] at hθ
      nlinarith
    · rw [abs_of_nonpos h] at hθ
      nlinarith
  have hlam : S.lam 0 v = 1 / 2 := initial_lam_eq_of_gauge H hr hv
  have hsource : g ≤ C := by
    dsimp [g, C]
    rw [hr v hv, hlam]
    have heq : S.theta 0 v ^ 2 / ((v / 2) * (1 / 2)) =
        4 * S.theta 0 v ^ 2 / v := by
      field_simp [ne_of_gt hv.1]
      ring
    rw [heq]
    apply (div_le_div_iff₀ hv.1 hvBar).2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hθsq) hvBar.le,
      mul_nonneg (sub_nonneg.mpr (sub_nonneg.mpr hvBarv)) (sq_nonneg T)]
  have hq : 0 ≤ q :=
    (H.mass_gap_pos_of_c1 (p := (0, v)) ⟨le_refl 0, hv.1, hv.2⟩).le
  have hμ : 0 ≤ μ :=
    H.mass_ratio_nonneg_of_c1 (p := (0, v)) ⟨le_refl 0, hv.1, hv.2⟩
  have hrpos : 0 < S.r 0 v :=
    H.solution.radius_pos (0, v) ⟨le_refl 0, hv.1, hv.2⟩
  have hterm : 0 ≤ μ * S.lam 0 v / S.r 0 v :=
    div_nonneg (mul_nonneg hμ (by rw [hlam]; norm_num)) hrpos.le
  have hneg : -(C * q) ≤ -(q * g) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hsource) hq]
  have hd := (initial_mass_gap_hasDerivAt_v_of_c1 H hr hv).deriv
  rw [hd]
  have hform : -(C * q) ≤
      -q * S.theta 0 v ^ 2 / (S.r 0 v * S.lam 0 v) +
        μ * S.lam 0 v / S.r 0 v := by
    calc
      _ ≤ -(q * g) := hneg
      _ = -q * S.theta 0 v ^ 2 / (S.r 0 v * S.lam 0 v) := by
        dsimp [g]
        ring
      _ ≤ _ := by linarith only [hterm]
  exact hform

end ChristodoulouBV.Uniqueness

end
