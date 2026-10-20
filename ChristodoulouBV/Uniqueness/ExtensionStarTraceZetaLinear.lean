module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalarDerivative
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.BoundedDerivativeEndpoint
import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Linear vanishing of zeta at the old regular axis

The uniform outgoing derivative bound and zero regular-axis value give a
cutoff-independent linear bound in the coordinate distance to the axis.
-/

public section

open Set
open scoped NNReal

namespace ChristodoulouBV.Uniqueness

/-- On every strict old ray, `ζ` vanishes at most linearly in `v-u`, with
one constant independent of the family cutoff. -/
theorem exists_uniform_zeta_linear_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |(S b).zeta u v| ≤ M * (v - u) := by
  obtain ⟨B, N, hB, hN, hderiv⟩ :=
    exists_uniform_scalar_outgoing_derivative_bounds_before_star
      hu₀ hα hfamily hε1 htail
  let M : ℝ := N * B / 4
  have hM : 0 ≤ M := div_nonneg (mul_nonneg hN hB) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  let T : ℝ := (v + b) / 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hTb : T < b := by dsimp [T]; linarith
  have hvT : v < T := by dsimp [T]; linarith
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.le, (huv.trans hvT).le⟩
  have haxis : (S b).zeta u u = 0 :=
    C1Solution.zeta_axis_eq_zero hT hTb H huT
  have hζ := (C1Solution.five_fields_contDiffOn hT hTb H).2.2.2.2
  have hcont : ContinuousOn ((S b).zeta u) (Icc u v) := by
    exact hζ.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨hu.le, hw.1, (hw.2.trans hvT.le)⟩)
  have hdiff : ∀ w ∈ Ioo u v,
      DifferentiableAt ℝ ((S b).zeta u) w := by
    intro w hw
    exact (zeta_hasDerivAt_v_of_c1 H
      (show (u, w) ∈ openDevelopment 0 b from
        ⟨⟨hu, (hw.1.trans (hw.2.trans hvb))⟩,
          ⟨hw.1, hw.2.trans hvb⟩⟩)).differentiableAt
  have hbound : ∀ w ∈ Ioo u v,
      |deriv ((S b).zeta u) w| ≤ M := by
    intro w hw
    exact (hderiv b hb u w hu hw.1 (hw.2.trans hvb)).2
  have hLip := lipschitzOnWith_Icc_of_continuousOn_deriv_bound_Ioo
    huv hM hcont hdiff hbound
  have hdist := hLip.dist_le_mul v
    (show v ∈ Icc u v from ⟨huv.le, le_rfl⟩)
    u
    (show u ∈ Icc u v from ⟨le_rfl, huv.le⟩)
  change dist ((S b).zeta u v) ((S b).zeta u u) ≤
    M * dist v u at hdist
  have hresult : |(S b).zeta u v| ≤ M * (v - u) := by
    simpa only [Real.dist_eq, haxis, sub_zero,
      abs_of_nonneg (sub_nonneg.mpr huv.le)] using hdist
  exact hresult

end ChristodoulouBV.Uniqueness

end
