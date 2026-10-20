module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyInitial
public import ChristodoulouBV.Uniqueness.ExtensionFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge

/-!
# Uniform initial mass gap across the extension family

One fixed member gives a positive gap at `vBar`. The initial-edge ODE and
the common scalar data propagate a single lower bound to all later outgoing
points, regardless of the member used to represent them.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The mass gap on the initial edge has one positive
lower bound for every compatible member before `vStar`. -/
theorem exists_initial_mass_gap_floor_before_star
    {alpha₀ : ℝ → ℝ} {vStar vBar : ℝ} {S : ℝ → Fields}
    (hvBar : 0 < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ q₀ : ℝ, 0 < q₀ ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ v : ℝ, vBar ≤ v → v < b →
          q₀ ≤ 1 - 2 * (S b).m 0 v / (S b).r 0 v := by
  obtain ⟨A, hA, hscalar⟩ :=
    exists_initial_scalar_bound_before_star (hvBar.trans hvBarStar) hα hfamily
  let T := 2 * A
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let C := 4 * T ^ 2 / vBar
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let b₀ := (vBar + vStar) / 2
  have hvBarB₀ : vBar < b₀ := by dsimp [b₀]; linarith
  have hB₀Star : b₀ < vStar := by dsimp [b₀]; linarith
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨hvBar.trans hvBarB₀, hB₀Star⟩
  let qBase := 1 - 2 * (S b₀).m 0 vBar / (S b₀).r 0 vBar
  have hqBase : 0 < qBase :=
    (hfamily b₀ hb₀).1.mass_gap_pos_of_c1
      (p := (0, vBar)) ⟨le_refl 0, hvBar, hvBarB₀⟩
  let q₀ := qBase * Real.exp (-(C * (vStar - vBar)))
  have hq₀ : 0 < q₀ := mul_pos hqBase (Real.exp_pos _)
  refine ⟨q₀, hq₀, ?_⟩
  intro b hb v hvBarv hvb
  have hvBarb : vBar < b := hvBarv.trans_lt hvb
  let q : ℝ → ℝ := fun w =>
    1 - 2 * (S b).m 0 w / (S b).r 0 w
  have hH := (hfamily b hb).1
  have hr : ∀ w ∈ Ioo (0 : ℝ) b, (S b).r 0 w = w / 2 :=
    fun w hw => ((hfamily b hb).2 w hw).1
  have hqcont : ContinuousOn q (Icc vBar v) := by
    intro w hw
    have hw' : w ∈ Ioo (0 : ℝ) b :=
      ⟨hvBar.trans_le hw.1, hw.2.trans_lt hvb⟩
    exact (initial_mass_gap_hasDerivAt_v_of_c1 hH hr hw').continuousAt.continuousWithinAt
  have hqdiff : DifferentiableOn ℝ q (Ioo vBar v) := by
    intro w hw
    have hw' : w ∈ Ioo (0 : ℝ) b :=
      ⟨hvBar.trans hw.1, hw.2.trans hvb⟩
    exact (initial_mass_gap_hasDerivAt_v_of_c1 hH hr hw').differentiableAt.differentiableWithinAt
  have hderiv : ∀ w ∈ Ioo vBar v, -(C * q w) ≤ deriv q w := by
    intro w hw
    have hw' : w ∈ Ioo (0 : ℝ) b :=
      ⟨hvBar.trans hw.1, hw.2.trans hvb⟩
    exact initial_mass_gap_deriv_ge_of_theta_bound hH hr hvBar hw.1.le hw' hT
      (hscalar b hb w hw').2
  have hpoint := initial_gap_lower_of_deriv_ge hvBarv hqcont hqdiff hderiv
    v ⟨hvBarv, le_refl v⟩
  have hfields := family_fields_eq_on_common_development hfamily hb₀ hb
    (p := (0, vBar))
    ⟨⟨le_refl 0, hvBar, hvBarB₀⟩,
      ⟨le_refl 0, hvBar, hvBarb⟩⟩
  have hqeq : qBase = q vBar := by
    dsimp [qBase, q]
    rw [hfields.1, hfields.2.2.1]
  have hexp : Real.exp (-(C * (vStar - vBar))) ≤
      Real.exp (-(C * (v - vBar))) := by
    apply Real.exp_le_exp.mpr
    have hvStar : v ≤ vStar := (hvb.trans hb.2).le
    nlinarith only [hC, hvStar]
  calc
    q₀ = qBase * Real.exp (-(C * (vStar - vBar))) := rfl
    _ ≤ qBase * Real.exp (-(C * (v - vBar))) :=
      mul_le_mul_of_nonneg_left hexp hqBase.le
    _ = q vBar * Real.exp (-(C * (v - vBar))) := by rw [hqeq]
    _ ≤ q v := hpoint
    _ = 1 - 2 * (S b).m 0 v / (S b).r 0 v := rfl

/-- The uniform initial gap also bounds the positive expansion quotient on
the initial edge. Propagation in `u` is proved separately by the incoming strip estimates. -/
theorem exists_initial_quotient_ceiling_before_star
    {alpha₀ : ℝ → ℝ} {vStar vBar : ℝ} {S : ℝ → Fields}
    (hvBar : 0 < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ v : ℝ, vBar ≤ v → v < b →
          (S b).lam 0 v /
            (1 - 2 * (S b).m 0 v / (S b).r 0 v) ≤ K := by
  obtain ⟨q₀, hq₀, hgap⟩ :=
    exists_initial_mass_gap_floor_before_star hvBar hvBarStar hα hfamily
  refine ⟨1 / (2 * q₀), by positivity, ?_⟩
  intro b hb v hvBarv hvb
  have hv : v ∈ Ioo (0 : ℝ) b := ⟨hvBar.trans_le hvBarv, hvb⟩
  have hlam : (S b).lam 0 v = 1 / 2 :=
    initial_lam_eq_of_gauge (hfamily b hb).1
      (fun w hw => ((hfamily b hb).2 w hw).1) hv
  have hq := hgap b hb v hvBarv hvb
  have hqpos : 0 < 1 - 2 * (S b).m 0 v / (S b).r 0 v :=
    hq₀.trans_le hq
  rw [hlam]
  apply (div_le_div_iff₀ hqpos (by positivity : 0 < 2 * q₀)).2
  nlinarith only [hq]

end ChristodoulouBV.Uniqueness

end
