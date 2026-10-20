module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyQuotient
public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyRadius
public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import Mathlib.Analysis.ODE.Gronwall
import ChristodoulouBV.BVSolution.Signs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Uniform outgoing control of the incoming expansion

On an off-axis strip, the equation for `ν` is linear in the outgoing
coordinate. The coefficient is at most the quotient ceiling divided by the
radius floor.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A scalar linear equation with a bounded nonnegative coefficient has an
exponential bound up to the right endpoint. -/
theorem abs_le_exp_of_linear_deriv
    {a b C : ℝ} {f A : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ w ∈ Ico a b,
      HasDerivAt f (A w * f w) w)
    (hcoeff : ∀ w ∈ Ico a b, 0 ≤ A w ∧ A w ≤ C) :
    ∀ w ∈ Icc a b, |f w| ≤ |f a| * Real.exp (C * (w - a)) := by
  have hderiv' : ∀ w ∈ Ico a b,
      HasDerivWithinAt f (A w * f w) (Ici w) w :=
    fun w hw => (hderiv w hw).hasDerivWithinAt
  have hbound : ∀ w ∈ Ico a b,
      ‖A w * f w‖ ≤ C * ‖f w‖ := by
    intro w hw
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hcoeff w hw).1]
    exact mul_le_mul_of_nonneg_right (hcoeff w hw).2 (abs_nonneg _)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := ‖f a‖) (K := C) (ε := 0) hf hderiv'
    (le_refl _) (fun w hw => by simpa only [add_zero] using hbound w hw)
  intro w hw
  simpa only [gronwallBound_ε0, Real.norm_eq_abs] using h w hw

/-- A fixed member bounds the initial values of `ν` on the incoming strip.
Compatibility transfers this compact bound to every later member. -/
theorem exists_nu_bound_at_vBar_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 ≤ u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ N₀ : ℝ, 0 ≤ N₀ ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc (0 : ℝ) u₁, vBar < b →
          |(S b).nu u vBar| ≤ N₀ := by
  let b₀ := (vBar + vStar) / 2
  have hvBar : 0 < vBar := hu₁.trans_lt hu₁v
  have hBarB₀ : vBar < b₀ := by dsimp [b₀]; linarith
  have hB₀Star : b₀ < vStar := by dsimp [b₀]; linarith
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨hvBar.trans hBarB₀, hB₀Star⟩
  have hcont : ContinuousOn (fun u => (S b₀).nu u vBar) (Icc 0 u₁) := by
    have hbase := (hfamily b₀ hb₀).1.nu_c1.continuousOn
    apply hbase.comp (continuous_id.prodMk continuous_const).continuousOn
    intro u hu
    apply subset_closure
    exact ⟨hu.1, hu.2.trans_lt hu₁v, hBarB₀⟩
  obtain ⟨N₀, hN₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hN₀pos : 0 ≤ N₀ := by
    have h := hN₀ 0 ⟨le_refl 0, hu₁⟩
    exact (norm_nonneg _).trans h
  refine ⟨N₀, hN₀pos, ?_⟩
  intro b hb u hu hBarb
  have hp₀ : (u, vBar) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu.1, hu.2.trans_lt hu₁v, hBarB₀⟩
  have hpb : (u, vBar) ∈ developmentWithInitialEdge b :=
    ⟨hu.1, hu.2.trans_lt hu₁v, hBarb⟩
  have heq := (family_fields_eq_on_common_development hfamily hb₀ hb
    ⟨hp₀, hpb⟩).2.2.2.2.1
  rw [← heq]
  simpa only [Real.norm_eq_abs] using hN₀ u hu

/-- The outgoing growth coefficient of `ν` is bounded by the quotient
ceiling divided by the radius floor. -/
theorem nu_growth_coefficient_le
    {m r lam ρ K : ℝ}
    (hρ : 0 < ρ) (hr : ρ ≤ r)
    (hμ : 0 ≤ 2 * m / r ∧ 2 * m / r < 1)
    (hlam : 0 ≤ lam)
    (hκ : lam / (1 - 2 * m / r) ≤ K) :
    0 ≤ (2 * m / r) * lam / ((1 - 2 * m / r) * r) ∧
      (2 * m / r) * lam / ((1 - 2 * m / r) * r) ≤ K / ρ := by
  let μ := 2 * m / r
  let q := 1 - μ
  let κ := lam / q
  have hrpos : 0 < r := hρ.trans_le hr
  have hqpos : 0 < q := by dsimp [q, μ]; linarith [hμ.2]
  have hκpos : 0 ≤ κ := div_nonneg hlam hqpos.le
  have hK : 0 ≤ K := hκpos.trans hκ
  have hμκ : μ * κ ≤ K := by
    have hμ1 : μ ≤ 1 := hμ.2.le
    calc
      μ * κ ≤ 1 * κ := mul_le_mul_of_nonneg_right hμ1 hκpos
      _ = κ := one_mul _
      _ ≤ K := hκ
  have hcoeff : (2 * m / r) * lam / ((1 - 2 * m / r) * r) =
      μ * κ / r := by
    dsimp [μ, κ, q]
    field_simp
  rw [hcoeff]
  constructor
  · exact div_nonneg (mul_nonneg hμ.1 hκpos) hrpos.le
  apply (div_le_div_iff₀ hrpos hρ).2
  have hleft : μ * κ * ρ ≤ K * ρ :=
    mul_le_mul_of_nonneg_right hμκ hρ.le
  have hright : K * ρ ≤ K * r :=
    mul_le_mul_of_nonneg_left hr hK
  exact hleft.trans hright

/-- On one outgoing segment strictly inside a C¹ member, uniform radius and
quotient bounds control `ν` by its value at the left endpoint. -/
theorem nu_abs_le_initial_mul_exp_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u vBar v ρ K : ℝ}
    (hu : 0 < u) (huBar : u < vBar)
    (hBarv : vBar ≤ v) (hvb : v < b)
    (hρ : 0 < ρ)
    (hr : ∀ w ∈ Icc vBar v, ρ ≤ S.r u w)
    (hκ : ∀ w ∈ Icc vBar v,
      S.lam u w / (1 - 2 * S.m u w / S.r u w) ≤ K) :
    |S.nu u v| ≤ |S.nu u vBar| *
      Real.exp ((K / ρ) * (v - vBar)) := by
  let A : ℝ → ℝ := fun w =>
    (2 * S.m u w / S.r u w) * S.lam u w /
      ((1 - 2 * S.m u w / S.r u w) * S.r u w)
  have hcont : ContinuousOn (S.nu u) (Icc vBar v) := by
    have hbase := H.nu_c1.continuousOn
    apply hbase.comp (continuous_const.prodMk continuous_id).continuousOn
    intro w hw
    apply subset_closure
    exact ⟨hu.le, huBar.trans_le hw.1, hw.2.trans_lt hvb⟩
  have hderiv : ∀ w ∈ Ico vBar v,
      HasDerivAt (S.nu u) (A w * S.nu u w) w := by
    intro w hw
    have hp : (u, w) ∈ openDevelopment 0 b :=
      ⟨⟨hu, huBar.trans_le hw.1 |>.trans hw.2 |>.trans hvb⟩,
        ⟨huBar.trans_le hw.1, hw.2.trans hvb⟩⟩
    convert nu_hasDerivAt_v_of_c1 H hp using 1
    dsimp [A]
    ring
  have hcoeff : ∀ w ∈ Ico vBar v, 0 ≤ A w ∧ A w ≤ K / ρ := by
    intro w hw
    have hp : (u, w) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, huBar.trans_le hw.1, hw.2.trans hvb⟩
    exact nu_growth_coefficient_le hρ (hr w ⟨hw.1, hw.2.le⟩)
      ((H.isBVSolution_development (hu.trans huBar |>.trans_le hBarv |>.trans hvb)).mass_ratio_bounds hp)
      (H.solution.lam_pos (u, w) hp).le
      (hκ w ⟨hw.1, hw.2.le⟩)
  exact abs_le_exp_of_linear_deriv hcont hderiv hcoeff v ⟨hBarv, le_refl v⟩

/-- The incoming expansion `ν` is uniformly bounded at strict positive incoming
coordinates on the entire off-axis family strip. -/
theorem exists_nu_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 < u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u ≤ u₁ → vBar ≤ v → v < b →
          |(S b).nu u v| ≤ N := by
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_radius_floor_before_star hu₁.le hu₁v hvBarStar hfamily
  obtain ⟨K, hK, hκ⟩ :=
    exists_quotient_ceiling_before_star hu₁.le hu₁v hvBarStar hα hfamily
  obtain ⟨N₀, hN₀, hbase⟩ :=
    exists_nu_bound_at_vBar_before_star hu₁.le hu₁v hvBarStar hfamily
  let N := N₀ * Real.exp ((K / ρ) * (vStar - vBar))
  have hN : 0 ≤ N := mul_nonneg hN₀ (Real.exp_nonneg _)
  refine ⟨N, hN, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  have hBarb : vBar < b := hvBarv.trans_lt hvb
  have hlocal := nu_abs_le_initial_mul_exp_of_c1 (hfamily b hb).1
    hu (huu₁.trans_lt hu₁v) hvBarv hvb hρ
    (fun w hw => hr b hb u w hu.le huu₁ hw.1 (hw.2.trans_lt hvb))
    (fun w hw => hκ b hb u w hu.le huu₁ hw.1 (hw.2.trans_lt hvb))
  have hC : 0 ≤ K / ρ := div_nonneg hK.le hρ.le
  have hexp : Real.exp ((K / ρ) * (v - vBar)) ≤
      Real.exp ((K / ρ) * (vStar - vBar)) := by
    apply Real.exp_le_exp.mpr
    have hvStar : v ≤ vStar := (hvb.trans hb.2).le
    exact mul_le_mul_of_nonneg_left (by linarith : v - vBar ≤ vStar - vBar) hC
  calc
    |(S b).nu u v| ≤
        |(S b).nu u vBar| * Real.exp ((K / ρ) * (v - vBar)) := hlocal
    _ ≤ N₀ * Real.exp ((K / ρ) * (v - vBar)) :=
      mul_le_mul_of_nonneg_right
        (hbase b hb u ⟨hu.le, huu₁⟩ hBarb) (Real.exp_nonneg _)
    _ ≤ N := mul_le_mul_of_nonneg_left hexp hN₀

/-- The same family bound includes the initial edge by continuity in the
incoming coordinate of each C¹ member. -/
theorem exists_nu_bound_closed_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 < u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₁ → vBar ≤ v → v < b →
          |(S b).nu u v| ≤ N := by
  obtain ⟨N, hN, hpositive⟩ :=
    exists_nu_bound_before_star hu₁ hu₁v hvBarStar hα hfamily
  refine ⟨N, hN, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  by_cases hu0 : u = 0
  · subst u
    have hcont : ContinuousOn (fun t => |(S b).nu t v|) (Icc 0 u₁) := by
      have hbase := (hfamily b hb).1.nu_c1.continuousOn
      have hline : ContinuousOn (fun t => (S b).nu t v) (Icc 0 u₁) := by
        apply hbase.comp (continuous_id.prodMk continuous_const).continuousOn
        intro t ht
        apply subset_closure
        exact ⟨ht.1, ht.2.trans_lt (hu₁v.trans_le hvBarv), hvb⟩
      exact continuous_abs.comp_continuousOn hline
    have hclosure : (0 : ℝ) ∈ closure (Ioo 0 u₁) := by
      rw [closure_Ioo (ne_of_lt hu₁)]
      exact ⟨le_refl 0, hu₁.le⟩
    have hcont' : ContinuousOn (fun t => |(S b).nu t v|)
        (closure (Ioo 0 u₁)) := by
      rwa [closure_Ioo (ne_of_lt hu₁)]
    exact le_on_closure
      (fun t ht => hpositive b hb t v ht.1 ht.2.le hvBarv hvb)
      hcont' continuousOn_const hclosure
  · exact hpositive b hb u v (lt_of_le_of_ne hu (Ne.symm hu0)) huu₁ hvBarv hvb

end ChristodoulouBV.Uniqueness

end
