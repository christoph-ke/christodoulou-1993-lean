module

public import ChristodoulouBV.Uniqueness.ExtensionLocalMixed
import ChristodoulouBV.BVSolution.SignAux

/-!
# Signs on an arbitrary C¹ development

The positive mass gap makes the outgoing mass density nonnegative. Its
regular-axis trace fixes the mass sign.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The Hawking mass is nonnegative on any C¹ development. -/
theorem mass_nonneg_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) : 0 ≤ S.m u v := by
  have huv : u < v := (H.solution.development.1 hp).2
  have haxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq hp] using
      H.solution.mass_axis u (H.solution.development.axis_mem hp)
  have hbound : ∀ᶠ a in 𝓝[>] u, S.m u a ≤ S.m u v := by
    filter_upwards [Ioo_mem_nhdsGT huv] with a ha
    have hseg : outSeg u a v ⊆ U :=
      H.solution.development.out_seg_subset hp ha.1 ha.2.le le_rfl
    have hmass := H.solution.mass_out u a v ha.2.le hseg
    have hint : 0 ≤ ∫ s in a..v,
        (1 - 2 * S.m u s / S.r u s) * (S.theta u s)^2 /
          (2 * S.lam u s) := by
      apply intervalIntegral.integral_nonneg ha.2.le
      intro s hs
      have hsU := H.solution.development.outgoing_mem hp
        (ha.1.trans_le hs.1) hs.2
      have hgap : 0 ≤ 1 - 2 * S.m u s / S.r u s :=
        (sub_pos.mpr (mass_ratio_lt_one_of_c1_domain H hsU)).le
      have hden : 0 ≤ 2 * S.lam u s :=
        (mul_pos (by norm_num) (H.solution.lam_pos (u, s) hsU)).le
      exact div_nonneg (mul_nonneg hgap (sq_nonneg _)) hden
    linarith only [hmass.2, hint]
  exact le_of_tendsto haxis hbound

/-- The mass ratio is nonnegative at every point of a C¹ development. -/
theorem mass_ratio_nonneg_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    0 ≤ 2 * S.m u v / S.r u v := by
  exact div_nonneg
    (mul_nonneg (by norm_num) (mass_nonneg_of_c1_domain H hp))
    (H.solution.radius_pos (u, v) hp).le

/-- The conformal identity fixes the sign of the incoming expansion. -/
theorem nu_neg_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) : S.nu u v < 0 := by
  obtain ⟨Ω, hΩ, hconf⟩ := H.solution.conformal (u, v) hp
  have hgap : 0 < 1 - 2 * S.m u v / S.r u v :=
    sub_pos.mpr (mass_ratio_lt_one_of_c1_domain H hp)
  have hprod : 0 < -(4 * S.lam u v * S.nu u v) := by
    rw [← hconf]
    exact mul_pos hgap (sq_pos_of_pos hΩ)
  have hlam := H.solution.lam_pos (u, v) hp
  nlinarith only [hprod, hlam]

end ChristodoulouBV.Uniqueness

end
