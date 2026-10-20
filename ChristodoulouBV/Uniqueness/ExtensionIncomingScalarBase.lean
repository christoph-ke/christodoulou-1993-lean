module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingNu
import Mathlib.Tactic.Linarith

/-!
# Scalar data at the left edge of the off-axis strip

The initial-edge bound for `θ` is already available. This module supplies
the other datum required by the coupled scalar transport equations: a
cutoff independent bound for `ζ` on the fixed outgoing coordinate `vBar`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming scalar amplitude on the fixed left edge of the strip is
bounded uniformly across all compatible family members. -/
theorem exists_zeta_bound_at_vBar_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 ≤ u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ Z₀ : ℝ, 0 ≤ Z₀ ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc (0 : ℝ) u₁, vBar < b →
          |(S b).zeta u vBar| ≤ Z₀ := by
  let b₀ := (vBar + vStar) / 2
  have hvBar : 0 < vBar := hu₁.trans_lt hu₁v
  have hBarB₀ : vBar < b₀ := by dsimp [b₀]; linarith
  have hB₀Star : b₀ < vStar := by dsimp [b₀]; linarith
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨hvBar.trans hBarB₀, hB₀Star⟩
  have hcont : ContinuousOn (fun u => (S b₀).zeta u vBar) (Icc 0 u₁) := by
    have hbase := (hfamily b₀ hb₀).1.zeta_c1.continuousOn
    apply hbase.comp (continuous_id.prodMk continuous_const).continuousOn
    intro u hu
    apply subset_closure
    exact ⟨hu.1, hu.2.trans_lt hu₁v, hBarB₀⟩
  obtain ⟨Z₀, hZ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hZ₀pos : 0 ≤ Z₀ := by
    have h := hZ₀ 0 ⟨le_refl 0, hu₁⟩
    exact (norm_nonneg _).trans h
  refine ⟨Z₀, hZ₀pos, ?_⟩
  intro b hb u hu hBarb
  have hp₀ : (u, vBar) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu.1, hu.2.trans_lt hu₁v, hBarB₀⟩
  have hpb : (u, vBar) ∈ developmentWithInitialEdge b :=
    ⟨hu.1, hu.2.trans_lt hu₁v, hBarb⟩
  have heq := family_fields_eq_on_common_development hfamily hb₀ hb
    ⟨hp₀, hpb⟩
  have hzeta : (S b₀).zeta u vBar = (S b).zeta u vBar := by
    simp only [Fields.zeta, heq.2.2.2.2.2.2,
      heq.2.2.2.2.1, heq.2.1]
  rw [← hzeta]
  simpa only [Real.norm_eq_abs] using hZ₀ u hu

end ChristodoulouBV.Uniqueness

end
