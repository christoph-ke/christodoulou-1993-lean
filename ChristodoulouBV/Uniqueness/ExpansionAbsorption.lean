module

public import ChristodoulouBV.Uniqueness.ExpansionTransport

/-!
# Algebraic absorption for the expansion comparison

This elementary estimate is applied after the two characteristic coefficient
integrals have been bounded. Its smallness threshold is chosen after the
fixed transport constant.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- One absorption of the outgoing and incoming expansion inequalities.
The constant `C` is fixed before the final variation size `ε`. -/
theorem expansion_bounds_of_transport
    {L N Γ Γstar C ε : ℝ}
    (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (hsmall : C ^ 2 * ε ≤ 1 / 2)
    (hN : 0 ≤ N) (hΓ : 0 ≤ Γ) (hΓstar : 0 ≤ Γstar)
    (hOut : N ≤ C * (L + Γ))
    (hIn : L ≤ C * (ε * N + Γstar)) :
    L ≤ 2 * C ^ 2 * (Γ + Γstar) ∧
      N ≤ 2 * C ^ 2 * (Γ + Γstar) := by
  have hCnonneg : 0 ≤ C := by linarith
  have hC₂ : C ≤ C ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) hCnonneg]
  have hsmallN : C ^ 2 * ε * N ≤ N / 2 := by
    convert mul_le_mul_of_nonneg_right hsmall hN using 1
    ring
  have hInC := mul_le_mul_of_nonneg_left hIn hCnonneg
  have hCΓ := mul_le_mul_of_nonneg_right hC₂ hΓ
  have hNbound : N ≤ 2 * C ^ 2 * (Γ + Γstar) := by
    nlinarith
  have hLbound : L ≤ 2 * C ^ 2 * (Γ + Γstar) := by
    have hεnonneg : 0 ≤ C * ε := mul_nonneg hCnonneg hε
    have hprod := mul_le_mul_of_nonneg_left hNbound hεnonneg
    have hsmall' : 2 * C ^ 2 * ε ≤ 1 := by linarith
    have hsmallC := mul_le_mul_of_nonneg_left hsmall' hCnonneg
    have hprod' := mul_le_mul_of_nonneg_right hsmallC
      (add_nonneg hΓ hΓstar)
    have hCΓstar := mul_le_mul_of_nonneg_right hC₂ hΓstar
    nlinarith
  exact ⟨hLbound, hNbound⟩

end ChristodoulouBV.Uniqueness

end
