module

public import ChristodoulouBV.Uniqueness.RadiusScalarBase

/-!
# Algebraic bounds for the scalar characteristic fields

These bounds isolate the pointwise algebra in (3.8). The comparison norms
enter only after their good-ray point bounds have been established.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- The θ difference is bounded by the outgoing quotient, expansion, and
scalar differences at any actual point of the common triangle. -/
theorem ComparisonData.theta_diff_pointwise_le (D : ComparisonData)
    {u v C A L P : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hC : 0 ≤ C)
    (hlam : |D.S₁.lam u v| ≤ C)
    (hq₂ : |D.S₂.theta u v / D.S₂.lam u v| ≤ C)
    (hA : |D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v| ≤ A)
    (hL : |D.S₁.lam u v - D.S₂.lam u v| ≤ L)
    (hP : |D.S₁.phi u v - D.S₂.phi u v| ≤ P) :
    |D.S₁.theta u v - D.S₂.theta u v| ≤ C * (A + L + P) := by
  rw [D.theta_diff_identity huv]
  calc
    |D.S₁.lam u v *
          (D.S₁.alpha u v / D.S₁.lam u v -
            D.S₂.alpha u v / D.S₂.lam u v) +
        (D.S₂.theta u v / D.S₂.lam u v) *
          (D.S₁.lam u v - D.S₂.lam u v) -
        D.S₁.lam u v * (D.S₁.phi u v - D.S₂.phi u v)| ≤
        |D.S₁.lam u v| *
          |D.S₁.alpha u v / D.S₁.lam u v -
            D.S₂.alpha u v / D.S₂.lam u v| +
        |D.S₂.theta u v / D.S₂.lam u v| *
          |D.S₁.lam u v - D.S₂.lam u v| +
        |D.S₁.lam u v| * |D.S₁.phi u v - D.S₂.phi u v| := by
      calc
        _ ≤ |D.S₁.lam u v *
              (D.S₁.alpha u v / D.S₁.lam u v -
                D.S₂.alpha u v / D.S₂.lam u v) +
            (D.S₂.theta u v / D.S₂.lam u v) *
              (D.S₁.lam u v - D.S₂.lam u v)| +
            |D.S₁.lam u v * (D.S₁.phi u v - D.S₂.phi u v)| :=
          abs_sub _ _
        _ ≤ _ := by
          have hh := abs_add_le
            (D.S₁.lam u v *
              (D.S₁.alpha u v / D.S₁.lam u v -
                D.S₂.alpha u v / D.S₂.lam u v))
            ((D.S₂.theta u v / D.S₂.lam u v) *
              (D.S₁.lam u v - D.S₂.lam u v))
          simpa only [abs_mul] using add_le_add_left hh _
    _ ≤ C * A + C * L + C * P := by
      apply add_le_add
      · apply add_le_add
        · exact (mul_le_mul_of_nonneg_right hlam (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hA hC)
        · exact (mul_le_mul_of_nonneg_right hq₂ (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hL hC)
      · exact (mul_le_mul_of_nonneg_right hlam (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hP hC)
    _ = C * (A + L + P) := by ring

/-- The ζ difference obeys the corresponding incoming algebraic bound. -/
theorem ComparisonData.zeta_diff_pointwise_le (D : ComparisonData)
    {u v C B N P : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hC : 0 ≤ C)
    (hnu : |D.S₁.nu u v| ≤ C)
    (hq₂ : |D.S₂.zeta u v / D.S₂.nu u v| ≤ C)
    (hB : |D.S₁.beta u v / D.S₁.nu u v -
      D.S₂.beta u v / D.S₂.nu u v| ≤ B)
    (hN : |D.S₁.nu u v - D.S₂.nu u v| ≤ N)
    (hP : |D.S₁.phi u v - D.S₂.phi u v| ≤ P) :
    |D.S₁.zeta u v - D.S₂.zeta u v| ≤ C * (B + N + P) := by
  rw [D.zeta_diff_identity huv]
  calc
    |D.S₁.nu u v *
          (D.S₁.beta u v / D.S₁.nu u v -
            D.S₂.beta u v / D.S₂.nu u v) +
        (D.S₂.zeta u v / D.S₂.nu u v) *
          (D.S₁.nu u v - D.S₂.nu u v) -
        D.S₁.nu u v * (D.S₁.phi u v - D.S₂.phi u v)| ≤
        |D.S₁.nu u v| *
          |D.S₁.beta u v / D.S₁.nu u v -
            D.S₂.beta u v / D.S₂.nu u v| +
        |D.S₂.zeta u v / D.S₂.nu u v| *
          |D.S₁.nu u v - D.S₂.nu u v| +
        |D.S₁.nu u v| * |D.S₁.phi u v - D.S₂.phi u v| := by
      calc
        _ ≤ |D.S₁.nu u v *
              (D.S₁.beta u v / D.S₁.nu u v -
                D.S₂.beta u v / D.S₂.nu u v) +
            (D.S₂.zeta u v / D.S₂.nu u v) *
              (D.S₁.nu u v - D.S₂.nu u v)| +
            |D.S₁.nu u v * (D.S₁.phi u v - D.S₂.phi u v)| :=
          abs_sub _ _
        _ ≤ _ := by
          have hh := abs_add_le
            (D.S₁.nu u v *
              (D.S₁.beta u v / D.S₁.nu u v -
                D.S₂.beta u v / D.S₂.nu u v))
            ((D.S₂.zeta u v / D.S₂.nu u v) *
              (D.S₁.nu u v - D.S₂.nu u v))
          simpa only [abs_mul] using add_le_add_left hh _
    _ ≤ C * B + C * N + C * P := by
      apply add_le_add
      · apply add_le_add
        · exact (mul_le_mul_of_nonneg_right hnu (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hB hC)
        · exact (mul_le_mul_of_nonneg_right hq₂ (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hN hC)
      · exact (mul_le_mul_of_nonneg_right hnu (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hP hC)
    _ = C * (B + N + P) := by ring

end ChristodoulouBV.Uniqueness

end
