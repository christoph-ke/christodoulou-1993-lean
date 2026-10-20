module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pointwise bound for the incoming lambda derivative source

This is the algebraic estimate used after equation (10), before Gronwall.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- A linear bound for the source in the incoming `λᵥ` equation when the
mixed coefficient and its outgoing derivative are uniformly bounded. -/
theorem lambda_v_source_abs_le
    {lam nu Q Qv L N D C : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hnu : |nu| ≤ N) (hQ0 : 0 ≤ Q) (hQ : Q ≤ D)
    (hQv : |Qv| ≤ C) :
    |((nu * lam * Q) * lam + nu * L) * Q + nu * lam * Qv| ≤
      N * D * |L| + (N * D ^ 2 + N * C) := by
  have hLamAbs : |lam| ≤ 1 := by
    rw [abs_of_nonneg hlam0]
    exact hlam1
  have hQabs : |Q| = Q := abs_of_nonneg hQ0
  have hN : 0 ≤ N := (abs_nonneg nu).trans hnu
  have hD : 0 ≤ D := hQ0.trans hQ
  have hC : 0 ≤ C := (abs_nonneg Qv).trans hQv
  have hA : |nu * lam * Q| ≤ N * D := by
    calc
      |nu * lam * Q| = |nu| * |lam| * Q := by rw [abs_mul, abs_mul, hQabs]
      _ ≤ N * 1 * D := by gcongr
      _ = N * D := by ring
  have hB : |nu * lam * Qv| ≤ N * C := by
    calc
      |nu * lam * Qv| = |nu| * |lam| * |Qv| := by rw [abs_mul, abs_mul]
      _ ≤ N * 1 * C := by gcongr
      _ = N * C := by ring
  have hAL : |(nu * lam * Q) * lam| ≤ N * D := by
    calc
      |(nu * lam * Q) * lam| = |nu * lam * Q| * |lam| := abs_mul _ _
      _ ≤ (N * D) * 1 := by gcongr
      _ = N * D := by ring
  have hBL : |nu * L| ≤ N * |L| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hnu (abs_nonneg L)
  have hleft : |((nu * lam * Q) * lam + nu * L) * Q| ≤
      (N * D + N * |L|) * D := by
    rw [abs_mul, hQabs]
    calc
      |(nu * lam * Q) * lam + nu * L| * Q ≤
          (|(nu * lam * Q) * lam| + |nu * L|) * Q :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) hQ0
      _ ≤ (N * D + N * |L|) * Q := by
        gcongr
      _ ≤ (N * D + N * |L|) * D := by
        exact mul_le_mul_of_nonneg_left hQ
          (add_nonneg (mul_nonneg hN hD)
            (mul_nonneg hN (abs_nonneg L)))
  calc
    |((nu * lam * Q) * lam + nu * L) * Q + nu * lam * Qv| ≤
        |((nu * lam * Q) * lam + nu * L) * Q| + |nu * lam * Qv| :=
      abs_add_le _ _
    _ ≤ (N * D + N * |L|) * D + N * C := add_le_add hleft hB
    _ = N * D * |L| + (N * D ^ 2 + N * C) := by ring

end ChristodoulouBV.Uniqueness

end
