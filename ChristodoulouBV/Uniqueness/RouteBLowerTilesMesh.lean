module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesGaugeMarch
import Mathlib.Tactic

/-!
# A finite mesh after the first lower tile

The first tile has a height chosen by the rectangle theorem. The remaining
closed base interval admits equally spaced tiles of any prescribed maximum
width.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Starting with a fixed nondegenerate first interval, subdivide the rest
of `[0,a]` into finitely many equal intervals shorter than `ε`. -/
theorem exists_finite_mesh_after_first
    {a h ε : ℝ} (hh : 0 < h) (hha : h < a) (hε : 0 < ε) :
    ∃ (n : ℕ) (u : ℕ → ℝ) (s : ℝ),
      0 < s ∧ s < ε ∧
      u 0 = 0 ∧ u 1 = h ∧ u (n + 1) = a ∧
      (∀ i ≤ n, u i < u (i + 1)) ∧
      (∀ i ≤ n + 1, u i ∈ Icc 0 a) ∧
      (∀ i < n, u (i + 2) - u (i + 1) = s) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((a - h) / ε)
  let n : ℕ := N + 1
  let s : ℝ := (a - h) / n
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hs : 0 < s := div_pos (by linarith only [hha]) hn
  have hsε : s < ε := by
    have hmul : a - h < (N : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hN
    apply (div_lt_iff₀ hn).mpr
    dsimp [s, n]
    push_cast
    nlinarith only [hmul, hε]
  let u : ℕ → ℝ := fun i =>
    if i = 0 then 0 else h + ((i - 1 : ℕ) : ℝ) * s
  have hu₀ : u 0 = 0 := by simp [u]
  have hu₁ : u 1 = h := by simp [u]
  have huLast : u (n + 1) = a := by
    have hnNat : n + 1 ≠ 0 := by omega
    simp only [u, ite_eq_right hnNat]
    have hnat : n + 1 - 1 = n := by omega
    rw [hnat]
    dsimp [s]
    field_simp
    ring
  have hstep : ∀ i ≤ n, u i < u (i + 1) := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [hu₀, hu₁]
      exact hh
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hisucc : i + 1 ≠ 0 := by omega
      have hminus : i + 1 - 1 = (i - 1) + 1 := by omega
      simp only [u, ite_eq_right hi0, ite_eq_right hisucc, hminus]
      push_cast
      nlinarith only [hs]
  have hmem : ∀ i ≤ n + 1, u i ∈ Icc 0 a := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [hu₀]
      exact ⟨le_rfl, (hh.trans hha).le⟩
    · have hindex : i - 1 ≤ n := by omega
      have hindexNonneg : 0 ≤ (((i - 1 : ℕ) : ℝ)) := by positivity
      have hindexLe : (((i - 1 : ℕ) : ℝ)) ≤ (n : ℝ) :=
        by exact_mod_cast hindex
      have hprod := mul_le_mul_of_nonneg_right hindexLe hs.le
      have hlastAlgebra : h + (n : ℝ) * s = a := by
        dsimp [s]
        field_simp
        ring
      simp only [u, ite_eq_right hi0]
      constructor
      · nlinarith only [hh.le, hindexNonneg, hs.le]
      · nlinarith only [hprod, hlastAlgebra]
  have hwidth : ∀ i < n, u (i + 2) - u (i + 1) = s := by
    intro i hi
    have hsucc : i + 1 ≠ 0 := by omega
    have hsucc₂ : i + 2 ≠ 0 := by omega
    have hminus₁ : i + 1 - 1 = i := by omega
    have hminus₂ : i + 2 - 1 = i + 1 := by omega
    simp only [u, ite_eq_right hsucc, ite_eq_right hsucc₂,
      hminus₁, hminus₂]
    push_cast
    ring
  exact ⟨n, u, s, hs, hsε, hu₀, hu₁, huLast, hstep, hmem, hwidth⟩

end ChristodoulouBV.Uniqueness

end
