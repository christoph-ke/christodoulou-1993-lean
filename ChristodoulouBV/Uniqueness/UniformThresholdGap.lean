module

public import ChristodoulouBV.Uniqueness.UniformThresholdBounds
public import ChristodoulouBV.Uniqueness.Comparison

/-!
# A package-uniform preliminary mass gap

The baseline field bounds determine the first scalar variation threshold.
This threshold is shared by every normalized comparison satisfying the same
numeric package.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The first variation threshold depends only on the numerical baseline
field bounds. -/
noncomputable def UniformThresholdBounds.gapThreshold
    (P : UniformThresholdBounds) : ℝ :=
  1 / (2 * (P.C / P.c + 1))

/-- The numerical preliminary threshold is positive. -/
theorem UniformThresholdBounds.gapThreshold_pos
    (P : UniformThresholdBounds) : 0 < P.gapThreshold := by
  unfold UniformThresholdBounds.gapThreshold
  have hM : 0 ≤ P.C / P.c := div_nonneg P.C_nonneg P.c_pos.le
  positivity

/-- The normalized package bounds the scalar quotient on every outgoing ray. -/
theorem UniformThresholdBounds.theta_div_lam_le
    (P : UniformThresholdBounds) (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    (hP : P.Holds D.S₁ D.S₂)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
    |S.theta u v / S.lam u v| ≤ P.C / P.c := by
  have hpt : (u, v) ∈ triangle 0 1 := by simpa only [ha, hb] using huv
  obtain ⟨hlam, _, _, _, _, htheta, _⟩ := hP u v hpt S hS
  have hlamPos : 0 < S.lam u v := P.c_pos.trans_le hlam
  rw [abs_div, abs_of_pos hlamPos]
  apply (div_le_div_iff₀ hlamPos P.c_pos).2
  calc
    |S.theta u v| * P.c ≤ P.C * P.c :=
      mul_le_mul_of_nonneg_right htheta P.c_pos.le
    _ ≤ P.C * S.lam u v :=
      mul_le_mul_of_nonneg_left hlam P.C_nonneg

/-- Small outgoing scalar variation gives a common positive mass gap for
both fields of any normalized comparison satisfying the numeric package. -/
theorem UniformThresholdBounds.gap_ge_half
    (P : UniformThresholdBounds) (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    (hP : P.Holds D.S₁ D.S₂)
    {ε : ℝ} (hεle : ε ≤ P.gapThreshold)
    (hsmall : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε) :
    ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        1 / 2 ≤ 1 - IsBVSolution.mu S u v := by
  have hM : 0 ≤ P.C / P.c := div_nonneg P.C_nonneg P.c_pos.le
  have hden : 0 < 2 * (P.C / P.c + 1) := by positivity
  have hcoeff : (P.C / P.c) * ε ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hεle hM
    have hfrac : (P.C / P.c) * P.gapThreshold ≤ 1 / 2 := by
      unfold UniformThresholdBounds.gapThreshold
      rw [mul_one_div]
      apply (div_le_iff₀ hden).2
      nlinarith
    exact hh.trans hfrac
  intro u v huv S hS
  have hquot : ∀ t ∈ Ioc u v,
      |S.theta u t / S.lam u t| ≤ P.C / P.c := by
    intro t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    exact P.theta_div_lam_le D ha hb hP htT S hS
  rcases hS with rfl | rfl
  · exact D.h₁.gap_ge_half_of_small_outgoing_variation
      (D.hT huv).1 hM hquot (hsmall u v huv D.S₁ (Or.inl rfl)) hcoeff
  · exact D.h₂.gap_ge_half_of_small_outgoing_variation
      (D.hT huv).2 hM hquot (hsmall u v huv D.S₂ (Or.inr rfl)) hcoeff

end ChristodoulouBV.Uniqueness

end
