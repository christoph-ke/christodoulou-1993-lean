module

public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingNorm

/-!
# Incoming transport coefficient integral from a shared package

The negative incoming logarithmic coefficient is controlled by incoming
scalar variation with a constant chosen before the normalized comparison.
-/

@[expose] public section

open Set
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- One package bounds the incoming scalar quotient on the normalized
triangle. -/
theorem UniformThresholdBounds.zeta_div_nu_le
    (P : UniformThresholdBounds) (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    (hP : P.Holds D.S₁ D.S₂)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
    |S.zeta u v / S.nu u v| ≤ P.C / P.c := by
  have hpt : (u, v) ∈ triangle 0 1 := by simpa only [ha, hb] using huv
  obtain ⟨_, _, hnu, _, _, _, hzeta, _, _⟩ := hP u v hpt S hS
  have hnuPos : 0 < |S.nu u v| := P.c_pos.trans_le hnu
  rw [abs_div]
  apply (div_le_div_iff₀ hnuPos P.c_pos).2
  calc
    |S.zeta u v| * P.c ≤ P.C * P.c :=
      mul_le_mul_of_nonneg_right hzeta P.c_pos.le
    _ ≤ P.C * |S.nu u v| :=
      mul_le_mul_of_nonneg_left hnu P.C_nonneg

/-- The usable incoming equation has a coefficient fixed by the numerical
package for every normalized comparison. -/
theorem UniformThresholdBounds.incomingCoeff_integral_small
    (P : UniformThresholdBounds) :
    ∃ J : ℝ, 0 ≤ J ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε →
          ∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε →
              -(∫ s in u..v, IsBVSolution.incomingCoeff S s v) ≤ J * ε := by
  let J := P.C / P.c
  have hJ : 0 ≤ J := div_nonneg P.C_nonneg P.c_pos.le
  refine ⟨J, hJ, ?_⟩
  intro D ha hb hP ε hε u v huv S hS hY
  have hquot : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ J := by
    intro s hs
    have hspt : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩
    exact P.zeta_div_nu_le D ha hb hP hspt S hS
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ D.U₁ ∩ D.U₂ := by
    intro s hs
    exact D.hT ((mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  rcases hS with rfl | rfl
  · have hineq := D.h₁.eq3_1b huv.2.1
      (fun s hs => (haccess s hs).1) hquot
    simpa only [IsBVSolution.incomingCoeff, J] using
      hineq.trans (mul_le_mul_of_nonneg_left hY hJ)
  · have hineq := D.h₂.eq3_1b huv.2.1
      (fun s hs => (haccess s hs).2) hquot
    simpa only [IsBVSolution.incomingCoeff, J] using
      hineq.trans (mul_le_mul_of_nonneg_left hY hJ)

end ChristodoulouBV.Uniqueness

end
