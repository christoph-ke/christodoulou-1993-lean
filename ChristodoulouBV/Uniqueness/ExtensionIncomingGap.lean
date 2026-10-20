module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Propagation of the tail gap across an incoming strip

Once the flux argument supplies a lower bound for `κ = λ/(1-μ)` and the
initial data supply an upper bound, the tail mass bound gives a lower bound
for `λ` throughout the incoming segment, and hence for `1-μ` there.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- At one outgoing coordinate, a lower quotient bound at a tail line and a
mass gap there imply a lower `λ` bound at all earlier incoming coordinates.
The needed monotonicity follows from the C¹ equations. -/
theorem lam_lower_of_tail_quotient_lower {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u u₁ v η c₁ : ℝ}
    (hu : 0 ≤ u) (hu₁ : u ≤ u₁) (hu₁v : u₁ < v) (hvb : v < b)
    (hc₁ : 0 ≤ c₁)
    (htail : 2 * S.m u₁ v / S.r u₁ v ≤ η)
    (hκ : c₁ ≤ S.lam u₁ v /
      (1 - 2 * S.m u₁ v / S.r u₁ v)) :
    (1 - η) * c₁ ≤ S.lam u v := by
  have hq₁ : 0 < 1 - 2 * S.m u₁ v / S.r u₁ v :=
    H.mass_gap_pos_of_c1 (p := (u₁, v)) ⟨hu.trans hu₁, hu₁v, hvb⟩
  have hqη : 1 - η ≤ 1 - 2 * S.m u₁ v / S.r u₁ v := by linarith
  have hκmul : c₁ * (1 - 2 * S.m u₁ v / S.r u₁ v) ≤ S.lam u₁ v :=
    (le_div_iff₀ hq₁).mp hκ
  have hlow : (1 - η) * c₁ ≤ S.lam u₁ v := by
    calc
      (1 - η) * c₁ = c₁ * (1 - η) := by ring
      _ ≤ c₁ * (1 - 2 * S.m u₁ v / S.r u₁ v) :=
        mul_le_mul_of_nonneg_left hqη hc₁
      _ ≤ S.lam u₁ v := hκmul
  exact hlow.trans (lam_antitone_on_incoming_of_c1 H hu hu₁ hu₁v hvb)

/-- The upper quotient bound converts the propagated `λ` bound into a
uniform lower mass gap. The hypotheses `c₁` and `K` are the bounds obtained
from the flux and initial-edge estimates for the incoming strip. -/
theorem mass_gap_lower_of_tail_quotient_bounds {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u u₁ v η c₁ K : ℝ}
    (hu : 0 ≤ u) (hu₁ : u ≤ u₁) (hu₁v : u₁ < v) (hvb : v < b)
    (hη : η < 1) (hc₁ : 0 < c₁) (hK : 0 < K)
    (htail : 2 * S.m u₁ v / S.r u₁ v ≤ η)
    (hκlower : c₁ ≤ S.lam u₁ v /
      (1 - 2 * S.m u₁ v / S.r u₁ v))
    (hκupper : S.lam u v /
      (1 - 2 * S.m u v / S.r u v) ≤ K) :
    0 < (1 - η) * c₁ / K ∧
      (1 - η) * c₁ / K ≤
        1 - 2 * S.m u v / S.r u v := by
  constructor
  · exact div_pos (mul_pos (by linarith) hc₁) hK
  have hq : 0 < 1 - 2 * S.m u v / S.r u v :=
    H.mass_gap_pos_of_c1 (p := (u, v)) ⟨hu, hu₁.trans_lt hu₁v, hvb⟩
  have hlam : (1 - η) * c₁ ≤ S.lam u v :=
    lam_lower_of_tail_quotient_lower H hu hu₁ hu₁v hvb hc₁.le htail hκlower
  have hupper : S.lam u v ≤ K * (1 - 2 * S.m u v / S.r u v) :=
    (div_le_iff₀ hq).mp hκupper
  apply (div_le_iff₀ hK).mpr
  calc
    (1 - η) * c₁ ≤ S.lam u v := hlam
    _ ≤ K * (1 - 2 * S.m u v / S.r u v) := hupper
    _ = (1 - 2 * S.m u v / S.r u v) * K := by ring

end ChristodoulouBV.Uniqueness

end
