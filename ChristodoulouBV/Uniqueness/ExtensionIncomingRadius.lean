module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-!
# Radius lower bounds on the off-axis rectangle

The frozen radius primitives and the signs of `ν` and `λ` compare each point
of a finite rectangle to its lower right corner. Compatibility will later
make that corner independent of the cutoff member.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- The radius decreases along an incoming segment of one C¹ member. -/
theorem radius_antitone_on_incoming_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {a c v : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hcv : c < v) (hvb : v < b) :
    S.r c v ≤ S.r a v := by
  have hseg : inSeg v a c ⊆ developmentWithInitialEdge b := by
    intro p hp
    obtain ⟨x, y⟩ := p
    change x ∈ Icc a c ∧ y ∈ ({v} : Set ℝ) at hp
    rcases hp with ⟨hx, rfl⟩
    exact ⟨ha.trans hx.1, hx.2.trans_lt hcv, hvb⟩
  obtain ⟨_, hEq⟩ := H.solution.radius_in v a c hac hseg
  have hneg : 0 ≤ ∫ s in a..c, -(S.nu s v) := by
    apply intervalIntegral.integral_nonneg hac
    intro s hs
    have hp : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨ha.trans hs.1, hs.2.trans_lt hcv, hvb⟩
    exact (neg_pos.mpr (H.reduced_signs_of_c1 hp).1).le
  simp only [intervalIntegral.integral_neg] at hneg
  linarith only [hEq, hneg]

/-- The radius increases along an outgoing segment of one C¹ member. -/
theorem radius_monotone_on_outgoing_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u a c : ℝ} (hu : 0 ≤ u) (hua : u < a) (hac : a ≤ c) (hcb : c < b) :
    S.r u a ≤ S.r u c := by
  have hseg : outSeg u a c ⊆ developmentWithInitialEdge b := by
    intro p hp
    obtain ⟨x, y⟩ := p
    change x ∈ ({u} : Set ℝ) ∧ y ∈ Icc a c at hp
    rcases hp with ⟨rfl, hy⟩
    exact ⟨hu, hua.trans_le hy.1, hy.2.trans_lt hcb⟩
  obtain ⟨_, hEq⟩ := H.solution.radius_out u a c hac hseg
  have hpos : 0 ≤ ∫ s in a..c, S.lam u s := by
    apply intervalIntegral.integral_nonneg hac
    intro s hs
    exact (H.solution.lam_pos (u, s)
      ⟨hu, hua.trans_le hs.1, hs.2.trans_lt hcb⟩).le
  linarith only [hEq, hpos]

/-- Every point of an off-axis rectangle has radius at least the radius at
its lower right corner, with no estimate depending on the top cutoff. -/
theorem radius_lower_on_offaxis_rectangle_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u u₁ vBar v : ℝ}
    (hu : 0 ≤ u) (hu₁ : u ≤ u₁) (hu₁v : u₁ < vBar)
    (hv : vBar ≤ v) (hvb : v < b) :
    S.r u₁ vBar ≤ S.r u v := by
  calc
    S.r u₁ vBar ≤ S.r u₁ v :=
      radius_monotone_on_outgoing_of_c1 H (hu.trans hu₁) hu₁v hv hvb
    _ ≤ S.r u v :=
      radius_antitone_on_incoming_of_c1 H hu hu₁ (hu₁v.trans_le hv) hvb

end ChristodoulouBV.Uniqueness

end
