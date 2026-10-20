module

public import ChristodoulouBV.Frozen.IsSolution
public import ChristodoulouBV.Frozen.AxisVanishingVariation

/-! The six defining BV conditions in Section 3. -/

@[expose] public section

open scoped Topology

namespace ChristodoulouBV

/-- Christodoulou's original BV class, without a right-continuity convention (D5).
The constants express uniformity over the whole domain.
Christodoulou 1993, pp. 1146–1147;
`source/transcription/s3-uniqueness.tex:19-50`. -/
structure IsBVSolution (U : Set (ℝ × ℝ)) (S : Fields) : Prop where
  solution : IsSolution U S
  nu_bounded_below : ∃ N : ℝ, ∀ p ∈ U, -S.nu p.1 p.2 ≤ N
  lam_bounded_below : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ U, c ≤ S.lam p.1 p.2
  item1 : ∃ C : ℝ,
    (∀ u, eVariationOn (S.lam u) {v | (u, v) ∈ U} ≤ ENNReal.ofReal C) ∧
    (∀ v, eVariationOn (fun u => S.nu u v) {u | (u, v) ∈ U} ≤ ENNReal.ofReal C)
  item2 : ∀ a ∈ adjacentAxis U,
    Filter.Tendsto (fun v => S.nu a v + S.lam a v)
      (nhdsWithin a (Set.Ioi a) ⊓ Filter.principal {v | (a, v) ∈ U}) (𝓝 (0 : ℝ))
  item3_ac_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
    AbsolutelyContinuousOnInterval (S.phi u) a b
  item3_ac_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
    AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b
  item3_variation : ∃ C : ℝ,
    (∀ u, eVariationOn (S.phi u) {v | (u, v) ∈ U} ≤ ENNReal.ofReal C) ∧
    (∀ v, eVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U} ≤ ENNReal.ofReal C)
  item4 : ∀ a ∈ adjacentAxis U, AxisVanishingVariation U S a
  item5 : ∃ C : ℝ,
    (∀ u, eVariationOn (S.theta u) {v | (u, v) ∈ U} ≤ ENNReal.ofReal C) ∧
    (∀ v, eVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U} ≤ ENNReal.ofReal C)
  item6 : ∀ a ∈ adjacentAxis U,
    Filter.Tendsto (fun v => S.alpha a v + S.beta a v)
      (nhdsWithin a (Set.Ioi a) ⊓ Filter.principal {v | (a, v) ∈ U}) (𝓝 (0 : ℝ))

end ChristodoulouBV

end
