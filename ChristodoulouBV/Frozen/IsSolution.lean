module

public import ChristodoulouBV.Frozen.DomainOfDevelopment
public import ChristodoulouBV.Frozen.FieldsTheta
public import ChristodoulouBV.Frozen.FieldsZeta
public import ChristodoulouBV.Frozen.OutSeg
public import ChristodoulouBV.Frozen.InSeg
public import ChristodoulouBV.Frozen.IntervalPrimitive
public import ChristodoulouBV.Frozen.AdjacentAxis

/-! The reduced characteristic system in integral form. -/

@[expose] public section

open scoped Topology

namespace ChristodoulouBV

/-- The reduced system on a domain of development, with regular-axis limits (D4).
Christodoulou 1993, (1.5), p. 1133 (with `r > 0` and `Ω > 0` on `Q`, p. 1132); (1.7), p. 1135;
(1.11)–(1.18), pp. 1137–1138; restriction to the causal past of `Γ`, where `∂r/∂v > 0`,
p. 1146; BV limit verification, pp. 1185–1187.
See `source/transcription/s1-introduction.tex:116-121,301-346` and
`source/transcription/s6-existence.tex:390-455`. -/
structure IsSolution (U : Set (ℝ × ℝ)) (S : Fields) : Prop where
  development : IsDomainOfDevelopment U
  radius_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
    IntervalPrimitive (S.r u) (S.lam u) a b
  radius_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
    IntervalPrimitive (fun u => S.r u v) (fun u => S.nu u v) a b
  scalar_radius_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
    IntervalPrimitive (fun v => S.r u v * S.phi u v) (S.alpha u) a b
  scalar_radius_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
    IntervalPrimitive (fun u => S.r u v * S.phi u v) (fun u => S.beta u v) a b
  mass_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
    IntervalPrimitive (S.m u)
      (fun v => (1 - 2 * S.m u v / S.r u v) * (S.theta u v) ^ 2 /
        (2 * S.lam u v)) a b
  mass_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
    IntervalPrimitive (fun u => S.m u v)
      (fun u => (1 - 2 * S.m u v / S.r u v) * (S.zeta u v) ^ 2 /
        (2 * S.nu u v)) a b
  lam_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
    IntervalPrimitive (fun u => S.lam u v)
      (fun u => (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) a b
  nu_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
    IntervalPrimitive (S.nu u)
      (fun v => (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) a b
  alpha_in : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
    IntervalPrimitive (fun u => S.alpha u v)
      (fun u => ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) a b
  beta_out : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
    IntervalPrimitive (S.beta u)
      (fun v => ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) a b
  radius_axis : ∀ a ∈ adjacentAxis U,
    Filter.Tendsto (S.r a)
      (nhdsWithin a (Set.Ioi a) ⊓ Filter.principal {v | (a, v) ∈ U}) (𝓝 (0 : ℝ))
  mass_axis : ∀ a ∈ adjacentAxis U,
    Filter.Tendsto (S.m a)
      (nhdsWithin a (Set.Ioi a) ⊓ Filter.principal {v | (a, v) ∈ U}) (𝓝 (0 : ℝ))
  radius_pos : ∀ p ∈ U, 0 < S.r p.1 p.2
  lam_pos : ∀ p ∈ U, 0 < S.lam p.1 p.2
  conformal : ∀ p ∈ U, ∃ Ω : ℝ, 0 < Ω ∧
    (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * Ω ^ 2 =
      -(4 * S.lam p.1 p.2 * S.nu p.1 p.2)

end ChristodoulouBV

end
