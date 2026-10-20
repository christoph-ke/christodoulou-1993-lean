module

public import ChristodoulouBV.Frozen.CausalPast

/-! Domains closed under the printed causal past. -/

@[expose] public section

namespace ChristodoulouBV

/-- Past closure in the regular wedge; relative openness is omitted by decision D3.
Christodoulou 1993, p. 1146; `source/transcription/s3-uniqueness.tex:7-17`. -/
def IsDomainOfDevelopment (U : Set (ℝ × ℝ)) : Prop :=
  U ⊆ {p | 0 ≤ p.1 ∧ p.1 < p.2} ∧
    ∀ p ∈ U, causalPast p.1 p.2 ⊆ U

end ChristodoulouBV

end
