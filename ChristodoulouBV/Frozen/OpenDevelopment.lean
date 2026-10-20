module

public import Mathlib

/-! The printed open triangular development. -/

@[expose] public section

namespace ChristodoulouBV

/-- The literal open `𝒟(u₀,v₀)`.
Christodoulou 1993, p. 1148; `source/transcription/s3-uniqueness.tex:117-120`. -/
def openDevelopment (u₀ v₀ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Ioo u₀ v₀ ∧ p.2 ∈ Set.Ioo p.1 v₀}

end ChristodoulouBV

end
