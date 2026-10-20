module

public import ChristodoulouBV.Frozen.Fields

/-! Incoming scalar amplitude. -/

@[expose] public section

namespace ChristodoulouBV

/-- `ζ = β - νφ`, by (1.13) and (1.17).
Christodoulou 1993, p. 1137; `source/transcription/s1-introduction.tex:313-337`. -/
def Fields.zeta (S : Fields) (u v : ℝ) : ℝ :=
  S.beta u v - S.nu u v * S.phi u v

end ChristodoulouBV

end
