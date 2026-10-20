module

public import ChristodoulouBV.Frozen.Fields

/-! Outgoing scalar amplitude. -/

@[expose] public section

namespace ChristodoulouBV

/-- `θ = α - λφ`, by (1.13) and (1.17).
Christodoulou 1993, p. 1137; `source/transcription/s1-introduction.tex:313-337`. -/
def Fields.theta (S : Fields) (u v : ℝ) : ℝ :=
  S.alpha u v - S.lam u v * S.phi u v

end ChristodoulouBV

end
