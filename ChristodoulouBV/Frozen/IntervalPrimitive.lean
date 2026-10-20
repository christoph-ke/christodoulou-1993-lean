module

public import Mathlib

/-! Null primitives in integral form at BV regularity. -/

@[expose] public section

namespace ChristodoulouBV

/-- `f` has interval-integrable primitive density `g` on `[a,b]` (D4).
Christodoulou 1993, pp. 1185–1187; `source/transcription/s6-existence.tex:390-455`. -/
def IntervalPrimitive (f g : ℝ → ℝ) (a b : ℝ) : Prop :=
  IntervalIntegrable g MeasureTheory.volume a b ∧
    f b - f a = ∫ x in a..b, g x

end ChristodoulouBV

end
