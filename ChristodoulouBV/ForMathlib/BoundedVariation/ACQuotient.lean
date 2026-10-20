module

public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus

/-!
# Quotients of absolutely continuous functions with positive denominator

The positive lower bound needed for the standard quotient theorem follows
automatically from compactness of the closed interval.
-/

public section

open Set

namespace AbsolutelyContinuousOnInterval

/-- A quotient of two absolutely continuous real functions is absolutely
continuous when the denominator is positive on the interval. -/
theorem div_of_pos {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hpos : ∀ x ∈ Icc a b, 0 < g x) :
    AbsolutelyContinuousOnInterval (fun x => f x / g x) a b := by
  have hcont : ContinuousOn g (Icc a b) := by
    simpa only [uIcc_of_le hab] using hg.continuousOn
  obtain ⟨c, hc, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont
  have hcpos : 0 < g c := hpos c hc
  apply (hf.div_and_ae_deriv hg hcpos ?_).1
  intro x hx
  rw [uIcc_of_le hab] at hx
  rw [abs_of_pos (hpos x hx)]
  exact hmin hx

end AbsolutelyContinuousOnInterval

end
