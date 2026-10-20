module

public import ChristodoulouBV.Existence.C1FamilyExitTopology
import Mathlib.Tactic

/-!
# Uniform null-integral comparison at neighboring cutoffs

A uniform pointwise error in a nonnegative null density changes every
outgoing or incoming null integral by at most the same error on the unit
triangle. This comparison is independent of the characteristic slice.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- A uniform real error between integrands on a subinterval of `[0,1]`
changes the extended nonnegative null integral by at most that error. -/
theorem s6_lintegral_nearby {a b ε : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    {g₀ g₁ : ℝ → ℝ}
    (hclose : ∀ t ∈ Ioo a b, |g₁ t - g₀ t| ≤ ε) :
    (∫⁻ t in Ioo a b, ENNReal.ofReal (g₁ t)) ≤
      (∫⁻ t in Ioo a b, ENNReal.ofReal (g₀ t)) +
        ENNReal.ofReal ε := by
  have hmeasure : volume (Ioo a b) ≤ (1 : ℝ≥0∞) := by
    rw [Real.volume_Ioo]
    have hwidth : b - a ≤ 1 := by linarith only [ha, hb]
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_le_ofReal hwidth)
  calc
    (∫⁻ t in Ioo a b, ENNReal.ofReal (g₁ t)) ≤
        ∫⁻ t in Ioo a b,
          ENNReal.ofReal (g₀ t) + ENNReal.ofReal ε := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpoint := (abs_le.mp (hclose t ht)).2
      exact (ENNReal.ofReal_le_ofReal (by linarith only [hpoint])).trans
        ENNReal.ofReal_add_le
    _ = (∫⁻ t in Ioo a b, ENNReal.ofReal (g₀ t)) +
          ENNReal.ofReal ε * volume (Ioo a b) := by
      rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ (∫⁻ t in Ioo a b, ENNReal.ofReal (g₀ t)) +
          ENNReal.ofReal ε := by
      gcongr
      calc
        ENNReal.ofReal ε * volume (Ioo a b) ≤
            ENNReal.ofReal ε * 1 := by gcongr
        _ = ENNReal.ofReal ε := mul_one _

end ChristodoulouBV

end
