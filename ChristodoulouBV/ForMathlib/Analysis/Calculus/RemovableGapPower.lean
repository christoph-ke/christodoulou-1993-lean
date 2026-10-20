module

public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Continuous diagonal extensions of normalized gap powers

A uniform order-`n` diagonal expansion gives a continuous extension of the
quotient by the `n`th power of the coordinate gap. The argument uses the
expansion itself and does not differentiate the quotient.
-/

public section

open Set Filter
open scoped Topology

namespace intervalIntegral

/-- A quotient by a power of the coordinate gap with a prescribed diagonal
value. Its values below the diagonal are irrelevant to the closed triangle. -/
@[expose] noncomputable def gapPowerQuotient
    (n : ℕ) (f A : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then f p / (p.2 - p.1) ^ n else A p

/-- A uniform diagonal expansion makes its normalized gap quotient
continuous on the whole closed coordinate triangle. -/
theorem continuousOn_gapPowerQuotient_of_uniform_axis
    {a b : ℝ} {n : ℕ} {f A : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hA : ContinuousOn A (closedCoordTriangle a b))
    (haxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ closedCoordTriangle a b, p.2 - p.1 < δ →
        |f p - A p * (p.2 - p.1) ^ n| ≤
          ε * (p.2 - p.1) ^ n) :
    ContinuousOn (gapPowerQuotient n f A) (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let d : ℝ × ℝ → ℝ := fun p => p.2 - p.1
  let q := gapPowerQuotient n f A
  have hdcont : ContinuousOn d K := by fun_prop
  intro p hp
  by_cases hstrict : p.1 < p.2
  · have hdne : d p ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hstrict.ne')
    have hquot : ContinuousWithinAt (fun z => f z / d z ^ n) K p :=
      (hf.continuousWithinAt hp).div ((hdcont.pow n).continuousWithinAt hp) hdne
    have hlt : IsOpen {z : ℝ × ℝ | z.1 < z.2} :=
      isOpen_lt continuous_fst continuous_snd
    have hnhds : {z : ℝ × ℝ | z.1 < z.2} ∈ 𝓝[K] p :=
      nhdsWithin_le_nhds (hlt.mem_nhds hstrict)
    have hevent : q =ᶠ[𝓝[K] p] (fun z => f z / d z ^ n) := by
      filter_upwards [hnhds] with z hz
      simp [q, gapPowerQuotient, d, hz]
    exact hquot.congr_of_eventuallyEq hevent (hevent.self_of_nhdsWithin hp)
  · have hcoords : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have heq : p.1 = p.2 := le_antisymm hcoords.2.1 (le_of_not_gt hstrict)
    have hqaxis : q p = A p := by simp [q, gapPowerQuotient, hstrict]
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hε₂ : 0 < ε / 2 := by positivity
    obtain ⟨δaxis, hδaxis, hbound⟩ := haxis (ε / 2) hε₂
    obtain ⟨δgap, hδgap, hgap⟩ :=
      Metric.continuousWithinAt_iff.mp (hdcont.continuousWithinAt hp)
        δaxis hδaxis
    obtain ⟨δA, hδA, hAclose⟩ :=
      Metric.continuousWithinAt_iff.mp (hA.continuousWithinAt hp)
        (ε / 2) hε₂
    refine ⟨min δgap δA, lt_min hδgap hδA, ?_⟩
    intro z hzK hzdist
    have hzcoord : a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := hzK
    have hdz : 0 ≤ d z := sub_nonneg.mpr hzcoord.2.1
    have hdp : d p = 0 := by simp [d, heq]
    have hzdaxis : d z < δaxis := by
      have hh := hgap hzK (lt_of_lt_of_le hzdist (min_le_left _ _))
      simpa only [Real.dist_eq, hdp, sub_zero, abs_of_nonneg hdz] using hh
    have hAz : |A z - A p| < ε / 2 := by
      have hh := hAclose hzK (lt_of_lt_of_le hzdist (min_le_right _ _))
      simpa only [Real.dist_eq] using hh
    have hqA : |q z - A z| ≤ ε / 2 := by
      by_cases hzstrict : z.1 < z.2
      · have hdpos : 0 < d z := sub_pos.mpr hzstrict
        have hpow : 0 < d z ^ n := pow_pos hdpos n
        have h := hbound z hzK hzdaxis
        change |f z - A z * d z ^ n| ≤ ε / 2 * d z ^ n at h
        have hid : q z - A z =
            (f z - A z * d z ^ n) / d z ^ n := by
          simp only [q, gapPowerQuotient, hzstrict, ↓reduceIte]
          change f z / d z ^ n - A z =
            (f z - A z * d z ^ n) / d z ^ n
          field_simp [hpow.ne']
        rw [hid, abs_div, abs_of_pos hpow]
        exact (div_le_iff₀ hpow).2 h
      · have hqz : q z = A z := by simp [q, gapPowerQuotient, hzstrict]
        simp [hqz, le_of_lt hε₂]
    have htri : |q z - q p| ≤ |q z - A z| + |A z - A p| := by
      rw [hqaxis]
      have hid : q z - A p = (q z - A z) + (A z - A p) := by ring
      rw [hid]
      exact abs_add_le _ _
    have hfinal : |q z - q p| < ε := by linarith only [htri, hqA, hAz]
    simpa only [Real.dist_eq] using hfinal

end intervalIntegral

end
