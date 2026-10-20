module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-!
# Contraction of two nonnegative variation bounds

This is the numerical absorption step used after the two residual
limits in (6.9) and (6.12). The section estimates themselves are not
premises of a claimed source-facing existence theorem here.
-/

public section

open Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Absorb a pair of real nonnegative bounds with a common coefficient
strictly below one. -/
theorem coupled_variation_bounds
    {A B R S κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hA : A ≤ R + κ * B) (hB : B ≤ S + κ * A) :
    A ≤ (R + κ * S) / (1 - κ ^ 2) ∧
      B ≤ (S + κ * R) / (1 - κ ^ 2) := by
  have hden : 0 < 1 - κ ^ 2 := by
    nlinarith only [hκ0, hκ1]
  have hmulA := mul_le_mul_of_nonneg_left hA hκ0
  have hmulB := mul_le_mul_of_nonneg_left hB hκ0
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith only [hA, hmulB]
  · apply (le_div_iff₀ hden).mpr
    nlinarith only [hB, hmulA]

/-- Two vanishing residuals force both nonnegative quantities to tend
to zero once their coupled coefficient is strictly below one. -/
theorem tendsto_zero_of_coupled_variation_bounds
    {ι : Type*} {L : Filter ι} {A B R S : ι → ℝ} {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hA0 : ∀ᶠ i in L, 0 ≤ A i) (hB0 : ∀ᶠ i in L, 0 ≤ B i)
    (hA : ∀ᶠ i in L, A i ≤ R i + κ * B i)
    (hB : ∀ᶠ i in L, B i ≤ S i + κ * A i)
    (hR : Tendsto R L (𝓝 0)) (hS : Tendsto S L (𝓝 0)) :
    Tendsto A L (𝓝 0) ∧ Tendsto B L (𝓝 0) := by
  have hupperA : Tendsto (fun i => (R i + κ * S i) / (1 - κ ^ 2)) L (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_div] using
      (hR.add (tendsto_const_nhds.mul hS)).div_const (1 - κ ^ 2)
  have hupperB : Tendsto (fun i => (S i + κ * R i) / (1 - κ ^ 2)) L (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_div] using
      (hS.add (tendsto_const_nhds.mul hR)).div_const (1 - κ ^ 2)
  have hb : ∀ᶠ i in L,
      A i ≤ (R i + κ * S i) / (1 - κ ^ 2) ∧
        B i ≤ (S i + κ * R i) / (1 - κ ^ 2) := by
    filter_upwards [hA, hB] with i hiA hiB
    exact coupled_variation_bounds hκ0 hκ1 hiA hiB
  exact ⟨squeeze_zero' hA0 (hb.mono fun _ hi => hi.1) hupperA,
    squeeze_zero' hB0 (hb.mono fun _ hi => hi.2) hupperB⟩

/-- Coupled absorption for extended variations. Finiteness is needed only
eventually; both residual limits imply their eventual finiteness automatically. -/
theorem tendsto_zero_of_coupled_ennreal_variation_bounds
    {ι : Type*} {L : Filter ι} {A B R S : ι → ℝ≥0∞} {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hAfin : ∀ᶠ i in L, A i ≠ ∞) (hBfin : ∀ᶠ i in L, B i ≠ ∞)
    (hA : ∀ᶠ i in L, A i ≤ 3 * R i + ENNReal.ofReal κ * B i)
    (hB : ∀ᶠ i in L, B i ≤ S i + ENNReal.ofReal κ * A i)
    (hR : Tendsto R L (𝓝 0)) (hS : Tendsto S L (𝓝 0)) :
    Tendsto A L (𝓝 0) ∧ Tendsto B L (𝓝 0) := by
  have hRfin : ∀ᶠ i in L, R i ≠ ∞ := by
    filter_upwards [hR.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)]
      with i hi
    exact ne_of_lt (hi.trans (by norm_num))
  have hSfin : ∀ᶠ i in L, S i ≠ ∞ := by
    filter_upwards [hS.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)]
      with i hi
    exact ne_of_lt (hi.trans (by norm_num))
  have hAR : ∀ᶠ i in L, (A i).toReal ≤ 3 * (R i).toReal + κ * (B i).toReal := by
    filter_upwards [hA, hRfin, hBfin] with i hi hRi hBi
    have hh := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hRi,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBi⟩) hi
    simpa only [ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num : (3 : ℝ≥0∞) ≠ ∞) hRi)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBi), ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hκ0] using hh
  have hBR : ∀ᶠ i in L, (B i).toReal ≤ (S i).toReal + κ * (A i).toReal := by
    filter_upwards [hB, hSfin, hAfin] with i hi hSi hAi
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hSi,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAi⟩) hi
    simpa only [ENNReal.toReal_add hSi (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAi),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ0] using hh
  have hRt : Tendsto (fun i => 3 * (R i).toReal) L (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero, mul_zero] using
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hR).const_mul 3
  have hSt : Tendsto (fun i => (S i).toReal) L (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS
  have ht := tendsto_zero_of_coupled_variation_bounds hκ0 hκ1
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hAR hBR hRt hSt
  constructor
  · have hh := (ENNReal.continuous_ofReal.tendsto 0).comp ht.1
    simp only [ENNReal.ofReal_zero] at hh
    exact hh.congr' (hAfin.mono fun i hi => ENNReal.ofReal_toReal hi)
  · have hh := (ENNReal.continuous_ofReal.tendsto 0).comp ht.2
    simp only [ENNReal.ofReal_zero] at hh
    exact hh.congr' (hBfin.mono fun i hi => ENNReal.ofReal_toReal hi)

end ChristodoulouBV

end
