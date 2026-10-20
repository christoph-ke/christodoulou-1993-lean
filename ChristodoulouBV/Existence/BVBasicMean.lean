module

public import ChristodoulouBV.Existence.RadiusLimitCore
public import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
import Mathlib.Tactic

/-!
# Weighted BV averages on a compact interval

A positive primitive supplies the weight and an initial atom. Jordan
decomposition reduces variation contraction to monotonicity of averages.
No variation assumption on the averaged function is used as an input.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- A weighted mean with initial mass `r c` and initial value `f c`. -/
@[expose] noncomputable def bvWeightedMean (r w : ℝ → ℝ) (c : ℝ)
    (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (r c * f c + ∫ s in c..t, w s * f s) / r t

private theorem weighted_product_integrable {w f : ℝ → ℝ} {c b L : ℝ}
    (hcb : c ≤ b) (hw : IntervalIntegrable w volume c b)
    (hwb : ∀ t ∈ Icc c b, |w t| ≤ L)
    (hf : IntervalIntegrable f volume c b) :
    IntervalIntegrable (fun t => w t * f t) volume c b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hcb] at hw hf ⊢
  exact hf.bdd_mul hw.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs] using hwb t ht)

/-- A positive weighted average of a monotone function is monotone and
stays between its endpoint values. The initial atom is included. -/
theorem bv_weighted_mean_monotone_on
    {r w f : ℝ → ℝ} {c b L : ℝ} (hcb : c ≤ b)
    (hr : ∀ t ∈ Icc c b, 0 < r t)
    (hw : IntervalIntegrable w volume c b)
    (hwb : ∀ t ∈ Icc c b, 0 ≤ w t ∧ |w t| ≤ L)
    (hprim : ∀ x ∈ Icc c b, ∀ y ∈ Icc c b, x ≤ y →
      r y - r x = ∫ t in x..y, w t)
    (hf : MonotoneOn f (Icc c b)) :
    MonotoneOn (bvWeightedMean r w c f) (Icc c b) ∧
      ∀ t ∈ Icc c b, f c ≤ bvWeightedMean r w c f t ∧
        bvWeightedMean r w c f t ≤ f t := by
  have hc : c ∈ Icc c b := ⟨le_rfl, hcb⟩
  have hfint : IntervalIntegrable f volume c b :=
    (show MonotoneOn f (uIcc c b) by rwa [uIcc_of_le hcb]).intervalIntegrable
  have hprod := weighted_product_integrable hcb hw (fun t ht => (hwb t ht).2) hfint
  have hsub {x y : ℝ} (hx : x ∈ Icc c b) (hy : y ∈ Icc c b) :
      uIcc x y ⊆ uIcc c b := by
    rw [uIcc_of_le hcb]
    exact uIcc_subset_Icc hx hy
  have hbnd (t : ℝ) (ht : t ∈ Icc c b) :
      f c ≤ bvWeightedMean r w c f t ∧ bvWeightedMean r w c f t ≤ f t := by
    have hwi := hw.mono_set (hsub hc ht)
    have hpi := hprod.mono_set (hsub hc ht)
    have hlo : f c * (∫ s in c..t, w s) ≤ ∫ s in c..t, w s * f s := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on ht.1 (hwi.const_mul _) hpi
      intro s hs
      have hs' : s ∈ Icc c b := ⟨hs.1, hs.2.trans ht.2⟩
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hf hc hs' hs.1) (hwb s hs').1
    have hhi : (∫ s in c..t, w s * f s) ≤ f t * (∫ s in c..t, w s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on ht.1 hpi (hwi.const_mul _)
      intro s hs
      have hs' : s ∈ Icc c b := ⟨hs.1, hs.2.trans ht.2⟩
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hf hs' ht hs.2) (hwb s hs').1
    have hp := hprim c hc t ht ht.1
    rw [← hp] at hlo hhi
    constructor
    · rw [bvWeightedMean, le_div_iff₀ (hr t ht)]
      nlinarith only [hlo]
    · rw [bvWeightedMean, div_le_iff₀ (hr t ht)]
      nlinarith only [hhi, mul_le_mul_of_nonneg_left (hf hc ht ht.1) (hr c hc).le]
  refine ⟨?_, hbnd⟩
  intro x hx y hy hxy
  have hwi := hw.mono_set (hsub hx hy)
  have hpi := hprod.mono_set (hsub hx hy)
  have hA := (hbnd x hx).2
  have hinc : bvWeightedMean r w c f x * (∫ s in x..y, w s) ≤
      ∫ s in x..y, w s * f s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hxy (hwi.const_mul _) hpi
    intro s hs
    have hs' : s ∈ Icc c b := ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (hA.trans (hf hx hs' hs.1)) (hwb s hs').1
  have hp := hprim x hx y hy hxy
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hprod.mono_set (hsub hc hx)) hpi
  have hAx : bvWeightedMean r w c f x * r x =
      r c * f c + ∫ s in c..x, w s * f s := by
    rw [bvWeightedMean, div_mul_cancel₀ _ (hr x hx).ne']
  change bvWeightedMean r w c f x ≤
    (r c * f c + ∫ s in c..y, w s * f s) / r y
  rw [le_div_iff₀ (hr y hy)]
  rw [← hp] at hinc
  nlinarith only [hinc, hp, hadd, hAx]

/-- Weighted averaging contracts pointwise BV variation on a closed
interval. All regularity is imposed on the weight and the input quotient;
the variation of the average is a conclusion. -/
theorem bv_weighted_mean_variation_le
    {r w f : ℝ → ℝ} {c b L : ℝ} (hcb : c ≤ b)
    (hr : ∀ t ∈ Icc c b, 0 < r t)
    (hw : IntervalIntegrable w volume c b)
    (hwb : ∀ t ∈ Icc c b, 0 ≤ w t ∧ |w t| ≤ L)
    (hprim : ∀ x ∈ Icc c b, ∀ y ∈ Icc c b, x ≤ y →
      r y - r x = ∫ t in x..y, w t)
    (hf : BoundedVariationOn f (Icc c b)) :
    eVariationOn (bvWeightedMean r w c f) (Icc c b) ≤ eVariationOn f (Icc c b) := by
  obtain ⟨p, q, hp, hq, hfpq, hsum⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  have hc : c ∈ Icc c b := ⟨le_rfl, hcb⟩
  have hb : b ∈ Icc c b := ⟨hcb, le_rfl⟩
  obtain ⟨hmp, hpbound⟩ := bv_weighted_mean_monotone_on hcb hr hw hwb hprim hp
  obtain ⟨hmq, hqbound⟩ := bv_weighted_mean_monotone_on hcb hr hw hwb hprim hq
  have hpint : IntervalIntegrable p volume c b :=
    (show MonotoneOn p (uIcc c b) by rwa [uIcc_of_le hcb]).intervalIntegrable
  have hqint : IntervalIntegrable q volume c b :=
    (show MonotoneOn q (uIcc c b) by rwa [uIcc_of_le hcb]).intervalIntegrable
  have hwp := weighted_product_integrable hcb hw (fun t ht => (hwb t ht).2) hpint
  have hwq := weighted_product_integrable hcb hw (fun t ht => (hwb t ht).2) hqint
  have heq : EqOn (bvWeightedMean r w c f)
      (bvWeightedMean r w c p - bvWeightedMean r w c q) (Icc c b) := by
    intro t ht
    have hs : uIcc c t ⊆ uIcc c b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hcb]
      exact Icc_subset_Icc le_rfl ht.2
    rw [hfpq]
    simp only [bvWeightedMean, Pi.sub_apply, mul_sub, Pi.sub_apply,
      intervalIntegral.integral_sub (hwp.mono_set hs) (hwq.mono_set hs)]
    ring
  have hpV : eVariationOn (bvWeightedMean r w c p) (Icc c b) ≤
      ENNReal.ofReal (p b - p c) := by
    have he := hmp.eVariationOn_eq hc hb
    rw [inter_self] at he
    rw [he]
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub (hpbound b hb).2 (hpbound c hc).1)
  have hqV : eVariationOn (bvWeightedMean r w c q) (Icc c b) ≤
      ENNReal.ofReal (q b - q c) := by
    have he := hmq.eVariationOn_eq hc hb
    rw [inter_self] at he
    rw [he]
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub (hqbound b hb).2 (hqbound c hc).1)
  calc
    _ = eVariationOn (bvWeightedMean r w c p - bvWeightedMean r w c q) (Icc c b) :=
      eVariationOn.congr heq
    _ ≤ eVariationOn (bvWeightedMean r w c p) (Icc c b) +
        eVariationOn (bvWeightedMean r w c q) (Icc c b) := eVariationOn.sub_le _ _ _
    _ ≤ ENNReal.ofReal (p b - p c) + ENNReal.ofReal (q b - q c) :=
      add_le_add hpV hqV
    _ = ENNReal.ofReal ((p b - p c) + (q b - q c)) :=
      (ENNReal.ofReal_add (sub_nonneg.mpr (hp hc hb hcb))
        (sub_nonneg.mpr (hq hc hb hcb))).symm
    _ = eVariationOn f (Icc c b) := by
      rw [hsum c hc b hb, variationOnFromTo.eq_of_le f (Icc c b) hcb,
        inter_self, ENNReal.ofReal_toReal hf]

end ChristodoulouBV

end
