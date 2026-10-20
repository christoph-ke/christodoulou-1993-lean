module

public import ChristodoulouBV.Existence.BVBasicMean
public import ChristodoulouBV.ForMathlib.BoundedVariation.PointwiseLimit
import Mathlib.Tactic

/-!
# Variation contraction at a zero-radius endpoint

The compact weighted means approach the quotient of the two primitives
as their initial mass tends to zero. Lower semicontinuity then gives the
sharp BV bound on the open interval adjacent to the axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The BV weighted-mean contraction on an axis-anchored open interval.
Neither finite nor uniform variation of the quotient `N / r` is assumed.
The zero limits of both primitives remove the initial atom. -/
theorem bv_axis_weighted_variation_le
    {r N w q : ℝ → ℝ} {A B L M : ℝ}
    (hr : ∀ t ∈ Ioo A B, 0 < r t)
    (hw : ∀ t ∈ Ioo A B, 0 ≤ w t ∧ |w t| ≤ L)
    (hq : ∀ t ∈ Ioo A B, |q t| ≤ M)
    (hqBV : BoundedVariationOn q (Ioo A B))
    (hrprim : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo A B, x ≤ y → IntervalPrimitive r w x y)
    (hNprim : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo A B, x ≤ y →
      IntervalPrimitive N (fun t => w t * q t) x y)
    (hr0 : Tendsto r (𝓝[>] A) (𝓝 0)) (hN0 : Tendsto N (𝓝[>] A) (𝓝 0)) :
    eVariationOn (fun t => N t / r t) (Ioo A B) ≤ eVariationOn q (Ioo A B) := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  apply iSup_le
  rintro ⟨x, y⟩
  apply iSup_le
  rintro ⟨hx, hy, hxy⟩
  have hsub : Icc x y ⊆ Ioo A B := fun t ht =>
    ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
  rw [inter_eq_right.mpr hsub]
  have hB : A < B := hx.1.trans hx.2
  have hmul0 : Tendsto (fun c => r c * q c) (𝓝[>] A) (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [abs_zero, zero_mul] using hr0.abs.mul_const M)
    filter_upwards [Ioo_mem_nhdsGT hB] with c hc
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hq c hc) (abs_nonneg _)
  apply eVariationOn.le_of_tendsto_pointwise
    (F := fun c => bvWeightedMean r w c q)
    (p := 𝓝[>] A)
  · intro t ht
    have hlim := ((hmul0.add (tendsto_const_nhds (x := N t))).sub hN0).div_const (r t)
    have he : ∀ᶠ c in 𝓝[>] A,
        bvWeightedMean r w c q t = (r c * q c + N t - N c) / r t := by
      filter_upwards [Ioo_mem_nhdsGT (hx.1.trans_le ht.1)] with c hc
      have hcB : c ∈ Ioo A B := ⟨hc.1, hc.2.trans (hsub ht).2⟩
      rw [bvWeightedMean, ← (hNprim c hcB t (hsub ht) hc.2.le).2]
      congr 1
      ring
    apply (show Tendsto (fun c => (r c * q c + N t - N c) / r t)
      (𝓝[>] A) (𝓝 (N t / r t)) from by simpa only [zero_add, sub_zero] using hlim).congr'
    exact he.mono (fun _ hc => hc.symm)
  · filter_upwards [Ioo_mem_nhdsGT hx.1] with c hc
    have hcB : c ∈ Ioo A B := ⟨hc.1, hc.2.trans hx.2⟩
    have hcy : Icc c y ⊆ Ioo A B := fun t ht =>
      ⟨hc.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    calc
      eVariationOn (bvWeightedMean r w c q) (Icc x y) ≤
          eVariationOn (bvWeightedMean r w c q) (Icc c y) :=
        eVariationOn.mono _ (Icc_subset_Icc hc.2.le le_rfl)
      _ ≤ eVariationOn q (Icc c y) := bv_weighted_mean_variation_le
        (hc.2.le.trans hxy) (fun t ht => hr t (hcy ht))
        (hrprim c hcB y hy (hc.2.le.trans hxy)).1
        (fun t ht => hw t (hcy ht))
        (fun s hs t ht hst => (hrprim s (hcy hs) t (hcy ht) hst).2)
        (hqBV.mono hcy)
      _ ≤ eVariationOn q (Ioo A B) := eVariationOn.mono _ hcy

end ChristodoulouBV

end
