module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
public import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Variation and absolute continuity on a real interval

This file relates the variation of a real function on a compact interval to the integral of
the absolute value of its derivative. It also records the invariance of variation under removal
of endpoints at which the function is continuous.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace eVariationOn

/-- Removing both endpoints of a real interval does not change the variation of a
function continuous on that interval. -/
theorem Ioo_eq_Icc_of_continuousOn {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    eVariationOn f (Ioo a b) = eVariationOn f (Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hb : ContinuousWithinAt f (Ioi a ∩ Iic b) b := by
    exact (hf.continuousWithinAt ⟨hab.le, le_rfl⟩).mono (by grind)
  have hnb : (𝓝[Ioi a ∩ Iio b] b).NeBot := by
    rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (Ioi_mem_nhds hab))]
    infer_instance
  have hna : (𝓝[Iic b ∩ Ioi a] a).NeBot := by
    rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (Iic_mem_nhds hab))]
    infer_instance
  have ha : ContinuousWithinAt f (Iic b ∩ Ici a) a := by
    simpa only [Iic_inter_Ici] using hf.continuousWithinAt ⟨le_rfl, hab.le⟩
  calc
    eVariationOn f (Ioo a b) = eVariationOn f (Ioc a b) := by
      simpa only [Ioi_inter_Iio, Ioi_inter_Iic] using
        (eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hnb hb)
    _ = eVariationOn f (Icc a b) := by
      simpa only [Iic_inter_Ioi, Iic_inter_Ici] using
        (eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt hna ha)

end eVariationOn

namespace BoundedVariationOn

/-- For a real function of bounded variation, the integral of the absolute derivative is bounded
by its total variation. Equality need not hold without absolute continuity. -/
theorem integral_abs_deriv_le_eVariationOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) :
    ∫ x in a..b, |deriv f x| ≤ (eVariationOn f (Icc a b)).toReal := by
  obtain ⟨p, q, hp, hq, hfp, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  have hp' : MonotoneOn p (uIcc a b) := by simpa only [uIcc_of_le hab] using hp
  have hq' : MonotoneOn q (uIcc a b) := by simpa only [uIcc_of_le hab] using hq
  have hf' : BoundedVariationOn f (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hf
  have hpi : IntervalIntegrable (deriv p) volume a b := by
    exact hp'.intervalIntegrable_deriv
  have hqi : IntervalIntegrable (deriv q) volume a b := by
    exact hq'.intervalIntegrable_deriv
  have hfi : IntervalIntegrable (deriv f) volume a b := by
    exact hf'.intervalIntegrable_deriv
  have hpbv : BoundedVariationOn p (Icc a b) := by
    simpa only [inter_self] using
      (hp.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩)
  have hqbv : BoundedVariationOn q (Icc a b) := by
    simpa only [inter_self] using
      (hq.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩)
  have hpbv' : BoundedVariationOn p (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hpbv
  have hqbv' : BoundedVariationOn q (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hqbv
  have hae : ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv f x| ≤ deriv p x + deriv q x := by
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hpbv'.ae_differentiableAt_of_mem_uIcc,
      hqbv'.ae_differentiableAt_of_mem_uIcc] with x hpx hqx hx
    have hx' : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have hpx' := hpx (by simpa only [uIcc_of_le hab] using hx')
    have hqx' := hqx (by simpa only [uIcc_of_le hab] using hx')
    have hp0 : 0 ≤ deriv p x := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      exact hp.derivWithin_nonneg
    have hq0 : 0 ≤ deriv q x := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
      exact hq.derivWithin_nonneg
    have heq : deriv f x = deriv p x - deriv q x := by
      rw [hfp]
      exact (hpx'.hasDerivAt.sub hqx'.hasDerivAt).deriv
    rw [heq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpbound : ∫ x in a..b, deriv p x ≤ p b - p a := by
    have h := hp'.intervalIntegral_deriv_mem_uIcc
    rw [uIcc_of_le (sub_nonneg.mpr (hp ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))] at h
    exact h.2
  have hqbound : ∫ x in a..b, deriv q x ≤ q b - q a := by
    have h := hq'.intervalIntegral_deriv_mem_uIcc
    rw [uIcc_of_le (sub_nonneg.mpr (hq ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))] at h
    exact h.2
  calc
    ∫ x in a..b, |deriv f x| ≤ ∫ x in a..b, (deriv p x + deriv q x) :=
      intervalIntegral.integral_mono_ae_restrict hab hfi.abs (hpi.add hqi) hae
    _ = (∫ x in a..b, deriv p x) + ∫ x in a..b, deriv q x :=
      intervalIntegral.integral_add hpi hqi
    _ ≤ (p b - p a) + (q b - q a) := add_le_add hpbound hqbound
    _ = (eVariationOn f (Icc a b)).toReal := by
      rw [hpq a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩,
        variationOnFromTo.eq_of_le _ _ hab]
      simp only [inter_self]

end BoundedVariationOn

namespace AbsolutelyContinuousOnInterval

/-- On a real interval, the total variation of an absolutely continuous function is the
integral of the absolute value of its derivative. -/
theorem eVariationOn_eq_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, |deriv f x|) := by
  have hfi : IntervalIntegrable (fun x ↦ |deriv f x|) volume a b :=
    hf.intervalIntegrable_deriv.abs
  have hfv : BoundedVariationOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.boundedVariationOn
  have hle : ∫ x in a..b, |deriv f x| ≤ (eVariationOn f (Icc a b)).toReal :=
    hfv.integral_abs_deriv_le_eVariationOn hab
  have hupper : eVariationOn f (Icc a b) ≤
      ENNReal.ofReal (∫ x in a..b, |deriv f x|) := by
    rw [eVariationOn]
    refine iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_
    have hmem (i : ℕ) : a ≤ u i ∧ u i ≤ b := hus i
    have hpiece (i : ℕ) :
        |f (u (i + 1)) - f (u i)| ≤
          ∫ x in u i..u (i + 1), |deriv f x| := by
      have hsub : uIcc (u i) (u (i + 1)) ⊆ uIcc a b := by
        rw [uIcc_of_le (hu (Nat.le_succ i)), uIcc_of_le hab]
        exact Icc_subset_Icc (hmem i).1 (hmem (i + 1)).2
      have hfac := hf.mono hsub
      rw [← hfac.integral_deriv_eq_sub]
      exact intervalIntegral.abs_integral_le_integral_abs (hu (Nat.le_succ i))
    have hsum :
        (∑ i ∈ Finset.range n, |f (u (i + 1)) - f (u i)|) ≤
          ∫ x in a..b, |deriv f x| := by
      calc
        _ ≤ ∑ i ∈ Finset.range n,
            ∫ x in u i..u (i + 1), |deriv f x| :=
          Finset.sum_le_sum fun i _ ↦ hpiece i
        _ = ∫ x in u 0..u n, |deriv f x| := by
          apply intervalIntegral.sum_integral_adjacent_intervals
          intro i hi
          apply hfi.mono_set
          rw [uIcc_of_le (hu (Nat.le_succ i)), uIcc_of_le hab]
          exact Icc_subset_Icc (hmem i).1 (hmem (i + 1)).2
        _ ≤ ∫ x in a..b, |deriv f x| := by
          apply intervalIntegral.integral_mono_interval (hmem 0).1 (hu (Nat.zero_le n))
            (hmem n).2 _ hfi
          exact Filter.Eventually.of_forall (fun x ↦ abs_nonneg _)
    have hed (i : ℕ) :
        edist (f (u (i + 1))) (f (u i)) =
          ENNReal.ofReal |f (u (i + 1)) - f (u i)| := by
      rw [edist_dist, Real.dist_eq]
    simp_rw [hed]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hsum
  exact le_antisymm hupper <| by
    rw [← ENNReal.ofReal_toReal hfv]
    exact ENNReal.ofReal_le_ofReal hle

/-- The variation of an absolutely continuous function on an open interval equals its
integrated absolute derivative, including when the interval is empty. -/
theorem eVariationOn_Ioo_eq_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    eVariationOn f (Ioo a b) = ENNReal.ofReal (∫ x in a..b, |deriv f x|) := by
  have hcont : ContinuousOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.continuousOn
  rw [eVariationOn.Ioo_eq_Icc_of_continuousOn hab hcont,
    hf.eVariationOn_eq_integral_abs_deriv hab]

/-- The variation of an absolutely continuous function on a left-open interval equals its
integrated absolute derivative. -/
theorem eVariationOn_Ioc_eq_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    eVariationOn f (Ioc a b) = ENNReal.ofReal (∫ x in a..b, |deriv f x|) := by
  have heq : eVariationOn f (Ioo a b) = eVariationOn f (Icc a b) := by
    have hcont : ContinuousOn f (Icc a b) := by
      simpa only [uIcc_of_le hab] using hf.continuousOn
    exact eVariationOn.Ioo_eq_Icc_of_continuousOn hab hcont
  have hvar : eVariationOn f (Ioc a b) = eVariationOn f (Icc a b) := by
    apply le_antisymm (eVariationOn.mono f Ioc_subset_Icc_self)
    calc
      eVariationOn f (Icc a b) = eVariationOn f (Ioo a b) := heq.symm
      _ ≤ eVariationOn f (Ioc a b) := eVariationOn.mono f Ioo_subset_Ioc_self
  rw [hvar, hf.eVariationOn_eq_integral_abs_deriv hab]

/-- The variation of an absolutely continuous function on a right-open interval equals its
integrated absolute derivative. -/
theorem eVariationOn_Ico_eq_integral_abs_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    eVariationOn f (Ico a b) = ENNReal.ofReal (∫ x in a..b, |deriv f x|) := by
  have heq : eVariationOn f (Ioo a b) = eVariationOn f (Icc a b) := by
    have hcont : ContinuousOn f (Icc a b) := by
      simpa only [uIcc_of_le hab] using hf.continuousOn
    exact eVariationOn.Ioo_eq_Icc_of_continuousOn hab hcont
  have hvar : eVariationOn f (Ico a b) = eVariationOn f (Icc a b) := by
    apply le_antisymm (eVariationOn.mono f Ico_subset_Icc_self)
    calc
      eVariationOn f (Icc a b) = eVariationOn f (Ioo a b) := heq.symm
      _ ≤ eVariationOn f (Ico a b) := eVariationOn.mono f Ioo_subset_Ico_self
  rw [hvar, hf.eVariationOn_eq_integral_abs_deriv hab]

end AbsolutelyContinuousOnInterval

namespace IntervalIntegrable

/-- A function that agrees on `[a,b]` with a primitive of an interval-integrable function has
variation equal to the integral of the absolute value of its integrand. -/
theorem eVariationOn_eq_integral_abs {g F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hF : ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, g t) :
    eVariationOn F (Icc a b) = ENNReal.ofReal (∫ t in a..b, |g t|) := by
  let H (x : ℝ) := F a + ∫ t in a..x, g t
  have hGac : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, g t) a b :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (by simp [hab])
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ F a) a b :=
    (LipschitzWith.const (F a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hHac : AbsolutelyContinuousOnInterval H a b := by
    apply (hc.add hGac).congr
    intro x _
    simp [H, Pi.add_apply]
  have hFH : EqOn F H (Icc a b) := fun x hx ↦ hF x hx
  have hderiv : ∀ᵐ x : ℝ, x ∈ uIoc a b → deriv H x = g x := by
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hg] with x hx hxIoc
    have hxIcc : x ∈ uIcc a b := Ioc_subset_Icc_self hxIoc
    have hdx := hx hxIcc a (by simp [hab])
    exact (hdx.const_add (F a)).deriv
  have hInt : (∫ t in a..b, |deriv H t|) = ∫ t in a..b, |g t| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx hxIoc
    rw [hx hxIoc]
  calc
    eVariationOn F (Icc a b) = eVariationOn H (Icc a b) :=
      eVariationOn.eq_of_eqOn hFH
    _ = ENNReal.ofReal (∫ t in a..b, |deriv H t|) :=
      hHac.eVariationOn_eq_integral_abs_deriv hab
    _ = ENNReal.ofReal (∫ t in a..b, |g t|) := by rw [hInt]

end IntervalIntegrable
