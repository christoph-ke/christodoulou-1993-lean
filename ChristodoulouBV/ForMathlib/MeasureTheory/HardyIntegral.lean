module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Singular integral estimates for interval primitives

The endpoint limit only needs interval integrability of the weighted density.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace intervalIntegral

/-- Integration by parts for a primitive against the inverse distance to a
strictly earlier point. This finite-interval identity is the truncated Hardy
formula. -/
theorem integral_integral_div_sq {f : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    ∫ t in c..b, (∫ s in a..t, f s) / (t - a) ^ 2 =
      (∫ t in c..b, f t / (t - a)) -
        (∫ s in a..b, f s) / (b - a) +
        (∫ s in a..c, f s) / (c - a) := by
  have hab : a ≤ b := hac.le.trans hcb
  have hsub : uIcc c b ⊆ uIcc a b := by
    rw [uIcc_of_le hcb, uIcc_of_le hab]
    exact Icc_subset_Icc hac.le le_rfl
  have hFac : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in a..t, f s) c b :=
    (hf.absolutelyContinuousOnInterval_intervalIntegral (c := a)
      (by simp [hab])).mono hsub
  have hGac : AbsolutelyContinuousOnInterval
      (fun t : ℝ => (t - a)⁻¹) c b := by
    have hD : ContDiffOn ℝ 1 (fun t : ℝ => (t - a)⁻¹) (uIcc c b) := by
      apply (contDiffOn_id.sub contDiffOn_const).inv
      intro t ht
      rw [uIcc_of_le hcb] at ht
      exact ne_of_gt (sub_pos.mpr (hac.trans_le ht.1))
    exact hD.absolutelyContinuousOnInterval
  have hderivF : ∀ᵐ t ∂volume, t ∈ uIoc c b →
      deriv (fun x => ∫ s in a..x, f s) t = f t := by
    filter_upwards [hf.ae_hasDerivAt_integral] with t ht htu
    have ht' : t ∈ uIcc a b := hsub (uIoc_subset_uIcc htu)
    exact (ht ht' a (by simp [hab])).deriv
  have hderivG : ∀ t ∈ uIcc c b,
      deriv (fun x : ℝ => (x - a)⁻¹) t = -1 / (t - a) ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc c b := by simpa only [uIcc_of_le hcb] using ht
    have hta : t - a ≠ 0 := ne_of_gt (sub_pos.mpr (hac.trans_le ht'.1))
    have h := deriv_fun_inv'' (c := fun x : ℝ => x - a)
      (by fun_prop) hta
    simpa [deriv_sub_const, deriv_id] using h
  have hIBP := hFac.integral_mul_deriv_eq_deriv_mul hGac
  have hleft :
      (∫ t in c..b, (∫ s in a..t, f s) *
        deriv (fun x : ℝ => (x - a)⁻¹) t) =
        -(∫ t in c..b, (∫ s in a..t, f s) / (t - a) ^ 2) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t ht
    rw [hderivG t (uIoc_subset_uIcc ht)]
    ring
  have hright :
      (∫ t in c..b, deriv (fun x => ∫ s in a..x, f s) t * (t - a)⁻¹) =
        ∫ t in c..b, f t / (t - a) := by
    apply integral_congr_ae
    filter_upwards [hderivF] with t hft ht
    rw [hft ht]
    exact (div_eq_mul_inv _ _).symm
  rw [hleft, hright] at hIBP
  simp only [div_eq_mul_inv] at hIBP ⊢
  linarith

/-- If both a nonnegative density and its reciprocal-distance weight are integrable,
its primitive divided by distance to the initial endpoint tends to zero. -/
theorem tendsto_integral_div_sub_right {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hw : IntervalIntegrable (fun t => f t / (t - a)) volume a b)
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t) :
    Tendsto (fun t => (∫ s in a..t, f s) / (t - a)) (𝓝[>] a) (𝓝 0) := by
  have hWcont : ContinuousWithinAt (fun t => ∫ s in a..t, f s / (s - a))
      (Icc a b) a := by
    have ha : a ∈ uIcc a b := by simp [hab.le]
    have hAC := hw.absolutelyContinuousOnInterval_intervalIntegral (c := a) ha
    have h := hAC.continuousOn.continuousWithinAt ha
    simpa only [uIcc_of_le hab.le] using h
  have hWlim : Tendsto (fun t => ∫ s in a..t, f s / (s - a))
      (𝓝[>] a) (𝓝 0) := by
    have hmem : Icc a b ∈ 𝓝[>] a :=
      mem_of_superset (Ioc_mem_nhdsGT hab) Ioc_subset_Icc_self
    have h := hWcont.mono_of_mem_nhdsWithin hmem
    change Tendsto (fun t => ∫ s in a..t, f s / (s - a)) (𝓝[>] a)
      (𝓝 (∫ s in a..a, f s / (s - a))) at h
    simpa using h
  have hnonneg : ∀ᶠ t in 𝓝[>] a,
      0 ≤ (∫ s in a..t, f s) / (t - a) := by
    filter_upwards [Ioc_mem_nhdsGT hab] with t ht
    have hft : 0 ≤ ∫ s in a..t, f s := by
      apply integral_nonneg ht.1.le
      intro s hs
      exact hfn s ⟨hs.1, hs.2.trans ht.2⟩
    exact div_nonneg hft (sub_nonneg.mpr ht.1.le)
  have hbound : ∀ᶠ t in 𝓝[>] a,
      (∫ s in a..t, f s) / (t - a) ≤
        ∫ s in a..t, f s / (s - a) := by
    filter_upwards [Ioc_mem_nhdsGT hab] with t ht
    have hsub : Icc a t ⊆ Icc a b :=
      Icc_subset_Icc le_rfl ht.2
    have hfi : IntervalIntegrable f volume a t := by
      apply hf.mono_set
      simpa only [uIcc_of_le hab.le, uIcc_of_le ht.1.le] using hsub
    have hwi : IntervalIntegrable (fun s => f s / (s - a)) volume a t := by
      apply hw.mono_set
      simpa only [uIcc_of_le hab.le, uIcc_of_le ht.1.le] using hsub
    rw [← integral_div]
    apply integral_mono_on_of_le_Ioo ht.1.le (hfi.div_const (t - a)) hwi
    intro s hs
    have hsab : s ∈ Icc a b := ⟨hs.1.le, hs.2.le.trans ht.2⟩
    apply div_le_div_of_nonneg_left (hfn s hsab) (sub_pos.mpr hs.1)
    exact sub_le_sub_right hs.2.le a
  exact squeeze_zero' hnonneg hbound hWlim

/-- The conjugate endpoint limit for a terminal primitive. -/
theorem tendsto_integral_div_sub_left {f : ℝ → ℝ} {a v : ℝ}
    (hav : a < v) (hf : IntervalIntegrable f volume a v)
    (hw : IntervalIntegrable (fun t => f t / (v - t)) volume a v)
    (hfn : ∀ t ∈ Icc a v, 0 ≤ f t) :
    Tendsto (fun u => (∫ s in u..v, f s) / (v - u)) (𝓝[<] v) (𝓝 0) := by
  have hWcont : ContinuousWithinAt (fun u => ∫ s in u..v, f s / (v - s))
      (Icc a v) v := by
    have hv : v ∈ uIcc a v := by simp [hav.le]
    have hAC := hw.absolutelyContinuousOnInterval_intervalIntegral (c := v) hv
    have h := hAC.continuousOn.continuousWithinAt hv
    have h' : ContinuousWithinAt (fun u => -(∫ s in v..u, f s / (v - s)))
        (Icc a v) v := by
      have hfun : -(fun u => ∫ s in v..u, f s / (v - s)) =
          (fun u => -(∫ s in v..u, f s / (v - s))) := by
        funext u
        exact Pi.neg_apply _ _
      rw [← hfun]
      simpa only [uIcc_of_le hav.le] using h.neg
    have heq : (fun u => ∫ s in u..v, f s / (v - s)) =
        (fun u => -(∫ s in v..u, f s / (v - s))) := by
      funext u
      have hs := integral_symm (μ := volume) (f := fun s => f s / (v - s)) v u
      exact hs
    rw [heq]
    exact h'
  have hWlim : Tendsto (fun u => ∫ s in u..v, f s / (v - s))
      (𝓝[<] v) (𝓝 0) := by
    have hmem : Icc a v ∈ 𝓝[<] v :=
      mem_of_superset (Ico_mem_nhdsLT hav) Ico_subset_Icc_self
    have h := hWcont.mono_of_mem_nhdsWithin hmem
    change Tendsto (fun u => ∫ s in u..v, f s / (v - s)) (𝓝[<] v)
      (𝓝 (∫ s in v..v, f s / (v - s))) at h
    simpa using h
  have hnonneg : ∀ᶠ u in 𝓝[<] v,
      0 ≤ (∫ s in u..v, f s) / (v - u) := by
    filter_upwards [Ico_mem_nhdsLT hav] with u hu
    have hft : 0 ≤ ∫ s in u..v, f s := by
      apply integral_nonneg hu.2.le
      intro s hs
      exact hfn s ⟨hu.1.trans hs.1, hs.2⟩
    exact div_nonneg hft (sub_nonneg.mpr hu.2.le)
  have hbound : ∀ᶠ u in 𝓝[<] v,
      (∫ s in u..v, f s) / (v - u) ≤
        ∫ s in u..v, f s / (v - s) := by
    filter_upwards [Ico_mem_nhdsLT hav] with u hu
    have hsub : Icc u v ⊆ Icc a v :=
      Icc_subset_Icc hu.1 le_rfl
    have hfi : IntervalIntegrable f volume u v := by
      apply hf.mono_set
      simpa only [uIcc_of_le hav.le, uIcc_of_le hu.2.le] using hsub
    have hwi : IntervalIntegrable (fun s => f s / (v - s)) volume u v := by
      apply hw.mono_set
      simpa only [uIcc_of_le hav.le, uIcc_of_le hu.2.le] using hsub
    rw [← integral_div]
    apply integral_mono_on_of_le_Ioo hu.2.le (hfi.div_const (v - u)) hwi
    intro s hs
    have hsav : s ∈ Icc a v := ⟨hu.1.trans hs.1.le, hs.2.le⟩
    apply div_le_div_of_nonneg_left (hfn s hsav) (sub_pos.mpr hs.2)
    exact sub_le_sub_left hs.1.le v
  exact squeeze_zero' hnonneg hbound hWlim

/-- The reciprocal-square Hardy kernel is integrable at the initial endpoint
when the density divided by the endpoint distance is integrable. -/
theorem integrableOn_integral_div_sq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hw : IntervalIntegrable (fun t => f t / (t - a)) volume a b)
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t) :
    IntegrableOn (fun t => (∫ s in a..t, f s) / (t - a) ^ 2)
      (Ioc a b) volume := by
  let c : ℕ → ℝ := fun n => a + (b - a) / ((n : ℝ) + 1)
  have hc (n : ℕ) : c n ∈ Ioc a b := by
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have hnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpos : 0 < (b - a) / ((n : ℝ) + 1) :=
      div_pos (sub_pos.mpr hab) hp
    have hle : (b - a) / ((n : ℝ) + 1) ≤ b - a := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) hnonneg]
    exact ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hc_lim : Tendsto c atTop (𝓝 a) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b - a)).const_add a
    simpa only [c, div_eq_mul_inv, one_mul, mul_zero, add_zero] using h
  have hc_lim_right : Tendsto c atTop (𝓝[>] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hc_lim, .of_forall (fun n => (hc n).1)⟩
  have hWlim : Tendsto (fun n => ∫ s in a..c n, f s / (s - a))
      atTop (𝓝 0) := by
    have ha : a ∈ uIcc a b := by simp [hab.le]
    have hAC := hw.absolutelyContinuousOnInterval_intervalIntegral (c := a) ha
    have hcn : Tendsto c atTop (𝓝[uIcc a b] a) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hc_lim, .of_forall (fun n => by
          rw [uIcc_of_le hab.le]
          exact ⟨(hc n).1.le, (hc n).2⟩)⟩
    have hprim : Tendsto (fun t => ∫ s in a..t, f s / (s - a))
        (𝓝[uIcc a b] a) (𝓝 (∫ s in a..a, f s / (s - a))) :=
      hAC.continuousOn.continuousWithinAt ha
    have h := hprim.comp hcn
    change Tendsto (fun n => ∫ s in a..c n, f s / (s - a)) atTop
      (𝓝 (∫ s in a..a, f s / (s - a))) at h
    simpa using h
  have hFlim : Tendsto (fun n => (∫ s in a..c n, f s) / (c n - a))
      atTop (𝓝 0) :=
    (tendsto_integral_div_sub_right hab hf hw hfn).comp hc_lim_right
  have hWtail (n : ℕ) :
      (∫ s in c n..b, f s / (s - a)) =
        (∫ s in a..b, f s / (s - a)) -
          (∫ s in a..c n, f s / (s - a)) := by
    have hsub1 : uIcc a (c n) ⊆ uIcc a b := by
      rw [uIcc_of_le (hc n).1.le, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl (hc n).2
    have hsub2 : uIcc (c n) b ⊆ uIcc a b := by
      rw [uIcc_of_le (hc n).2, uIcc_of_le hab.le]
      exact Icc_subset_Icc (hc n).1.le le_rfl
    have h := integral_add_adjacent_intervals (hw.mono_set hsub1) (hw.mono_set hsub2)
    linarith
  have hTlim : Tendsto
      (fun n => ∫ t in c n..b, (∫ s in a..t, f s) / (t - a) ^ 2)
      atTop (𝓝 ((∫ t in a..b, f t / (t - a)) -
        (∫ s in a..b, f s) / (b - a))) := by
    have heq (n : ℕ) := integral_integral_div_sq (hc n).1 (hc n).2 hf
    have htail : Tendsto (fun n => ∫ s in c n..b, f s / (s - a))
        atTop (𝓝 (∫ s in a..b, f s / (s - a))) := by
      simp_rw [hWtail]
      simpa using (tendsto_const_nhds.sub hWlim)
    have hconst : Tendsto
        (fun _ : ℕ => (∫ s in a..b, f s) / (b - a)) atTop
        (𝓝 ((∫ s in a..b, f s) / (b - a))) := tendsto_const_nhds
    have h := (htail.sub hconst).add hFlim
    simpa only [heq, add_zero] using h
  have hFac : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in a..t, f s) a b :=
    hf.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by simp [hab.le])
  have hlocal (n : ℕ) :
      IntegrableOn (fun t => (∫ s in a..t, f s) / (t - a) ^ 2)
        (Ioc (c n) b) volume := by
    have hsub : Icc (c n) b ⊆ Icc a b :=
      Icc_subset_Icc (hc n).1.le le_rfl
    have hFcont : ContinuousOn (fun t => ∫ s in a..t, f s)
        (Icc (c n) b) := by
      apply hFac.continuousOn.mono
      simpa only [uIcc_of_le hab.le] using hsub
    have hGcont : ContinuousOn (fun t => (∫ s in a..t, f s) / (t - a) ^ 2)
        (Icc (c n) b) := by
      apply hFcont.div ((continuousOn_id.sub continuousOn_const).pow 2)
      intro t ht
      exact pow_ne_zero _ (ne_of_gt (sub_pos.mpr ((hc n).1.trans_le ht.1)))
    have hgi : IntervalIntegrable
        (fun t => (∫ s in a..t, f s) / (t - a) ^ 2) volume (c n) b :=
      hGcont.intervalIntegrable_of_Icc (hc n).2
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc n).2).mp hgi
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∫ t in Ioc (c n) b,
        ‖(∫ s in a..t, f s) / (t - a) ^ 2‖) ≤
        ((∫ t in a..b, f t / (t - a)) -
          (∫ s in a..b, f s) / (b - a)) + 1 := by
    have hH : ∀ᶠ n : ℕ in atTop,
        (∫ t in c n..b, (∫ s in a..t, f s) / (t - a) ^ 2) <
          ((∫ t in a..b, f t / (t - a)) -
            (∫ s in a..b, f s) / (b - a)) + 1 :=
      hTlim.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hH] with n hn
    have hnonneg : ∀ t ∈ Ioc (c n) b,
        0 ≤ (∫ s in a..t, f s) / (t - a) ^ 2 := by
      intro t ht
      have hft : 0 ≤ ∫ s in a..t, f s := by
        apply integral_nonneg (le_trans (hc n).1.le ht.1.le)
        intro s hs
        exact hfn s ⟨hs.1, hs.2.trans ht.2⟩
      exact div_nonneg hft (sq_nonneg _)
    have heq : (∫ t in Ioc (c n) b,
        ‖(∫ s in a..t, f s) / (t - a) ^ 2‖) =
        ∫ t in c n..b, (∫ s in a..t, f s) / (t - a) ^ 2 := by
      rw [integral_of_le (hc n).2]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change ‖(∫ s in a..t, f s) / (t - a) ^ 2‖ =
        (∫ s in a..t, f s) / (t - a) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht)]
    rw [heq]
    exact hn.le
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hlocal hc_lim hbound

/-- The Hardy identity at an initial endpoint. The integrability of the
reciprocal-square kernel follows from the weighted density hypothesis. -/
theorem integral_integral_div_sq_eq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hw : IntervalIntegrable (fun t => f t / (t - a)) volume a b)
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t) :
    ∫ t in a..b, (∫ s in a..t, f s) / (t - a) ^ 2 =
      (∫ t in a..b, f t / (t - a)) -
        (∫ s in a..b, f s) / (b - a) := by
  let G : ℝ → ℝ := fun t => (∫ s in a..t, f s) / (t - a) ^ 2
  let W : ℝ → ℝ := fun t => f t / (t - a)
  have hG : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
      (integrableOn_integral_div_sq hab hf hw hfn)
  have htail (h : ℝ → ℝ) (hh : IntervalIntegrable h volume a b) :
      Tendsto (fun c => ∫ t in c..b, h t) (𝓝[>] a)
        (𝓝 (∫ t in a..b, h t)) := by
    have ha : a ∈ uIcc a b := by simp [hab.le]
    have hAC := hh.absolutelyContinuousOnInterval_intervalIntegral (c := a) ha
    have hmem : Icc a b ∈ 𝓝[>] a :=
      mem_of_superset (Ioc_mem_nhdsGT hab) Ioc_subset_Icc_self
    have hprim := (hAC.continuousOn.continuousWithinAt ha).mono_of_mem_nhdsWithin
      (by simpa only [uIcc_of_le hab.le] using hmem)
    change Tendsto (fun c => ∫ t in a..c, h t) (𝓝[>] a)
      (𝓝 (∫ t in a..a, h t)) at hprim
    have hzero : Tendsto (fun c => ∫ t in a..c, h t) (𝓝[>] a) (𝓝 0) := by
      simpa using hprim
    have hlim := (tendsto_const_nhds (x := ∫ t in a..b, h t)).sub hzero
    have hEq : ∀ᶠ c in 𝓝[>] a,
        (∫ t in c..b, h t) =
          (∫ t in a..b, h t) - (∫ t in a..c, h t) := by
      filter_upwards [Ioc_mem_nhdsGT hab] with c hc
      have hsub1 : uIcc a c ⊆ uIcc a b := by
        rw [uIcc_of_le hc.1.le, uIcc_of_le hab.le]
        exact Icc_subset_Icc le_rfl hc.2
      have hsub2 : uIcc c b ⊆ uIcc a b := by
        rw [uIcc_of_le hc.2, uIcc_of_le hab.le]
        exact Icc_subset_Icc hc.1.le le_rfl
      have hadd := integral_add_adjacent_intervals (hh.mono_set hsub1)
        (hh.mono_set hsub2)
      linarith
    simpa only [sub_zero] using hlim.congr' (hEq.mono fun _ hc => hc.symm)
  have hGtail := htail G hG
  have hWtail := htail W hw
  have hratio := tendsto_integral_div_sub_right hab hf hw hfn
  have hconst : Tendsto
      (fun _ : ℝ => (∫ s in a..b, f s) / (b - a)) (𝓝[>] a)
      (𝓝 ((∫ s in a..b, f s) / (b - a))) := tendsto_const_nhds
  have hsum := (hWtail.sub hconst).add hratio
  have hEq : ∀ᶠ c in 𝓝[>] a,
      (∫ t in c..b, G t) =
        (∫ t in c..b, W t) - (∫ s in a..b, f s) / (b - a) +
          (∫ s in a..c, f s) / (c - a) := by
    filter_upwards [Ioc_mem_nhdsGT hab] with c hc
    exact integral_integral_div_sq hc.1 hc.2 hf
  have hGtail' : Tendsto (fun c => ∫ t in c..b, G t) (𝓝[>] a)
      (𝓝 ((∫ t in a..b, W t) - (∫ s in a..b, f s) / (b - a))) := by
    have h := hsum.congr' (hEq.mono fun _ hc => hc.symm)
    simpa only [add_zero] using h
  exact tendsto_nhds_unique hGtail hGtail'

/-- The nonnegative endpoint term makes the Hardy integral no larger than
the weighted density integral. -/
theorem integral_integral_div_sq_le {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hw : IntervalIntegrable (fun t => f t / (t - a)) volume a b)
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t) :
    (∫ t in a..b, (∫ s in a..t, f s) / (t - a) ^ 2) ≤
      ∫ t in a..b, f t / (t - a) := by
  rw [integral_integral_div_sq_eq hab hf hw hfn]
  have hF : 0 ≤ ∫ s in a..b, f s := integral_nonneg hab.le hfn
  exact sub_le_self _ (div_nonneg hF (sub_nonneg.mpr hab.le))

/-- The terminal-endpoint Hardy identity, obtained by reversing the real line. -/
theorem integral_integral_div_sq_eq_terminal {f : ℝ → ℝ} {a v : ℝ}
    (hav : a < v) (hf : IntervalIntegrable f volume a v)
    (hw : IntervalIntegrable (fun t => f t / (v - t)) volume a v)
    (hfn : ∀ t ∈ Icc a v, 0 ≤ f t) :
    ∫ u in a..v, (∫ s in u..v, f s) / (v - u) ^ 2 =
      (∫ u in a..v, f u / (v - u)) -
        (∫ s in a..v, f s) / (v - a) := by
  let g : ℝ → ℝ := fun x => f (-x)
  have hgf : IntervalIntegrable g volume (-v) (-a) := by
    exact (IntervalIntegrable.iff_comp_neg (f := f) (a := v) (b := a)).mp hf.symm
  have hgw : IntervalIntegrable (fun x => g x / (x - (-v))) volume (-v) (-a) := by
    have h := (IntervalIntegrable.iff_comp_neg
      (f := fun t => f t / (v - t)) (a := v) (b := a)).mp hw.symm
    simpa only [g, neg_neg, sub_neg_eq_add, add_comm] using h
  have hgn : ∀ x ∈ Icc (-v) (-a), 0 ≤ g x := by
    intro x hx
    exact hfn (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hinner (x : ℝ) : (∫ s in -v..x, g s) = ∫ s in -x..v, f s := by
    simpa only [g, neg_neg] using
      (integral_comp_neg (f := f) (a := -v) (b := x))
  have hleft :
      (∫ x in -v..-a, (∫ s in -v..x, g s) / (x - (-v)) ^ 2) =
        ∫ u in a..v, (∫ s in u..v, f s) / (v - u) ^ 2 := by
    let H : ℝ → ℝ := fun u => (∫ s in u..v, f s) / (v - u) ^ 2
    calc
      (∫ x in -v..-a, (∫ s in -v..x, g s) / (x - (-v)) ^ 2) =
          ∫ x in -v..-a, H (-x) := by
        apply integral_congr
        intro x _
        dsimp [H]
        rw [hinner]
        congr 1
        ring
      _ = ∫ u in -(-a)..-(-v), H u := integral_comp_neg H
      _ = ∫ u in a..v, (∫ s in u..v, f s) / (v - u) ^ 2 := by
        simp only [neg_neg, H]
  have hweight :
      (∫ x in -v..-a, g x / (x - (-v))) =
        ∫ u in a..v, f u / (v - u) := by
    let H : ℝ → ℝ := fun u => f u / (v - u)
    calc
      (∫ x in -v..-a, g x / (x - (-v))) =
          ∫ x in -v..-a, H (-x) := by
        apply integral_congr
        intro x _
        dsimp [g, H]
        congr 1
        ring
      _ = ∫ u in -(-a)..-(-v), H u := integral_comp_neg H
      _ = ∫ u in a..v, f u / (v - u) := by simp only [neg_neg, H]
  have htotal : (∫ s in -v..-a, g s) = ∫ s in a..v, f s := by
    simpa only [g, neg_neg] using
      (integral_comp_neg (f := f) (a := -v) (b := -a))
  have h := integral_integral_div_sq_eq (neg_lt_neg hav) hgf hgw hgn
  rw [hleft, hweight, htotal] at h
  convert h using 1; ring

/-- The terminal Hardy kernel is integrable under the weighted density hypothesis. -/
theorem integrableOn_integral_div_sq_terminal {f : ℝ → ℝ} {a v : ℝ}
    (hav : a < v) (hf : IntervalIntegrable f volume a v)
    (hw : IntervalIntegrable (fun t => f t / (v - t)) volume a v)
    (hfn : ∀ t ∈ Icc a v, 0 ≤ f t) :
    IntegrableOn (fun u => (∫ s in u..v, f s) / (v - u) ^ 2)
      (Ioc a v) volume := by
  let g : ℝ → ℝ := fun x => f (-x)
  have hgf : IntervalIntegrable g volume (-v) (-a) :=
    (IntervalIntegrable.iff_comp_neg (f := f) (a := v) (b := a)).mp hf.symm
  have hgw : IntervalIntegrable (fun x => g x / (x - (-v))) volume (-v) (-a) := by
    have h := (IntervalIntegrable.iff_comp_neg
      (f := fun t => f t / (v - t)) (a := v) (b := a)).mp hw.symm
    simpa only [g, neg_neg, sub_neg_eq_add, add_comm] using h
  have hgn : ∀ x ∈ Icc (-v) (-a), 0 ≤ g x := by
    intro x hx
    exact hfn (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  let G : ℝ → ℝ := fun x => (∫ s in -v..x, g s) / (x - (-v)) ^ 2
  have hGi : IntervalIntegrable G volume (-v) (-a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (neg_lt_neg hav).le).mpr
      (integrableOn_integral_div_sq (neg_lt_neg hav) hgf hgw hgn)
  have hGneg : IntervalIntegrable (fun u => G (-u)) volume v a :=
    by simpa only [neg_neg] using
      (IntervalIntegrable.iff_comp_neg (f := G) (a := -v) (b := -a)).mp hGi
  have heq : (fun u => G (-u)) =
      (fun u => (∫ s in u..v, f s) / (v - u) ^ 2) := by
    funext u
    have hinner : (∫ s in -v..-u, g s) = ∫ s in u..v, f s := by
      simpa only [g, neg_neg] using
        (integral_comp_neg (f := f) (a := -v) (b := -u))
    dsimp [G]
    rw [hinner]
    congr 1
    ring
  rw [heq] at hGneg
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).mp hGneg.symm

/-- The terminal Hardy integral is bounded by the reciprocal-distance
weighted density integral. -/
theorem integral_integral_div_sq_le_terminal {f : ℝ → ℝ} {a v : ℝ}
    (hav : a < v) (hf : IntervalIntegrable f volume a v)
    (hw : IntervalIntegrable (fun t => f t / (v - t)) volume a v)
    (hfn : ∀ t ∈ Icc a v, 0 ≤ f t) :
    (∫ u in a..v, (∫ s in u..v, f s) / (v - u) ^ 2) ≤
      ∫ u in a..v, f u / (v - u) := by
  rw [integral_integral_div_sq_eq_terminal hav hf hw hfn]
  have hF : 0 ≤ ∫ s in a..v, f s := integral_nonneg hav.le hfn
  exact sub_le_self _ (div_nonneg hF (sub_nonneg.mpr hav.le))

/-- The finite `lintegral` form of the initial-endpoint Hardy identity for a
real nonnegative density. -/
theorem lintegral_ofReal_integral_div_sq_eq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hw : IntervalIntegrable (fun t => f t / (t - a)) volume a b)
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal
      ((∫ s in a..t, f s) / (t - a) ^ 2)) =
      ENNReal.ofReal ((∫ t in a..b, f t / (t - a)) -
        (∫ s in a..b, f s) / (b - a)) := by
  have hgi := integrableOn_integral_div_sq hab hf hw hfn
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc a b)]
      (fun t => (∫ s in a..t, f s) / (t - a) ^ 2) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    apply ae_of_all
    intro t ht
    have hft : 0 ≤ ∫ s in a..t, f s := by
      apply integral_nonneg ht.1.le
      intro s hs
      exact hfn s ⟨hs.1, hs.2.trans ht.2⟩
    exact div_nonneg hft (sq_nonneg _)
  have h := ofReal_integral_eq_lintegral_ofReal hgi hpos
  rw [← integral_of_le hab.le] at h
  rw [integral_integral_div_sq_eq hab hf hw hfn] at h
  exact h.symm

/-- The finite `lintegral` form of the terminal-endpoint Hardy identity for a
real nonnegative density. -/
theorem lintegral_ofReal_integral_div_sq_eq_terminal {f : ℝ → ℝ} {a v : ℝ}
    (hav : a < v) (hf : IntervalIntegrable f volume a v)
    (hw : IntervalIntegrable (fun t => f t / (v - t)) volume a v)
    (hfn : ∀ t ∈ Icc a v, 0 ≤ f t) :
    (∫⁻ u in Ioc a v, ENNReal.ofReal
      ((∫ s in u..v, f s) / (v - u) ^ 2)) =
      ENNReal.ofReal ((∫ u in a..v, f u / (v - u)) -
        (∫ s in a..v, f s) / (v - a)) := by
  have hgi := integrableOn_integral_div_sq_terminal hav hf hw hfn
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc a v)]
      (fun u => (∫ s in u..v, f s) / (v - u) ^ 2) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    apply ae_of_all
    intro u hu
    have hft : 0 ≤ ∫ s in u..v, f s := by
      apply integral_nonneg hu.2
      intro s hs
      exact hfn s ⟨hu.1.le.trans hs.1, hs.2⟩
    exact div_nonneg hft (sq_nonneg _)
  have h := ofReal_integral_eq_lintegral_ofReal hgi hpos
  rw [← integral_of_le hav.le] at h
  rw [integral_integral_div_sq_eq_terminal hav hf hw hfn] at h
  exact h.symm

end intervalIntegral

end
