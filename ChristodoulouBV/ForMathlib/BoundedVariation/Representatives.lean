module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Group.Order

/-!
# One-sided representatives of functions of bounded variation

Endpoint variation conventions, uniqueness of right-continuous representatives, and
one-sided limits on intervals.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace eVariationOn

/-- Adding a point approached from the right does not change variation if the value at
that point is the right limit. -/
theorem union_singleton_eq_of_continuousWithinAt {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hx : x ∈ closure (s ∩ Ioi x))
    (hf : ContinuousWithinAt f (s ∪ {x}) x) :
    eVariationOn f ((s ∩ Ici x) ∪ {x}) = eVariationOn f (s ∩ Ioi x) := by
  have hne : (𝓝[s ∩ Ioi x] x).NeBot := mem_closure_iff_clusterPt.mp hx
  have hcont : ContinuousWithinAt f ((s ∪ {x}) ∩ Ici x) x :=
    hf.mono inter_subset_left
  have hs : (s ∪ {x}) ∩ Ici x = (s ∩ Ici x) ∪ {x} := by
    ext y
    by_cases hy : y = x <;> simp [hy]
  have ht : (s ∪ {x}) ∩ Ioi x = s ∩ Ioi x := by
    ext y
    by_cases hy : y = x <;> simp [hy]
  have hne' : (𝓝[(s ∪ {x}) ∩ Ioi x] x).NeBot := by
    simpa only [ht] using hne
  have h := eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    (s := s ∪ {x}) hne' hcont
  simpa only [hs, ht] using h.symm

/-- Right continuity removes the endpoint cost on a right ray. -/
theorem Ici_eq_Ioi_of_continuousWithinAt {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousWithinAt f (Ici x) x) :
    eVariationOn f (Ici x) = eVariationOn f (Ioi x) := by
  have hne : (𝓝[Set.univ ∩ Ioi x] x).NeBot := by
    simpa using (nhdsGT_neBot x)
  simpa using (eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    (s := Set.univ) hne (by simpa using hf)).symm

/-- Right continuity at the left endpoint removes its cost on an open upper interval. -/
theorem Ico_eq_Ioo_of_continuousWithinAt {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ico a b) = eVariationOn f (Ioo a b) := by
  have hne : (𝓝[Iio b ∩ Ioi a] a).NeBot := by
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab))]
    exact nhdsGT_neBot a
  have hcont : ContinuousWithinAt f (Iio b ∩ Ici a) a := hf.mono inter_subset_right
  have hs : Iio b ∩ Ici a = Ico a b := by
    ext y; simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico]; tauto
  have ht : Iio b ∩ Ioi a = Ioo a b := by
    ext y; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
  simpa only [hs, ht] using
    (eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
      (s := Iio b) hne hcont).symm

/-- Left continuity removes the endpoint cost on a left ray. -/
theorem Iic_eq_Iio_of_continuousWithinAt {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousWithinAt f (Iic x) x) :
    eVariationOn f (Iic x) = eVariationOn f (Iio x) := by
  have hne : (𝓝[Set.univ ∩ Iio x] x).NeBot := by
    simpa using (nhdsLT_neBot x)
  simpa using (eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
    (s := Set.univ) hne (by simpa using hf)).symm

/-- Left continuity at the right endpoint removes its cost on an open lower interval. -/
theorem Ioc_eq_Ioo_of_continuousWithinAt {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousWithinAt f (Iic b) b) :
    eVariationOn f (Ioc a b) = eVariationOn f (Ioo a b) := by
  have hne : (𝓝[Ioi a ∩ Iio b] b).NeBot := by
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab))]
    exact nhdsLT_neBot b
  have hcont : ContinuousWithinAt f (Ioi a ∩ Iic b) b := hf.mono inter_subset_right
  have hs : Ioi a ∩ Iic b = Ioc a b := by
    ext y; simp only [mem_inter_iff, mem_Ioi, mem_Iic, mem_Ioc]
  have ht : Ioi a ∩ Iio b = Ioo a b := by
    ext y; simp only [mem_inter_iff, mem_Ioi, mem_Iio, mem_Ioo]
  simpa only [hs, ht] using
    (eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
      (s := Ioi a) hne hcont).symm

/-- Taking right limits does not increase variation on an open interval. -/
theorem rightLim_Ioo_le {f : ℝ → ℝ} (a b : ℝ) :
    eVariationOn f.rightLim (Ioo a b) ≤ eVariationOn f (Ioo a b) :=
  eVariationOn_rightLim_le isOpen_Ioo

end eVariationOn

namespace BoundedVariationOn

/-- At a point of `[a,b)`, BV on `(a,b)` gives a genuine right limit. -/
theorem exists_tendsto_right_Ioo {f : ℝ → ℝ} {a b x : ℝ}
    (hf : BoundedVariationOn f (Ioo a b)) (hx : x ∈ Ico a b) :
    ∃ l : ℝ, Tendsto f (𝓝[>] x) (𝓝 l) := by
  have hs : Ioo a b ∩ Ioi x = Ioi x ∩ Iio b := by
    ext y
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi, mem_Iio]
    constructor
    · rintro ⟨⟨hay, hyb⟩, hxy⟩
      exact ⟨hxy, hyb⟩
    · rintro ⟨hxy, hyb⟩
      exact ⟨⟨lt_of_le_of_lt hx.1 hxy, hyb⟩, hxy⟩
  have hfilter : 𝓝[Ioo a b ∩ Ioi x] x = 𝓝[>] x := by
    rw [hs, inter_comm, nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2))]
  simpa only [hfilter] using hf.exists_tendsto_right x

/-- At a point of `[a,b)`, BV on `[a,b)` gives a genuine right limit. -/
theorem exists_tendsto_right_Ico {f : ℝ → ℝ} {a b x : ℝ}
    (hf : BoundedVariationOn f (Ico a b)) (hx : x ∈ Ico a b) :
    ∃ l : ℝ, Tendsto f (𝓝[>] x) (𝓝 l) := by
  have hs : Ico a b ∩ Ioi x = Ioi x ∩ Iio b := by
    ext y
    simp only [mem_inter_iff, mem_Ico, mem_Ioi, mem_Iio]
    constructor
    · rintro ⟨⟨hay, hyb⟩, hxy⟩
      exact ⟨hxy, hyb⟩
    · rintro ⟨hxy, hyb⟩
      exact ⟨⟨le_trans hx.1 hxy.le, hyb⟩, hxy⟩
  have hfilter : 𝓝[Ico a b ∩ Ioi x] x = 𝓝[>] x := by
    rw [hs, inter_comm, nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hx.2))]
  simpa only [hfilter] using hf.exists_tendsto_right x

end BoundedVariationOn

namespace MeasureTheory

/-- Two right-continuous functions on a half-open interval that agree almost everywhere
on its interior agree at every point of the half-open interval. -/
theorem eqOn_Ico_of_ae_eq_of_right_continuous {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hg : ∀ x ∈ Ico a b, ContinuousWithinAt g (Ici x) x)
    (hfg : f =ᵐ[volume.restrict (Ioo a b)] g) : EqOn f g (Ico a b) := by
  have hgood : ∀ᵐ y ∂volume, y ∈ Ioo a b → f y = g y :=
    (ae_restrict_iff' isOpen_Ioo.measurableSet).mp hfg
  have hdense : Dense {y | y ∈ Ioo a b → f y = g y} := volume.dense_of_ae hgood
  intro x hx
  have hxb : x < b := hx.2
  let S : Set ℝ := {y | y ∈ Ioo a b → f y = g y} ∩ Ioo x b
  have hxcl : x ∈ closure (Ioo x b) := by
    rw [closure_Ioo hxb.ne]
    exact ⟨le_rfl, hxb.le⟩
  have hxS : x ∈ closure S := by
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨z, hzU, hzI⟩ := (mem_closure_iff.mp hxcl) U hU hxU
    obtain ⟨y, hygood, hyopen⟩ :=
      hdense.exists_mem_open (isOpen_Ioo.inter hU) ⟨z, hzI, hzU⟩
    exact ⟨y, hyopen.2, ⟨hygood, hyopen.1⟩⟩
  have hSsub : S ⊆ Ici x := fun y hy => hy.2.1.le
  have hEq : EqOn f g S := by
    intro y hy
    exact hy.1 ⟨lt_of_le_of_lt hx.1 hy.2.1, hy.2.2⟩
  have : (𝓝[S] x).NeBot := mem_closure_iff_clusterPt.mp hxS
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf x hx).mono hSsub) ((hg x hx).mono hSsub)
    (hEq.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- A locally integrable right-continuous integrand is the right derivative of any
primitive with the interval-integral increment identity. -/
theorem tendsto_right_slope_of_intervalIntegral_eq_sub {F g : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Ico a b)
    (hgi : IntervalIntegrable g volume a b)
    (hF : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → F v - F u = ∫ t in u..v, g t)
    (hcont : ContinuousWithinAt g (Ici x) x) :
    Tendsto (fun h : ℝ => (F (x + h) - F x) / h) (𝓝[>] 0) (𝓝 (g x)) := by
  have hxb : x < b := hx.2
  have hax : a ≤ x := hx.1
  have hgi_ax : IntervalIntegrable g volume a x := by
    apply hgi.mono_set
    rw [uIcc_of_le hax, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl (le_of_lt hxb)
  have hgi_xb : IntervalIntegrable g volume x b := by
    apply hgi.mono_set
    rw [uIcc_of_le hxb.le, uIcc_of_le hab]
    exact Icc_subset_Icc hax le_rfl
  have hmem : Icc x b ∈ 𝓝[Ici x] x := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin (Ici x) (Iic_mem_nhds hxb)
  have hmemR : Ioc x b ∈ 𝓝[>] x := by
    rw [← Ioi_inter_Iic]
    exact inter_mem_nhdsWithin (Ioi x) (Iic_mem_nhds hxb)
  have hmeas : StronglyMeasurableAtFilter g (𝓝[>] x) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      (AEStronglyMeasurable.mono_set Ioc_subset_Icc_self
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hxb.le).mp hgi_xb).aestronglyMeasurable)
      hmemR
  have hFTC : HasDerivWithinAt (fun y => ∫ t in a..y, g t) (g x) (Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_right hgi_ax hmeas
      (hcont.mono Ioi_subset_Ici_self)
  have hFTC' : HasDerivWithinAt (fun y => F a + ∫ t in a..y, g t)
      (g x) (Ici x) x := by
    simpa using hFTC.const_add (F a)
  have hEq (y : ℝ) (hy : y ∈ Icc x b) : F y = F a + ∫ t in a..y, g t := by
    have hay : a ≤ y := hax.trans hy.1
    have hyab : y ∈ Icc a b := ⟨hay, hy.2⟩
    have h := hF a ⟨le_rfl, hab⟩ y hyab hay
    linarith
  have hDeriv : HasDerivWithinAt F (g x) (Ici x) x :=
    (hFTC'.congr_mono hEq (hEq x ⟨le_rfl, hxb.le⟩) Icc_subset_Ici_self).mono_of_mem_nhdsWithin hmem
  have hSlope : Tendsto (slope F x) (𝓝[>] x) (𝓝 (g x)) := by
    simpa [Ici_sdiff_left] using (hasDerivWithinAt_iff_tendsto_slope.mp hDeriv)
  have hshift : Tendsto (fun h : ℝ => x + h) (𝓝[>] 0) (𝓝[>] x) := by
    simpa only [Filter.map_add_left_nhdsGT, add_zero] using
      (Filter.tendsto_map (f := fun h : ℝ => x + h) (x := 𝓝[>] (0 : ℝ)))
  simpa only [Function.comp_def, slope_def_field, add_sub_cancel_left] using hSlope.comp hshift

/-- Right-continuous integrands with the same primitive agree at every point
of a half-open interval. -/
theorem eqOn_Ico_of_same_intervalIntegral {f g F : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hfInt : IntervalIntegrable f volume a b)
    (hgInt : IntervalIntegrable g volume a b)
    (hf : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x)
    (hg : ∀ x ∈ Ico a b, ContinuousWithinAt g (Ici x) x)
    (hFf : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → F v - F u = ∫ t in u..v, f t)
    (hFg : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → F v - F u = ∫ t in u..v, g t) :
    EqOn f g (Ico a b) := by
  intro x hx
  have hfLim := tendsto_right_slope_of_intervalIntegral_eq_sub hab hx hfInt hFf (hf x hx)
  have hgLim := tendsto_right_slope_of_intervalIntegral_eq_sub hab hx hgInt hFg (hg x hx)
  exact tendsto_nhds_unique hfLim hgLim

end MeasureTheory

end
