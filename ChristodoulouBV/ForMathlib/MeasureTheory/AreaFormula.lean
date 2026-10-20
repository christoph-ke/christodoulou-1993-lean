module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Topology.Bases
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Area formula with multiplicity

This file extends the injective Jacobian formula to maps with countable local multiplicity.
The central bookkeeping lemma counts each fiber through a disjoint injective partition.
-/

public section

open MeasureTheory Set MeasureTheory.Measure
open scoped ENNReal Function

namespace MeasureTheory

private theorem exists_countable_open_injOn_cover {E : Type*} [TopologicalSpace E]
    [SecondCountableTopology E] {f : E → E} {s : Set E}
    (hlocal : ∀ x ∈ s, ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ InjOn f u) :
    ∃ t : ℕ → Set E, (∀ n, IsOpen (t n) ∧ InjOn f (t n)) ∧ s ⊆ ⋃ n, t n := by
  classical
  let I : Set (Set E) := {u | IsOpen u ∧ InjOn f u}
  obtain ⟨T, hTI, hTc, hUnion⟩ :=
    TopologicalSpace.isOpen_biUnion_countable I id
      (fun u hu => hu.1)
  let S : Set (Set E) := insert ∅ T
  have hSc : S.Countable := hTc.insert ∅
  have hSne : S.Nonempty := ⟨∅, mem_insert ∅ T⟩
  obtain ⟨e, he⟩ := hSc.exists_surjective hSne
  let t : ℕ → Set E := fun n => e n
  have ht : ∀ n, IsOpen (t n) ∧ InjOn f (t n) := by
    intro n
    rcases (e n).2 with h | h
    · simp [t, h]
    · exact hTI h
  refine ⟨t, ht, ?_⟩
  intro x hx
  obtain ⟨u, huopen, hxu, huinj⟩ := hlocal x hx
  have hxI : x ∈ ⋃ v ∈ I, v := mem_iUnion₂.mpr ⟨u, ⟨huopen, huinj⟩, hxu⟩
  have hUnion' : (⋃ v ∈ T, v) = ⋃ v ∈ I, v := by simpa using hUnion
  rw [← hUnion'] at hxI
  obtain ⟨v, hvT, hxv⟩ := mem_iUnion₂.mp hxI
  obtain ⟨n, hn⟩ := he ⟨v, Or.inr hvT⟩
  exact mem_iUnion.mpr ⟨n, by simpa [t, hn] using hxv⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

/-- Cardinality of a fiber, with `⊤` for an infinite fiber. -/
@[expose] noncomputable def fiberCard (f : E → E) (s : Set E) (y : E) : ℕ∞ :=
  (s ∩ f ⁻¹' {y}).encard

/-- The fiber counting function, valued in `ℝ≥0∞`. -/
@[expose] noncomputable def fiberMultiplicity (f : E → E) (s : Set E) (y : E) : ℝ≥0∞ :=
  ((s ∩ f ⁻¹' {y}).encard : ℝ≥0∞)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The real-valued multiplicity is the canonical cast of the fiber cardinality. -/
theorem fiberMultiplicity_eq_coe_fiberCard (f : E → E) (s : Set E) (y : E) :
    fiberMultiplicity f s y = (fiberCard f s y : ℝ≥0∞) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- On a countable disjoint partition of injectivity, the fiber count is the sum of the
indicators of the images of the pieces. -/
theorem fiberMultiplicity_eq_tsum_indicator {f : E → E} {s : Set E} {p : ℕ → Set E}
    (hp : s = ⋃ n, p n) (hd : Pairwise (Disjoint on p))
    (hi : ∀ n, InjOn f (p n)) (y : E) :
    fiberMultiplicity f s y = ∑' n, (f '' p n).indicator (1 : E → ℝ≥0∞) y := by
  classical
  have hfiber : s ∩ f ⁻¹' {y} = ⋃ n, p n ∩ f ⁻¹' {y} := by
    rw [hp, iUnion_inter]
  have hdisj : Set.univ.PairwiseDisjoint (fun n => p n ∩ f ⁻¹' {y}) := by
    intro i _ j _ hij
    exact (hd hij).mono inter_subset_left inter_subset_left
  rw [fiberMultiplicity, hfiber, ← ENNReal.tsum_set_one]
  have hsum := (ENNReal.tsum_biUnion (f := fun _ : E => (1 : ℝ≥0∞)) hdisj)
  rw [hsum]
  congr 1
  ext n
  rw [ENNReal.tsum_set_one]
  by_cases hy : y ∈ f '' p n
  · obtain ⟨x, hx, rfl⟩ := hy
    have heq : p n ∩ f ⁻¹' {f x} = {x} := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨hz, hfz⟩
        exact mem_singleton_iff.mpr (hi n hz hx hfz)
      · intro hz
        subst z
        exact ⟨hx, rfl⟩
    have hy' : f x ∈ f '' p n := ⟨x, hx, rfl⟩
    simp [heq, hy']
  · have heq : p n ∩ f ⁻¹' {y} = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hy ⟨x, hx.1, hx.2⟩)
      · intro hx
        simp at hx
    simp [heq, hy]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] in
/-- The fiber counting function is measurable when its domain has a countable measurable
partition into injectivity sets with measurable images. -/
theorem measurable_fiberMultiplicity_of_partition {f : E → E} {s : Set E} {p : ℕ → Set E}
    (hp : s = ⋃ n, p n) (hd : Pairwise (Disjoint on p))
    (hi : ∀ n, InjOn f (p n)) (hm : ∀ n, MeasurableSet (f '' p n)) :
    Measurable (fiberMultiplicity f s) := by
  rw [funext fun y => fiberMultiplicity_eq_tsum_indicator hp hd hi y]
  exact Measurable.tsum fun n => (measurable_const.indicator (hm n))

/-- The area formula with multiplicity for a measurable disjoint partition into pieces
on which the map is differentiable and injective. -/
theorem lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv_of_partition
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} {p : ℕ → Set E}
    (hp : s = ⋃ n, p n) (hd : Pairwise (Disjoint on p))
    (hm : ∀ n, MeasurableSet (p n))
    (hf' : ∀ n, ∀ x ∈ p n, HasFDerivWithinAt f (f' x) (p n) x)
    (hi : ∀ n, InjOn f (p n)) :
    (∫⁻ y, fiberMultiplicity f s y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  have him : ∀ n, MeasurableSet (f '' p n) := by
    intro n
    exact measurable_image_of_fderivWithin (hm n) (hf' n) (hi n)
  calc
    (∫⁻ y, fiberMultiplicity f s y ∂μ) =
        ∫⁻ y, ∑' n, (f '' p n).indicator (1 : E → ℝ≥0∞) y ∂μ := by
      congr 1
      funext y
      exact fiberMultiplicity_eq_tsum_indicator hp hd hi y
    _ = ∑' n, μ (f '' p n) := by
      rw [lintegral_tsum]
      · congr 1
        funext n
        exact lintegral_indicator_one (him n)
      · intro n
        exact (measurable_const.indicator (him n)).aemeasurable
    _ = ∑' n, ∫⁻ x in p n, ENNReal.ofReal |(f' x).det| ∂μ := by
      congr 1
      funext n
      exact (lintegral_abs_det_fderiv_eq_addHaar_image μ (hm n) (hf' n) (hi n)).symm
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
      rw [hp, lintegral_iUnion hm hd]

/-- An injective measurable cover suffices for the area formula; overlaps are removed by
`disjointed` before applying the partition version. -/
theorem lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv_of_cover
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} {t : ℕ → Set E}
    (hs : MeasurableSet s) (ht : ∀ n, MeasurableSet (t n))
    (hcover : s ⊆ ⋃ n, t n) (hi : ∀ n, InjOn f (s ∩ t n))
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) :
    (∫⁻ y, fiberMultiplicity f s y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| ∂μ := by
  let p n := s ∩ disjointed t n
  have hp : s = ⋃ n, p n := by
    simp only [p, ← inter_iUnion, iUnion_disjointed]
    exact (inter_eq_left.mpr hcover).symm
  have hd : Pairwise (Disjoint on p) :=
    (disjoint_disjointed t).mono fun _ _ h ↦ h.mono inter_subset_right inter_subset_right
  have hm : ∀ n, MeasurableSet (p n) :=
    fun n => hs.inter (MeasurableSet.disjointed ht n)
  have hp_sub : ∀ n, p n ⊆ s ∩ t n := by
    intro n x hx
    exact ⟨hx.1, disjointed_subset t n hx.2⟩
  have hi' : ∀ n, InjOn f (p n) := fun n => (hi n).mono (hp_sub n)
  have hf'' : ∀ n, ∀ x ∈ p n, HasFDerivWithinAt f (f' x) (p n) x := by
    intro n x hx
    exact (hf' x hx.1).hasFDerivWithinAt
  exact lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv_of_partition μ
    hp hd hm hf'' hi'

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_open_injOn_of_contDiffAt_det_ne_zero
    {f : E → E} {x : E} (hf : ContDiffAt ℝ 1 f x)
    (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ InjOn f u := by
  let d := fderiv ℝ f x
  have hunit : IsUnit d := by
    apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
    exact (LinearMap.isUnit_iff_isUnit_det (d : E →ₗ[ℝ] E)).mpr
      (isUnit_iff_ne_zero.mpr hdet)
  have hbij : Function.Bijective d := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective d
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hed : (e : E →L[ℝ] E) = d := by
    ext v
    simp [e]
  have he : HasStrictFDerivAt f (e : E →L[ℝ] E) x := by
    rw [hed]
    exact hf.hasStrictFDerivAt one_ne_zero
  let g := he.toOpenPartialHomeomorph f
  exact ⟨g.source, g.open_source, he.mem_toOpenPartialHomeomorph_source, g.injOn⟩

private theorem areaFormula_aux
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    AEMeasurable (fiberMultiplicity f s) μ ∧
      (∫⁻ y, fiberMultiplicity f s y ∂μ) =
        ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
  let d : E → ℝ := fun x => (fderiv ℝ f x).det
  let R : Set E := U ∩ d ⁻¹' ({0}ᶜ)
  let r : Set E := s ∩ R
  let c : Set E := s \ R
  have hdcont : ContinuousOn d U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num))
  have hR : IsOpen R := hdcont.isOpen_inter_preimage hU isOpen_compl_singleton
  have hr : MeasurableSet r := hs.inter hR.measurableSet
  have hc : MeasurableSet c := hs.diff hR.measurableSet
  have hlocal : ∀ x ∈ r, ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ InjOn f u := by
    intro x hx
    exact exists_open_injOn_of_contDiffAt_det_ne_zero
      (hf.contDiffAt (hU.mem_nhds hx.2.1)) hx.2.2
  obtain ⟨t, ht, hcover⟩ := exists_countable_open_injOn_cover hlocal
  let p n := r ∩ disjointed t n
  have hp : r = ⋃ n, p n := by
    simp only [p, ← inter_iUnion, iUnion_disjointed]
    exact (inter_eq_left.mpr hcover).symm
  have hpd : Pairwise (Disjoint on p) :=
    (disjoint_disjointed t).mono fun _ _ h ↦ h.mono inter_subset_right inter_subset_right
  have hpm : ∀ n, MeasurableSet (p n) :=
    fun n => hr.inter (MeasurableSet.disjointed (fun n => (ht n).1.measurableSet) n)
  have hpi : ∀ n, InjOn f (p n) := by
    intro n
    exact (ht n).2.mono (fun x hx => disjointed_subset t n hx.2)
  have hpderiv : ∀ n, ∀ x ∈ p n, HasFDerivWithinAt f (fderiv ℝ f x) (p n) x := by
    intro n x hx
    exact ((hf.contDiffAt (hU.mem_nhds hx.1.2.1)).differentiableAt
      one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have hmeasr : Measurable (fiberMultiplicity f r) :=
    measurable_fiberMultiplicity_of_partition hp hpd hpi
      (fun n => measurable_image_of_fderivWithin (hpm n) (hpderiv n) (hpi n))
  have hregular : (∫⁻ y, fiberMultiplicity f r y ∂μ) =
      ∫⁻ x in r, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
    apply lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv_of_cover μ hr
      (fun n => (ht n).1.measurableSet) hcover
    · intro n
      exact (ht n).2.mono inter_subset_right
    · intro x hx
      exact ((hf.contDiffAt (hU.mem_nhds hx.2.1)).differentiableAt
        one_ne_zero).hasFDerivAt
  have hcrit : μ (f '' c) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    · intro x hx
      exact ((hf.contDiffAt (hU.mem_nhds (hsU hx.1))).differentiableAt
        one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      have hnot : x ∉ R := hx.2
      have hz : d x = 0 := by
        by_contra hn
        exact hnot ⟨hsU hx.1, hn⟩
      exact hz
  have hfull : s = r ∪ c := by
    ext x
    simp [r, c]
  have hdisj : Disjoint r c := by
    apply Set.disjoint_left.mpr
    intro x hxr hxc
    exact hxc.2 hxr.2
  have hzero : (∫⁻ x in c, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ) = 0 := by
    calc
      (∫⁻ x in c, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ) = ∫⁻ x in c, 0 ∂μ := by
        apply setLIntegral_congr_fun hc
        intro x hx
        have hnot : x ∉ R := hx.2
        have hz : d x = 0 := by
          by_contra hn
          exact hnot ⟨hsU hx.1, hn⟩
        simp [d] at hz
        simp [hz]
      _ = 0 := by simp
  have hright : (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ) =
      ∫⁻ x in r, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
    rw [hfull, lintegral_union hc hdisj, hzero, add_zero]
  have hleftAe : fiberMultiplicity f s =ᵐ[μ] fiberMultiplicity f r := by
    have hae : ∀ᵐ y ∂μ, y ∉ f '' c := by
      simpa only [ae_iff, not_not, ofPred_mem_eq] using hcrit
    filter_upwards [hae] with y hy
    have hfiber : s ∩ f ⁻¹' {y} = r ∩ f ⁻¹' {y} := by
      ext x
      constructor
      · intro hx
        have hxr : x ∈ r := by
          by_contra hxr
          have hxc : x ∈ c := ⟨hx.1, by
            intro hR'
            exact hxr ⟨hx.1, hR'⟩⟩
          exact hy ⟨x, hxc, hx.2⟩
        exact ⟨hxr, hx.2⟩
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
    simp [fiberMultiplicity, hfiber]
  exact ⟨hmeasr.aemeasurable.congr hleftAe.symm,
    (lintegral_congr_ae hleftAe).trans (hregular.trans hright.symm)⟩

/-- Area formula with multiplicity for a `C¹` map on an open set, integrated over a
measurable subset of that set. -/
theorem lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    (∫⁻ y, fiberMultiplicity f s y ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ :=
  (areaFormula_aux μ hU hs hsU hf).2

/-- The multiplicity function is almost everywhere measurable for a `C¹` map on an open set. -/
theorem aemeasurable_fiberMultiplicity
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    AEMeasurable (fiberMultiplicity f s) μ :=
  (areaFormula_aux μ hU hs hsU hf).1

/-- The fiber count is measurable in the completion of the Haar measure. -/
theorem nullMeasurable_fiberMultiplicity
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    NullMeasurable (fiberMultiplicity f s) μ :=
  (aemeasurable_fiberMultiplicity μ hU hs hsU hf).nullMeasurable

/-- On the completed measure space, the fiber count is a measurable function. -/
theorem measurable_fiberMultiplicity_completion
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    Measurable (fun y : NullMeasurableSpace E μ => fiberMultiplicity f s y) := by
  intro t ht
  exact nullMeasurable_fiberMultiplicity μ hU hs hsU hf ht

/-- The `ℕ∞`-valued fiber cardinality is measurable on the completed measure space. -/
theorem measurable_fiberCard_completion
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    Measurable (fun y : NullMeasurableSpace E μ => fiberCard f s y) := by
  apply ENat.measurable_iff.mpr
  intro n
  have hpre : (fun y : NullMeasurableSpace E μ => fiberCard f s y) ⁻¹' {(n : ℕ∞)} =
      (fun y : NullMeasurableSpace E μ => fiberMultiplicity f s y) ⁻¹'
        {((n : ℕ∞) : ℝ≥0∞)} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      exact congrArg (fun m : ℕ∞ => (m : ℝ≥0∞)) h
    · intro h
      exact ENat.toENNReal_strictMono.injective h
  rw [hpre]
  exact (measurable_fiberMultiplicity_completion μ hU hs hsU hf)
    (measurableSet_singleton _)

/-- Area formula stated directly with the `ℕ∞`-valued fiber cardinality. -/
theorem lintegral_fiberCard_eq_lintegral_abs_det_fderiv
    {f : E → E} {U s : Set E} (hU : IsOpen U) (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U) :
    (∫⁻ y, (fiberCard f s y : ℝ≥0∞) ∂μ) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ := by
  simpa only [fiberMultiplicity_eq_coe_fiberCard] using
    (lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv μ hU hs hsU hf)

/-- Finite area implies that almost every fiber has finitely many points. -/
theorem ae_finite_fiber_of_lintegral_abs_det_fderiv_ne_top
    {f : E → E} {U s : Set E} (hU : IsOpen U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (hfinite : (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ) ≠ ∞) :
    ∀ᵐ y ∂μ, (s ∩ f ⁻¹' {y}).Finite := by
  have harea := lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv μ hU hs hsU hf
  have hmulfinite : (∫⁻ y, fiberMultiplicity f s y ∂μ) ≠ ∞ := by
    rw [harea]
    exact hfinite
  filter_upwards [ae_lt_top' (aemeasurable_fiberMultiplicity μ hU hs hsU hf)
    hmulfinite] with y hy
  exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp hy)

/-- The area formula on the real plane with its product Lebesgue measure. -/
theorem lintegral_fiberMultiplicity_real_prod
    {f : ℝ × ℝ → ℝ × ℝ} {U s : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    (∫⁻ y, fiberMultiplicity f s y ∂((volume : Measure ℝ).prod volume)) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det|
        ∂((volume : Measure ℝ).prod volume) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  simpa only [← Measure.volume_eq_prod ℝ ℝ] using
    (lintegral_fiberMultiplicity_eq_lintegral_abs_det_fderiv
      (μ := (volume : Measure (ℝ × ℝ))) hU hs hsU hf)

/-- The plane area formula with the `ℕ∞`-valued fiber cardinality and product measure. -/
theorem lintegral_fiberCard_real_prod
    {f : ℝ × ℝ → ℝ × ℝ} {U s : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    (∫⁻ y, (fiberCard f s y : ℝ≥0∞) ∂((volume : Measure ℝ).prod volume)) =
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det|
        ∂((volume : Measure ℝ).prod volume) := by
  simpa only [fiberMultiplicity_eq_coe_fiberCard] using
    (lintegral_fiberMultiplicity_real_prod hU hs hsU hf)

end MeasureTheory
