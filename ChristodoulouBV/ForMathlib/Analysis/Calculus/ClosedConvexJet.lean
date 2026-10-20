module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
# First jets on closed convex domains

A continuously extended interior derivative is the relative derivative on the closed domain.
The domain must have nonempty interior, so that its relative derivative is unique.
-/

public section

open Set Filter
open scoped Topology ContDiff Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous extension of the derivative from the interior of a closed convex set is
its derivative within the closed set, including at boundary points. -/
theorem Convex.hasFDerivWithinAt_of_continuousOn_fderiv
    {K : Set E} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hinterior : (interior K).Nonempty) {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f K) (hG : ContinuousOn G K)
    (hdiff : DifferentiableOn ℝ f (interior K))
    (hderiv : ∀ x ∈ interior K, fderiv ℝ f x = G x)
    {x : E} (hx : x ∈ K) : HasFDerivWithinAt f (G x) K x := by
  have hclosure : closure (interior K) = K := by
    rw [hK.closure_interior_eq_closure_of_nonempty_interior hinterior,
      hclosed.closure_eq]
  have hfcont : ∀ y ∈ closure (interior K), ContinuousWithinAt f (interior K) y := by
    intro y hy
    exact (hf y (hclosure ▸ hy)).mono interior_subset
  have hGtend : Tendsto G (𝓝[interior K] x) (𝓝 (G x)) :=
    (hG x hx).mono_left (nhdsWithin_mono x interior_subset)
  have hderivtend : Tendsto (fun y => fderiv ℝ f y)
      (𝓝[interior K] x) (𝓝 (G x)) := by
    apply hGtend.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hderiv y hy).symm
  rw [← hclosure]
  exact hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff
    hK.interior isOpen_interior hfcont hderivtend

/-- The continuous interior jet gives `C¹` regularity on the entire closed convex domain. -/
theorem Convex.contDiffOn_one_of_continuousOn_fderiv
    {K : Set E} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hinterior : (interior K).Nonempty) {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f K) (hG : ContinuousOn G K)
    (hdiff : DifferentiableOn ℝ f (interior K))
    (hderiv : ∀ x ∈ interior K, fderiv ℝ f x = G x) :
    ContDiffOn ℝ 1 f K := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (uniqueDiffOn_convex hK hinterior)]
  refine ⟨by simp, G, ?_, ?_⟩
  · simpa using hG
  · intro x hx
    exact hK.hasFDerivWithinAt_of_continuousOn_fderiv hclosed hinterior hf hG
      hdiff hderiv hx

/-- On a full-dimensional closed convex set, the continuous interior jet is the unique
relative derivative everywhere, including on the boundary. -/
theorem Convex.fderivWithin_eq_of_continuousOn_fderiv
    {K : Set E} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hinterior : (interior K).Nonempty) {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f K) (hG : ContinuousOn G K)
    (hdiff : DifferentiableOn ℝ f (interior K))
    (hderiv : ∀ x ∈ interior K, fderiv ℝ f x = G x)
    {x : E} (hx : x ∈ K) : fderivWithin ℝ f K x = G x :=
  (hK.hasFDerivWithinAt_of_continuousOn_fderiv hclosed hinterior hf hG
    hdiff hderiv hx).fderivWithin (uniqueDiffOn_convex hK hinterior x hx)

/-- Integrating a continuous relative first jet along a segment recovers the change in values. -/
theorem Convex.sub_eq_integral_fderivWithin
    [CompleteSpace F] {K : Set E} (hK : Convex ℝ K) {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f K) (hG : ContinuousOn G K)
    (hjet : ∀ x ∈ K, HasFDerivWithinAt f (G x) K x)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    f y - f x = ∫ t in (0 : ℝ)..1, G (x + t • (y - x)) (y - x) := by
  let ℓ : ℝ → E := AffineMap.lineMap x y
  have hmaps : MapsTo ℓ (Icc (0 : ℝ) 1) K := by
    intro t ht
    exact hK.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)
  have hcont : ContinuousOn (f ∘ ℓ) (Icc (0 : ℝ) 1) :=
    hf.comp AffineMap.lineMap_continuous.continuousOn hmaps
  have hGcont : ContinuousOn (fun t : ℝ => G (ℓ t) (y - x)) (Icc 0 1) := by
    fun_prop (disch := exact hmaps)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (f ∘ ℓ) (G (ℓ t) (y - x)) t := by
    intro t ht
    have htK : ℓ t ∈ K := hmaps (mem_Icc_of_Ioo ht)
    have hnear : ∀ᶠ t' in 𝓝 t, ℓ t' ∈ K := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t' ht'
      exact hmaps (mem_Icc_of_Ioo ht')
    exact (hjet (ℓ t) htK).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap hnear
  have hint : IntervalIntegrable (fun t : ℝ => G (ℓ t) (y - x))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hGcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hcont hderiv hint
  simpa [ℓ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using hFTC.symm

/-- The continuous interior derivative gives the segment formula even for endpoints on
the boundary of a closed convex domain. -/
theorem Convex.sub_eq_integral_of_continuousOn_fderiv
    [CompleteSpace F] {K : Set E} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hinterior : (interior K).Nonempty) {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f K) (hG : ContinuousOn G K)
    (hdiff : DifferentiableOn ℝ f (interior K))
    (hderiv : ∀ x ∈ interior K, fderiv ℝ f x = G x)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    f y - f x = ∫ t in (0 : ℝ)..1, G (x + t • (y - x)) (y - x) :=
  hK.sub_eq_integral_fderivWithin hf hG
    (fun _ hz => hK.hasFDerivWithinAt_of_continuousOn_fderiv
      hclosed hinterior hf hG hdiff hderiv hz) hx hy

/-- A continuous field of derivatives within a set makes the function `C¹` there. -/
theorem contDiffOn_one_of_continuousOn_hasFDerivWithinAt
    {K : Set E} {f : E → F} {G : E → E →L[ℝ] F}
    (hG : ContinuousOn G K)
    (hjet : ∀ x ∈ K, HasFDerivWithinAt f (G x) K x) :
    ContDiffOn ℝ 1 f K := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt (n := 0) (by simp)]
  intro x hx
  refine ⟨K, ?_, by simp, G, hjet, ?_⟩
  · simpa [hx] using (self_mem_nhdsWithin : K ∈ 𝓝[K] x)
  · simpa using hG

/-- Compatible full first jets on two closed pieces glue to a first jet on their union. -/
theorem contDiffOn_one_union_of_closed_jets
    {S T : Set E} {f : E → F} {G : E → E →L[ℝ] F}
    (hS : IsClosed S) (hT : IsClosed T)
    (hGS : ContinuousOn G S) (hGT : ContinuousOn G T)
    (hjetS : ∀ x ∈ S, HasFDerivWithinAt f (G x) S x)
    (hjetT : ∀ x ∈ T, HasFDerivWithinAt f (G x) T x) :
    ContDiffOn ℝ 1 f (S ∪ T) := by
  apply contDiffOn_one_of_continuousOn_hasFDerivWithinAt
    (hGS.union_of_isClosed hGT hS hT)
  intro x hx
  have hs : HasFDerivWithinAt f (G x) S x := by
    by_cases hxs : x ∈ S
    · exact hjetS x hxs
    · exact HasFDerivWithinAt.of_notMem_closure (by simpa [hS.closure_eq] using hxs)
  have ht : HasFDerivWithinAt f (G x) T x := by
    by_cases hxt : x ∈ T
    · exact hjetT x hxt
    · exact HasFDerivWithinAt.of_notMem_closure (by simpa [hT.closure_eq] using hxt)
  exact hs.union ht

/-- Two closed convex pieces with continuously extended interior derivatives have a compatible
`C¹` union when they share a single full derivative field. -/
theorem Convex.contDiffOn_one_union_of_continuousOn_fderiv
    {S T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    (hSi : (interior S).Nonempty) (hTi : (interior T).Nonempty)
    {f : E → F} {G : E → E →L[ℝ] F}
    (hfS : ContinuousOn f S) (hfT : ContinuousOn f T)
    (hGS : ContinuousOn G S) (hGT : ContinuousOn G T)
    (hdiffS : DifferentiableOn ℝ f (interior S))
    (hdiffT : DifferentiableOn ℝ f (interior T))
    (hderivS : ∀ x ∈ interior S, fderiv ℝ f x = G x)
    (hderivT : ∀ x ∈ interior T, fderiv ℝ f x = G x) :
    ContDiffOn ℝ 1 f (S ∪ T) :=
  contDiffOn_one_union_of_closed_jets hSc hTc hGS hGT
    (fun _ hx => hS.hasFDerivWithinAt_of_continuousOn_fderiv hSc hSi hfS hGS
      hdiffS hderivS hx)
    (fun _ hx => hT.hasFDerivWithinAt_of_continuousOn_fderiv hTc hTi hfT hGT
      hdiffT hderivT hx)

/-- A finite union of closed sets carrying one continuous full first jet is `C¹`.
The common global functions express agreement of values and full jets on overlaps. -/
theorem contDiffOn_one_finset_iUnion_of_closed_jets
    {ι : Type*} (I : Finset ι) {K : ι → Set E}
    {f : E → F} {G : E → E →L[ℝ] F}
    (hclosed : ∀ i, IsClosed (K i))
    (hG : ∀ i, ContinuousOn G (K i))
    (hjet : ∀ i, ∀ x ∈ K i, HasFDerivWithinAt f (G x) (K i) x) :
    ContDiffOn ℝ 1 f (⋃ i ∈ I, K i) := by
  classical
  let U (J : Finset ι) : Set E := ⋃ i ∈ J, K i
  have h : ∀ J : Finset ι, IsClosed (U J) ∧ ContinuousOn G (U J) ∧
      ∀ x ∈ U J, HasFDerivWithinAt f (G x) (U J) x := by
    intro J
    induction J using Finset.induction_on with
    | empty => simp [U]
    | @insert i J hi ih =>
        have hU : U (insert i J) = K i ∪ U J := by
          ext x
          simp [U, Finset.mem_insert]
        rw [hU]
        refine ⟨(hclosed i).union ih.1,
          (hG i).union_of_isClosed ih.2.1 (hclosed i) ih.1, ?_⟩
        intro x hx
        have hleft : HasFDerivWithinAt f (G x) (K i) x := by
          by_cases hxi : x ∈ K i
          · exact hjet i x hxi
          · exact HasFDerivWithinAt.of_notMem_closure
              (by simpa [(hclosed i).closure_eq] using hxi)
        have hright : HasFDerivWithinAt f (G x) (U J) x := by
          by_cases hxJ : x ∈ U J
          · exact ih.2.2 x hxJ
          · exact HasFDerivWithinAt.of_notMem_closure
              (by simpa [ih.1.closure_eq] using hxJ)
        exact hleft.union hright
  exact contDiffOn_one_of_continuousOn_hasFDerivWithinAt (h I).2.1 (h I).2.2

/-- A finite family of closed convex pieces with matching values and full jets is `C¹`
on its union. The same total `f` and `G` are used on every piece. -/
theorem Convex.contDiffOn_one_finset_iUnion_of_continuousOn_fderiv
    {ι : Type*} (I : Finset ι) {K : ι → Set E}
    (hconv : ∀ i, Convex ℝ (K i))
    (hclosed : ∀ i, IsClosed (K i))
    (hinterior : ∀ i, (interior (K i)).Nonempty)
    {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ∀ i, ContinuousOn f (K i))
    (hG : ∀ i, ContinuousOn G (K i))
    (hdiff : ∀ i, DifferentiableOn ℝ f (interior (K i)))
    (hderiv : ∀ i, ∀ x ∈ interior (K i), fderiv ℝ f x = G x) :
    ContDiffOn ℝ 1 f (⋃ i ∈ I, K i) :=
  contDiffOn_one_finset_iUnion_of_closed_jets I hclosed hG
    (fun i _ hx => (hconv i).hasFDerivWithinAt_of_continuousOn_fderiv
      (hclosed i) (hinterior i) (hf i) (hG i) (hdiff i) (hderiv i) hx)

/-- Finitely many closed convex pieces with matching values and full first jets admit
a global glued function which is `C¹` on their union. -/
theorem Convex.exists_contDiffOn_one_finset_glue
    {ι : Type*} (I : Finset ι) (K : ι → Set E)
    (hconv : ∀ i ∈ I, Convex ℝ (K i))
    (hclosed : ∀ i ∈ I, IsClosed (K i))
    (hinterior : ∀ i ∈ I, (interior (K i)).Nonempty)
    (f : ι → E → F) (G : ι → E → E →L[ℝ] F)
    (hf : ∀ i ∈ I, ContinuousOn (f i) (K i))
    (hG : ∀ i ∈ I, ContinuousOn (G i) (K i))
    (hdiff : ∀ i ∈ I, DifferentiableOn ℝ (f i) (interior (K i)))
    (hderiv : ∀ i ∈ I, ∀ x ∈ interior (K i), fderiv ℝ (f i) x = G i x)
    (hfagree : ∀ i ∈ I, ∀ j ∈ I, EqOn (f i) (f j) (K i ∩ K j))
    (hGagree : ∀ i ∈ I, ∀ j ∈ I, EqOn (G i) (G j) (K i ∩ K j)) :
    ∃ fglue : E → F, ∃ Gglue : E → E →L[ℝ] F,
      ContDiffOn ℝ 1 fglue (⋃ i ∈ I, K i) ∧
      (∀ i ∈ I, EqOn fglue (f i) (K i)) ∧
      (∀ i ∈ I, EqOn Gglue (G i) (K i)) := by
  classical
  let fglue : E → F := fun x =>
    if h : ∃ i ∈ I, x ∈ K i then f h.choose x else 0
  let Gglue : E → E →L[ℝ] F := fun x =>
    if h : ∃ i ∈ I, x ∈ K i then G h.choose x else 0
  have hfeq : ∀ i ∈ I, EqOn fglue (f i) (K i) := by
    intro i hi x hx
    have h : ∃ j ∈ I, x ∈ K j := ⟨i, hi, hx⟩
    change (if h' : ∃ j ∈ I, x ∈ K j then f h'.choose x else 0) = f i x
    rw [dite_eq_left h]
    exact hfagree h.choose (Classical.choose_spec h).1 i hi
      ⟨(Classical.choose_spec h).2, hx⟩
  have hGeq : ∀ i ∈ I, EqOn Gglue (G i) (K i) := by
    intro i hi x hx
    have h : ∃ j ∈ I, x ∈ K j := ⟨i, hi, hx⟩
    change (if h' : ∃ j ∈ I, x ∈ K j then G h'.choose x else 0) = G i x
    rw [dite_eq_left h]
    exact hGagree h.choose (Classical.choose_spec h).1 i hi
      ⟨(Classical.choose_spec h).2, hx⟩
  have hcont : ∀ i ∈ I, ContinuousOn Gglue (K i) := by
    intro i hi
    exact (hG i hi).congr (hGeq i hi)
  have hjet : ∀ i ∈ I, ∀ x ∈ K i,
      HasFDerivWithinAt fglue (Gglue x) (K i) x := by
    intro i hi x hx
    rw [hGeq i hi hx]
    exact ((hconv i hi).hasFDerivWithinAt_of_continuousOn_fderiv
      (hclosed i hi) (hinterior i hi) (hf i hi) (hG i hi)
      (hdiff i hi) (hderiv i hi) hx).congr' (hfeq i hi) hx
  have hresult : ContDiffOn ℝ 1 fglue (⋃ i : I, K i.1) := by
    simpa using contDiffOn_one_finset_iUnion_of_closed_jets (Finset.univ : Finset I)
      (K := fun i : I => K i.1)
      (fun i => hclosed i.1 i.2)
      (fun i => hcont i.1 i.2)
      (fun i x hx => hjet i.1 i.2 x hx)
  refine ⟨fglue, Gglue, ?_, hfeq, hGeq⟩
  have hset : (⋃ i : I, K i.1) = (⋃ i ∈ I, K i) := by
    ext x
    simp
  rw [← hset]
  exact hresult

end
