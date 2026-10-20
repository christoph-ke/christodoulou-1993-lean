module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointOutputBounds
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Continuous first jets of horizontal axis primitives

The normalized segment from the initial edge to an interior point stays in
the closed coordinate triangle. Differentiation under its fixed interval
integral gives a relative first jet even at the initial edge and the axis.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace ChristodoulouBV.AxisPicard

/-- The normalized horizontal segment from the initial edge. -/
@[expose] def horizontalSegment (a : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (a + t * (p.1 - a), p.2)

/-- The derivative of the horizontal segment with respect to its endpoint. -/
@[expose] def horizontalSegmentFDeriv (t : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (t • (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Evaluation of the horizontal segment derivative. -/
theorem horizontalSegmentFDeriv_apply (t : ℝ) (e : ℝ × ℝ) :
    horizontalSegmentFDeriv t e = (t * e.1, e.2) := by
  simp [horizontalSegmentFDeriv, smul_eq_mul]

/-- The normalized horizontal segment is affine in its endpoint. -/
theorem hasFDerivAt_horizontalSegment (a : ℝ) (p : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt (fun q => horizontalSegment a q t)
      (horizontalSegmentFDeriv t) p := by
  have hfirst : HasFDerivAt
      (fun q : ℝ × ℝ => a + t * (q.1 - a))
      (t • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have h := ((hasFDerivAt_const (a * (1 - t)) p).add
      ((hasFDerivAt_fst : HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p).const_smul t))
    convert h using 1
    · ext q
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [zero_add]
  have hsecond : HasFDerivAt (fun q : ℝ × ℝ => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  exact hfirst.prodMk hsecond

/-- The horizontal segment derivative varies continuously with its
parameter. -/
theorem continuous_horizontalSegmentFDeriv :
    Continuous horizontalSegmentFDeriv := by
  have h : Continuous (fun t : ℝ =>
      (t • (ContinuousLinearMap.fst ℝ ℝ ℝ),
        (ContinuousLinearMap.snd ℝ ℝ ℝ))) := by fun_prop
  exact (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := ℝ × ℝ)
    (F := ℝ) (G := ℝ) ℝ).continuous.comp h

/-- A horizontal segment stays in the closed axis triangle. -/
theorem horizontalSegment_mem_closedCoordTriangle {a b : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    horizontalSegment a p t ∈ closedCoordTriangle a b := by
  have hlo : 0 ≤ t * (p.1 - a) :=
    mul_nonneg ht.1 (sub_nonneg.mpr hp.1)
  have hhi : t * (p.1 - a) ≤ p.1 - a := by
    nlinarith only [ht.2, hp.1]
  change a ≤ a + t * (p.1 - a) ∧
    a + t * (p.1 - a) ≤ p.2 ∧ p.2 ≤ b
  exact ⟨by linarith only [hlo], by linarith only [hhi, hp.2.1], hp.2.2⟩

/-- A positive parameter sends an interior endpoint to an interior point. -/
theorem horizontalSegment_mem_openCoordTriangle {a b : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    horizontalSegment a p t ∈ openCoordTriangle a b := by
  have hp' : a < p.1 ∧ p.1 < p.2 ∧ p.2 < b := hp
  have hlo : 0 < t * (p.1 - a) := mul_pos ht.1 (sub_pos.mpr hp'.1)
  have hhi : t * (p.1 - a) ≤ p.1 - a := by
    nlinarith only [ht.2, hp'.1.le]
  change a < a + t * (p.1 - a) ∧
    a + t * (p.1 - a) < p.2 ∧ p.2 < b
  exact ⟨by linarith only [hlo], by linarith only [hhi, hp'.2.1], hp'.2.2⟩

/-- The normalized horizontal integral of a kernel. -/
@[expose] noncomputable def horizontalMean (a : ℝ) (k : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, k (horizontalSegment a p t)

/-- The candidate first jet of the normalized horizontal integral. -/
@[expose] noncomputable def horizontalMeanJet (a : ℝ)
    (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1,
    (G (horizontalSegment a p t)).comp (horizontalSegmentFDeriv t)

/-- The normalized horizontal mean is continuous on the closed triangle. -/
theorem continuousOn_horizontalMean {a b : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b)) :
    ContinuousOn (horizontalMean a k) (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let kK : C(K, ℝ) := ⟨_, hk.domRestrict⟩
  obtain ⟨F, hF⟩ := kK.exists_restrict_eq (isClosed_closedCoordTriangle a b)
  have hFeq : ∀ p ∈ K, F p = k p := by
    intro p hp
    have h := congrArg (fun H : C(K, ℝ) => H ⟨p, hp⟩) hF
    simpa [kK] using h
  have hseg : Continuous (fun pt : (ℝ × ℝ) × ℝ =>
      horizontalSegment a pt.1 pt.2) := by
    unfold horizontalSegment
    fun_prop
  have hcont : Continuous (horizontalMean a F) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact F.continuous.comp hseg
  apply hcont.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact (hFeq _ (horizontalSegment_mem_closedCoordTriangle hp htI)).symm

/-- The candidate first jet of the horizontal mean is continuous on the
closed triangle. -/
theorem continuousOn_horizontalMeanJet {a b : ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b)) :
    ContinuousOn (horizontalMeanJet a G) (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let GK : C(K, (ℝ × ℝ) →L[ℝ] ℝ) := ⟨_, hG.domRestrict⟩
  obtain ⟨F, hF⟩ := GK.exists_restrict_eq (isClosed_closedCoordTriangle a b)
  have hFeq : ∀ p ∈ K, F p = G p := by
    intro p hp
    have h := congrArg (fun H : C(K, (ℝ × ℝ) →L[ℝ] ℝ) => H ⟨p, hp⟩) hF
    simpa [GK] using h
  have hseg : Continuous (fun pt : (ℝ × ℝ) × ℝ =>
      horizontalSegment a pt.1 pt.2) := by
    unfold horizontalSegment
    fun_prop
  have hint : Continuous (fun pt : (ℝ × ℝ) × ℝ =>
      (F (horizontalSegment a pt.1 pt.2)).comp
        (horizontalSegmentFDeriv pt.2)) := by
    exact (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ).continuous₂.comp
      ((F.continuous.comp hseg).prodMk
        (continuous_horizontalSegmentFDeriv.comp continuous_snd))
  have hcont : Continuous (horizontalMeanJet a F) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact hint
  apply hcont.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  change (G (horizontalSegment a p t)).comp (horizontalSegmentFDeriv t) =
    (F (horizontalSegment a p t)).comp (horizontalSegmentFDeriv t)
  rw [hFeq _ (horizontalSegment_mem_closedCoordTriangle hp htI)]

/-- The normalized horizontal integral has its prescribed full derivative
at each interior point. -/
theorem hasFDerivAt_horizontalMean {a b : ℝ}
    {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ k (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b),
      fderiv ℝ k p = G p)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    HasFDerivAt (horizontalMean a k) (horizontalMeanJet a G p) p := by
  have hopen : IsOpen (openCoordTriangle a b) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hmemK : ∀ q ∈ openCoordTriangle a b,
      q ∈ closedCoordTriangle a b := by
    intro q hq
    exact interior_subset (by simpa only [interior_closedCoordTriangle] using hq)
  obtain ⟨A, hA⟩ :=
    (isCompact_closedCoordTriangle a b).exists_bound_of_continuousOn hG
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      continuous_horizontalSegmentFDeriv.continuousOn
  have hF_meas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable
      (fun t => k (horizontalSegment a q t))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    have hseg : Continuous (fun t : ℝ => horizontalSegment a q t) := by
      unfold horizontalSegment
      fun_prop
    have hcont : ContinuousOn (fun t => k (horizontalSegment a q t))
        (Icc (0 : ℝ) 1) :=
      hk.comp hseg.continuousOn
        (fun t ht => horizontalSegment_mem_closedCoordTriangle (hmemK q hq) ht)
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable
      (fun t => k (horizontalSegment a p t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    have hseg : Continuous (fun t : ℝ => horizontalSegment a p t) := by
      unfold horizontalSegment
      fun_prop
    exact hk.comp hseg.continuousOn
      (fun t ht => horizontalSegment_mem_closedCoordTriangle (hmemK p hp) ht)
  have hintcont : ContinuousOn (fun pt : (ℝ × ℝ) × ℝ =>
      (G (horizontalSegment a pt.1 pt.2)).comp
        (horizontalSegmentFDeriv pt.2))
      (closedCoordTriangle a b ×ˢ Icc (0 : ℝ) 1) := by
    have hseg : Continuous (fun pt : (ℝ × ℝ) × ℝ =>
        horizontalSegment a pt.1 pt.2) := by
      unfold horizontalSegment
      fun_prop
    have hmap : MapsTo (fun pt : (ℝ × ℝ) × ℝ =>
        horizontalSegment a pt.1 pt.2)
        (closedCoordTriangle a b ×ˢ Icc (0 : ℝ) 1)
        (closedCoordTriangle a b) := by
      intro pt hpt
      exact horizontalSegment_mem_closedCoordTriangle hpt.1 hpt.2
    exact (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ).continuous₂.comp_continuousOn
      ((hG.comp hseg.continuousOn hmap).prodMk
        (continuous_horizontalSegmentFDeriv.comp continuous_snd).continuousOn)
  have hF'_meas : AEStronglyMeasurable
      (fun t => (G (horizontalSegment a p t)).comp
        (horizontalSegmentFDeriv t))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hcont := hintcont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hmemK p hp, ht⟩)
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
      ∀ q ∈ openCoordTriangle a b,
        ‖(G (horizontalSegment a q t)).comp
            (horizontalSegmentFDeriv t)‖ ≤ A * B := by
    apply ae_of_all
    intro t ht q hq
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact Ioc_subset_Icc_self ht
    have hA' := hA (horizontalSegment a q t)
      (horizontalSegment_mem_closedCoordTriangle (hmemK q hq) htI)
    have hB' := hB t htI
    calc
      _ ≤ ‖G (horizontalSegment a q t)‖ * ‖horizontalSegmentFDeriv t‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ A * B := by
        have hA0 : 0 ≤ A := (norm_nonneg _).trans hA'
        gcongr
  have hbound_int : IntervalIntegrable (fun _ : ℝ => A * B) volume 0 1 := by simp
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
      ∀ q ∈ openCoordTriangle a b,
        HasFDerivAt (fun q => k (horizontalSegment a q t))
          ((G (horizontalSegment a q t)).comp
            (horizontalSegmentFDeriv t)) q := by
    apply ae_of_all
    intro t ht q hq
    have htI : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hseg : horizontalSegment a q t ∈ interior
        (closedCoordTriangle a b) := by
      rw [interior_closedCoordTriangle]
      exact horizontalSegment_mem_openCoordTriangle hq htI
    have hkAt : HasFDerivAt k (G (horizontalSegment a q t))
        (horizontalSegment a q t) := by
      rw [← hderiv (horizontalSegment a q t) hseg]
      exact (hdiff.differentiableAt (isOpen_interior.mem_nhds hseg)).hasFDerivAt
    simpa only [Function.comp_def] using
      hkAt.comp q (hasFDerivAt_horizontalSegment a q t)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (hopen.mem_nhds hp) hF_meas hF_int hF'_meas hbound hbound_int h_diff

/-- The normalized horizontal integral has a relative derivative at every
point of the closed triangle. -/
theorem hasFDerivWithinAt_horizontalMean {a b : ℝ} (hab : a < b)
    {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ k (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b),
      fderiv ℝ k p = G p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    HasFDerivWithinAt (horizontalMean a k) (horizontalMeanJet a G p)
      (closedCoordTriangle a b) p := by
  have hFcont := continuousOn_horizontalMean hk
  have hJcont := continuousOn_horizontalMeanJet hG
  have hdiffF : DifferentiableOn ℝ (horizontalMean a k)
      (interior (closedCoordTriangle a b)) := by
    intro q hq
    have hqo : q ∈ openCoordTriangle a b := by
      simpa only [interior_closedCoordTriangle] using hq
    exact (hasFDerivAt_horizontalMean hk hG hdiff hderiv hqo).differentiableAt
      |>.differentiableWithinAt
  have hderivF : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ (horizontalMean a k) q = horizontalMeanJet a G q := by
    intro q hq
    have hqo : q ∈ openCoordTriangle a b := by
      simpa only [interior_closedCoordTriangle] using hq
    exact (hasFDerivAt_horizontalMean hk hG hdiff hderiv hqo).fderiv
  exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hFcont hJcont hdiffF hderivF hp

/-- The normalized horizontal integral is relatively `C¹` on the closed
triangle. -/
theorem contDiffOn_horizontalMean {a b : ℝ} (hab : a < b)
    {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ k (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b),
      fderiv ℝ k p = G p) :
    ContDiffOn ℝ 1 (horizontalMean a k) (closedCoordTriangle a b) :=
  contDiffOn_one_of_continuousOn_hasFDerivWithinAt
    (continuousOn_horizontalMeanJet hG)
    (fun _ hp => hasFDerivWithinAt_horizontalMean hab hk hG hdiff hderiv hp)

/-- The variable-endpoint horizontal primitive is a width times the
normalized fixed-interval integral. -/
theorem horizontal_integral_eq_gap_mul_mean (a : ℝ)
    (k : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (∫ s in a..p.1, k (s, p.2)) = (p.1 - a) * horizontalMean a k p := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (f := fun s : ℝ => k (s, p.2))
    (a := (0 : ℝ)) (b := 1) (p.1 - a) a
  simpa [horizontalMean, horizontalSegment, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- A relatively `C¹` triangle kernel has a relatively `C¹` horizontal
primitive from the initial edge. -/
theorem contDiffOn_horizontal_integral {a b : ℝ} (hab : a < b)
    {k : ℝ × ℝ → ℝ}
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ∫ s in a..p.1, k (s, p.2))
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  let G := fderivWithin ℝ k K
  have hG : ContinuousOn G K :=
    hk.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ k (interior K) :=
    (hk.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K, fderiv ℝ k p = G p := by
    intro p hp
    exact (fderivWithin_eq_fderiv
      (hunique p (interior_subset hp))
      ((hdiff p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hmean := contDiffOn_horizontalMean hab hk.continuousOn hG hdiff hderiv
  have hgap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.1 - a) K := by fun_prop
  have hprod := hgap.mul hmean
  apply hprod.congr
  intro p hp
  exact horizontal_integral_eq_gap_mul_mean a k p

/-- The full relative derivative candidate for a horizontal primitive. -/
@[expose] noncomputable def horizontalIntegralJet (a : ℝ)
    (k : ℝ × ℝ → ℝ)
    (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  (p.1 - a) • horizontalMeanJet a G p +
    (horizontalMean a k p) • (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The horizontal primitive has its explicit relative first jet on the
whole closed triangle. -/
theorem hasFDerivWithinAt_horizontal_integral {a b : ℝ} (hab : a < b)
    {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ k (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b),
      fderiv ℝ k p = G p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    HasFDerivWithinAt (fun q : ℝ × ℝ => ∫ s in a..q.1, k (s, q.2))
      (horizontalIntegralJet a k G p) (closedCoordTriangle a b) p := by
  have hgap : HasFDerivWithinAt (fun q : ℝ × ℝ => q.1 - a)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (closedCoordTriangle a b) p := by
    have h := (hasFDerivAt_fst : HasFDerivAt (fun q : ℝ × ℝ => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p).sub
        (hasFDerivAt_const a p)
    have h' : HasFDerivAt (fun q : ℝ × ℝ => q.1 - a)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      convert h using 1
      simp only [sub_zero]
    exact h'.hasFDerivWithinAt
  have hmean := hasFDerivWithinAt_horizontalMean hab hk hG hdiff hderiv hp
  have hprod := hgap.mul hmean
  have heq : EqOn (fun q : ℝ × ℝ => ∫ s in a..q.1, k (s, q.2))
      (fun q => (q.1 - a) * horizontalMean a k q)
      (closedCoordTriangle a b) := by
    intro q hq
    exact horizontal_integral_eq_gap_mul_mean a k q
  have h := hprod.congr' heq hp
  simpa only [horizontalIntegralJet] using h

/-- The relative derivative of the horizontal primitive equals its explicit
jet on a nondegenerate triangle. -/
theorem fderivWithin_horizontal_integral {a b : ℝ} (hab : a < b)
    {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ k (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b),
      fderiv ℝ k p = G p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    fderivWithin ℝ (fun q : ℝ × ℝ => ∫ s in a..q.1, k (s, q.2))
      (closedCoordTriangle a b) p = horizontalIntegralJet a k G p :=
  (hasFDerivWithinAt_horizontal_integral hab hk hG hdiff hderiv hp).fderivWithin
    ((uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)) p hp)

end ChristodoulouBV.AxisPicard

end
