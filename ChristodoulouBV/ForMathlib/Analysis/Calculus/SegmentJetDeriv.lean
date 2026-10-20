module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJetComplete
import Mathlib.Tactic

/-!
# Derivatives from a continuous segment jet

The segment fundamental-theorem identity and continuity of its linear-map
field imply the relative first derivative at every point of a convex domain.
This includes boundary points and does not require nonempty interior.
-/

public section

open Set Filter
open scoped Topology Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous field satisfying the segment integral identity is the relative
Fréchet derivative, including at points on the boundary of the convex set. -/
theorem Convex.hasFDerivWithinAt_of_segment_integral
    {K : Set E} (hK : Convex ℝ K) {f : E → F} {G : E → E →L[ℝ] F}
    (hG : ContinuousOn G K)
    (hsegment : ∀ x ∈ K, ∀ y ∈ K,
      f y - f x = ∫ t in (0 : ℝ)..1, G (x + t • (y - x)) (y - x))
    {x : E} (hx : x ∈ K) : HasFDerivWithinAt f (G x) K x := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousWithinAt_iff.mp (hG x hx)) ε hε
  have hnear : ∀ᶠ y in 𝓝[K] x, y ∈ K ∧ dist y x < δ :=
    eventually_mem_nhdsWithin.and
      ((show ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x δ from
          Metric.ball_mem_nhds x hδ).filter_mono nhdsWithin_le_nhds)
  filter_upwards [hnear] with y ⟨hy, hxy⟩
  let ℓ : ℝ → E := fun t => x + t • (y - x)
  have hmaps : MapsTo ℓ (Icc (0 : ℝ) 1) K := by
    intro t ht
    change x + t • (y - x) ∈ K
    convert hK.segment_subset hx hy (lineMap_mem_segment ℝ x y ht) using 1
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  have hcont : ContinuousOn (fun t : ℝ => G (ℓ t) (y - x)) (Icc 0 1) := by
    fun_prop (disch := exact hmaps)
  have hint : IntervalIntegrable (fun t : ℝ => G (ℓ t) (y - x))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hcont
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(G (ℓ t) - G x) (y - x)‖ ≤ ε * ‖y - x‖ := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      exact ⟨ht'.1.le, ht'.2⟩
    have hdist : dist (ℓ t) x ≤ dist y x := by
      have hmul : ‖t • (y - x)‖ ≤ ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htI.1]
        exact mul_le_of_le_one_left (norm_nonneg _) htI.2
      simpa only [ℓ, dist_eq_norm, add_sub_cancel_left] using hmul
    have hGlt : ‖G (ℓ t) - G x‖ < ε := by
      simpa only [dist_eq_norm] using hclose (hmaps htI) (lt_of_le_of_lt hdist hxy)
    calc
      ‖(G (ℓ t) - G x) (y - x)‖ ≤ ‖G (ℓ t) - G x‖ * ‖y - x‖ :=
        (G (ℓ t) - G x).le_opNorm (y - x)
      _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hGlt.le (norm_nonneg _)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hident : f y - f x - G x (y - x) =
      ∫ t in (0 : ℝ)..1, (G (ℓ t) - G x) (y - x) := by
    rw [hsegment x hx y hy]
    have hconst : (∫ _t in (0 : ℝ)..1, G x (y - x)) = G x (y - x) := by
      simp
    rw [← hconst]
    rw [← intervalIntegral.integral_sub hint (intervalIntegrable_const)]
    simp only [sub_apply]
  rw [hident]
  simpa using hnorm

/-- A continuous segment jet is continuously differentiable on its convex
domain, with the prescribed field as its relative derivative. -/
theorem Convex.contDiffOn_one_of_segment_integral
    {K : Set E} (hK : Convex ℝ K) {f : E → F} {G : E → E →L[ℝ] F}
    (hG : ContinuousOn G K)
    (hsegment : ∀ x ∈ K, ∀ y ∈ K,
      f y - f x = ∫ t in (0 : ℝ)..1, G (x + t • (y - x)) (y - x)) :
    ContDiffOn ℝ 1 f K :=
  contDiffOn_one_of_continuousOn_hasFDerivWithinAt hG
    (fun _ hx => hK.hasFDerivWithinAt_of_segment_integral hG hsegment hx)

/-- A segment point clipped to the parameter interval `[0,1]`. -/
@[expose] def Convex.clampedSegmentPoint {K : Set E} (hK : Convex ℝ K)
    (x y : K) (t : ℝ) : K := by
  let c : ℝ := max 0 (min t 1)
  have hc : c ∈ Icc (0 : ℝ) 1 := by
    dsimp [c]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)
  exact ⟨AffineMap.lineMap x.1 y.1 c,
    hK.segment_subset x.2 y.2 (lineMap_mem_segment ℝ x.1 y.1 hc)⟩

/-- On `[0,1]`, clipping leaves the affine segment point unchanged. -/
theorem Convex.clampedSegmentPoint_val_of_mem {K : Set E} (hK : Convex ℝ K)
    (x y : K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (hK.clampedSegmentPoint x y t : E) = x.1 + t • (y.1 - x.1) := by
  simp [Convex.clampedSegmentPoint, min_eq_left ht.2, max_eq_right ht.1,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

private theorem clampedSegmentPoint_continuous {K : Set E}
    (hK : Convex ℝ K) (x y : K) :
    Continuous (hK.clampedSegmentPoint x y) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ =>
    AffineMap.lineMap x.1 y.1 (max 0 (min t 1)))
  fun_prop

/-- The public segment integral used by explicit continuous jets. -/
@[expose] noncomputable def Convex.explicitSegmentIntegral {K : Set E} (hK : Convex ℝ K)
    (x y : K) (G : BoundedContinuousFunction K (E →L[ℝ] F)) : F :=
  ∫ t in (0 : ℝ)..1, G (hK.clampedSegmentPoint x y t) (y.1 - x.1)

/-- A continuous bounded value and linear-map pair with a public segment
identity. The explicit identity supplements the earlier opaque jet predicate. -/
@[expose] def Convex.IsExplicitSegmentJet {K : Set E} (hK : Convex ℝ K)
    (p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F)) : Prop :=
  ∀ x y : K, p.1 y - p.1 x = hK.explicitSegmentIntegral x y p.2

omit [CompleteSpace F] in
private theorem explicitSegmentIntegral_intervalIntegrable {K : Set E}
    (hK : Convex ℝ K) (x y : K)
    (G : BoundedContinuousFunction K (E →L[ℝ] F)) :
    IntervalIntegrable
      (fun t : ℝ => G (hK.clampedSegmentPoint x y t) (y.1 - x.1))
      MeasureTheory.volume 0 1 := by
  have hc : Continuous
      (fun t : ℝ => G (hK.clampedSegmentPoint x y t) (y.1 - x.1)) :=
    (G.continuous.comp (clampedSegmentPoint_continuous hK x y)).clm_apply continuous_const
  exact hc.intervalIntegrable 0 1

private noncomputable def explicitSegmentIntegralCLM {K : Set E} (hK : Convex ℝ K)
    (x y : K) : BoundedContinuousFunction K (E →L[ℝ] F) →L[ℝ] F := by
  let L : BoundedContinuousFunction K (E →L[ℝ] F) →ₗ[ℝ] F :=
    { toFun := hK.explicitSegmentIntegral x y
      map_add' := by
        intro G H
        change (∫ t in (0 : ℝ)..1,
          (G + H) (hK.clampedSegmentPoint x y t) (y.1 - x.1)) =
          (∫ t in (0 : ℝ)..1,
            G (hK.clampedSegmentPoint x y t) (y.1 - x.1)) +
          (∫ t in (0 : ℝ)..1,
            H (hK.clampedSegmentPoint x y t) (y.1 - x.1))
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_apply]
        exact intervalIntegral.integral_add
          (explicitSegmentIntegral_intervalIntegrable hK x y G)
          (explicitSegmentIntegral_intervalIntegrable hK x y H)
      map_smul' := by
        intro c G
        change (∫ t in (0 : ℝ)..1,
          (c • G) (hK.clampedSegmentPoint x y t) (y.1 - x.1)) =
          c • (∫ t in (0 : ℝ)..1,
            G (hK.clampedSegmentPoint x y t) (y.1 - x.1))
        simp only [BoundedContinuousFunction.coe_smul, smul_apply]
        exact intervalIntegral.integral_smul c _ }
  apply L.mkContinuous ‖y.1 - x.1‖
  intro G
  change ‖hK.explicitSegmentIntegral x y G‖ ≤ ‖y.1 - x.1‖ * ‖G‖
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖G (hK.clampedSegmentPoint x y t) (y.1 - x.1)‖ ≤
        ‖y.1 - x.1‖ * ‖G‖ := by
    intro t ht
    calc
      ‖G (hK.clampedSegmentPoint x y t) (y.1 - x.1)‖ ≤
          ‖G (hK.clampedSegmentPoint x y t)‖ * ‖y.1 - x.1‖ :=
        (G (hK.clampedSegmentPoint x y t)).le_opNorm (y.1 - x.1)
      _ ≤ ‖G‖ * ‖y.1 - x.1‖ := mul_le_mul_of_nonneg_right
        (G.norm_coe_le_norm _) (norm_nonneg _)
      _ = ‖y.1 - x.1‖ * ‖G‖ := mul_comm _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [Convex.explicitSegmentIntegral, mul_comm] using h

omit [CompleteSpace F] in
/-- The explicit segment-identity condition is closed in the uniform product
norm, so it may be imposed on the established complete jet space. -/
theorem Convex.isClosed_isExplicitSegmentJet {K : Set E} (hK : Convex ℝ K) :
    IsClosed {p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F) |
        hK.IsExplicitSegmentJet p} := by
  have hsingle (x y : K) :
      IsClosed {p : BoundedContinuousFunction K F ×
        BoundedContinuousFunction K (E →L[ℝ] F) |
          p.1 y - p.1 x = hK.explicitSegmentIntegral x y p.2} := by
    have hleft : Continuous (fun p : BoundedContinuousFunction K F ×
        BoundedContinuousFunction K (E →L[ℝ] F) => p.1 y - p.1 x) := by
      fun_prop
    have hright : Continuous (fun p : BoundedContinuousFunction K F ×
        BoundedContinuousFunction K (E →L[ℝ] F) =>
        hK.explicitSegmentIntegral x y p.2) :=
      (explicitSegmentIntegralCLM hK x y).continuous.comp continuous_snd
    exact isClosed_eq hleft hright
  have heq : {p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F) |
        hK.IsExplicitSegmentJet p} =
      ⋂ x : K, ⋂ y : K,
        {p | p.1 y - p.1 x = hK.explicitSegmentIntegral x y p.2} := by
    ext p
    simp [Convex.IsExplicitSegmentJet]
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun y => hsingle x y

/-- The explicit bounded continuous segment jet gives a relative derivative
for any total representatives that agree with its values and linear maps. -/
theorem Convex.hasFDerivWithinAt_of_explicitSegmentJet
    {K : Set E} (hK : Convex ℝ K)
    (p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F))
    (hp : hK.IsExplicitSegmentJet p)
    {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ∀ x : K, f x.1 = p.1 x)
    (hG : ∀ x : K, G x.1 = p.2 x)
    {x : E} (hx : x ∈ K) : HasFDerivWithinAt f (G x) K x := by
  have hGcont : ContinuousOn G K := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert p.2.continuous using 1
    funext z
    exact hG z
  apply hK.hasFDerivWithinAt_of_segment_integral hGcont
  · intro u hu v hv
    let up : K := ⟨u, hu⟩
    let vp : K := ⟨v, hv⟩
    have h := hp up vp
    rw [← hf up, ← hf vp] at h
    convert h using 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    change G (u + t • (v - u)) (v - u) =
      p.2 (hK.clampedSegmentPoint up vp t) (v - u)
    rw [← hG (hK.clampedSegmentPoint up vp t),
      hK.clampedSegmentPoint_val_of_mem up vp htI]
  · exact hx

/-- The value field of an explicit bounded continuous segment jet is `C¹`
on the convex domain. -/
theorem Convex.contDiffOn_one_of_explicitSegmentJet
    {K : Set E} (hK : Convex ℝ K)
    (p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F))
    (hp : hK.IsExplicitSegmentJet p)
    {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ∀ x : K, f x.1 = p.1 x)
    (hG : ∀ x : K, G x.1 = p.2 x) :
    ContDiffOn ℝ 1 f K := by
  have hGcont : ContinuousOn G K := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert p.2.continuous using 1
    funext z
    exact hG z
  exact contDiffOn_one_of_continuousOn_hasFDerivWithinAt hGcont
    (fun _ hx => hK.hasFDerivWithinAt_of_explicitSegmentJet p hp hf hG hx)


end
