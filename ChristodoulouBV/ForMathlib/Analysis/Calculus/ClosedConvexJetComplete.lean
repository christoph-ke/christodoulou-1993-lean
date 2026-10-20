module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Completeness of continuous segment jets

A segment jet is a pair of bounded continuous value and derivative fields obeying the
fundamental theorem of calculus on every segment of a convex domain. The product norm
is the maximum of the two uniform norms.
-/

public section

noncomputable section

open Set
open scoped Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def clampedSegmentPoint {K : Set E} (hK : Convex ℝ K) (x y : K)
    (t : ℝ) : K := by
  let c : ℝ := max 0 (min t 1)
  have hc : c ∈ Icc (0 : ℝ) 1 := by
    dsimp [c]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)
  exact ⟨AffineMap.lineMap x.1 y.1 c,
    hK.segment_subset x.2 y.2 (lineMap_mem_segment ℝ x.1 y.1 hc)⟩

private theorem clampedSegmentPoint_continuous {K : Set E}
    (hK : Convex ℝ K) (x y : K) : Continuous (clampedSegmentPoint hK x y) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ => AffineMap.lineMap x.1 y.1 (max 0 (min t 1)))
  fun_prop

private theorem clampedSegmentPoint_val_of_mem {K : Set E}
    (hK : Convex ℝ K) (x y : K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (clampedSegmentPoint hK x y t : E) = x.1 + t • (y.1 - x.1) := by
  simp [clampedSegmentPoint, min_eq_left ht.2, max_eq_right ht.1,
    AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

private def segmentIntegral {K : Set E} (hK : Convex ℝ K) (x y : K)
    (g : BoundedContinuousFunction K (E →L[ℝ] F)) : F :=
  ∫ t in (0 : ℝ)..1, g (clampedSegmentPoint hK x y t) (y.1 - x.1)

omit [CompleteSpace F] in
private theorem segmentIntegral_intervalIntegrable {K : Set E}
    (hK : Convex ℝ K) (x y : K)
    (g : BoundedContinuousFunction K (E →L[ℝ] F)) :
    IntervalIntegrable (fun t : ℝ => g (clampedSegmentPoint hK x y t) (y.1 - x.1))
      MeasureTheory.volume 0 1 := by
  have hc : Continuous (fun t : ℝ => g (clampedSegmentPoint hK x y t) (y.1 - x.1)) := by
    exact (g.continuous.comp (clampedSegmentPoint_continuous hK x y)).clm_apply continuous_const
  exact hc.intervalIntegrable 0 1

private def segmentIntegralCLM {K : Set E} (hK : Convex ℝ K) (x y : K) :
    BoundedContinuousFunction K (E →L[ℝ] F) →L[ℝ] F := by
  let L : BoundedContinuousFunction K (E →L[ℝ] F) →ₗ[ℝ] F :=
    { toFun := segmentIntegral hK x y
      map_add' := by
        intro g h
        change (∫ t in (0 : ℝ)..1,
          (g + h) (clampedSegmentPoint hK x y t) (y.1 - x.1)) =
          (∫ t in (0 : ℝ)..1, g (clampedSegmentPoint hK x y t) (y.1 - x.1)) +
          (∫ t in (0 : ℝ)..1, h (clampedSegmentPoint hK x y t) (y.1 - x.1))
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, add_apply]
        exact intervalIntegral.integral_add
          (segmentIntegral_intervalIntegrable hK x y g)
          (segmentIntegral_intervalIntegrable hK x y h)
      map_smul' := by
        intro c g
        change (∫ t in (0 : ℝ)..1,
          (c • g) (clampedSegmentPoint hK x y t) (y.1 - x.1)) =
          c • (∫ t in (0 : ℝ)..1, g (clampedSegmentPoint hK x y t) (y.1 - x.1))
        simp only [BoundedContinuousFunction.coe_smul, smul_apply]
        exact intervalIntegral.integral_smul c _ }
  apply L.mkContinuous ‖y.1 - x.1‖
  intro g
  change ‖segmentIntegral hK x y g‖ ≤ ‖y.1 - x.1‖ * ‖g‖
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖g (clampedSegmentPoint hK x y t) (y.1 - x.1)‖ ≤
        ‖y.1 - x.1‖ * ‖g‖ := by
    intro t ht
    calc
      ‖g (clampedSegmentPoint hK x y t) (y.1 - x.1)‖ ≤
          ‖g (clampedSegmentPoint hK x y t)‖ * ‖y.1 - x.1‖ :=
        (g (clampedSegmentPoint hK x y t)).le_opNorm (y.1 - x.1)
      _ ≤ ‖g‖ * ‖y.1 - x.1‖ := mul_le_mul_of_nonneg_right
        (g.norm_coe_le_norm _) (norm_nonneg _)
      _ = ‖y.1 - x.1‖ * ‖g‖ := mul_comm _ _
  have hbound' := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [segmentIntegral, mul_comm] using hbound'

/-- The segment identity for bounded continuous value and derivative fields on a convex set. -/
def Convex.IsContinuousSegmentJet {K : Set E} (hK : Convex ℝ K)
    (p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F)) : Prop :=
  ∀ x y : K, p.1 y - p.1 x = segmentIntegral hK x y p.2

omit [CompleteSpace F] in
/-- The segment-identity condition is closed in the product of uniform norm spaces. -/
theorem Convex.isClosed_isContinuousSegmentJet {K : Set E} (hK : Convex ℝ K) :
    IsClosed {p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F) |
      hK.IsContinuousSegmentJet p} := by
  have hsingle (x y : K) :
      IsClosed {p : BoundedContinuousFunction K F ×
        BoundedContinuousFunction K (E →L[ℝ] F) |
        p.1 y - p.1 x = segmentIntegral hK x y p.2} := by
    have hleft : Continuous (fun p : BoundedContinuousFunction K F ×
        BoundedContinuousFunction K (E →L[ℝ] F) => p.1 y - p.1 x) := by
      fun_prop
    have hright : Continuous (fun p : BoundedContinuousFunction K F ×
        BoundedContinuousFunction K (E →L[ℝ] F) =>
        segmentIntegral hK x y p.2) :=
      (segmentIntegralCLM hK x y).continuous.comp continuous_snd
    exact isClosed_eq hleft hright
  have heq : {p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F) |
      hK.IsContinuousSegmentJet p} =
      ⋂ x : K, ⋂ y : K,
        {p | p.1 y - p.1 x = segmentIntegral hK x y p.2} := by
    ext p
    simp [Convex.IsContinuousSegmentJet]
  rw [heq]
  exact isClosed_iInter fun x => isClosed_iInter fun y => hsingle x y

/-- A sequence of continuous segment jets that is Cauchy in the maximum uniform norm
converges to another continuous segment jet. -/
theorem Convex.exists_limit_continuousSegmentJet {K : Set E} (hK : Convex ℝ K)
    (u : ℕ → BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F))
    (hu : CauchySeq u) (hjet : ∀ n, hK.IsContinuousSegmentJet (u n)) :
    ∃ p, hK.IsContinuousSegmentJet p ∧ Filter.Tendsto u Filter.atTop (nhds p) := by
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hu
  exact ⟨p, hK.isClosed_isContinuousSegmentJet.mem_of_tendsto hp
    (Filter.Eventually.of_forall hjet), hp⟩

/-- The restrictions of an interior `C¹` function and its continuous boundary jet satisfy
the segment identity. The product norm on these restrictions is the usual maximum of the
two uniform `C¹` data norms (`Prod.norm_def`). -/
theorem Convex.isContinuousSegmentJet_of_continuousOn_fderiv
    {K : Set E} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hinterior : (interior K).Nonempty) {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f K) (hG : ContinuousOn G K)
    (hdiff : DifferentiableOn ℝ f (interior K))
    (hderiv : ∀ x ∈ interior K, fderiv ℝ f x = G x)
    (p : BoundedContinuousFunction K F ×
      BoundedContinuousFunction K (E →L[ℝ] F))
    (hpval : ∀ x : K, p.1 x = f x.1)
    (hpderiv : ∀ x : K, p.2 x = G x.1) :
    hK.IsContinuousSegmentJet p := by
  intro x y
  have hmain := hK.sub_eq_integral_of_continuousOn_fderiv hclosed hinterior
    hf hG hdiff hderiv x.2 y.2
  calc
    p.1 y - p.1 x = f y.1 - f x.1 := by rw [hpval y, hpval x]
    _ = ∫ t in (0 : ℝ)..1, G (x.1 + t • (y.1 - x.1)) (y.1 - x.1) := hmain
    _ = segmentIntegral hK x y p.2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
      simp [hpderiv,
        clampedSegmentPoint_val_of_mem hK x y htI]

end
