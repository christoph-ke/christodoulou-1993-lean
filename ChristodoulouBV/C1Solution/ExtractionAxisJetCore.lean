module

public import ChristodoulouBV.C1Solution.ExtractionRemovable
public import ChristodoulouBV.C1Solution.ExtractionJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Axis jets of a function with a continuous gap factor

These elementary closed-triangle lemmas identify first jets on the axis
without assuming that the gap factor itself is differentiable.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- A C¹ function that vanishes along the diagonal has opposite coordinate
derivatives there, including at the two vertices. -/
theorem diagonal_coordinate_jets_sum_zero {B : ℝ} (hB : 0 < B)
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (haxis : ∀ u ∈ Icc 0 B, F (u, u) = 0)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, u)) (1, 0) +
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, u)) (0, 1) = 0 := by
  let K := closedCoordTriangle 0 B
  have hdiagOpen : ∀ t ∈ Ioo 0 B,
      (fderivWithin ℝ F K (t, t)) (1, 0) +
        (fderivWithin ℝ F K (t, t)) (0, 1) = 0 := by
    intro t ht
    have htK : (t, t) ∈ K := ⟨ht.1.le, le_rfl, ht.2.le⟩
    have hdiff : DifferentiableWithinAt ℝ F K (t, t) :=
      hF.differentiableOn (by norm_num) (t, t) htK
    have hpair : HasDerivAt (fun s : ℝ => (s, s)) (1, 1) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_id' t)
    have hnear : ∀ᶠ s in 𝓝 t, (s, s) ∈ K := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact ⟨hs.1.le, le_rfl, hs.2.le⟩
    have hcomp : HasDerivAt (fun s => F (s, s))
        ((fderivWithin ℝ F K (t, t)) (1, 1)) t := by
      simpa only [Function.comp_def] using
        (hdiff.hasFDerivWithinAt.comp_hasDerivAt
          (f := fun s : ℝ => (s, s)) t hpair hnear)
    have hzero : HasDerivAt (fun s => F (s, s)) 0 t := by
      have heq : (fun s => F (s, s)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact haxis s ⟨hs.1.le, hs.2.le⟩
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
    have hvec : ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
      ext <;> norm_num
    rw [hvec, map_add] at hcomp
    exact hcomp.unique hzero
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hjet : ContinuousOn (fun p => fderivWithin ℝ F K p) K :=
    hF.continuousOn_fderivWithin hunique (by norm_num)
  have hcont : ContinuousOn (fun t =>
      (fderivWithin ℝ F K (t, t)) (1, 0) +
        (fderivWithin ℝ F K (t, t)) (0, 1)) (Icc 0 B) :=
    ((hjet.clm_apply continuousOn_const).add
      (hjet.clm_apply continuousOn_const)).comp
      (continuous_id.prodMk continuous_id).continuousOn
      (fun t ht => ⟨ht.1, le_rfl, ht.2⟩)
  have hEq : EqOn (fun t =>
      (fderivWithin ℝ F K (t, t)) (1, 0) +
        (fderivWithin ℝ F K (t, t)) (0, 1)) (fun _ => 0)
      (Icc 0 B) :=
    (show EqOn (fun t =>
      (fderivWithin ℝ F K (t, t)) (1, 0) +
        (fderivWithin ℝ F K (t, t)) (0, 1)) (fun _ => 0)
      (Ioo 0 B) from hdiagOpen).of_subset_closure hcont continuousOn_const
      Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt hB)])
  exact hEq hu

/-- If a C¹ field is the coordinate gap times a continuous field, its axis
coordinate jets are minus and plus that field, respectively. -/
theorem axis_coordinate_jets_of_gap_factor {B : ℝ} (hB : 0 < B)
    {F P : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hP : ContinuousOn P (closedCoordTriangle 0 B))
    (hfactor : ∀ p ∈ closedCoordTriangle 0 B,
      F p = (p.2 - p.1) * P p)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -P (u, u) ∧
    (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, u)) (0, 1) =
      P (u, u) := by
  let K := closedCoordTriangle 0 B
  let G := fderivWithin ℝ F K
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG : ContinuousOn G K :=
    hF.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ F (interior K) :=
    (hF.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K, fderiv ℝ F p = G p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      (hdiff.differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hdiag (t : ℝ) (ht : t ∈ Icc 0 B) : F (t, t) = 0 := by
    rw [hfactor (t, t) ⟨ht.1, le_rfl, ht.2⟩]
    ring
  have hmeanOpen : EqOn (intervalIntegral.verticalJetMean G) P
      (openCoordTriangle 0 B) := by
    intro p hp
    have hpK : p ∈ K := interior_subset (by
      rw [interior_closedCoordTriangle]; exact hp)
    have hmain := intervalIntegral.sub_diag_eq_gap_mul_verticalJetMean hB
      hF.continuousOn hG hdiff hderiv hpK
    have hdiagP : p.1 ∈ Icc 0 B := ⟨hpK.1, hpK.2.1.trans hpK.2.2⟩
    rw [hdiag p.1 hdiagP, sub_zero, hfactor p hpK] at hmain
    have hd : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hp.2.1.ne'
    exact (mul_left_cancel₀ hd hmain.symm)
  have hmean : EqOn (intervalIntegral.verticalJetMean G) P K :=
    hmeanOpen.of_subset_closure
      (intervalIntegral.continuousOn_verticalJetMean hG) hP
      (fun _ hp => interior_subset (by rw [interior_closedCoordTriangle]; exact hp))
      (by rw [closure_openCoordTriangle hB])
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hv : G (u, u) (0, 1) = P (u, u) := by
    simpa only [intervalIntegral.verticalJetMean_diag] using hmean hp
  have hsum := diagonal_coordinate_jets_sum_zero hB hF hdiag hu
  exact ⟨by linarith, hv⟩

end ChristodoulouBV.C1Solution

end
