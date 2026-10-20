module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanIntegral
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Regularity and diagonal jets of positive weighted means

The normalized fixed-interval representation yields a continuous first jet
on a closed coordinate triangle, including its diagonal.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- A positive weighted diagonal mean has a continuous first jet on a
nondegenerate closed coordinate triangle. -/
theorem contDiffOn_weightedDiagonalMean {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContDiffOn ℝ 1 (weightedDiagonalMean w f) (closedCoordTriangle a b) := by
  let Gprod : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := w • Gf + f • Gw
  have hprod : ContinuousOn (w * f) (closedCoordTriangle a b) := hw.mul hf
  have hGprod : ContinuousOn Gprod (closedCoordTriangle a b) := by
    exact (hw.smul hGf).add (hf.smul hGw)
  have hdiffprod : DifferentiableOn ℝ (w * f)
      (interior (closedCoordTriangle a b)) := hdw.mul hdf
  have hderivprod : ∀ p ∈ interior (closedCoordTriangle a b),
      fderiv ℝ (w * f) p = Gprod p := by
    intro p hp
    have hop : IsOpen (interior (closedCoordTriangle a b)) := isOpen_interior
    have hwAt := hdw.differentiableAt (hop.mem_nhds hp)
    have hfAt := hdf.differentiableAt (hop.mem_nhds hp)
    have heval : Gprod p = w p • Gf p + f p • Gw p := rfl
    rw [heval, ← hderivw p hp, ← hderivf p hp]
    exact fderiv_mul hwAt hfAt
  have hnum := contDiffOn_integral_diagonalSegment hab hprod hGprod
    hdiffprod hderivprod
  have hden := contDiffOn_integral_diagonalSegment hab hw hGw hdw hderivw
  have hden_ne : ∀ p ∈ closedCoordTriangle a b,
      (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) ≠ 0 := by
    intro p hp
    exact ne_of_gt (hc.trans_le (integral_diagonalSegment_weight_ge hw hweight hp))
  have hquot := hnum.div hden hden_ne
  apply hquot.congr
  intro p hp
  rfl

/-- The error of a positive weighted diagonal mean is `C¹` on the closed
coordinate triangle under the same first-jet hypotheses. -/
theorem contDiffOn_weightedDiagonalError {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContDiffOn ℝ 1 (weightedDiagonalError w f) (closedCoordTriangle a b) := by
  have hfC1 := (convex_closedCoordTriangle a b).contDiffOn_one_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hf hGf hdf hderivf
  have hmean := contDiffOn_weightedDiagonalMean hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hsub := hfC1.sub hmean
  apply hsub.congr
  intro p hp
  rfl

/-- The relative first derivatives of the weighted mean and its error vary
continuously, including along the diagonal of the triangle. -/
theorem continuousOn_fderivWithin_weightedDiagonalMean_and_error
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContinuousOn (fderivWithin ℝ (weightedDiagonalMean w f)
      (closedCoordTriangle a b)) (closedCoordTriangle a b) ∧
    ContinuousOn (fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b)) (closedCoordTriangle a b) := by
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  exact ⟨(contDiffOn_weightedDiagonalMean hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc).continuousOn_fderivWithin hunique (by norm_num),
    (contDiffOn_weightedDiagonalError hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc).continuousOn_fderivWithin hunique (by norm_num)⟩

private theorem weightedMean_diag_algebra (w f X Y : ℝ) (hw : w ≠ 0) :
    w * f * (Y * -(w ^ 2)⁻¹) + w⁻¹ * (w * X + f * Y) = X := by
  field_simp [hw]
  ring

/-- The relative derivative of a weighted diagonal mean at the diagonal
depends only on the first jet of the averaged function. -/
theorem fderivWithin_weightedDiagonalMean_diag_apply {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u : ℝ} (hu : a ≤ u) (hub : u ≤ b) (q : ℝ × ℝ) :
    (fderivWithin ℝ (weightedDiagonalMean w f) (closedCoordTriangle a b) (u, u)) q =
      Gf (u, u) (q.1, q.1 + (q.2 - q.1) / 2) := by
  let p : ℝ × ℝ := (u, u)
  have hp : p ∈ closedCoordTriangle a b := by
    simpa only [p, closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ u ∧ u ≤ u ∧ u ≤ b from ⟨hu, le_rfl, hub⟩)
  have hwu : w p ≠ 0 := ne_of_gt (hc.trans_le (hweight p hp))
  let N : ℝ × ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..1, (w * f) (diagonalSegment z t)
  let D : ℝ × ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..1, w (diagonalSegment z t)
  let Gprod : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := w • Gf + f • Gw
  have hprod : ContinuousOn (w * f) (closedCoordTriangle a b) := hw.mul hf
  have hGprod : ContinuousOn Gprod (closedCoordTriangle a b) :=
    (hw.smul hGf).add (hf.smul hGw)
  have hdiffprod : DifferentiableOn ℝ (w * f)
      (interior (closedCoordTriangle a b)) := hdw.mul hdf
  have hderivprod : ∀ z ∈ interior (closedCoordTriangle a b),
      fderiv ℝ (w * f) z = Gprod z := by
    intro z hz
    have hwAt := hdw.differentiableAt (isOpen_interior.mem_nhds hz)
    have hfAt := hdf.differentiableAt (isOpen_interior.mem_nhds hz)
    have heval : Gprod z = w z • Gf z + f z • Gw z := rfl
    rw [heval, ← hderivw z hz, ← hderivf z hz]
    exact fderiv_mul hwAt hfAt
  have hN : HasFDerivWithinAt N (integralDiagonalSegmentJet Gprod p)
      (closedCoordTriangle a b) p :=
    hasFDerivWithinAt_integral_diagonalSegment hab hprod hGprod
      hdiffprod hderivprod hp
  have hD : HasFDerivWithinAt D (integralDiagonalSegmentJet Gw p)
      (closedCoordTriangle a b) p :=
    hasFDerivWithinAt_integral_diagonalSegment hab hw hGw hdw hderivw hp
  have hDval : D p = w p := by simp [D, p, diagonalSegment]
  have hNval : N p = w p * f p := by simp [N, p, diagonalSegment, Pi.mul_apply]
  have hDne : D p ≠ 0 := by rw [hDval]; exact hwu
  have hInv : HasFDerivWithinAt (fun z => (D z)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(D p ^ 2)⁻¹)).comp
        (integralDiagonalSegmentJet Gw p))
      (closedCoordTriangle a b) p := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_inv hDne).comp_hasFDerivWithinAt p hD
  have hmul := hN.mul hInv
  have hEq : EqOn (weightedDiagonalMean w f) (N * fun z => (D z)⁻¹)
      (closedCoordTriangle a b) := by
    intro z hz
    simp [weightedDiagonalMean, N, D, div_eq_mul_inv, Pi.mul_apply]
  have hmean := hmul.congr' hEq hp
  have hdiffWithin := hmean.fderivWithin
    ((uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)) p hp)
  rw [hdiffWithin]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, hNval, hDval]
  have hJf := integralDiagonalSegmentJet_diag_apply Gf u q
  have hJw := integralDiagonalSegmentJet_diag_apply Gw u q
  have hJprod := integralDiagonalSegmentJet_diag_apply Gprod u q
  simp only [p] at hJf hJw hJprod ⊢
  rw [hJw, hJprod]
  have hprodval : Gprod (u, u) (q.1, q.1 + (q.2 - q.1) / 2) =
      w (u, u) * Gf (u, u) (q.1, q.1 + (q.2 - q.1) / 2) +
        f (u, u) * Gw (u, u) (q.1, q.1 + (q.2 - q.1) / 2) := by
    simp [Gprod, smul_eq_mul]
  rw [hprodval]
  simpa only [p] using weightedMean_diag_algebra
    (w (u, u)) (f (u, u))
    (Gf (u, u) (q.1, q.1 + (q.2 - q.1) / 2))
    (Gw (u, u) (q.1, q.1 + (q.2 - q.1) / 2)) hwu

/-- The relative derivative of the weighted-mean error at the diagonal is
the difference between the original jet and its endpoint average. -/
theorem fderivWithin_weightedDiagonalError_diag_apply {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u : ℝ} (hu : a ≤ u) (hub : u ≤ b) (q : ℝ × ℝ) :
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) (u, u)) q =
      Gf (u, u) q - Gf (u, u) (q.1, q.1 + (q.2 - q.1) / 2) := by
  have hp : (u, u) ∈ closedCoordTriangle a b := by
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ u ∧ u ≤ u ∧ u ≤ b from ⟨hu, le_rfl, hub⟩)
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hfC1 := (convex_closedCoordTriangle a b).contDiffOn_one_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hf hGf hdf hderivf
  have hmeanC1 := contDiffOn_weightedDiagonalMean hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hsub := fderivWithin_sub (hunique (u, u) hp)
    ((hfC1.differentiableOn (by norm_num)) (u, u) hp)
    ((hmeanC1.differentiableOn (by norm_num)) (u, u) hp)
  have herror : weightedDiagonalError w f = f - weightedDiagonalMean w f := by
    funext z
    rfl
  rw [herror, hsub]
  have hfjet := (convex_closedCoordTriangle a b).fderivWithin_eq_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hf hGf hdf hderivf hp
  rw [hfjet, sub_apply]
  rw [fderivWithin_weightedDiagonalMean_diag_apply hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hu hub q]

/-- The four diagonal coordinate identities for the weighted mean and its
error, expressed through their relative derivatives on the closed triangle. -/
theorem weightedDiagonalMean_diag_coordinate_derivatives {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u : ℝ} (hu : a ≤ u) (hub : u ≤ b) :
    (fderivWithin ℝ (weightedDiagonalMean w f) (closedCoordTriangle a b) (u, u)) (0, 1) =
        Gf (u, u) (0, 1) / 2 ∧
    (fderivWithin ℝ (weightedDiagonalMean w f) (closedCoordTriangle a b) (u, u)) (1, 0) =
        Gf (u, u) (1, 0) + Gf (u, u) (0, 1) / 2 ∧
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) (u, u)) (0, 1) =
        Gf (u, u) (0, 1) / 2 ∧
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) (u, u)) (1, 0) =
        -Gf (u, u) (0, 1) / 2 := by
  have hvvec : ((0 : ℝ), (1 : ℝ) / 2) = (1 / 2 : ℝ) • (0, 1) := by
    ext <;> norm_num [smul_eq_mul]
  have huvec : ((1 : ℝ), (1 : ℝ) / 2) =
      (1, 0) + (1 / 2 : ℝ) • (0, 1) := by
    ext <;> norm_num [smul_eq_mul]
  have hvG : Gf (u, u) (0, (1 : ℝ) / 2) = Gf (u, u) (0, 1) / 2 := by
    rw [hvvec, map_smul]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have huG : Gf (u, u) (1, (1 : ℝ) / 2) =
      Gf (u, u) (1, 0) + Gf (u, u) (0, 1) / 2 := by
    rw [huvec, map_add, map_smul]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hφv := fderivWithin_weightedDiagonalMean_diag_apply hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hu hub (0, 1)
  have hφu := fderivWithin_weightedDiagonalMean_diag_apply hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hu hub (1, 0)
  have hHv := fderivWithin_weightedDiagonalError_diag_apply hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hu hub (0, 1)
  have hHu := fderivWithin_weightedDiagonalError_diag_apply hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hu hub (1, 0)
  norm_num at hφv hφu hHv hHu
  rw [hvG] at hφv hHv
  rw [huG] at hφu hHu
  constructor
  · exact hφv
  constructor
  · exact hφu
  constructor
  · rw [hHv]
    ring
  · rw [hHu]
    ring

/-- The supremum bound for the weighted-mean error under continuous
interior first-jet hypotheses on the closed triangle. -/
theorem abs_weightedDiagonalError_le_csSup_vertical_fderiv
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    |weightedDiagonalError w f (u, v)| ≤
      sSup ((fun p => ‖Gf p (0, 1)‖) '' closedCoordTriangle a b) * (v - u) := by
  apply abs_weightedDiagonalError_le_csSup_vertical_jet hab hw hf hGf hweight hc
    (fun p hp => (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf hGf hdf hderivf hp) hu huv hv


end intervalIntegral

end
