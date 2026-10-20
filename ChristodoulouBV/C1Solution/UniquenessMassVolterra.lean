module

public import ChristodoulouBV.C1Solution.UniquenessKernelRegularity
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraJet
import ChristodoulouBV.C1Solution.Uniqueness
import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Volterra representation of the canonical mass

The canonical double mass and the attenuated Volterra integral solve the
same vertical linear equation with zero axis data.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV.C1Solution

/-- The canonical double mass is the attenuated Volterra integral of its
quadratic source and quotient kernel on the closed triangle. -/
theorem canonical_mass_numerator_eq_attenuatedVolterra {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMassNumerator b S p =
      intervalIntegral.attenuatedVolterraIntegral
        (intervalIntegral.weightedDiagonalQuadraticKernel
          (fun q => S.lam q.1 q.2) (outgoingQuotient S))
        (intervalIntegral.weightedDiagonalQuotientKernel
          (fun q => S.lam q.1 q.2) (outgoingQuotient S)) p.1 p.2 := by
  let K := closedCoordTriangle 0 B
  let j := intervalIntegral.weightedDiagonalQuadraticKernel
    (fun q => S.lam q.1 q.2) (outgoingQuotient S)
  let k := intervalIntegral.weightedDiagonalQuotientKernel
    (fun q => S.lam q.1 q.2) (outgoingQuotient S)
  let J := canonicalMassNumerator b S
  let V : ℝ × ℝ → ℝ := fun q =>
    intervalIntegral.attenuatedVolterraIntegral j k q.1 q.2
  have hjk := canonical_mass_kernels_contDiffOn hB hBb H
  have hJc1 := (canonical_mass_numerator_cubic_factor hB hBb H).1
  have hVc1 : ContDiffOn ℝ 1 V K :=
    intervalIntegral.contDiffOn_attenuatedVolterraIntegral hB hjk.1 hjk.2
  rcases p with ⟨u, v⟩
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · let kk : ℝ → ℝ := fun t => -k (u, t)
    let g : ℝ → ℝ := fun t => j (u, t)
    let y : ℝ → ℝ := fun t => J (u, t)
    let z : ℝ → ℝ := fun t => V (u, t)
    have hmap : Set.MapsTo (fun t : ℝ => (u, t)) (Icc u v) K := by
      intro t ht
      exact ⟨hp.1, ht.1, ht.2.trans hp.2.2⟩
    have hkcont : ContinuousOn kk (Icc u v) :=
      (hjk.2.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap).neg
    have hgcont : ContinuousOn g (Icc u v) :=
      hjk.1.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hycont : ContinuousOn y (Icc u v) :=
      hJc1.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hzcont : ContinuousOn z (Icc u v) :=
      hVc1.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hki : IntervalIntegrable kk volume u v :=
      hkcont.intervalIntegrable_of_Icc huv.le
    have hgi : IntervalIntegrable g volume u v :=
      hgcont.intervalIntegrable_of_Icc huv.le
    have hky : IntervalIntegrable (fun t => kk t * y t) volume u v :=
      (hkcont.mul hycont).intervalIntegrable_of_Icc huv.le
    have hkz : IntervalIntegrable (fun t => kk t * z t) volume u v :=
      (hkcont.mul hzcont).intervalIntegrable_of_Icc huv.le
    have hODEy : ∀ t ∈ Icc u v,
        y t - y u = ∫ s in u..t, (kk s * y s + g s) := by
      intro t ht
      have hFTC := integral_vertical_jet_eq_sub hB hJc1
        hp.1 ht.1 (ht.2.trans hp.2.2)
      dsimp [y]
      rw [← hFTC]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hsK : (u, s) ∈ K :=
        ⟨hp.1, hs.1, hs.2.trans (ht.2.trans hp.2.2)⟩
      change (fderivWithin ℝ J K (u, s)) (0, 1) =
        kk s * y s + g s
      rw [canonical_mass_numerator_vertical_ode hB hBb H
        hp.1 hs.1 (hs.2.trans (ht.2.trans hp.2.2))]
      dsimp [kk, y, g, j, k, J]
      ring
    have hODEz : ∀ t ∈ Icc u v,
        z t - z u = ∫ s in u..t, (kk s * z s + g s) := by
      intro t ht
      have hFTC := integral_vertical_jet_eq_sub hB hVc1
        hp.1 ht.1 (ht.2.trans hp.2.2)
      dsimp [z]
      rw [← hFTC]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hsK : (u, s) ∈ K :=
        ⟨hp.1, hs.1, hs.2.trans (ht.2.trans hp.2.2)⟩
      change (fderivWithin ℝ V K (u, s)) (0, 1) =
        kk s * z s + g s
      rw [intervalIntegral.fderivWithin_attenuatedVolterraIntegral_vertical
        hB hjk.1 hjk.2 hsK]
      dsimp [kk, y, z, g, j, k, V]
      ring
    have hzero : y u = z u := by
      simp [y, z, J, V, canonicalMassNumerator, canonicalMass_axis,
        intervalIntegral.attenuatedVolterraIntegral]
    exact intervalIntegral.eq_on_of_integral_eq huv.le hki hgi hky hkz
      hODEy hODEz hzero ⟨huv.le, le_rfl⟩
  · change u = v at huv
    subst v
    simp [canonicalMassNumerator, canonicalMass_axis,
      intervalIntegral.attenuatedVolterraIntegral]

end ChristodoulouBV.C1Solution

end
