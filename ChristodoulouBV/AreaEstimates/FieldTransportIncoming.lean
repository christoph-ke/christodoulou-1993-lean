module

public import ChristodoulouBV.AreaEstimates.FieldTransportOutgoing
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Incoming field transport and regular-axis endpoint

The incoming residual starts on the diagonal. Its initial value is expressed
using the derivatives of the `α` and `λ` axis traces.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- Equation (4.5a): the incoming residual is bounded by its regular-axis
value and the Jacobian integral along the incoming segment. -/
theorem eq4_5a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ENNReal.ofReal
      |deriv (fun x => S.beta x v) u -
        deriv (fun x => S.nu x v) u * S.phi u v| ≤
      ENNReal.ofReal
        |deriv (fun x => S.beta x x) u -
          deriv (fun x => S.nu x x) u * S.phi u u| +
      ∫⁻ y in Ioo u v,
        ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, y)).det| := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let beta : ℝ × ℝ → ℝ := fun p => S.beta p.1 p.2
  let nu : ℝ × ℝ → ℝ := fun p => S.nu p.1 p.2
  let phi : ℝ × ℝ → ℝ := fun p => S.phi p.1 p.2
  let betaU : ℝ → ℝ := fun y => (fderivWithin ℝ beta K (u, y)) (1, 0)
  let nuU : ℝ → ℝ := fun y => (fderivWithin ℝ nu K (u, y)) (1, 0)
  let nuV : ℝ → ℝ := fun y => (fderivWithin ℝ nu K (u, y)) (0, 1)
  let phiU : ℝ → ℝ := fun y => (fderivWithin ℝ phi K (u, y)) (1, 0)
  let phiV : ℝ → ℝ := fun y => (fderivWithin ℝ phi K (u, y)) (0, 1)
  let R : ℝ → ℝ := fun y => betaU y - nuU y * phi (u, y)
  let J : ℝ → ℝ := fun y =>
    -(nuU y * phiV y - nuV y * phiU y)
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have huB : u < B := huv.trans hvB
  have hmap : MapsTo (fun y : ℝ => (u, y)) (Icc u v) K := by
    intro y hy
    exact ⟨hu.le, hy.1, hy.2.trans hvB.le⟩
  obtain ⟨_, hNuK, hPhiK, _, _⟩ := C1Solution.five_fields_contDiffOn hB hBb H
  have hBetaK := C1Solution.beta_contDiffOn hB hBb H
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hLine : Continuous (fun y : ℝ => (u, y)) :=
    continuous_const.prodMk continuous_id
  have hJetCont {f : ℝ × ℝ → ℝ}
      (hf : ContDiffOn ℝ 1 f K) (e : ℝ × ℝ) :
      ContinuousOn (fun y => (fderivWithin ℝ f K (u, y)) e) (Icc u v) := by
    have hC : ContinuousOn (fun p => (fderivWithin ℝ f K p) e) K :=
      ((hf.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply
        continuousOn_const)
    exact hC.comp hLine.continuousOn hmap
  have hPhiLine : ContinuousOn (fun y => phi (u, y)) (Icc u v) :=
    hPhiK.continuousOn.comp hLine.continuousOn hmap
  have hRCont : ContinuousOn R (Icc u v) :=
    (hJetCont hBetaK (1, 0)).sub
      ((hJetCont hNuK (1, 0)).mul hPhiLine)
  have hJCont : ContinuousOn J (Icc u v) :=
    (((hJetCont hNuK (1, 0)).mul (hJetCont hPhiK (0, 1))).sub
      ((hJetCont hNuK (0, 1)).mul (hJetCont hPhiK (1, 0)))).neg
  have hJetEq (y : ℝ) (hy : u < y ∧ y ≤ v) :
      R y = (fderiv ℝ beta (u, y)) (1, 0) -
        (fderiv ℝ nu (u, y)) (1, 0) * phi (u, y) ∧
      J y = -(fderiv ℝ (sourceNuPhiMap S) (u, y)).det := by
    have hyB : y < B := hy.2.trans_lt hvB
    have hpK : (u, y) ∈ K := ⟨hu.le, hy.1.le, hyB.le⟩
    have hpInt : (u, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu, hy.1, hyB⟩
    have hnhds : K ∈ 𝓝 (u, y) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
    have hBetaDiff : DifferentiableAt ℝ beta (u, y) :=
      (hBetaK.differentiableOn (by norm_num) (u, y) hpK).differentiableAt hnhds
    have hNuDiff : DifferentiableAt ℝ nu (u, y) :=
      (hNuK.differentiableOn (by norm_num) (u, y) hpK).differentiableAt hnhds
    have hPhiDiff : DifferentiableAt ℝ phi (u, y) :=
      (hPhiK.differentiableOn (by norm_num) (u, y) hpK).differentiableAt hnhds
    have hbEq := fderivWithin_eq_fderiv (hUnique (u, y) hpK) hBetaDiff
    have hnEq := fderivWithin_eq_fderiv (hUnique (u, y) hpK) hNuDiff
    have hpEq := fderivWithin_eq_fderiv (hUnique (u, y) hpK) hPhiDiff
    constructor
    · simp only [R, betaU, nuU, hbEq, hnEq]
    · simp only [J, nuU, nuV, phiU, phiV, hnEq, hpEq]
      change _ = -(fderiv ℝ (fun q => (nu q, phi q)) (u, y)).det
      rw [det_fderiv_prodMk hNuDiff hPhiDiff]
  have hRDeriv (y : ℝ) (hy : y ∈ Ioo u v) :
      HasDerivAt R (J y) y := by
    have hEq : R =ᶠ[𝓝 y] (fun z =>
        (fderiv ℝ beta (u, z)) (1, 0) -
          (fderiv ℝ nu (u, z)) (1, 0) * phi (u, z)) := by
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      exact (hJetEq z ⟨hz.1, hz.2.le⟩).1
    have hDeriv := eq4_beta_jacobian H
      hu hy.1 (hy.2.trans hv)
    have hJy := (hJetEq y ⟨hy.1, hy.2.le⟩).2
    rw [hJy]
    exact hDeriv.congr_of_eventuallyEq hEq
  have hBound := ofReal_abs_endpoint_le_initial_add_lintegral
    huv.le hRCont hJCont hRDeriv
  have hRv := (hJetEq v ⟨huv, le_rfl⟩).1
  have hRv' : R v = deriv (fun x => S.beta x v) u -
      deriv (fun x => S.nu x v) u * S.phi u v := by
    rw [hRv]
    have hpInt : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu, huv, hvB⟩
    have hnhds : K ∈ 𝓝 (u, v) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
    have hBetaDiff : DifferentiableAt ℝ beta (u, v) :=
      (hBetaK.differentiableOn (by norm_num) (u, v)
        ⟨hu.le, huv.le, hvB.le⟩).differentiableAt hnhds
    have hNuDiff : DifferentiableAt ℝ nu (u, v) :=
      (hNuK.differentiableOn (by norm_num) (u, v)
        ⟨hu.le, huv.le, hvB.le⟩).differentiableAt hnhds
    have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    have hBetaPair : HasDerivAt (fun t => beta (t, v))
        ((fderiv ℝ beta (u, v)) (1, 0)) u := by
      simpa only [Function.comp_def] using
        hBetaDiff.hasFDerivAt.comp_hasDerivAt u hpair
    have hNuPair : HasDerivAt (fun t => nu (t, v))
        ((fderiv ℝ nu (u, v)) (1, 0)) u := by
      simpa only [Function.comp_def] using
        hNuDiff.hasFDerivAt.comp_hasDerivAt u hpair
    rw [← hBetaPair.deriv, ← hNuPair.deriv]
  have hAxisEq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) B) :
      S.beta t t = -S.alpha t t ∧ S.nu t t = -S.lam t t := by
    have h := axis_traces hB hBb H
      (show t ∈ Icc 0 B from ⟨ht.1.le, ht.2.le⟩)
    exact ⟨h.2.2.2.2.1, h.2.2.1⟩
  have hBetaEq : (fun t => S.beta t t) =ᶠ[𝓝 u]
      (fun t => -S.alpha t t) := by
    filter_upwards [Ioo_mem_nhds hu huB] with t ht
    exact (hAxisEq t ht).1
  have hNuEq : (fun t => S.nu t t) =ᶠ[𝓝 u]
      (fun t => -S.lam t t) := by
    filter_upwards [Ioo_mem_nhds hu huB] with t ht
    exact (hAxisEq t ht).2
  have hBetaDeriv : deriv (fun t => S.beta t t) u =
      -deriv (fun t => S.alpha t t) u := by
    rw [hBetaEq.deriv_eq]
    exact deriv.neg
  have hNuDeriv : deriv (fun t => S.nu t t) u =
      -deriv (fun t => S.lam t t) u := by
    rw [hNuEq.deriv_eq]
    exact deriv.neg
  have hRu : R u = deriv (fun x => S.beta x x) u -
      deriv (fun x => S.nu x x) u * S.phi u u := by
    have haxis := axis_trace_derivatives hB hBb H
      (show u ∈ Ioo (0 : ℝ) B from ⟨hu, huB⟩)
    simp only [R, betaU, nuU, beta, nu, phi, K]
    rw [haxis.1, haxis.2]
    rw [hBetaDeriv, hNuDeriv]
  have hJIntegral :
      (∫⁻ y in Ioo u v, ENNReal.ofReal |J y|) =
        ∫⁻ y in Ioo u v,
          ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, y)).det| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [(hJetEq y ⟨hy.1, hy.2.le⟩).2, abs_neg]
  simpa only [hRv', hRu, hJIntegral] using hBound

end ChristodoulouBV

end
