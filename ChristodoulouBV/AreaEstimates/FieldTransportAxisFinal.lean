module

public import ChristodoulouBV.AreaEstimates.FieldTransportVariation
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Axis transport and equation (4.6)

The outgoing residual is transported horizontally to the axis. The regular
axis jet identities turn its endpoint into the diagonal trace derivative.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The outgoing residual estimate at the axis endpoint, used in (4.6). -/
theorem eq4_4a_axis {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal
      |deriv (fun t => S.alpha t t) u -
        deriv (fun t => S.lam t t) u * S.phi u u| ≤
      ENNReal.ofReal
        |deriv (S.alpha 0) u - deriv (S.lam 0) u * S.phi 0 u| +
      ∫⁻ x in Ioo 0 u,
        ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (x, u)).det| := by
  let B : ℝ := (u + 1) / 2
  let K := closedCoordTriangle 0 B
  let alpha : ℝ × ℝ → ℝ := fun p => S.alpha p.1 p.2
  let lam : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let phi : ℝ × ℝ → ℝ := fun p => S.phi p.1 p.2
  let alphaV : ℝ → ℝ := fun x => (fderivWithin ℝ alpha K (x, u)) (0, 1)
  let lamV : ℝ → ℝ := fun x => (fderivWithin ℝ lam K (x, u)) (0, 1)
  let lamU : ℝ → ℝ := fun x => (fderivWithin ℝ lam K (x, u)) (1, 0)
  let phiV : ℝ → ℝ := fun x => (fderivWithin ℝ phi K (x, u)) (0, 1)
  let phiU : ℝ → ℝ := fun x => (fderivWithin ℝ phi K (x, u)) (1, 0)
  let R : ℝ → ℝ := fun x => alphaV x - lamV x * phi (x, u)
  let J : ℝ → ℝ := fun x => lamU x * phiV x - lamV x * phiU x
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, hu.2]
  have hBb : B < 1 := by dsimp [B]; linarith only [hu.1, hu.2]
  have huB : u < B := by dsimp [B]; linarith only [hu.1, hu.2]
  have hmap : MapsTo (fun x : ℝ => (x, u)) (Icc 0 u) K := by
    intro x hx
    exact ⟨hx.1, hx.2, huB.le⟩
  obtain ⟨hLamK, _, hPhiK, _, _⟩ := C1Solution.five_fields_contDiffOn hB hBb H
  have hAlphaK := C1Solution.alpha_contDiffOn hB hBb H
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hLine : Continuous (fun x : ℝ => (x, u)) :=
    continuous_id.prodMk continuous_const
  have hJetCont {f : ℝ × ℝ → ℝ}
      (hf : ContDiffOn ℝ 1 f K) (e : ℝ × ℝ) :
      ContinuousOn (fun x => (fderivWithin ℝ f K (x, u)) e) (Icc 0 u) := by
    have hC : ContinuousOn (fun p => (fderivWithin ℝ f K p) e) K :=
      ((hf.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply
        continuousOn_const)
    exact hC.comp hLine.continuousOn hmap
  have hPhiLine : ContinuousOn (fun x => phi (x, u)) (Icc 0 u) :=
    hPhiK.continuousOn.comp hLine.continuousOn hmap
  have hRCont : ContinuousOn R (Icc 0 u) :=
    (hJetCont hAlphaK (0, 1)).sub
      ((hJetCont hLamK (0, 1)).mul hPhiLine)
  have hJCont : ContinuousOn J (Icc 0 u) :=
    ((hJetCont hLamK (1, 0)).mul (hJetCont hPhiK (0, 1))).sub
      ((hJetCont hLamK (0, 1)).mul (hJetCont hPhiK (1, 0)))
  have hJetEq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) u) :
      R x = (fderiv ℝ alpha (x, u)) (0, 1) -
        (fderiv ℝ lam (x, u)) (0, 1) * phi (x, u) ∧
      J x = (fderiv ℝ (sourceLamPhiMap S) (x, u)).det := by
    have hpK : (x, u) ∈ K := ⟨hx.1.le, hx.2.le, huB.le⟩
    have hpInt : (x, u) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨hx.1, hx.2, huB⟩
    have hnhds : K ∈ 𝓝 (x, u) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
    have hAlphaDiff : DifferentiableAt ℝ alpha (x, u) :=
      (hAlphaK.differentiableOn (by norm_num) (x, u) hpK).differentiableAt hnhds
    have hLamDiff : DifferentiableAt ℝ lam (x, u) :=
      (hLamK.differentiableOn (by norm_num) (x, u) hpK).differentiableAt hnhds
    have hPhiDiff : DifferentiableAt ℝ phi (x, u) :=
      (hPhiK.differentiableOn (by norm_num) (x, u) hpK).differentiableAt hnhds
    have haEq := fderivWithin_eq_fderiv (hUnique (x, u) hpK) hAlphaDiff
    have hlEq := fderivWithin_eq_fderiv (hUnique (x, u) hpK) hLamDiff
    have hpEq := fderivWithin_eq_fderiv (hUnique (x, u) hpK) hPhiDiff
    constructor
    · simp only [R, alphaV, lamV, haEq, hlEq]
    · simp only [J, lamU, lamV, phiV, phiU, hlEq, hpEq]
      exact (det_fderiv_prodMk hLamDiff hPhiDiff).symm
  have hRDeriv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) u) :
      HasDerivAt R (J x) x := by
    have hEq : R =ᶠ[𝓝 x] (fun y =>
        (fderiv ℝ alpha (y, u)) (0, 1) -
          (fderiv ℝ lam (y, u)) (0, 1) * phi (y, u)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (hJetEq y hy).1
    have hDeriv := eq4_alpha_jacobian H
      hx.1 hx.2 hu.2
    have hJx := (hJetEq x hx).2
    rw [hJx]
    exact hDeriv.congr_of_eventuallyEq hEq
  have hBound := ofReal_abs_endpoint_le_initial_add_lintegral
    hu.1.le hRCont hJCont hRDeriv
  have hAxis := axis_traces hB hBb H
    (show u ∈ Icc 0 B from ⟨hu.1.le, huB.le⟩)
  obtain ⟨_, _, _, _, _, _, _, _, _, hNuAxis, hBetaAxis⟩ := hAxis
  obtain ⟨hNuTrace, hBetaTrace⟩ :=
    axis_trace_derivatives hB hBb H
      (show u ∈ Ioo (0 : ℝ) B from ⟨hu.1, huB⟩)
  have hAlphaV : alphaV u = deriv (fun t => S.alpha t t) u := by
    dsimp [alphaV, alpha, K]
    rw [hBetaAxis] at hBetaTrace
    exact neg_inj.mp hBetaTrace
  have hLamV : lamV u = deriv (fun t => S.lam t t) u := by
    dsimp [lamV, lam, K]
    rw [hNuAxis] at hNuTrace
    exact neg_inj.mp hNuTrace
  have hRu : R u = deriv (fun t => S.alpha t t) u -
      deriv (fun t => S.lam t t) u * S.phi u u := by
    simp only [R, hAlphaV, hLamV]
    rfl
  have hR0 : R 0 = deriv (S.alpha 0) u -
      deriv (S.lam 0) u * S.phi 0 u := by
    have hα := (vertical_edge_hasDerivAt hAlphaK
      (show u ∈ Ioo (0 : ℝ) B from ⟨hu.1, huB⟩)).deriv
    have hLamEdge := (vertical_edge_hasDerivAt hLamK
      (show u ∈ Ioo (0 : ℝ) B from ⟨hu.1, huB⟩)).deriv
    have hα' : deriv (S.alpha 0) u = alphaV 0 := by
      simpa only [alphaV, alpha, K] using hα
    have hLamEdge' : deriv (S.lam 0) u = lamV 0 := by
      simpa only [lamV, lam, K] using hLamEdge
    rw [hα', hLamEdge']
  have hJIntegral :
      (∫⁻ x in Ioo 0 u, ENNReal.ofReal |J x|) =
        ∫⁻ x in Ioo 0 u,
          ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (x, u)).det| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [(hJetEq x hx).2]
  simpa only [hRu, hR0, hJIntegral] using hBound

/-- Equation (4.6): regular-axis variation of `α` is controlled by the
initial variation, axis variation of `λ`, and outgoing analytic area. -/
theorem eq4_6 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    eVariationOn (fun t => S.alpha t t) (Ioo 0 1) ≤
      sourceD S + ENNReal.ofReal (sourceP S) *
        eVariationOn (fun t => S.lam t t) (Ioo 0 1) +
      smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) := by
  let E := openCoordTriangle 0 1
  let F := sourceLamPhiMap S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |(fderiv ℝ F p).det|
  let R : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal
    |deriv (fun t => S.alpha t t) u -
      deriv (fun t => S.lam t t) u * S.phi u u|
  let I : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |deriv (S.alpha 0) u|
  have hopen : IsOpen E := by
    change IsOpen (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hmap : ContDiffOn ℝ 1 F E :=
    (sourceLamPhiMap_contDiffOn H).mono (fun p hp =>
      ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
  have hJ : AEMeasurable J (volume.restrict E) :=
    jacobianDensity_aemeasurable_of_contDiffOn hopen hmap
  have hI : AEMeasurable I (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (measurable_deriv (S.alpha 0)).abs.ennreal_ofReal.aemeasurable
  have hpoint (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      R u ≤ I u + ∫⁻ x in Ioo 0 u, J (x, u) := by
    have h0 := initial_lam_deriv_eq_zero H hr hu
    have hbound := eq4_4a_axis H hr hcenter hboot hu
    simpa only [R, I, J, F, h0, zero_mul, sub_zero] using hbound
  have hset : E = {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} := by
    ext p
    simp only [E, openCoordTriangle, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h0, h12, h21⟩
      exact ⟨⟨h0, h12.trans h21⟩, ⟨h12, h21⟩⟩
    · rintro ⟨⟨h0, _⟩, ⟨h12, h21⟩⟩
      exact ⟨h0, h12, h21⟩
  have hRaw : (∫⁻ u in Ioo 0 1, R u) ≤
      (∫⁻ u in Ioo 0 1, I u) + ∫⁻ p in E, J p := by
    calc
      (∫⁻ u in Ioo 0 1, R u) ≤
          ∫⁻ u in Ioo 0 1, I u + ∫⁻ x in Ioo 0 u, J (x, u) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact hpoint u hu
      _ = (∫⁻ u in Ioo 0 1, I u) +
          ∫⁻ u in Ioo 0 1, ∫⁻ x in Ioo 0 u, J (x, u) := by
        rw [lintegral_add_left' hI]
      _ = (∫⁻ u in Ioo 0 1, I u) + ∫⁻ p in E, J p := by
        congr 1
        exact (lintegral_open_triangle_swap 0 1 J (by
          simpa only [← hset] using hJ)).symm.trans (by rw [← hset])
  have hD : (∫⁻ u in Ioo 0 1, I u) = sourceD S :=
    (sourceD_eq_lintegral_initial_alpha H).symm
  have harea : (∫⁻ p in E, J p) = smoothAnalyticArea F E :=
    (smooth_analytic_area F hopen.measurableSet).symm
  have hResidual : (∫⁻ u in Ioo 0 1, R u) ≤
      sourceD S + smoothAnalyticArea F E := by
    simpa only [hD, harea] using hRaw
  have hPnn : 0 ≤ sourceP S :=
    (abs_nonneg (S.phi (1 / 2) (1 / 2))).trans
      (abs_phi_axis_le_sourceP H (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1))
  obtain ⟨hLam, _, hAlpha, _⟩ := unit_axis_traces_contDiffOn H
  have hAC (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc 0 1)) :
      AbsolutelyContinuousOnInterval f 0 1 :=
    (show ContDiffOn ℝ 1 f (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf).absolutelyContinuousOnInterval
  have hvar := variation_le_residual_add
    (by norm_num : (0 : ℝ) ≤ 1)
    (hAC _ hAlpha) (hAC _ hLam) hPnn
    (fun u hu => abs_phi_axis_le_sourceP H hu)
  calc
    eVariationOn (fun t => S.alpha t t) (Ioo 0 1) ≤
        (∫⁻ u in Ioo 0 1, R u) +
          ENNReal.ofReal (sourceP S) *
            eVariationOn (fun t => S.lam t t) (Ioo 0 1) := hvar
    _ ≤ sourceD S + smoothAnalyticArea F E +
        ENNReal.ofReal (sourceP S) *
          eVariationOn (fun t => S.lam t t) (Ioo 0 1) :=
      add_le_add_left hResidual _
    _ = _ := by ac_rfl

end ChristodoulouBV

end
