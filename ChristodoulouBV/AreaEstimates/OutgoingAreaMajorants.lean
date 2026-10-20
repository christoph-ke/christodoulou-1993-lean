module

public import ChristodoulouBV.AreaEstimates.LogTransport
public import ChristodoulouBV.AreaEstimates.ScalarAreaIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Logarithmic residual majorants for the area estimates

The incoming logarithmic residual has the corrected `- f*` sign from the
sign correction of (4.11b)–(4.13b) and its extension to the area estimates;
see ERRATA.md, ERR-23.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem incoming_area_triangle_carrier :
    {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} =
      openCoordTriangle 0 1 := by
  ext p
  simp only [openCoordTriangle, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h0u, hu1⟩, ⟨huv, hv1⟩⟩
    exact ⟨h0u, huv, hv1⟩
  · rintro ⟨h0u, huv, hv1⟩
    exact ⟨⟨h0u, huv.trans hv1⟩, ⟨huv, hv1⟩⟩

/-- The outgoing logarithmic majorant `G(v)` from (4.19b). -/
noncomputable def sourceOutgoingLogMajorant (S : Fields) (v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |sourceOutgoingLogResidual S 0 v| +
    ∫⁻ u in Ioo 0 v,
      ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|

/-- Equation (4.19b), the defining expression for `G`. -/
theorem eq4_19b {S : Fields}
    (_H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {v : ℝ} (_hv : v ∈ Ioo (0 : ℝ) 1) :
    sourceOutgoingLogMajorant S v =
      ENNReal.ofReal |sourceOutgoingLogResidual S 0 v| +
        ∫⁻ u in Ioo 0 v,
          ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det| :=
  rfl

/-- Equation (4.19a): the outgoing logarithmic residual is bounded by `G`. -/
theorem eq4_19a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |sourceOutgoingLogResidual S u v| ≤
      sourceOutgoingLogMajorant S v := by
  exact (eq4_12a H hr hcenter hboot hp).trans (by
    simp only [sourceOutgoingLogMajorant]
    exact add_le_add le_rfl
      (lintegral_mono_set (fun x hx => ⟨hx.1, hx.2.trans hp.2.1⟩)))

/-- Equation (4.19c): `G` has integral bounded by the initial logarithmic
residual and the analytic area. The source's universal `c` is `108`. -/
theorem eq4_19c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫⁻ v in Ioo (0 : ℝ) 1, sourceOutgoingLogMajorant S v) ≤
      ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
        smoothAnalyticArea (sourcePhiBetaNuMap S)
          (openCoordTriangle 0 1) := by
  let I : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |sourceOutgoingLogResidual S 0 v|
  let J : ℝ → ℝ≥0∞ := fun v => ∫⁻ u in Ioo 0 v,
    ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|
  have hIOn : IntegrableOn (fun v => |sourceOutgoingLogResidual S 0 v|)
      (Ioo (0 : ℝ) 1) := by
    have h := (initial_log_residual_integrable H hr hcenter hboot).1
    exact h.mono_set Ioo_subset_Ioc_self
  have hI : AEMeasurable I (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hIOn.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hReal : (∫⁻ v in Ioo (0 : ℝ) 1, I v) =
      ENNReal.ofReal
        (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    exact (ofReal_integral_eq_lintegral_ofReal hIOn
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  have hT : MeasurableSet (openCoordTriangle 0 1) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hJac : (∫⁻ v in Ioo (0 : ℝ) 1, J v) =
      smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) := by
    let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det|
    have hK : AEMeasurable K (volume.restrict (openCoordTriangle 0 1)) :=
      (source_log_jacobian_densities_measurable S).1.aemeasurable
    rw [smooth_analytic_area _ hT]
    simpa only [J, K, incoming_area_triangle_carrier] using
      (lintegral_open_triangle_swap 0 1 K (by
        simpa only [incoming_area_triangle_carrier] using hK)).symm
  calc
    (∫⁻ v in Ioo (0 : ℝ) 1, sourceOutgoingLogMajorant S v) =
        (∫⁻ v in Ioo (0 : ℝ) 1, I v) +
          (∫⁻ v in Ioo (0 : ℝ) 1, J v) := by
      change (∫⁻ v in Ioo (0 : ℝ) 1, I v + J v) = _
      exact lintegral_add_left' hI J
    _ = ENNReal.ofReal
          (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) := by rw [hReal, hJac]
    _ ≤ ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) :=
      add_le_add
        (ENNReal.ofReal_le_ofReal
          (initial_log_residual H hr hcenter hboot)) le_rfl

/-- The incoming logarithmic majorant `G*(u)` from (4.25b), with the
corrected incoming residual from the sign correction described in ERRATA.md, ERR-23. -/
noncomputable def sourceIncomingLogMajorant (S : Fields) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |deriv (fun t => Real.log (-S.nu t t)) u| +
    ∫⁻ v in Ioo u 1,
      ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det|

/-- Equation (4.25b), the defining expression for `G*`. -/
theorem eq4_25b {S : Fields}
    (_H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {u : ℝ} (_hu : u ∈ Ioo (0 : ℝ) 1) :
    sourceIncomingLogMajorant S u =
      ENNReal.ofReal |deriv (fun t => Real.log (-S.nu t t)) u| +
        ∫⁻ v in Ioo u 1,
          ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det| :=
  rfl

/-- Corrected (4.25a): the incoming residual with `- f*` is bounded by
`G*`. This follows the sign correction in (4.11b)–(4.13b)
and its extension to the area estimates; see ERRATA.md, ERR-23. -/
theorem eq4_25a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |sourceIncomingLogResidual S u v| ≤
      sourceIncomingLogMajorant S u := by
  exact (eq4_13a H hr hcenter hboot hp).trans (by
    simp only [sourceIncomingLogMajorant]
    exact add_le_add le_rfl
      (lintegral_mono_set (Ioo_subset_Ioo_right hp.2.2.le)))

/-- Equation (4.25c): the incoming majorant integral is bounded by diagonal
logarithmic variation and the analytic area. Its residual has the corrected
sign from the sign correction of (4.11b)–(4.13b) and its extension to the area estimates; see ERRATA.md, ERR-23. -/
theorem eq4_25c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S) :
    (∫⁻ u in Ioo (0 : ℝ) 1, sourceIncomingLogMajorant S u) ≤
      eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
        smoothAnalyticArea (sourcePhiAlphaLamMap S)
          (openCoordTriangle 0 1) := by
  let I : ℝ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal |deriv (fun t => Real.log (-S.nu t t)) u|
  let J : ℝ → ℝ≥0∞ := fun u => ∫⁻ v in Ioo u 1,
    ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det|
  have hI : AEMeasurable I (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((measurable_deriv (fun t => Real.log (-S.nu t t))).abs.ennreal_ofReal).aemeasurable
  have hAxis : (∫⁻ u in Ioo (0 : ℝ) 1, I u) ≤
      eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) := by
    let b : ℕ → ℝ := fun n => 1 - 1 / (n + 1 : ℝ)
    let E : ℕ → Set ℝ := fun n => Ioo 0 (b n)
    have hbmono : Monotone b := by
      intro n m hnm
      dsimp [b]
      have hden : (n + 1 : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hnm 1
      have hpos : (0 : ℝ) < n + 1 := by positivity
      have hfrac : 1 / (m + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) :=
        one_div_le_one_div_of_le hpos hden
      linarith only [hfrac]
    have hEmono : Monotone E := by
      intro n m hnm x hx
      exact ⟨hx.1, hx.2.trans_le (hbmono hnm)⟩
    have hcover : (⋃ n, E n) = Ioo (0 : ℝ) 1 := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
        have hb1 : b n < 1 := by
          dsimp [b]
          have hfrac : 0 < 1 / (n + 1 : ℝ) := by positivity
          linarith only [hfrac]
        exact ⟨hxn.1, hxn.2.trans hb1⟩
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx.2)
        apply Set.mem_iUnion.mpr
        refine ⟨n, hx.1, ?_⟩
        dsimp [E, b]
        linarith only [hn]
    have hdir : Directed (· ⊆ ·) E := by
      intro n m
      exact ⟨max n m, hEmono (le_max_left n m), hEmono (le_max_right n m)⟩
    have hbound (n : ℕ) :
        (∫⁻ u in E n, I u) ≤
          eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) := by
      by_cases hn : n = 0
      · subst n
        have hE : E 0 = ∅ := by simp [E, b]
        simp [hE]
      · have hb0 : 0 < b n := by
          dsimp [b]
          have hnat : 1 < n + 1 := by omega
          have hlt : (1 : ℝ) < n + 1 := by exact_mod_cast hnat
          have hpos : (0 : ℝ) < n + 1 := by positivity
          have : 1 / (n + 1 : ℝ) < 1 := (div_lt_iff₀ hpos).2 (by linarith)
          linarith
        have hb1 : b n < 1 := by
          dsimp [b]
          have hfrac : 0 < 1 / (n + 1 : ℝ) := by positivity
          linarith only [hfrac]
        simpa only [E, I] using
          axis_log_derivative_lintegral_le_variation H ⟨hb0, hb1⟩
    calc
      (∫⁻ u in Ioo (0 : ℝ) 1, I u) = ∫⁻ u in ⋃ n, E n, I u := by rw [hcover]
      _ = ⨆ n, ∫⁻ u in E n, I u := setLIntegral_iUnion_of_directed I hdir
      _ ≤ eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) := iSup_le hbound
  have hT : MeasurableSet (openCoordTriangle 0 1) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hJac : (∫⁻ u in Ioo (0 : ℝ) 1, J u) =
      smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) := by
    let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) p).det|
    have hK : AEMeasurable K (volume.restrict (openCoordTriangle 0 1)) :=
      (source_log_jacobian_densities_measurable S).2.aemeasurable
    rw [smooth_analytic_area _ hT]
    simpa only [J, K, incoming_area_triangle_carrier] using
      (lintegral_open_triangle 0 1 K (by
        simpa only [incoming_area_triangle_carrier] using hK)).symm
  calc
    (∫⁻ u in Ioo (0 : ℝ) 1, sourceIncomingLogMajorant S u) =
        (∫⁻ u in Ioo (0 : ℝ) 1, I u) +
          (∫⁻ u in Ioo (0 : ℝ) 1, J u) := by
      change (∫⁻ u in Ioo (0 : ℝ) 1, I u + J u) = _
      exact lintegral_add_left' hI J
    _ ≤ eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 1) := by
      rw [hJac]
      exact add_le_add hAxis le_rfl

/-- The outgoing logarithmic majorant is measurable on its source interval,
in the almost everywhere sense needed by Tonelli. -/
theorem sourceOutgoingLogMajorant_aemeasurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    AEMeasurable (sourceOutgoingLogMajorant S)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let T := openCoordTriangle 0 1
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det|
  let F : ℝ → ℝ≥0∞ := fun v =>
    ∫⁻ u, T.indicator J (u, v)
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hJ : Measurable J := (source_log_jacobian_densities_measurable S).1
  have hF : Measurable F := (hJ.indicator hT).lintegral_prod_left'
  have hIOn : IntegrableOn (fun v => |sourceOutgoingLogResidual S 0 v|)
      (Ioo (0 : ℝ) 1) := by
    have h := (initial_log_residual_integrable H hr hcenter hboot).1
    exact h.mono_set Ioo_subset_Ioc_self
  have hI : AEMeasurable
      (fun v => ENNReal.ofReal |sourceOutgoingLogResidual S 0 v|)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hIOn.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hFeq (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) :
      F v = ∫⁻ u in Ioo 0 v,
        ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det| := by
    have hfiber : (fun u => T.indicator J (u, v)) =
        (Ioo 0 v).indicator (fun u => J (u, v)) := by
      funext u
      by_cases hu : u ∈ Ioo (0 : ℝ) v
      · have hp : (u, v) ∈ T := ⟨hu.1, hu.2, hv.2⟩
        simp only [indicator_of_mem hp, indicator_of_mem hu]
      · have hp : (u, v) ∉ T := by
          intro hx
          exact hu ⟨hx.1, hx.2.1⟩
        simp only [indicator_of_notMem hp, indicator_of_notMem hu]
    rw [show F v = ∫⁻ u, T.indicator J (u, v) from rfl,
      hfiber, lintegral_indicator measurableSet_Ioo]
  have hEq : (sourceOutgoingLogMajorant S) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun v => ENNReal.ofReal |sourceOutgoingLogResidual S 0 v| + F v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    simp only [sourceOutgoingLogMajorant, hFeq v hv]
  exact (hI.add hF.aemeasurable).congr hEq.symm

/-- The corrected incoming logarithmic majorant is almost everywhere
measurable on the source interval. -/
theorem sourceIncomingLogMajorant_aemeasurable (S : Fields) :
    AEMeasurable (sourceIncomingLogMajorant S)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let T := openCoordTriangle 0 1
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) p).det|
  let F : ℝ → ℝ≥0∞ := fun u =>
    ∫⁻ v, T.indicator J (u, v)
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hJ : Measurable J := (source_log_jacobian_densities_measurable S).2
  have hF : Measurable F := (hJ.indicator hT).lintegral_prod_right'
  have hI : Measurable
      (fun u => ENNReal.ofReal
        |deriv (fun t => Real.log (-S.nu t t)) u|) :=
    ((measurable_deriv _).abs).ennreal_ofReal
  have hFeq (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      F u = ∫⁻ v in Ioo u 1,
        ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det| := by
    have hfiber : (fun v => T.indicator J (u, v)) =
        (Ioo u 1).indicator (fun v => J (u, v)) := by
      funext v
      by_cases hv : v ∈ Ioo u 1
      · have hp : (u, v) ∈ T := ⟨hu.1, hv.1, hv.2⟩
        simp only [indicator_of_mem hp, indicator_of_mem hv]
      · have hp : (u, v) ∉ T := by
          intro hx
          exact hv ⟨hx.2.1, hx.2.2⟩
        simp only [indicator_of_notMem hp, indicator_of_notMem hv]
    rw [show F u = ∫⁻ v, T.indicator J (u, v) from rfl,
      hfiber, lintegral_indicator measurableSet_Ioo]
  have hEq : (sourceIncomingLogMajorant S) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun u => ENNReal.ofReal
        |deriv (fun t => Real.log (-S.nu t t)) u| + F u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simp only [sourceIncomingLogMajorant, hFeq u hu]
  exact (hI.aemeasurable.add hF.aemeasurable).congr hEq.symm

end ChristodoulouBV

end
