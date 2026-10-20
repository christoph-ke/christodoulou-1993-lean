module

public import ChristodoulouBV.Existence.C1EndpointCore
public import ChristodoulouBV.Existence.C1EndpointTransportCutoff
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing residual passage to a finite maximal endpoint

The two finite-cutoff Section 4 transport estimates are transferred to the
patched development and exhausted to the maximal parameter.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- The two outgoing residuals of the endpoint patch agree pointwise with a
finite family member on the strict interior of that member's development. -/
theorem endpointPatch_outgoing_residual_eq
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b) :
    let P := endpointPatch family vStar
    sourceOutgoingAlphaResidual P u v =
      sourceOutgoingAlphaResidual (family b) u v ∧
    sourceOutgoingLogResidual P u v =
      sourceOutgoingLogResidual (family b) u v := by
  let P := endpointPatch family vStar
  have hvalues (t : ℝ) (ht : t ∈ Ioo u b) :=
    endpointPatch_agrees hfamily hb
      (show (u, t) ∈ developmentWithInitialEdge b from
        ⟨hu.le, ht.1, ht.2⟩)
  have hv : v ∈ Ioo u b := ⟨huv, hvb⟩
  obtain ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta⟩ := hvalues v hv
  have hAlphaEq : (P.alpha u) =ᶠ[𝓝 v] ((family b).alpha u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    exact (hvalues t ht).2.2.2.2.2.1
  have hLamEq : (P.lam u) =ᶠ[𝓝 v] ((family b).lam u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    exact (hvalues t ht).2.2.2.1
  have hLogEq : (fun t => Real.log (P.lam u t)) =ᶠ[𝓝 v]
      (fun t => Real.log ((family b).lam u t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    rw [(hvalues t ht).2.2.2.1]
  constructor
  · simp only [sourceOutgoingAlphaResidual]
    rw [hAlphaEq.deriv_eq, hLamEq.deriv_eq, hphi]
  · simp only [sourceOutgoingLogResidual, sourceLogCorrection,
      Fields.theta, Fields.zeta]
    rw [hLogEq.deriv_eq, hr, hphi, hm, hlam, hnu, halpha, hbeta]

/-- On a smaller outgoing wedge, both analytic areas of the endpoint patch
are exactly those of a finite member. -/
theorem endpointPatch_outgoing_wedge_area_eq
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {b u a : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (_hu : 0 < u) (_hua : u < a) (hab : a < b) :
    let P := endpointPatch family vStar
    smoothAnalyticArea (sourceLamPhiMap P)
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) =
      smoothAnalyticArea (sourceLamPhiMap (family b))
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) ∧
    smoothAnalyticArea (sourcePhiBetaNuMap P)
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) =
      smoothAnalyticArea (sourcePhiBetaNuMap (family b))
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) := by
  let P := endpointPatch family vStar
  let E := Ioo (0 : ℝ) u ×ˢ Ioo u a
  have hOpen : IsOpen E := isOpen_Ioo.prod isOpen_Ioo
  have hvalues (p : ℝ × ℝ) (hp : p ∈ E) :=
    endpointPatch_agrees hfamily hb
      (show p ∈ developmentWithInitialEdge b from
        ⟨hp.1.1.le, hp.1.2.trans hp.2.1, hp.2.2.trans hab⟩)
  have hLam : EqOn (sourceLamPhiMap P)
      (sourceLamPhiMap (family b)) E := by
    intro p hp
    obtain ⟨_, hphi, _, hlam, _, _, _⟩ := hvalues p hp
    simp only [sourceLamPhiMap]
    rw [hlam, hphi]
  have hBeta : EqOn (sourcePhiBetaNuMap P)
      (sourcePhiBetaNuMap (family b)) E := by
    intro p hp
    obtain ⟨_, hphi, _, _, hnu, _, hbeta⟩ := hvalues p hp
    simp only [sourcePhiBetaNuMap]
    rw [hphi, hnu, hbeta]
  exact ⟨smoothAnalyticArea_eq_of_eqOn_open _ _ hOpen hLam,
    smoothAnalyticArea_eq_of_eqOn_open _ _ hOpen hBeta⟩

/-- Both outgoing transport inequalities hold on every strict cutoff of the
patched endpoint development, with the very same initial and area terms. -/
theorem endpointPatch_outgoing_cutoff_bounds
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (_hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {u a : ℝ} (hu : 0 < u) (hua : u < a) (haStar : a < vStar) :
    let P := endpointPatch family vStar
    (∫⁻ v in Ioo u a,
      ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) ≤
      eVariationOn (P.alpha 0) (Ioo u a) +
        smoothAnalyticArea (sourceLamPhiMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u a) ∧
    (∫⁻ v in Ioo u a,
      ENNReal.ofReal |sourceOutgoingLogResidual P u v|) ≤
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|) +
        smoothAnalyticArea (sourcePhiBetaNuMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u a) := by
  let P := endpointPatch family vStar
  obtain ⟨B, haB, hBStar⟩ := exists_between haStar
  obtain ⟨b, hBb, hbStar⟩ := exists_between hBStar
  have hB : 0 < B := (hu.trans hua).trans haB
  have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hB.trans hBb, hbStar⟩
  obtain ⟨H, hdata⟩ := hfamily b hb
  have hAlpha := s6_finite_cutoff_alpha_residual_bound
    hB hBb H hdata hD (hu.trans hua) haB ⟨hu, hua⟩
  have hLog := s6_finite_cutoff_log_residual_bound
    hB hBb H hdata hD (hu.trans hua) haB ⟨hu, hua⟩
  have hR (v : ℝ) (hv : v ∈ Ioo u a) :=
    endpointPatch_outgoing_residual_eq hfamily hb hu hv.1
      (hv.2.trans (haB.trans hBb))
  have hAlphaLin :
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) =
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingAlphaResidual (family b) u v|) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [(hR v hv).1]
  have hLogLin :
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual P u v|) =
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual (family b) u v|) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [(hR v hv).2]
  have hInitialLin :
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|) =
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual (family b) 0 v|) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    rw [endpointPatch_initial_log_residual_eq hfamily hb
      ⟨hu.trans hv.1, hv.2.trans (haB.trans hBb)⟩]
  have hVar : eVariationOn (P.alpha 0) (Ioo u a) =
      eVariationOn ((family b).alpha 0) (Ioo u a) := by
    apply eVariationOn.congr
    intro v hv
    rw [(endpointPatch_initial_data hfamily
      ⟨hu.trans hv.1, hv.2.trans haStar⟩).2,
      (hdata v ⟨hu.trans hv.1, hv.2.trans (haB.trans hBb)⟩).2]
  obtain ⟨hAreaAlpha, hAreaLog⟩ :=
    endpointPatch_outgoing_wedge_area_eq hfamily hb hu hua
      (haB.trans hBb)
  constructor
  · rw [hAlphaLin, hVar, hAreaAlpha]
    exact hAlpha
  · rw [hLogLin, hInitialLin, hAreaLog]
    exact hLog

/-- The two outgoing transport bounds remain valid on the entire open
finite-endpoint development. The initial and area terms retain their
shrinking terminal intervals. -/
theorem endpointPatch_outgoing_terminal_bounds
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) vStar) :
    let P := endpointPatch family vStar
    (∫⁻ v in Ioo u vStar,
      ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) ≤
      eVariationOn (P.alpha 0) (Ioo u vStar) +
        smoothAnalyticArea (sourceLamPhiMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u vStar) ∧
    (∫⁻ v in Ioo u vStar,
      ENNReal.ofReal |sourceOutgoingLogResidual P u v|) ≤
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|) +
        smoothAnalyticArea (sourcePhiBetaNuMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u vStar) := by
  let P := endpointPatch family vStar
  let Rα : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|
  let Rlog : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |sourceOutgoingLogResidual P u v|
  let Ilog : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|
  let W : ℝ → Set (ℝ × ℝ) := fun a => Ioo (0 : ℝ) u ×ˢ Ioo u a
  let Cα : ℝ≥0∞ :=
    eVariationOn (P.alpha 0) (Ioo u vStar) +
      smoothAnalyticArea (sourceLamPhiMap P) (W vStar)
  let Clog : ℝ≥0∞ :=
    (∫⁻ v in Ioo u vStar, Ilog v) +
      smoothAnalyticArea (sourcePhiBetaNuMap P) (W vStar)
  have hWsub (a : ℝ) (haStar : a < vStar) : W a ⊆ W vStar := by
    intro p hp
    exact ⟨hp.1, ⟨hp.2.1, hp.2.2.trans haStar⟩⟩
  have hαCut (a : ℝ) (hua : u ≤ a) (haStar : a < vStar) :
      (∫⁻ v in Ioo u a, Rα v) ≤ Cα := by
    rcases lt_or_eq_of_le hua with hlt | heq
    · have hcut :=
        (endpointPatch_outgoing_cutoff_bounds hStar hD hfamily
          hu.1 hlt haStar).1
      have hTV : eVariationOn (P.alpha 0) (Ioo u a) ≤
          eVariationOn (P.alpha 0) (Ioo u vStar) :=
        eVariationOn.mono _ (fun v hv => ⟨hv.1, hv.2.trans haStar⟩)
      have hArea : smoothAnalyticArea (sourceLamPhiMap P) (W a) ≤
          smoothAnalyticArea (sourceLamPhiMap P) (W vStar) :=
        measure_mono (hWsub a haStar)
      exact hcut.trans (add_le_add hTV hArea)
    · subst a
      simpa only [Ioo_self, MeasureTheory.setLIntegral_empty] using
        (show (0 : ℝ≥0∞) ≤ Cα from bot_le)
  have hlogCut (a : ℝ) (hua : u ≤ a) (haStar : a < vStar) :
      (∫⁻ v in Ioo u a, Rlog v) ≤ Clog := by
    rcases lt_or_eq_of_le hua with hlt | heq
    · have hcut :=
        (endpointPatch_outgoing_cutoff_bounds hStar hD hfamily
          hu.1 hlt haStar).2
      have hInitial : (∫⁻ v in Ioo u a, Ilog v) ≤
          ∫⁻ v in Ioo u vStar, Ilog v :=
        lintegral_mono_set (fun v hv => ⟨hv.1, hv.2.trans haStar⟩)
      have hArea : smoothAnalyticArea (sourcePhiBetaNuMap P) (W a) ≤
          smoothAnalyticArea (sourcePhiBetaNuMap P) (W vStar) :=
        measure_mono (hWsub a haStar)
      exact hcut.trans (add_le_add hInitial hArea)
    · subst a
      simpa only [Ioo_self, MeasureTheory.setLIntegral_empty] using
        (show (0 : ℝ≥0∞) ≤ Clog from bot_le)
  have hα := s6_measure_terminal_exhaustion_bound
    (volume.withDensity Rα) hu.2 (C := Cα) (by
      intro a hua haStar
      simpa only [withDensity_apply _ measurableSet_Ioo] using
        hαCut a hua haStar)
  have hlog := s6_measure_terminal_exhaustion_bound
    (volume.withDensity Rlog) hu.2 (C := Clog) (by
      intro a hua haStar
      simpa only [withDensity_apply _ measurableSet_Ioo] using
        hlogCut a hua haStar)
  simpa only [Rα, Rlog, Ilog, W, Cα, Clog,
    withDensity_apply _ measurableSet_Ioo] using And.intro hα hlog

/-- The two analytic areas of the moving outgoing wedge vanish at the
terminal parameter, without retaining the redundant triangle intersection. -/
theorem endpointPatch_outgoing_wedge_tails
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ => smoothAnalyticArea (sourceLamPhiMap P)
      (Ioo (0 : ℝ) u ×ˢ Ioo u vStar))
      (𝓝[<] vStar) (𝓝 0) ∧
    Tendsto (fun u : ℝ => smoothAnalyticArea (sourcePhiBetaNuMap P)
      (Ioo (0 : ℝ) u ×ˢ Ioo u vStar))
      (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hEq (F : ℝ × ℝ → ℝ × ℝ) :
      (fun u : ℝ => smoothAnalyticArea F
        (Ioo (0 : ℝ) u ×ˢ Ioo u vStar)) =ᶠ[𝓝[<] vStar]
      (fun u : ℝ => smoothAnalyticArea F
        ((Ioo (0 : ℝ) u ×ˢ Ioo u vStar) ∩
          openCoordTriangle 0 vStar)) := by
    filter_upwards [Ioo_mem_nhdsLT hStar] with u hu
    have hSub : Ioo (0 : ℝ) u ×ˢ Ioo u vStar ⊆
        openCoordTriangle 0 vStar := by
      intro p hp
      exact ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩
    rw [Set.inter_eq_left.mpr hSub]
  obtain ⟨hLam, hBeta⟩ := endpoint_area_tails hStar hD hfamily
  exact ⟨hLam.congr' (hEq _).symm, hBeta.congr' (hEq _).symm⟩

/-- The complete initial outgoing log residual has vanishing extended-real
integral tail at the terminal parameter. -/
theorem endpointPatch_initial_log_lintegral_tail
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ =>
      ∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|)
      (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hInt := endpointPatch_initial_residual_integrable hStar hD hfamily
  have hReal := (terminal_residual_tails hStar hD hfamily).2
  have hOfReal : Tendsto (fun u : ℝ => ENNReal.ofReal
      (∫ v in Ioo u vStar, |sourceOutgoingLogResidual P 0 v|))
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [Function.comp_def, P, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hReal
  have hEq : (fun u : ℝ =>
      ∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|) =ᶠ[𝓝[<] vStar]
      (fun u : ℝ => ENNReal.ofReal
        (∫ v in Ioo u vStar, |sourceOutgoingLogResidual P 0 v|)) := by
    filter_upwards [Ioo_mem_nhdsLT hStar] with u hu
    have hSub : Ioo u vStar ⊆ Ioo (0 : ℝ) vStar := by
      intro v hv
      exact ⟨hu.1.trans hv.1, hv.2⟩
    have hIOn := hInt.mono_set hSub
    exact (ofReal_integral_eq_lintegral_ofReal hIOn
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  exact hOfReal.congr' hEq.symm

/-- Extended-real form of (6.1): the outgoing alpha-lambda residual has
vanishing terminal integral on the patched finite-endpoint development. -/
theorem eq6_1_lintegral
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ =>
      ∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|)
      (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hTV := (terminal_residual_tails hStar hD hfamily).1
  have hArea := (endpointPatch_outgoing_wedge_tails hStar hD hfamily).1
  have hRight : Tendsto (fun u : ℝ =>
      eVariationOn (P.alpha 0) (Ioo u vStar) +
        smoothAnalyticArea (sourceLamPhiMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u vStar))
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [P, add_zero] using hTV.add hArea
  have hBound : ∀ᶠ u in 𝓝[<] vStar,
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) ≤
      eVariationOn (P.alpha 0) (Ioo u vStar) +
        smoothAnalyticArea (sourceLamPhiMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u vStar) := by
    filter_upwards [Ioo_mem_nhdsLT hStar] with u hu
    exact (endpointPatch_outgoing_terminal_bounds hStar hD hfamily hu).1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hRight
    (Filter.Eventually.of_forall fun _ => bot_le) hBound

/-- Extended-real form of (6.2): the complete outgoing logarithmic
residual has vanishing terminal integral. -/
theorem eq6_2_lintegral
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ =>
      ∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P u v|)
      (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hInitial := endpointPatch_initial_log_lintegral_tail hStar hD hfamily
  have hArea := (endpointPatch_outgoing_wedge_tails hStar hD hfamily).2
  have hRight : Tendsto (fun u : ℝ =>
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|) +
        smoothAnalyticArea (sourcePhiBetaNuMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u vStar))
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [P, add_zero] using hInitial.add hArea
  have hBound : ∀ᶠ u in 𝓝[<] vStar,
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P u v|) ≤
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P 0 v|) +
        smoothAnalyticArea (sourcePhiBetaNuMap P)
          (Ioo (0 : ℝ) u ×ˢ Ioo u vStar) := by
    filter_upwards [Ioo_mem_nhdsLT hStar] with u hu
    exact (endpointPatch_outgoing_terminal_bounds hStar hD hfamily hu).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hRight
    (Filter.Eventually.of_forall fun _ => bot_le) hBound

/-- Equation (6.1) in the paper's real-integral form. -/
theorem eq6_1
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ =>
      ∫ v in Ioo u vStar,
        |sourceOutgoingAlphaResidual P u v|)
      (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hENN := eq6_1_lintegral hStar hD hfamily
  have hToReal : Tendsto (fun u : ℝ =>
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|).toReal)
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [P, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hENN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hBound (u : ℝ) :
      ‖∫ v in Ioo u vStar,
          |sourceOutgoingAlphaResidual P u v|‖ ≤
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|).toReal := by
    simpa only [Real.norm_eq_abs, abs_abs] using
      (norm_integral_le_lintegral_norm
        (μ := volume.restrict (Ioo u vStar))
        (f := fun v => |sourceOutgoingAlphaResidual P u v|))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hToReal
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun u => hBound u)

/-- Equation (6.2) in the paper's real-integral form, with the complete
outgoing log residual and its positive `f` correction. -/
theorem eq6_2
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ =>
      ∫ v in Ioo u vStar,
        |sourceOutgoingLogResidual P u v|)
      (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hENN := eq6_2_lintegral hStar hD hfamily
  have hToReal : Tendsto (fun u : ℝ =>
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P u v|).toReal)
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [P, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hENN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hBound (u : ℝ) :
      ‖∫ v in Ioo u vStar,
          |sourceOutgoingLogResidual P u v|‖ ≤
      (∫⁻ v in Ioo u vStar,
        ENNReal.ofReal |sourceOutgoingLogResidual P u v|).toReal := by
    simpa only [Real.norm_eq_abs, abs_abs] using
      (norm_integral_le_lintegral_norm
        (μ := volume.restrict (Ioo u vStar))
        (f := fun v => |sourceOutgoingLogResidual P u v|))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hToReal
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun u => hBound u)

end ChristodoulouBV

end
