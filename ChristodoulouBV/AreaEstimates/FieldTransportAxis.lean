module

public import ChristodoulouBV.AreaEstimates.FieldTransportIncoming
import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationCore
import all ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Unit regular-axis variation

Closed C¹ regularity makes the diagonal traces absolutely continuous. The
scalar supremum on the open development also bounds the diagonal trace.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The five fields used by the transport estimates are C¹ on the closed
unit triangle. -/
theorem unit_field_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
        (closedCoordTriangle 0 1) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2)
        (closedCoordTriangle 0 1) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
        (closedCoordTriangle 0 1) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
        (closedCoordTriangle 0 1) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2)
        (closedCoordTriangle 0 1) := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hlam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.lam_c1
  have hnu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.nu_c1
  have hphi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  have htheta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.theta_c1
  have hzeta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.zeta p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.zeta_c1
  have ha : (fun p : ℝ × ℝ => S.alpha p.1 p.2) =
      (fun p => S.theta p.1 p.2 + S.lam p.1 p.2 * S.phi p.1 p.2) := by
    funext p; simp only [Fields.theta]; ring
  have hb : (fun p : ℝ × ℝ => S.beta p.1 p.2) =
      (fun p => S.zeta p.1 p.2 + S.nu p.1 p.2 * S.phi p.1 p.2) := by
    funext p; simp only [Fields.zeta]; ring
  exact ⟨hlam, hnu, hphi,
    by rw [ha]; exact htheta.add (hlam.mul hphi),
    by rw [hb]; exact hzeta.add (hnu.mul hphi)⟩

/-- The four axis traces in (4.5)–(4.6) are C¹ on the closed unit interval. -/
theorem unit_axis_traces_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (fun t => S.lam t t) (Icc 0 1) ∧
      ContDiffOn ℝ 1 (fun t => S.nu t t) (Icc 0 1) ∧
      ContDiffOn ℝ 1 (fun t => S.alpha t t) (Icc 0 1) ∧
      ContDiffOn ℝ 1 (fun t => S.beta t t) (Icc 0 1) := by
  have hdiag : ContDiffOn ℝ 1 (fun t : ℝ => (t, t)) (Icc 0 1) := by
    fun_prop
  have hmap : MapsTo (fun t : ℝ => (t, t)) (Icc 0 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨ht.1, le_rfl, ht.2⟩
  obtain ⟨hlam, hnu, _, ha, hb⟩ := unit_field_contDiffOn H
  exact ⟨hlam.comp hdiag hmap, hnu.comp hdiag hmap,
    ha.comp hdiag hmap, hb.comp hdiag hmap⟩

/-- Each axis derivative integral is exactly the variation of its axis trace. -/
theorem unit_axis_variation_eq_lintegral {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (fun t => S.lam t t) (Ioo 0 1) =
        ∫⁻ t in Ioo 0 1, ENNReal.ofReal |deriv (fun x => S.lam x x) t| ∧
    eVariationOn (fun t => S.nu t t) (Ioo 0 1) =
        ∫⁻ t in Ioo 0 1, ENNReal.ofReal |deriv (fun x => S.nu x x) t| ∧
    eVariationOn (fun t => S.alpha t t) (Ioo 0 1) =
        ∫⁻ t in Ioo 0 1, ENNReal.ofReal |deriv (fun x => S.alpha x x) t| ∧
    eVariationOn (fun t => S.beta t t) (Ioo 0 1) =
        ∫⁻ t in Ioo 0 1, ENNReal.ofReal |deriv (fun x => S.beta x x) t| := by
  obtain ⟨hlam, hnu, ha, hb⟩ := unit_axis_traces_contDiffOn H
  have hAC (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc 0 1)) :
      AbsolutelyContinuousOnInterval f 0 1 :=
    (show ContDiffOn ℝ 1 f (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf).absolutelyContinuousOnInterval
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact (null_lintegral_eq_scalar_variation
        (by norm_num : (0 : ℝ) ≤ 1) (hAC _ hlam) (fun _ _ => rfl)).symm
    | exact (null_lintegral_eq_scalar_variation
        (by norm_num : (0 : ℝ) ≤ 1) (hAC _ hnu) (fun _ _ => rfl)).symm
    | exact (null_lintegral_eq_scalar_variation
        (by norm_num : (0 : ℝ) ≤ 1) (hAC _ ha) (fun _ _ => rfl)).symm
    | exact (null_lintegral_eq_scalar_variation
        (by norm_num : (0 : ℝ) ≤ 1) (hAC _ hb) (fun _ _ => rfl)).symm

/-- The scalar supremum over the open unit development controls its closed
triangle trace. -/
theorem abs_phi_closed_le_sourceP {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 1) :
    |S.phi p.1 p.2| ≤ sourceP S := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => |S.phi p.1 p.2|)
      (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn (unit_field_contDiffOn H).2.2.1.continuousOn
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hcont).bddAbove
  have hbounded : BddAbove
      {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |S.phi p.1 p.2|} := by
    refine ⟨M, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    apply hM
    exact ⟨p, ⟨hp.1, hp.2.1.le, hp.2.2.le⟩, rfl⟩
  have hmaps : MapsTo (fun p : ℝ × ℝ => |S.phi p.1 p.2|)
      (developmentWithInitialEdge 1) (Iic (sourceP S)) := by
    intro p hp
    change |S.phi p.1 p.2| ≤ sourceP S
    simpa only [sourceP] using (le_csSup hbounded ⟨p, hp, rfl⟩)
  have hcl := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have h := hmaps.closure_of_continuousOn (hcl ▸ hcont)
    (hcl.symm ▸ hp)
  simpa only [isClosed_Iic.closure_eq, mem_Iic] using h

/-- The scalar supremum controls the regular-axis trace. -/
theorem abs_phi_axis_le_sourceP {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |S.phi u u| ≤ sourceP S :=
  abs_phi_closed_le_sourceP H (p := (u, u)) ⟨hu.1.le, le_rfl, hu.2.le⟩

/-- The absolute scalar supremum on the regular axis, in extended
nonnegative form for the variation estimates. -/
noncomputable def axisScalarSup (S : Fields) : ℝ≥0∞ :=
  ⨆ u ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal |S.phi u u|

/-- The axis scalar supremum is bounded by the Section 4 scalar supremum. -/
theorem axisScalarSup_le_sourceP {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    axisScalarSup S ≤ ENNReal.ofReal (sourceP S) := by
  rw [axisScalarSup]
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact ENNReal.ofReal_le_ofReal (abs_phi_axis_le_sourceP H hu)

/-- The incoming axis derivatives are the negatives of the outgoing axis
derivatives, with the signs from the regular-axis equations. -/
theorem unit_axis_deriv_neg {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t => S.beta t t) u =
        -deriv (fun t => S.alpha t t) u ∧
    deriv (fun t => S.nu t t) u =
        -deriv (fun t => S.lam t t) u := by
  have haxis (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      S.beta t t = -S.alpha t t ∧ S.nu t t = -S.lam t t := by
    let B := (t + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ht.1, ht.2]
    have hBb : B < 1 := by dsimp [B]; linarith only [ht.1, ht.2]
    have htB : t ≤ B := by dsimp [B]; linarith only [ht.1, ht.2]
    have h := axis_traces hB hBb H (show t ∈ Icc 0 B from ⟨ht.1.le, htB⟩)
    exact ⟨h.2.2.2.2.1, h.2.2.1⟩
  have hBetaEq : (fun t => S.beta t t) =ᶠ[𝓝 u]
      (fun t => -S.alpha t t) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
    exact (haxis t ht).1
  have hNuEq : (fun t => S.nu t t) =ᶠ[𝓝 u]
      (fun t => -S.lam t t) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
    exact (haxis t ht).2
  constructor
  · rw [hBetaEq.deriv_eq]
    exact deriv.neg
  · rw [hNuEq.deriv_eq]
    exact deriv.neg

end ChristodoulouBV

end
