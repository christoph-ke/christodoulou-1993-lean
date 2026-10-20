module

public import ChristodoulouBV.Existence.ScalarLimitFields
public import ChristodoulouBV.Existence.ScalarLimitTV
import Mathlib.Tactic

/-!
# Quantitative bounds for the canonical scalar representatives

Taking right representatives does not increase either complete three-term
variation. These bounds belong to the same field record as all four
right-continuity clauses and the exact right-continuous initial trace.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

private theorem right_limit_on_ray {f : ℝ → ℝ} {a x : ℝ}
    (hf : BoundedVariationOn f (Ioi a)) (hx : a < x) :
    Tendsto f (𝓝[>] x) (𝓝 (f.rightLim x)) := by
  apply tendsto_rightLim_of_tendsto
  have he : Ioi a ∩ Ioi x = Ioi x := inter_eq_right.mpr (Ioi_subset_Ioi hx.le)
  simpa only [he] using hf.exists_tendsto_right x

/-- All four raw derivative fields tend from the right to their canonical
representatives, in the corresponding null direction. -/
theorem scalar_right_limits
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      Tendsto (d.alpha p.1) (𝓝[>] p.2) (𝓝 (d.rightAlpha p.1 p.2)) ∧
      Tendsto (d.lam p.1) (𝓝[>] p.2) (𝓝 (d.rightLam p.1 p.2)) ∧
      Tendsto (fun u => d.beta u p.2) (𝓝[>] p.1) (𝓝 (d.rightBeta p.1 p.2)) ∧
      Tendsto (fun u => d.nu u p.2) (𝓝[>] p.1) (𝓝 (d.rightNu p.1 p.2)) := by
  have hV := lt_top_iff_ne_top.mpr (scalarVariationBound_ne_top hD C)
  have hW : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  obtain ⟨_, hα, hβ, _⟩ := alpha_beta_limit h d
  obtain ⟨hlam, hnu, _⟩ := expansions_limit h d
  intro p hp
  refine ⟨right_limit_on_ray (ne_of_lt ((hα p.1 hp.1).trans_lt hV)) hp.2,
    right_limit_on_ray (ne_of_lt ((hlam p.1 hp.1).trans_lt hW)) hp.2, ?_, ?_⟩
  · exact tendsto_rightLim_of_tendsto
      ((show BoundedVariationOn (fun u => d.beta u p.2) (Ico 0 p.2) from
        ne_of_lt ((hβ p.2 (hp.1.trans_lt hp.2)).trans_lt hV)).exists_tendsto_right_Ico hp)
  · exact tendsto_rightLim_of_tendsto
      ((show BoundedVariationOn (fun u => d.nu u p.2) (Ico 0 p.2) from
        ne_of_lt ((hnu p.2 (hp.1.trans_lt hp.2)).trans_lt hW)).exists_tendsto_right_Ico hp)

/-- Canonical selection does not increase either complete three-term TV.
The outgoing initial ray is included. -/
theorem scalar_right_fields_tv_le
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → e1OutgoingTV d.scalarRightFields u ≤ e1OutgoingTV d.rawFields u) ∧
    ∀ v, 0 < v → e1IncomingTV d.scalarRightFields v ≤ e1IncomingTV d.rawFields v := by
  have hlim := scalar_right_limits h hD d
  have hgeom := right_expansions_geometry h hD d
  constructor
  · intro u hu
    have hquot : EqOn (fun v => d.rightAlpha u v / d.rightLam u v)
        (fun v => (fun t => d.alpha u t / d.lam u t).rightLim v) (Ioi u) := by
      intro v hv
      have hp : (u, v) ∈ globalDomain := ⟨hu, hv⟩
      have hl0 : 0 < d.rightLam u v := lt_of_lt_of_le (by norm_num) (hgeom (u, v) hp).1
      exact (rightLim_eq_of_tendsto ((hlim (u, v) hp).1.div
        (hlim (u, v) hp).2.1 hl0.ne')).symm
    have hlog : EqOn (fun v => Real.log (d.rightLam u v))
        (fun v => (fun t => Real.log (d.lam u t)).rightLim v) (Ioi u) := by
      intro v hv
      have hp : (u, v) ∈ globalDomain := ⟨hu, hv⟩
      have hl0 : 0 < d.rightLam u v := lt_of_lt_of_le (by norm_num) (hgeom (u, v) hp).1
      exact (rightLim_eq_of_tendsto ((Real.continuousAt_log hl0.ne').tendsto.comp
        (hlim (u, v) hp).2.1)).symm
    change eVariationOn (fun v => d.rightAlpha u v / d.rightLam u v) (Ioi u) +
      eVariationOn (d.rawFields.phi u) (Ioi u) +
      eVariationOn (fun v => Real.log (d.rightLam u v)) (Ioi u) ≤ _
    rw [eVariationOn.congr hquot, eVariationOn.congr hlog]
    exact add_le_add
      (add_le_add (eVariationOn.eVariationOn_rightLim_le isOpen_Ioi) le_rfl)
      (eVariationOn.eVariationOn_rightLim_le isOpen_Ioi)
  · intro v hv
    have hquot : EqOn (fun u => d.rightBeta u v / d.rightNu u v)
        (fun u => (fun t => d.beta t v / d.nu t v).rightLim u) (Ioo 0 v) := by
      intro u hu
      have hp : (u, v) ∈ globalDomain := ⟨hu.1.le, hu.2⟩
      have hn0 : 0 < -d.rightNu u v :=
        lt_of_lt_of_le (by norm_num) (hgeom (u, v) hp).2.2.1
      exact (rightLim_eq_of_tendsto ((hlim (u, v) hp).2.2.1.div
        (hlim (u, v) hp).2.2.2 (neg_ne_zero.mp hn0.ne'))).symm
    have hlog : EqOn (fun u => Real.log (-d.rightNu u v))
        (fun u => (fun t => Real.log (-d.nu t v)).rightLim u) (Ioo 0 v) := by
      intro u hu
      have hp : (u, v) ∈ globalDomain := ⟨hu.1.le, hu.2⟩
      have hn0 : 0 < -d.rightNu u v :=
        lt_of_lt_of_le (by norm_num) (hgeom (u, v) hp).2.2.1
      exact (rightLim_eq_of_tendsto ((Real.continuousAt_log hn0.ne').tendsto.comp
        (hlim (u, v) hp).2.2.2.neg)).symm
    change eVariationOn (fun u => d.rightBeta u v / d.rightNu u v) (Ioo 0 v) +
      eVariationOn (fun u => d.rawFields.phi u v) (Ioo 0 v) +
      eVariationOn (fun u => Real.log (-d.rightNu u v)) (Ioo 0 v) ≤ _
    rw [eVariationOn.congr hquot, eVariationOn.congr hlog]
    exact add_le_add
      (add_le_add (eVariationOn.eVariationOn_rightLim_le isOpen_Ioo) le_rfl)
      (eVariationOn.eVariationOn_rightLim_le isOpen_Ioo)

/-- One universal three-term coefficient holds for the canonical fields
with their canonical right representatives, independent of all scalar offsets. -/
theorem scalar_right_fields_three_term_tv
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → e1OutgoingTV d.scalarRightFields u ≤
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal)) ∧
    ∀ v, 0 < v → e1IncomingTV d.scalarRightFields v ≤
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) := by
  obtain ⟨hout, hin⟩ := scalar_right_fields_tv_le h hD d
  obtain ⟨hrawout, hrawin⟩ := scalar_limit_three_term_tv h d
  exact ⟨fun u hu => (hout u hu).trans (hrawout u hu),
    fun v hv => (hin v hv).trans (hrawin v hv)⟩

end ChristodoulouBV

end
