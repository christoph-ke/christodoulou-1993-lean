module

public import ChristodoulouBV.Existence.AreaSectionLimitContinuity
public import ChristodoulouBV.Existence.AreaSectionLimitTransverse
import Mathlib.Tactic

/-!
# Joint continuity away from common physical jump lines

Uniform transverse control upgrades the separate continuity of the raw
fields to joint continuity away from the two countable sets of jump
lines. This applies in particular at the moving off-axis endpoints of
the triangular section charts.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem continuousAt_of_eventually_dist_le
    {Y : Type*} [TopologicalSpace Y] {f g e : Y → ℝ} {K : ℝ} {y : Y}
    (hg : ContinuousAt g y) (he : Tendsto e (𝓝 y) (𝓝 0))
    (hfg : f y = g y)
    (hb : ∀ᶠ z in 𝓝 y, dist (f z) (g z) ≤ K * e z) :
    ContinuousAt f y := by
  change Tendsto f (𝓝 y) (𝓝 (f y))
  rw [hfg]
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hg' : Tendsto g (𝓝 y) (𝓝 (g y)) := hg
  have hzero : Tendsto (fun z => K * e z + dist (g z) (g y)) (𝓝 y) (𝓝 0) := by
    simpa only [mul_zero, dist_self, add_zero] using
      ((tendsto_const_nhds (x := K)).mul he).add
        (hg'.dist (tendsto_const_nhds (x := g y)))
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hzero
  filter_upwards [hb] with z hz
  exact (dist_triangle _ _ _).trans (add_le_add hz le_rfl)

/-- The concrete raw coefficients are jointly continuous away from
common countable physical jump lines. The same sets also give separate
continuity on all admissible physical sections, including `u=0` in the
outgoing direction. -/
theorem raw_coefficients_common_continuity
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ Su Sv : Set ℝ, Su.Countable ∧ Sv.Countable ∧
      (∀ u v, 0 < u → u < v → u ∉ Su →
        ContinuousAt (fun t => areaSectionCoefficients d.rawFields (t, v)) u) ∧
      (∀ u v, 0 ≤ u → u < v → v ∉ Sv →
        ContinuousAt (fun t => areaSectionCoefficients d.rawFields (u, t)) v) ∧
      ∀ u v, 0 < u → u < v → u ∉ Su → v ∉ Sv →
        ContinuousAt (areaSectionCoefficients d.rawFields) (u, v) := by
  obtain ⟨Su, Sv, hSu, hSv, hcu, hcv⟩ := raw_coefficients_common_exceptional_sets h hD d
  refine ⟨Su, Sv, hSu, hSv, hcu, hcv, ?_⟩
  intro u v hu huv hus hvs
  let δ := (v - u) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr huv)
  have hδgap : δ < v - u := half_lt_self (sub_pos.mpr huv)
  have hu_near : ∀ᶠ p : ℝ × ℝ in 𝓝 (u, v), 0 ≤ p.1 :=
    ((continuous_fst.tendsto (u, v)).eventually (Ioi_mem_nhds hu)).mono
      (fun _ hp => hp.le)
  have hgap : ∀ᶠ p : ℝ × ℝ in 𝓝 (u, v), δ ≤ p.2 - p.1 :=
    (((continuous_snd.sub continuous_fst).tendsto (u, v)).eventually
      (Ioi_mem_nhds hδgap)).mono (fun _ hp => hp.le)
  have hgap_u : ∀ᶠ p : ℝ × ℝ in 𝓝 (u, v), δ ≤ p.2 - u :=
    (((continuous_snd.sub continuous_const).tendsto (u, v)).eventually
      (Ioi_mem_nhds hδgap)).mono (fun _ hp => hp.le)
  have hgap_v : ∀ᶠ p : ℝ × ℝ in 𝓝 (u, v), δ ≤ v - p.1 :=
    (((continuous_const.sub continuous_fst).tendsto (u, v)).eventually
      (Ioi_mem_nhds hδgap)).mono (fun _ hp => hp.le)
  have he_u : Tendsto (fun p : ℝ × ℝ => dist p.1 u) (𝓝 (u, v)) (𝓝 0) := by
    simpa only [dist_self] using
      (continuous_fst.tendsto (u, v)).dist (tendsto_const_nhds (x := u))
  have he_v : Tendsto (fun p : ℝ × ℝ => dist p.2 v) (𝓝 (u, v)) (𝓝 0) := by
    simpa only [dist_self] using
      (continuous_snd.tendsto (u, v)).dist (tendsto_const_nhds (x := v))
  have hlamv : ContinuousAt (d.rawFields.lam u) v :=
    (continuous_apply 1).continuousAt.comp (hcv u v hu.le huv hvs)
  have hαv : ContinuousAt (d.rawFields.alpha u) v :=
    (continuous_apply 4).continuousAt.comp (hcv u v hu.le huv hvs)
  have hνu : ContinuousAt (fun t => d.rawFields.nu t v) u :=
    (continuous_apply 2).continuousAt.comp (hcu u v hu huv hus)
  have hβu : ContinuousAt (fun t => d.rawFields.beta t v) u :=
    (continuous_apply 5).continuousAt.comp (hcu u v hu huv hus)
  have hl : ContinuousAt (fun p : ℝ × ℝ => d.rawFields.lam p.1 p.2) (u, v) := by
    apply continuousAt_of_eventually_dist_le
      (f := fun p : ℝ × ℝ => d.rawFields.lam p.1 p.2) (K := 9 / δ)
      (hlamv.comp continuous_snd.continuousAt) he_u rfl
    filter_upwards [hu_near, hgap, hgap_u] with p hp0 hpg hpu
    exact (raw_outgoing_fields_transverse_dist h d hδ hp0 hu.le hpg hpu).1
  have hα : ContinuousAt (fun p : ℝ × ℝ => d.rawFields.alpha p.1 p.2) (u, v) := by
    apply continuousAt_of_eventually_dist_le
      (f := fun p : ℝ × ℝ => d.rawFields.alpha p.1 p.2)
      (K := (9 / δ) * (6 * D.toReal + C))
      (hαv.comp continuous_snd.continuousAt) he_u rfl
    filter_upwards [hu_near, hgap, hgap_u] with p hp0 hpg hpu
    exact (raw_outgoing_fields_transverse_dist h d hδ hp0 hu.le hpg hpu).2
  have hn : ContinuousAt (fun p : ℝ × ℝ => d.rawFields.nu p.1 p.2) (u, v) := by
    apply continuousAt_of_eventually_dist_le
      (f := fun p : ℝ × ℝ => d.rawFields.nu p.1 p.2) (K := 9 / δ)
      (hνu.comp continuous_fst.continuousAt) he_v rfl
    filter_upwards [hu_near, hgap, hgap_v] with p hp0 hpg hpv
    exact (raw_incoming_fields_transverse_dist h d hδ hp0 hpg hpv).1
  have hβ : ContinuousAt (fun p : ℝ × ℝ => d.rawFields.beta p.1 p.2) (u, v) := by
    apply continuousAt_of_eventually_dist_le
      (f := fun p : ℝ × ℝ => d.rawFields.beta p.1 p.2)
      (K := (9 / δ) * (6 * D.toReal + C))
      (hβu.comp continuous_fst.continuousAt) he_v rfl
    filter_upwards [hu_near, hgap, hgap_v] with p hp0 hpg hpv
    exact (raw_incoming_fields_transverse_dist h d hδ hp0 hpg hpv).2
  have hp : (u, v) ∈ globalDomain := ⟨hu.le, huv⟩
  have hdom : globalDomain ∈ 𝓝 (u, v) := by
    filter_upwards [hu_near, hgap] with p hp0 hpg
    exact ⟨hp0, by linarith only [hpg, hδ]⟩
  have hφ := (d.scalar_continuousOn h).continuousAt hdom
  have hg := (expansions_limit h d).2.2 (u, v) hp
  have hq := (d.mass_geometry h (u, v) hp).1
  apply area_section_coefficients_continuousAt_of_fields d.radius_continuous.continuousAt
    d.mass_continuous.continuousAt hl hn hφ hα hβ (d.radius_pos h hp).ne'
  · change d.lam u v ≠ 0
    linarith only [hg.1]
  · change d.nu u v ≠ 0
    linarith only [hg.2.2.1]
  · change 1 - 2 * d.mass (u, v) / d.radius (u, v) ≠ 0
    linarith only [hq]

end ChristodoulouBV

end
