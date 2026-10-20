module

public import ChristodoulouBV.Existence.AreaSectionLimitJumpLines
public import ChristodoulouBV.Existence.AreaSectionLimitCalculus
import Mathlib.Tactic

/-!
# Separate continuity of the concrete coefficient kernels

The mixed interval primitives give continuous transverse sections.
Combining them with the common physical jump lines gives continuity of
all nine algebraic coefficients outside countable sets, uniformly over
the fixed longitudinal coordinate.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem continuousAt_of_primitives {f g : ℝ → ℝ} {a b x : ℝ}
    (hax : a < x) (hxb : x < b)
    (hp : ∀ s t, a ≤ s → s ≤ t → t ≤ b → IntervalPrimitive f g s t) :
    ContinuousAt f x := by
  have hc : ContinuousOn f (Icc a b) := by
    simpa only [uIcc_of_le (hax.le.trans hxb.le)] using
      (IntervalPrimitive.ac_ae_of_subsegments (hax.le.trans hxb.le) hp).1.continuousOn
  exact hc.continuousAt (Icc_mem_nhds hax hxb)

/-- The raw outgoing fields are continuous in `u` in the interior,
and the raw incoming fields are continuous in `v`, including on the
initial outgoing section. These facts use the mixed primitives. -/
theorem raw_fields_transverse_continuity
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T) :
    (∀ u v, 0 < u → u < v →
      ContinuousAt (fun t => d.rawFields.lam t v) u ∧
        ContinuousAt (fun t => d.rawFields.alpha t v) u) ∧
    (∀ u v, 0 ≤ u → u < v →
      ContinuousAt (d.rawFields.nu u) v ∧ ContinuousAt (d.rawFields.beta u) v) := by
  obtain ⟨hlam, hnu⟩ := raw_expansion_primitive_limit h d
  obtain ⟨hα, hβ⟩ := raw_alpha_beta_transport_limit h d
  constructor
  · intro u v hu huv
    have hub : u < (u + v) / 2 := by linarith only [huv]
    have hseg (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ (u + v) / 2) :
        inSeg v s t ⊆ globalDomain := by
      rintro ⟨x, y⟩ ⟨hx, rfl⟩
      exact ⟨hs.trans hx.1, by linarith only [hx.2, ht, huv]⟩
    exact ⟨continuousAt_of_primitives hu hub
        (fun s t hs hst ht => hlam v s t hst (hseg s t hs hst ht)),
      continuousAt_of_primitives hu hub
        (fun s t hs hst ht => hα v s t hst (hseg s t hs hst ht))⟩
  · intro u v hu huv
    have hav : (u + v) / 2 < v := by linarith only [huv]
    have hvb : v < v + 1 := by linarith
    have hseg (s t : ℝ) (hs : (u + v) / 2 ≤ s) (hst : s ≤ t) (ht : t ≤ v + 1) :
        outSeg u s t ⊆ globalDomain := by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      exact ⟨hu, by linarith only [hy.1, hs, huv]⟩
    exact ⟨continuousAt_of_primitives hav hvb
        (fun s t hs hst ht => hnu u s t hst (hseg s t hs hst ht)),
      continuousAt_of_primitives hav hvb
        (fun s t hs hst ht => hβ u s t hst (hseg s t hs hst ht))⟩

/-- Continuity of the seven fields and nonzero denominators imply
continuity of the concrete nine-coefficient vector. -/
theorem area_section_coefficients_continuousAt_of_fields
    {Y : Type*} [TopologicalSpace Y] {S : Fields} {c : Y → ℝ × ℝ} {y : Y}
    (hr : ContinuousAt (fun z => S.r (c z).1 (c z).2) y)
    (hm : ContinuousAt (fun z => S.m (c z).1 (c z).2) y)
    (hl : ContinuousAt (fun z => S.lam (c z).1 (c z).2) y)
    (hn : ContinuousAt (fun z => S.nu (c z).1 (c z).2) y)
    (hφ : ContinuousAt (fun z => S.phi (c z).1 (c z).2) y)
    (hα : ContinuousAt (fun z => S.alpha (c z).1 (c z).2) y)
    (hβ : ContinuousAt (fun z => S.beta (c z).1 (c z).2) y)
    (hr0 : S.r (c y).1 (c y).2 ≠ 0) (hl0 : S.lam (c y).1 (c y).2 ≠ 0)
    (hn0 : S.nu (c y).1 (c y).2 ≠ 0)
    (hq0 : 1 - 2 * S.m (c y).1 (c y).2 / S.r (c y).1 (c y).2 ≠ 0) :
    ContinuousAt (fun z => areaSectionCoefficients S (c z)) y := by
  have hμ : ContinuousAt (fun z => 2 * S.m (c z).1 (c z).2 / S.r (c z).1 (c z).2) y :=
    (continuousAt_const.mul hm).div hr hr0
  have hc : ContinuousAt (fun z => IsBVSolution.radiusCoeff S (c z).1 (c z).2) y :=
    ((hμ.mul hl).mul hn).div ((continuousAt_const.sub hμ).mul hr) (mul_ne_zero hq0 hr0)
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact hr.inv₀ hr0
  · exact hl
  · exact hn
  · exact hφ
  · exact hα
  · exact hβ
  · exact hc
  · exact hl.inv₀ hl0
  · exact hn.inv₀ hn0

/-- Common countable physical jump sets suffice for separate continuity
of every concrete coefficient. All continuity and denominator claims are
proved for the raw limit fields on the shared carrier. -/
theorem raw_coefficients_common_exceptional_sets
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ Su Sv : Set ℝ, Su.Countable ∧ Sv.Countable ∧
      (∀ u v, 0 < u → u < v → u ∉ Su →
        ContinuousAt (fun t => areaSectionCoefficients d.rawFields (t, v)) u) ∧
      (∀ u v, 0 ≤ u → u < v → v ∉ Sv →
        ContinuousAt (fun t => areaSectionCoefficients d.rawFields (u, t)) v) := by
  obtain ⟨Su, hSu, huc⟩ := raw_incoming_common_exceptional_set h hD d
  obtain ⟨Sv, hSv, hvc⟩ := raw_outgoing_common_exceptional_set h hD d
  obtain ⟨htu, htv⟩ := raw_fields_transverse_continuity h d
  have hgeom := (expansions_limit h d).2.2
  have hnonzero (u v : ℝ) (hp : (u, v) ∈ globalDomain) :
      d.rawFields.r u v ≠ 0 ∧ d.rawFields.lam u v ≠ 0 ∧
        d.rawFields.nu u v ≠ 0 ∧
        1 - 2 * d.rawFields.m u v / d.rawFields.r u v ≠ 0 := by
    have hg := hgeom (u, v) hp
    have hq := (d.mass_geometry h (u, v) hp).1
    refine ⟨(d.radius_pos h hp).ne', ?_, ?_, ?_⟩
    · change d.lam u v ≠ 0
      linarith only [hg.1]
    · change d.nu u v ≠ 0
      linarith only [hg.2.2.1]
    · change 1 - 2 * d.mass (u, v) / d.radius (u, v) ≠ 0
      linarith only [hq]
  refine ⟨Su, Sv, hSu, hSv, ?_, ?_⟩
  · intro u v hu huv hus
    obtain ⟨hl, hα⟩ := htu u v hu huv
    obtain ⟨hn, hβ⟩ := huc u v hu huv hus
    have hφ : ContinuousAt (fun t => d.rawFields.phi t v) u := by
      have hc := (d.scalar_continuousOn h).comp
        (continuous_id.prodMk continuous_const).continuousOn
        (s := Ioo 0 v) (fun t ht => ⟨ht.1.le, ht.2⟩)
      exact hc.continuousAt (Ioo_mem_nhds hu huv)
    obtain ⟨hr0, hl0, hn0, hq0⟩ := hnonzero u v ⟨hu.le, huv⟩
    exact area_section_coefficients_continuousAt_of_fields
      (d.radius_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
      (d.mass_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
      hl hn hφ hα hβ hr0 hl0 hn0 hq0
  · intro u v hu huv hvs
    obtain ⟨hn, hβ⟩ := htv u v hu huv
    obtain ⟨hl, hα⟩ := hvc u v hu huv hvs
    have hφ : ContinuousAt (d.rawFields.phi u) v := by
      have hc := (d.scalar_continuousOn h).comp
        (continuous_const.prodMk continuous_id).continuousOn
        (s := Ioi u) (fun t ht => ⟨hu, ht⟩)
      exact hc.continuousAt (Ioi_mem_nhds huv)
    obtain ⟨hr0, hl0, hn0, hq0⟩ := hnonzero u v ⟨hu, huv⟩
    exact area_section_coefficients_continuousAt_of_fields
      (d.radius_continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
      (d.mass_continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
      hl hn hφ hα hβ hr0 hl0 hn0 hq0

end ChristodoulouBV

end
