module

public import ChristodoulouBV.Existence.MassLimitPrimitives
import Mathlib.Tactic

/-!
# Mass limit for the canonical BV representatives

Mass compactness and the mass primitive identities hold along
the single shared existence subsequence. The mass and radius are unchanged by
the canonical representative choices. The outgoing and incoming mass
densities converge sectionwise almost everywhere to the densities of
`scalarRightFields`, which gives both exact frozen mass primitives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Nonnegative mass and the universal mass-ratio geometry for exactly
the canonical field record of the scalar limit. -/
theorem mass_limit_geometry
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      0 < d.scalarRightFields.r p.1 p.2 ∧ 0 ≤ d.scalarRightFields.m p.1 p.2 ∧
      2 * d.scalarRightFields.m p.1 p.2 ≤ d.scalarRightFields.r p.1 p.2 / 3 ∧
      0 ≤ 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ≤ 1 / 3 ∧
      (2 / 3 : ℝ) ≤ 1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ≤ 1 := by
  intro p hp
  obtain ⟨hm0, hm1⟩ := d.mass_bounds h hp
  obtain ⟨hq0, hq1⟩ := d.mass_geometry h p hp
  refine ⟨d.radius_pos h hp, hm0, hm1, ?_, ?_, hq0, hq1⟩
  · change 0 ≤ 2 * d.mass p / d.radius p
    linarith only [hq1]
  · change 2 * d.mass p / d.radius p ≤ 1 / 3
    linarith only [hq0]

/-- Both frozen mass identities pass to the canonical BV
representatives on every closed null segment. Convergence of the
representatives is used only sectionwise almost everywhere at jumps. -/
theorem mass_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.scalarRightFields.m u)
        (fun v => (1 - 2 * d.scalarRightFields.m u v / d.scalarRightFields.r u v) *
          d.scalarRightFields.theta u v ^ 2 / (2 * d.scalarRightFields.lam u v)) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.scalarRightFields.m u v)
        (fun u => (1 - 2 * d.scalarRightFields.m u v / d.scalarRightFields.r u v) *
          d.scalarRightFields.zeta u v ^ 2 / (2 * d.scalarRightFields.nu u v)) a b := by
  obtain ⟨hlout, hnin⟩ := right_expansions_segment_ae_limit h hD d
  obtain ⟨hαout, hβin⟩ := right_scalar_derivatives_segment_ae_limit h hD d
  have hgeom := scalar_right_fields_geometry h hD d
  constructor
  · intro u a b hab hs
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.mass_out u a b hab hs)
      (M := 100 * D.toReal ^ 2)
    · intro n t ht
      exact (h (d.subsequence n)).amplitudes.mass_out (u, t) (hs ⟨rfl, ht⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨rfl, ⟨le_rfl, hab⟩⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)
    · filter_upwards [hlout u a b hab hs, hαout u a b hab hs] with t hl hα ht
      have hp : (u, t) ∈ globalDomain := hs ⟨rfl, ht⟩
      have hq := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from
        tendsto_const_nhds).sub (d.mass_ratio_locally_uniform h |>.tendsto_at hp)
      have hφ := d.scalar_locally_uniform h |>.tendsto_at hp
      have hθ := (hα ht).sub ((hl ht).mul hφ)
      have hl0 := (hgeom (u, t) hp).1
      have hlne : 2 * d.scalarRightFields.lam u t ≠ 0 := by linarith only [hl0]
      exact (hq.mul (hθ.pow 2)).div (tendsto_const_nhds.mul (hl ht)) hlne
  · intro v a b hab hs
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.mass_in v a b hab hs)
      (M := 100 * D.toReal ^ 2)
    · intro n t ht
      exact (h (d.subsequence n)).amplitudes.mass_in (t, v) (hs ⟨ht, rfl⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨⟨le_rfl, hab⟩, rfl⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨⟨hab, le_rfl⟩, rfl⟩)
    · filter_upwards [hnin v a b hab hs, hβin v a b hab hs] with t hn hβ ht
      have hp : (t, v) ∈ globalDomain := hs ⟨ht, rfl⟩
      have hq := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from
        tendsto_const_nhds).sub (d.mass_ratio_locally_uniform h |>.tendsto_at hp)
      have hφ := d.scalar_locally_uniform h |>.tendsto_at hp
      have hζ := (hβ ht).sub ((hn ht).mul hφ)
      have hn0 := (hgeom (t, v) hp).2.2.1
      have hnne : 2 * d.scalarRightFields.nu t v ≠ 0 := by linarith only [hn0]
      exact (hq.mul (hζ.pow 2)).div (tendsto_const_nhds.mul (hn ht)) hnne

end ChristodoulouBV

end
