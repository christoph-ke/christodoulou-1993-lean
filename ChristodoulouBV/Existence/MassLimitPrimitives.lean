module

public import ChristodoulouBV.Existence.MassLimitCore
import Mathlib.Tactic

/-!
# Passing the mass primitives to the selected limit

Both smooth mass densities have the universal majorant `100 * D.toReal^2`
from the uniform smooth bounds. Dominated convergence gives interval integrability of each
limiting density as well as the exact frozen primitive identity. No
pointwise differentiability of the limiting mass at jumps is asserted.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- A uniformly bounded sequence of interval primitives passes to its
endpoint and almost-everywhere density limits. Integrability of the limit
is a conclusion, obtained from the same majorant. -/
theorem interval_primitive_limit_ae {f g : ℕ → ℝ → ℝ} {F G : ℝ → ℝ}
    {a b M : ℝ} (hab : a ≤ b) (hprim : ∀ n, IntervalPrimitive (f n) (g n) a b)
    (hbound : ∀ n t, t ∈ Icc a b → |g n t| ≤ M)
    (ha : Tendsto (fun n => f n a) atTop (𝓝 (F a)))
    (hb : Tendsto (fun n => f n b) atTop (𝓝 (F b)))
    (hg : ∀ᵐ t : ℝ, t ∈ Icc a b →
      Tendsto (fun n => g n t) atTop (𝓝 (G t))) : IntervalPrimitive F G a b := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (g n) (volume.restrict (Ioc a b)) := by
    simpa only [uIoc_of_le hab] using (hprim n).1.aestronglyMeasurable
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun n => g n t) atTop (𝓝 (G t)) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hg] with t ht htI
    exact ht ⟨htI.1.le, htI.2⟩
  have hGmeas := aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  have hGbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖G t‖ ≤ M := by
    filter_upwards [hlim, ae_restrict_mem measurableSet_Ioc] with t ht htI
    exact le_of_tendsto ht.norm (Eventually.of_forall (fun n => by
      simpa only [Real.norm_eq_abs] using hbound n t ⟨htI.1.le, htI.2⟩))
  have hconst : Integrable (fun _ : ℝ => M) (volume.restrict (Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp intervalIntegrable_const
  have hG : IntervalIntegrable G volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hconst.mono' hGmeas hGbound)
  have hi : Tendsto (fun n => ∫ t in a..b, g n t) atTop (𝓝 (∫ t in a..b, G t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => M)
    · exact Eventually.of_forall (fun n => by
        simpa only [uIoc_of_le hab] using hmeas n)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun t ht => by
        rw [uIoc_of_le hab] at ht
        simpa only [Real.norm_eq_abs] using hbound n t ⟨ht.1.le, ht.2⟩))
    · exact intervalIntegrable_const
    · filter_upwards [hg] with t ht htI
      rw [uIoc_of_le hab] at htI
      exact ht ⟨htI.1.le, htI.2⟩
  refine ⟨hG, tendsto_nhds_unique (hb.sub ha) ?_⟩
  exact hi.congr' (Eventually.of_forall (fun n => (hprim n).2.symm))

/-- At every domain point both raw mass densities converge. The scalar,
radius and mass use the same joint selection as all four Helly fields. -/
theorem raw_mass_densities_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto
      (fun n => (1 - 2 * (T (d.subsequence n)).m p.1 p.2 /
        (T (d.subsequence n)).r p.1 p.2) * (T (d.subsequence n)).theta p.1 p.2 ^ 2 /
        (2 * (T (d.subsequence n)).lam p.1 p.2))
      atTop (𝓝 ((1 - 2 * d.rawFields.m p.1 p.2 / d.rawFields.r p.1 p.2) *
        d.rawFields.theta p.1 p.2 ^ 2 / (2 * d.rawFields.lam p.1 p.2))) ∧
    Tendsto
      (fun n => (1 - 2 * (T (d.subsequence n)).m p.1 p.2 /
        (T (d.subsequence n)).r p.1 p.2) * (T (d.subsequence n)).zeta p.1 p.2 ^ 2 /
        (2 * (T (d.subsequence n)).nu p.1 p.2))
      atTop (𝓝 ((1 - 2 * d.rawFields.m p.1 p.2 / d.rawFields.r p.1 p.2) *
        d.rawFields.zeta p.1 p.2 ^ 2 / (2 * d.rawFields.nu p.1 p.2))) := by
  have hq := (show Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) from
    tendsto_const_nhds).sub (d.mass_ratio_locally_uniform h |>.tendsto_at hp)
  have hφ := d.scalar_locally_uniform h |>.tendsto_at hp
  have hl := d.lam_limit p hp
  have hn := d.nu_limit p hp
  have hθ := (d.alpha_limit p hp).sub (hl.mul hφ)
  have hζ := (d.beta_limit p hp).sub (hn.mul hφ)
  obtain ⟨hl0, _, hn0, _⟩ := (expansions_limit h d).2.2 p hp
  have hlne : 2 * d.lam p.1 p.2 ≠ 0 := by linarith only [hl0]
  have hnne : 2 * d.nu p.1 p.2 ≠ 0 := by linarith only [hn0]
  exact ⟨(hq.mul (hθ.pow 2)).div (tendsto_const_nhds.mul hl) hlne,
    (hq.mul (hζ.pow 2)).div (tendsto_const_nhds.mul hn) hnne⟩

/-- Both frozen mass primitives hold for the raw representatives,
including every null segment on the initial-edge-inclusive carrier. -/
theorem raw_mass_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.rawFields.m u)
        (fun v => (1 - 2 * d.rawFields.m u v / d.rawFields.r u v) *
          d.rawFields.theta u v ^ 2 / (2 * d.rawFields.lam u v)) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.rawFields.m u v)
        (fun u => (1 - 2 * d.rawFields.m u v / d.rawFields.r u v) *
          d.rawFields.zeta u v ^ 2 / (2 * d.rawFields.nu u v)) a b := by
  constructor
  · intro u a b hab hs
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.mass_out u a b hab hs)
      (M := 100 * D.toReal ^ 2)
    · intro n t ht
      exact (h (d.subsequence n)).amplitudes.mass_out (u, t) (hs ⟨rfl, ht⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨rfl, ⟨le_rfl, hab⟩⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)
    · exact Eventually.of_forall (fun t ht => (raw_mass_densities_limit h d
        (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩))).1)
  · intro v a b hab hs
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.mass_in v a b hab hs)
      (M := 100 * D.toReal ^ 2)
    · intro n t ht
      exact (h (d.subsequence n)).amplitudes.mass_in (t, v) (hs ⟨ht, rfl⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨⟨le_rfl, hab⟩, rfl⟩)
    · exact d.mass_limit.tendsto_at (hs ⟨⟨hab, le_rfl⟩, rfl⟩)
    · exact Eventually.of_forall (fun t ht => (raw_mass_densities_limit h d
        (hs (show (t, v) ∈ inSeg v a b from ⟨ht, rfl⟩))).2)

end ChristodoulouBV

end
