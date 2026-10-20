module

public import ChristodoulouBV.Existence.ScalarLimitCore
import Mathlib.Tactic

/-!
# Universal scalar and ratio variation bounds for the selected limit

Pass the shift-invariant smooth three-term estimates directly through
pointwise convergence. The universal coefficient is enlarged by three;
the datum-dependent raw scalar offset never enters these estimates.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

private theorem three_variations_limit
    {f g k : ℕ → ℝ → ℝ} {F G K : ℝ → ℝ} {s : Set ℝ} {V : ℝ≥0∞}
    (hb : ∀ n, eVariationOn (f n) s + eVariationOn (g n) s + eVariationOn (k n) s ≤ V)
    (hf : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hg : ∀ x ∈ s, Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    (hk : ∀ x ∈ s, Tendsto (fun n => k n x) atTop (𝓝 (K x))) :
    eVariationOn F s + eVariationOn G s + eVariationOn K s ≤ 3 * V := by
  have hF : eVariationOn F s ≤ V := variation_bound_of_pointwise_limit
    (fun n => (le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (hb n))) hf
  have hG : eVariationOn G s ≤ V := variation_bound_of_pointwise_limit
    (fun n => (le_add_of_nonneg_left bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (hb n))) hg
  have hK : eVariationOn K s ≤ V := variation_bound_of_pointwise_limit
    (fun n => (le_add_of_nonneg_left bot_le).trans (hb n)) hk
  calc
    _ ≤ V + V + V := add_le_add (add_le_add hF hG) hK
    _ = 3 * V := by ring

/-- The selected raw fields satisfy both complete three-term TV bounds
with one universal coefficient, including the initial outgoing ray.
These estimates are independent of the smooth approximants' raw scalar offset. -/
theorem scalar_limit_three_term_tv
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → e1OutgoingTV d.rawFields u ≤
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal)) ∧
    ∀ v, 0 < v → e1IncomingTV d.rawFields v ≤
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) := by
  have hgeom := (expansions_limit h d).2.2
  have hφ := d.scalar_locally_uniform h
  constructor
  · intro u hu
    apply three_variations_limit (fun n => (h (d.subsequence n)).three_term_out u hu)
    · intro v hv
      have hlam : 0 < d.lam u v := lt_of_lt_of_le (by norm_num) (hgeom (u, v) ⟨hu, hv⟩).1
      exact (d.alpha_limit (u, v) ⟨hu, hv⟩).div (d.lam_limit (u, v) ⟨hu, hv⟩) hlam.ne'
    · intro v hv
      exact hφ.tendsto_at (a := (u, v)) ⟨hu, hv⟩
    · intro v hv
      have hlam : 0 < d.lam u v := lt_of_lt_of_le (by norm_num) (hgeom (u, v) ⟨hu, hv⟩).1
      exact (Real.continuousAt_log hlam.ne').tendsto.comp (d.lam_limit (u, v) ⟨hu, hv⟩)
  · intro v hv
    apply three_variations_limit (fun n => (h (d.subsequence n)).three_term_in v hv)
    · intro u hu
      have hν : 0 < -d.nu u v :=
        lt_of_lt_of_le (by norm_num) (hgeom (u, v) ⟨hu.1.le, hu.2⟩).2.2.1
      exact (d.beta_limit (u, v) ⟨hu.1.le, hu.2⟩).div
        (d.nu_limit (u, v) ⟨hu.1.le, hu.2⟩) (neg_ne_zero.mp hν.ne')
    · intro u hu
      exact hφ.tendsto_at (a := (u, v)) ⟨hu.1.le, hu.2⟩
    · intro u hu
      have hν : 0 < -d.nu u v :=
        lt_of_lt_of_le (by norm_num) (hgeom (u, v) ⟨hu.1.le, hu.2⟩).2.2.1
      exact (Real.continuousAt_log hν.ne').tendsto.comp
        (d.nu_limit (u, v) ⟨hu.1.le, hu.2⟩).neg

/-- Both shift-invariant scalar amplitudes pass to the same raw limit
with their universal coefficients, despite the uncentered scalar offset. -/
theorem scalar_limit_invariant_amplitudes
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      |d.rawFields.theta p.1 p.2| ≤ 5 * D.toReal ∧
      |d.rawFields.zeta p.1 p.2| ≤ 8 * D.toReal := by
  intro p hp
  have hφ := (d.scalar_locally_uniform h).tendsto_at hp
  have hθ := (d.alpha_limit p hp).sub ((d.lam_limit p hp).mul hφ)
  have hζ := (d.beta_limit p hp).sub ((d.nu_limit p hp).mul hφ)
  exact ⟨le_of_tendsto hθ.abs (Eventually.of_forall
      (fun n => (h (d.subsequence n)).amplitudes.theta p hp)),
    le_of_tendsto hζ.abs (Eventually.of_forall
      (fun n => (h (d.subsequence n)).amplitudes.zeta p hp))⟩

end ChristodoulouBV

end
