module

public import ChristodoulouBV.Existence.RadiusLimitTransverse
import Mathlib.Tactic

/-!
# The common global limit carrier

All subsequent existence constructions use `RadiusLimitData.subsequence`. The
pointwise limits retain Helly's actual point values; canonical right traces
are separate representatives of these same sectionwise BV classes.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The common subsequence and limit functions for the global BV existence construction. All four
derivative limits exist at every point of the global development. -/
structure RadiusLimitData (T : ℕ → Fields) extends SmoothCompactLimits T where
  /-- Pointwise outgoing expansion limit. -/
  lam : ℝ → ℝ → ℝ
  /-- Pointwise incoming expansion limit. -/
  nu : ℝ → ℝ → ℝ
  /-- Pointwise outgoing scalar derivative limit for the scalar limit construction. -/
  alpha : ℝ → ℝ → ℝ
  /-- Pointwise incoming scalar derivative limit for the scalar limit construction. -/
  beta : ℝ → ℝ → ℝ
  /-- Convergence of λ at every off-axis point, including the initial edge. -/
  lam_limit : ∀ p ∈ globalDomain,
    Tendsto (fun n => (T (subsequence n)).lam p.1 p.2) atTop (𝓝 (lam p.1 p.2))
  /-- Convergence of ν at every off-axis point. -/
  nu_limit : ∀ p ∈ globalDomain,
    Tendsto (fun n => (T (subsequence n)).nu p.1 p.2) atTop (𝓝 (nu p.1 p.2))
  /-- Convergence of α at every off-axis point. -/
  alpha_limit : ∀ p ∈ globalDomain,
    Tendsto (fun n => (T (subsequence n)).alpha p.1 p.2) atTop (𝓝 (alpha p.1 p.2))
  /-- Convergence of β at every off-axis point. -/
  beta_limit : ∀ p ∈ globalDomain,
    Tendsto (fun n => (T (subsequence n)).beta p.1 p.2) atTop (𝓝 (beta p.1 p.2))

/-- Rational Helly limits and the mixed primitive bounds produce one
global carrier for all seven fields. No later existence construction needs another extraction. -/
theorem s6_global_domain_limit {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞) :
    Nonempty (RadiusLimitData T) := by
  obtain ⟨c⟩ := exists_smooth_compact_limits h
  obtain ⟨τ, hτ, hlam, hν, hα, hβ⟩ :=
    s6_lam_nu_helly (fun n => h (c.subsequence n)) hD
  let d := c.subseq hτ
  have hsel (n : ℕ) : SmoothSolutionBounds (a (d.subsequence n)) D C (T (d.subsequence n)) :=
    h (d.subsequence n)
  have hout (p : ℝ × ℝ) (hp : p ∈ globalDomain) :
      (∃ l, Tendsto (fun n => (T (d.subsequence n)).lam p.1 p.2) atTop (𝓝 l)) ∧
      (∃ l, Tendsto (fun n => (T (d.subsequence n)).alpha p.1 p.2) atTop (𝓝 l)) := by
    have hd : 0 < (p.2 - p.1) / 2 := half_pos (sub_pos.mpr hp.2)
    have hL : 0 ≤ 18 / (p.2 - p.1) := div_nonneg (by norm_num) (sub_pos.mpr hp.2).le
    have hC : 0 ≤ 6 * D.toReal + C :=
      add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (h 0).offset_nonneg
    constructor
    · apply exists_tendsto_of_rational_right_control
        (f := fun n s => (T (d.subsequence n)).lam s p.2) hd hL
        (fun n s hs => ((hsel n).outgoing_fields_right_control hp hs).1)
      intro q hq hq'
      exact hlam q (hp.1.trans hq.le) p.2 (by
        change (q : ℝ) < p.2
        linarith only [hq', hp.2])
    · apply exists_tendsto_of_rational_right_control
        (f := fun n s => (T (d.subsequence n)).alpha s p.2) hd (mul_nonneg hL hC)
        (fun n s hs => ((hsel n).outgoing_fields_right_control hp hs).2)
      intro q hq hq'
      exact hα q (hp.1.trans hq.le) p.2 (by
        change (q : ℝ) < p.2
        linarith only [hq', hp.2])
  have hin (p : ℝ × ℝ) (hp : p ∈ globalDomain) :
      (∃ l, Tendsto (fun n => (T (d.subsequence n)).nu p.1 p.2) atTop (𝓝 l)) ∧
      (∃ l, Tendsto (fun n => (T (d.subsequence n)).beta p.1 p.2) atTop (𝓝 l)) := by
    have hd : 0 < (p.2 - p.1) / 2 := half_pos (sub_pos.mpr hp.2)
    have hL : 0 ≤ 18 / (p.2 - p.1) := div_nonneg (by norm_num) (sub_pos.mpr hp.2).le
    have hC : 0 ≤ 6 * D.toReal + C :=
      add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (h 0).offset_nonneg
    constructor
    · apply exists_tendsto_of_rational_right_control
        (f := fun n s => (T (d.subsequence n)).nu p.1 s) hd hL
        (fun n s hs => ((hsel n).incoming_fields_right_control hp hs).1)
      intro q hq hq'
      exact hν q ((hp.1.trans_lt hp.2).trans hq) p.1 ⟨hp.1, hp.2.trans hq⟩
    · apply exists_tendsto_of_rational_right_control
        (f := fun n s => (T (d.subsequence n)).beta p.1 s) hd (mul_nonneg hL hC)
        (fun n s hs => ((hsel n).incoming_fields_right_control hp hs).2)
      intro q hq hq'
      exact hβ q ((hp.1.trans_lt hp.2).trans hq) p.1 ⟨hp.1, hp.2.trans hq⟩
  exact ⟨{
    toSmoothCompactLimits := d
    lam := fun u v => limUnder atTop (fun n => (T (d.subsequence n)).lam u v)
    nu := fun u v => limUnder atTop (fun n => (T (d.subsequence n)).nu u v)
    alpha := fun u v => limUnder atTop (fun n => (T (d.subsequence n)).alpha u v)
    beta := fun u v => limUnder atTop (fun n => (T (d.subsequence n)).beta u v)
    lam_limit := fun p hp => tendsto_nhds_limUnder (hout p hp).1
    nu_limit := fun p hp => tendsto_nhds_limUnder (hin p hp).1
    alpha_limit := fun p hp => tendsto_nhds_limUnder (hout p hp).2
    beta_limit := fun p hp => tendsto_nhds_limUnder (hin p hp).2 }⟩

/-- Uniform variation bounds survive pointwise limits on the exact section carrier. -/
theorem variation_bound_of_pointwise_limit {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    {s : Set ℝ} {V : ℝ≥0∞} (hb : ∀ n, eVariationOn (f n) s ≤ V)
    (hl : ∀ x ∈ s, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    eVariationOn g s ≤ V := by
  by_contra hn
  obtain ⟨n, hn⟩ := (eVariationOn.lowerSemicontinuous_aux hl (lt_of_not_ge hn)).exists
  exact (not_lt_of_ge (hb n)) hn

/-- Every outgoing and incoming expansion section is BV, with the same
universal D² bound. The incoming section explicitly contains `u = 0`. -/
theorem expansions_limit {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → eVariationOn (d.lam u) (Ioi u) ≤ s4UniversalC * D ^ 2) ∧
    (∀ v, 0 < v → eVariationOn (fun u => d.nu u v) (Ico 0 v) ≤ s4UniversalC * D ^ 2) ∧
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ d.lam p.1 p.2 ∧ d.lam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -d.nu p.1 p.2 ∧ -d.nu p.1 p.2 ≤ 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    exact variation_bound_of_pointwise_limit
      (fun n => ((h (d.subsequence n)).variation_out u hu).2)
      (fun v hv => d.lam_limit (u, v) ⟨hu, hv⟩)
  · intro v hv
    exact variation_bound_of_pointwise_limit
      (fun n => (h (d.subsequence n)).variation_nu_initial_edge hv)
      (fun u hu => d.nu_limit (u, v) hu)
  · intro p hp
    have hlam := d.lam_limit p hp
    have hν := (d.nu_limit p hp).neg
    exact ⟨ge_of_tendsto hlam (Eventually.of_forall
        (fun n => ((h (d.subsequence n)).geometry p hp).1)),
      le_of_tendsto hlam (Eventually.of_forall
        (fun n => ((h (d.subsequence n)).geometry p hp).2.1)),
      ge_of_tendsto hν (Eventually.of_forall
        (fun n => ((h (d.subsequence n)).geometry p hp).2.2.1)),
      le_of_tendsto hν (Eventually.of_forall
        (fun n => ((h (d.subsequence n)).geometry p hp).2.2.2.1))⟩

end ChristodoulouBV

end
