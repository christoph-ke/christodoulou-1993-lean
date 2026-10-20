module

public import ChristodoulouBV.Existence.AreaSectionLimitCore
import Mathlib.Tactic

/-!
# Uniform domination of the concrete off-axis coefficients

The section majorants depend on the truncation and scalar offset. Every
numeric coefficient is universal. No additional bound on a limiting field
or derivative is assumed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The nine smooth coefficient functions are continuous on the entire
development, including its initial edge. -/
theorem SmoothSolutionBounds.area_section_coefficients_continuousOn
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) :
    ContinuousOn (areaSectionCoefficients S) globalDomain := by
  have hr := h.radius_lipschitz.continuousOn
  have hm := h.mass_lipschitz.continuousOn
  have hl := h.solution.lam_c1.continuousOn.mono subset_closure
  have hn := h.solution.nu_c1.continuousOn.mono subset_closure
  have hφ := h.solution.phi_c1.continuousOn.mono subset_closure
  have hθ := h.solution.theta_c1.continuousOn.mono subset_closure
  have hζ := h.solution.zeta_c1.continuousOn.mono subset_closure
  have hα : ContinuousOn (fun p : ℝ × ℝ => S.alpha p.1 p.2) globalDomain := by
    convert hθ.add (hl.mul hφ) using 1
    ext p
    simp only [Fields.theta, Pi.add_apply, Pi.mul_apply]
    ring
  have hβ : ContinuousOn (fun p : ℝ × ℝ => S.beta p.1 p.2) globalDomain := by
    convert hζ.add (hn.mul hφ) using 1
    ext p
    simp only [Fields.zeta, Pi.add_apply, Pi.mul_apply]
    ring
  have hr0 := fun p hp => (h.solution.solution.radius_pos p hp).ne'
  have hl0 : ∀ p ∈ globalDomain, S.lam p.1 p.2 ≠ 0 := by
    intro p hp
    have hb := (h.geometry p hp).1
    linarith only [hb]
  have hn0 : ∀ p ∈ globalDomain, S.nu p.1 p.2 ≠ 0 := by
    intro p hp
    have hb := (h.geometry p hp).2.2.1
    linarith only [hb]
  have hμ : ContinuousOn (fun p : ℝ × ℝ => 2 * S.m p.1 p.2 / S.r p.1 p.2)
      globalDomain := (continuousOn_const.mul hm).div hr hr0
  have hq0 : ∀ p ∈ globalDomain,
      (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2 ≠ 0 := by
    intro p hp
    have hb := (h.geometry p hp).2.2.2.2.1
    exact mul_ne_zero (by linarith only [hb]) (hr0 p hp)
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      IsBVSolution.radiusCoeff S p.1 p.2) globalDomain :=
    ((hμ.mul hl).mul hn).div ((continuousOn_const.sub hμ).mul hr) hq0
  apply continuousOn_pi.mpr
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

/-- A common bound for the nine algebraic coefficients on a region
whose coordinate gap is at least `δ`. -/
@[expose] noncomputable def areaSectionCoefficientBound
    (D : ℝ≥0∞) (C δ : ℝ) : ℝ :=
  10 + 10 * D.toReal + C + 12 / δ

/-- The smooth nine-coefficient vectors have a bound uniform in the
approximating sequence on every off-axis truncation. -/
theorem SmoothSolutionBounds.area_section_coefficients_bound
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {p : ℝ × ℝ} (hp : p ∈ globalDomain)
    {δ : ℝ} (hδ : 0 < δ) (hgap : δ ≤ p.2 - p.1) (i : Fin 9) :
    |areaSectionCoefficients S p i| ≤ areaSectionCoefficientBound D C δ := by
  have hD : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hC := h.offset_nonneg
  have hδ0 : 0 ≤ 1 / δ := le_of_lt (one_div_pos.mpr hδ)
  have hr : 0 < S.r p.1 p.2 := h.solution.solution.radius_pos p hp
  have hrbound : |(S.r p.1 p.2)⁻¹| ≤ 3 / δ := by
    rw [abs_of_pos (inv_pos.mpr hr), inv_eq_one_div]
    apply (div_le_div_iff₀ hr hδ).mpr
    have hb := h.radius_lower hp
    linarith only [hb, hgap]
  obtain ⟨hl0, hl1, hn0, hn1, _, _⟩ := h.geometry p hp
  have hl : |S.lam p.1 p.2| ≤ 1 := by
    rw [abs_of_nonneg (by linarith only [hl0])]
    linarith only [hl1]
  have hn : |S.nu p.1 p.2| ≤ 1 := by
    rw [abs_of_nonpos (by linarith only [hn0])]
    linarith only [hn1]
  have hli : |(S.lam p.1 p.2)⁻¹| ≤ 3 := by
    rw [abs_inv]
    exact (inv_le_comm₀ ((lt_of_lt_of_le (by norm_num) hl0).trans_le (le_abs_self _))
      (by norm_num : (0 : ℝ) < 3)).mpr (by
        rw [abs_of_nonneg (by linarith only [hl0])]
        simpa only [inv_eq_one_div] using hl0)
  have hni : |(S.nu p.1 p.2)⁻¹| ≤ 3 := by
    rw [abs_inv]
    exact (inv_le_comm₀ (by
        rw [abs_of_nonpos (by linarith only [hn0])]
        linarith only [hn0] : 0 < |S.nu p.1 p.2|)
      (by norm_num : (0 : ℝ) < 3)).mpr (by
        rw [abs_of_nonpos (by linarith only [hn0])]
        simpa only [inv_eq_one_div] using hn0)
  have hφ := h.amplitudes.phi p hp
  have hα := h.amplitudes.alpha p hp
  have hβ := h.amplitudes.beta p hp
  have hc := h.mixed_radius_bound hp hδ hgap
  fin_cases i <;> simp only [areaSectionCoefficients, Matrix.cons_val_zero',
    Matrix.cons_val_succ', areaSectionCoefficientBound, IsBVSolution.radiusCoeff,
    div_eq_mul_inv] at *
  all_goals linarith only [hrbound, hl, hn, hφ, hα, hβ, hc, hli, hni, hD, hC, hδ0]

/-- Continuous algebraic functions of the concrete coefficient vectors
have a common bound on an off-axis truncation. -/
theorem area_section_uniform_bound_of_continuous
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n))
    {δ : ℝ} (hδ : 0 < δ) {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    ∃ M : ℝ, ∀ n p, p ∈ globalDomain → δ ≤ p.2 - p.1 →
      |q (areaSectionCoefficients (T n) p)| ≤ M := by
  let B := areaSectionCoefficientBound D C δ
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (fun _ : Fin 9 => -B)
      (fun _ : Fin 9 => B))).exists_bound_of_continuousOn hq.continuousOn
  refine ⟨M, fun n p hp hgap => ?_⟩
  apply hM _
  constructor
  · intro i
    exact (abs_le.mp ((h n).area_section_coefficients_bound hp hδ hgap i)).1
  · intro i
    exact (abs_le.mp ((h n).area_section_coefficients_bound hp hδ hgap i)).2

end ChristodoulouBV

end
