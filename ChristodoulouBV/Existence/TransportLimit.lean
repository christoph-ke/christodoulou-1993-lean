module

public import ChristodoulouBV.Existence.TransportLimitPrimitives
import Mathlib.Tactic

/-!
# Geometry and the reduced system of the canonical BV limit

The transport limit construction completes the ten frozen primitive identities
on the shared existence subsequence for the canonical scalar representatives. The universal geometry
bounds give strict signs and a positive conformal witness; continuity of
the selected radius and mass gives the exact frozen axis limits.

The remaining BV variation and axis-cancellation conditions belong to the
subsequent BV existence constructions. No full `IsBVSolution` claim is made here.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The canonical radius has the exact one-sided zero-axis limit required
by the frozen solution definition. -/
theorem radius_axis_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    ∀ x ∈ adjacentAxis globalDomain,
      Tendsto (d.scalarRightFields.r x)
        (nhdsWithin x (Ioi x) ⊓ principal {v | (x, v) ∈ globalDomain}) (𝓝 (0 : ℝ)) := by
  intro x hx
  change Tendsto (fun v => d.radius (x, v)) _ (𝓝 (0 : ℝ))
  have hx0 : 0 ≤ x := by
    have hcl : (x, x) ∈ closure globalDomain := hx
    rw [s6_closure_globalDomain] at hcl
    exact hcl.1
  have hc : Continuous (fun v => d.radius (x, v)) :=
    d.radius_continuous.comp (continuous_const.prodMk continuous_id)
  have ht : Tendsto (fun v => d.radius (x, v))
      (𝓝[>] x ⊓ principal {v | (x, v) ∈ globalDomain}) (𝓝 (d.radius (x, x))) :=
    (hc.tendsto x).mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  simpa only [d.radius_axis h hx0] using ht

/-- The four strict signs and a positive conformal witness hold at every
point for exactly the canonical record, with the initial edge included. -/
theorem limit_signs_conformal
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      0 < d.scalarRightFields.r p.1 p.2 ∧
      0 < d.scalarRightFields.lam p.1 p.2 ∧
      d.scalarRightFields.nu p.1 p.2 < 0 ∧
      0 < 1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      ∃ Ω : ℝ, 0 < Ω ∧
        (1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2) * Ω ^ 2 =
          -(4 * d.scalarRightFields.lam p.1 p.2 * d.scalarRightFields.nu p.1 p.2) := by
  intro p hp
  obtain ⟨hl0, _, hn0, _, hq0, _⟩ := scalar_right_fields_geometry h hD d p hp
  have hl : 0 < d.scalarRightFields.lam p.1 p.2 := lt_of_lt_of_le (by norm_num) hl0
  have hn : d.scalarRightFields.nu p.1 p.2 < 0 := by linarith only [hn0]
  let q := 1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2
  let N := -(4 * d.scalarRightFields.lam p.1 p.2 * d.scalarRightFields.nu p.1 p.2)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hq0
  have hN : 0 < N := neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hl) hn)
  refine ⟨d.radius_pos h hp, hl, hn, hq, Real.sqrt (N / q),
    Real.sqrt_pos.mpr (div_pos hN hq), ?_⟩
  change q * Real.sqrt (N / q) ^ 2 = N
  rw [Real.sq_sqrt (div_pos hN hq).le]
  exact mul_div_cancel₀ N hq.ne'

/-- Full geometric conclusion for the canonical fields:
the exact carrier, four strict signs, a conformal witness and both frozen
axis limits. The six geometry inequalities keep their universal constants. -/
theorem limit_geometry
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    IsDomainOfDevelopment globalDomain ∧
    (∀ p ∈ globalDomain,
      0 < d.scalarRightFields.r p.1 p.2 ∧
      0 < d.scalarRightFields.lam p.1 p.2 ∧
      d.scalarRightFields.nu p.1 p.2 < 0 ∧
      0 < 1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      ∃ Ω : ℝ, 0 < Ω ∧
        (1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2) * Ω ^ 2 =
          -(4 * d.scalarRightFields.lam p.1 p.2 * d.scalarRightFields.nu p.1 p.2)) ∧
    (∀ x ∈ adjacentAxis globalDomain,
      Tendsto (d.scalarRightFields.r x)
        (nhdsWithin x (Ioi x) ⊓ principal {v | (x, v) ∈ globalDomain}) (𝓝 (0 : ℝ))) ∧
    (∀ x ∈ adjacentAxis globalDomain,
      Tendsto (d.scalarRightFields.m x)
        (nhdsWithin x (Ioi x) ⊓ principal {v | (x, v) ∈ globalDomain}) (𝓝 (0 : ℝ))) ∧
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ d.scalarRightFields.lam p.1 p.2 ∧
      d.scalarRightFields.lam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -d.scalarRightFields.nu p.1 p.2 ∧
      -d.scalarRightFields.nu p.1 p.2 ≤ 2 / 3 ∧
      (2 / 3 : ℝ) ≤ 1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ≤ 1 :=
  ⟨s6_globalDomain_isDomainOfDevelopment, limit_signs_conformal h hD d,
    radius_axis_limit h d, mass_axis_limit h d, scalar_right_fields_geometry h hD d⟩

/-- All ten frozen primitive fields, signs, conformal and axis clauses
assemble to `IsSolution` for the same canonical representatives. This
completes the reduced-system identities without adding any premise. -/
theorem transport_limit_is_solution
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) : IsSolution globalDomain d.scalarRightFields := by
  obtain ⟨hrout, hrin⟩ := right_radius_primitive_limit h hD d
  obtain ⟨hψout, hψin⟩ := scalar_right_fields_primitives h hD d
  obtain ⟨hmout, hmin⟩ := mass_primitive_limit h hD d
  obtain ⟨hlin, hnout⟩ := expansion_primitive_limit h hD d
  obtain ⟨hαin, hβout⟩ := alpha_beta_transport_limit h hD d
  have hgeom := limit_signs_conformal h hD d
  exact {
    development := s6_globalDomain_isDomainOfDevelopment
    radius_out := hrout
    radius_in := hrin
    scalar_radius_out := hψout
    scalar_radius_in := hψin
    mass_out := hmout
    mass_in := hmin
    lam_in := hlin
    nu_out := hnout
    alpha_in := hαin
    beta_out := hβout
    radius_axis := radius_axis_limit h d
    mass_axis := mass_axis_limit h d
    radius_pos := fun p hp => (hgeom p hp).1
    lam_pos := fun p hp => (hgeom p hp).2.1
    conformal := fun p hp => (hgeom p hp).2.2.2.2 }

end ChristodoulouBV

end
