module

public import ChristodoulouBV.Existence.RepresentativesTransport
import Mathlib.Tactic

/-!
# Stability of all ten frozen primitives

The four incoming integral densities are insensitive to the common
countable set of changed u values. The outgoing ν and β equations use
the right-u endpoint passage proved in `RepresentativesTransport`.
The other outgoing fields and every prescribed α datum remain literal.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem primitive_congr_density_ae {F g G : ℝ → ℝ} {a b : ℝ}
    (hp : IntervalPrimitive F g a b)
    (he : ∀ᵐ t : ℝ, t ∈ uIoc a b → G t = g t) : IntervalPrimitive F G a b := by
  refine ⟨hp.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (he.mono fun _ ht hi => (ht hi).symm)), ?_⟩
  rw [intervalIntegral.integral_congr_ae he]
  exact hp.2

/-- The incoming λ and α equations retain their raw endpoint values
after the common incoming representative change. -/
theorem incoming_right_fields_incoming_transport
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.incomingRightFields.lam u v)
        (fun u => IsBVSolution.radiusCoeff d.incomingRightFields u v) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.incomingRightFields.alpha u v)
        (fun u => IsBVSolution.radiusCoeff d.incomingRightFields u v *
          d.incomingRightFields.phi u v) a b := by
  have he (v a b : ℝ) (hab : a ≤ b) (hs : inSeg v a b ⊆ globalDomain) :
      ∀ᵐ u : ℝ, u ∈ uIoc a b →
        IsBVSolution.radiusCoeff d.incomingRightFields u v =
          IsBVSolution.radiusCoeff d.rawFields u v := by
    filter_upwards [incoming_representatives_ae h hD d hab hs] with u hu hi
    rw [uIoc_of_le hab] at hi
    have hn := (hu ⟨hi.1.le, hi.2⟩).1
    simp only [IsBVSolution.radiusCoeff, RadiusLimitData.incomingRightFields, hn,
      RadiusLimitData.rawFields]
  constructor
  · intro v a b hab hs
    exact primitive_congr_density_ae ((raw_expansion_primitive_limit h d).1 v a b hab hs)
      (he v a b hab hs)
  · intro v a b hab hs
    apply primitive_congr_density_ae ((raw_alpha_beta_transport_limit h d).1 v a b hab hs)
    filter_upwards [he v a b hab hs] with u hu hi
    exact congrArg (fun x => x * d.rawFields.phi u v) (hu hi)

/-- The incoming changes preserve strict signs and a positive conformal
factor at every point, with no new premise on representatives. -/
theorem incoming_right_fields_signs_conformal
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      0 < d.incomingRightFields.r p.1 p.2 ∧
      0 < d.incomingRightFields.lam p.1 p.2 ∧
      d.incomingRightFields.nu p.1 p.2 < 0 ∧
      0 < 1 - 2 * d.incomingRightFields.m p.1 p.2 / d.incomingRightFields.r p.1 p.2 ∧
      ∃ Ω : ℝ, 0 < Ω ∧
        (1 - 2 * d.incomingRightFields.m p.1 p.2 / d.incomingRightFields.r p.1 p.2) * Ω ^ 2 =
          -(4 * d.incomingRightFields.lam p.1 p.2 * d.incomingRightFields.nu p.1 p.2) := by
  intro p hp
  obtain ⟨hl0, _, hn0, _, hq0, _⟩ := incoming_right_fields_geometry h hD d p hp
  have hl : 0 < d.incomingRightFields.lam p.1 p.2 := lt_of_lt_of_le (by norm_num) hl0
  have hn : d.incomingRightFields.nu p.1 p.2 < 0 := by linarith only [hn0]
  let q := 1 - 2 * d.incomingRightFields.m p.1 p.2 / d.incomingRightFields.r p.1 p.2
  let N := -(4 * d.incomingRightFields.lam p.1 p.2 * d.incomingRightFields.nu p.1 p.2)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hq0
  have hN : 0 < N := neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hl) hn)
  refine ⟨d.radius_pos h hp, hl, hn, hq, Real.sqrt (N / q),
    Real.sqrt_pos.mpr (div_pos hN hq), ?_⟩
  change q * Real.sqrt (N / q) ^ 2 = N
  rw [Real.sq_sqrt (div_pos hN hq).le]
  exact mul_div_cancel₀ N hq.ne'

/-- Replacing ν and β by their simultaneous right-u representatives
preserves all ten frozen primitive equations, signs, conformal positivity,
and both radius/mass axis limits. The outgoing raw fields are retained,
so the literal arbitrary-value datum trace is preserved as well. -/
theorem representative_stability
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) : IsSolution globalDomain d.incomingRightFields := by
  obtain ⟨hrout, _⟩ := radius_primitive_limit h hD d
  obtain ⟨_, hrin⟩ := right_radius_primitive_limit h hD d
  obtain ⟨hψout, _⟩ := s6_scalar_primitive h hD d
  obtain ⟨_, hψin⟩ := scalar_right_fields_primitives h hD d
  obtain ⟨hmout, _⟩ := raw_mass_primitive_limit h d
  obtain ⟨_, hmin⟩ := mass_primitive_limit h hD d
  obtain ⟨hl, hα⟩ := incoming_right_fields_incoming_transport h hD d
  obtain ⟨hn, hβ⟩ := incoming_right_fields_outgoing_transport h hD d
  have hgeom := incoming_right_fields_signs_conformal h hD d
  exact {
    development := s6_globalDomain_isDomainOfDevelopment
    radius_out := hrout
    radius_in := hrin
    scalar_radius_out := hψout
    scalar_radius_in := hψin
    mass_out := hmout
    mass_in := hmin
    lam_in := hl
    nu_out := hn
    alpha_in := hα
    beta_out := hβ
    radius_axis := radius_axis_limit h d
    mass_axis := mass_axis_limit h d
    radius_pos := fun p hp => (hgeom p hp).1
    lam_pos := fun p hp => (hgeom p hp).2.1
    conformal := fun p hp => (hgeom p hp).2.2.2.2 }

end ChristodoulouBV

end
