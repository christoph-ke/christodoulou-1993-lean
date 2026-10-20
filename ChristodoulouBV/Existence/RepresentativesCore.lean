module

public import ChristodoulouBV.Existence.TransportLimit
public import ChristodoulouBV.Existence.AreaSectionLimitJumpLines
import Mathlib.Tactic

/-!
# Common incoming representatives

The incoming representative change retains the raw outgoing fields, hence
every prescribed initial value of α. Its ν and β are exactly the
canonical right-u traces from the radius and scalar limits. A single countable set of outgoing lines contains
every point changed by either replacement, including the initial line.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Replace only the incoming fields by their already selected right-u
traces. The outgoing fields retain arbitrary prescribed datum values. -/
@[expose] noncomputable def RadiusLimitData.incomingRightFields {T : ℕ → Fields}
    (d : RadiusLimitData T) : Fields :=
  { d.rawFields with nu := d.rightNu, beta := d.rightBeta }

/-- The selected ν trace exists and is right continuous at every domain
point, including the initial endpoint of each incoming section. -/
theorem nu_right_rep
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      Tendsto (fun u => d.nu u p.2) (𝓝[>] p.1) (𝓝 (d.rightNu p.1 p.2)) ∧
      ContinuousWithinAt (fun u => d.rightNu u p.2) (Ici p.1) p.1 := by
  intro p hp
  exact ⟨(scalar_right_limits h hD d p hp).2.2.2,
    (right_expansions_continuous h hD d p hp).2⟩

/-- The selected β trace exists and is right continuous on exactly the
same carrier and incoming sections as the ν representative. -/
theorem beta_right_rep
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      Tendsto (fun u => d.beta u p.2) (𝓝[>] p.1) (𝓝 (d.rightBeta p.1 p.2)) ∧
      ContinuousWithinAt (fun u => d.rightBeta u p.2) (Ici p.1) p.1 := by
  intro p hp
  exact ⟨(scalar_right_limits h hD d p hp).2.2.1,
    (right_scalar_derivatives_continuous h hD d p hp).2⟩

/-- One countable set of whole outgoing lines contains both incoming
representative changes. This choice is independent of all later axis points. -/
theorem incoming_common_jump_lines
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ J : Set ℝ, J.Countable ∧ ∀ p ∈ globalDomain, p.1 ∉ J →
      d.incomingRightFields.nu p.1 p.2 = d.rawFields.nu p.1 p.2 ∧
      d.incomingRightFields.beta p.1 p.2 = d.rawFields.beta p.1 p.2 := by
  obtain ⟨J, hJ, hj⟩ := raw_incoming_common_exceptional_set h hD d
  refine ⟨insert 0 J, hJ.insert 0, ?_⟩
  intro p hp hpJ
  have hp0 : 0 < p.1 := lt_of_le_of_ne hp.1 (fun he => hpJ (mem_insert_iff.mpr (.inl he.symm)))
  obtain ⟨hn, hb⟩ := hj p.1 p.2 hp0 hp.2 (fun hm => hpJ (mem_insert_of_mem 0 hm))
  exact ⟨hn.continuousWithinAt.rightLim_eq, hb.continuousWithinAt.rightLim_eq⟩

/-- Both incoming changes agree almost everywhere on every closed
incoming segment, with no exception in the transverse coordinate. -/
theorem incoming_representatives_ae
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (_hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    ∀ᵐ u : ℝ, u ∈ Icc a b →
      d.rightNu u v = d.nu u v ∧ d.rightBeta u v = d.beta u v := by
  obtain ⟨J, hJ, hj⟩ := incoming_common_jump_lines h hD d
  filter_upwards [hJ.ae_notMem volume] with u hu ht
  exact hj (u, v) (hs ⟨ht, rfl⟩) hu

/-- The incoming changes retain the six pointwise geometry bounds;
the raw outgoing expansion and the canonical incoming expansion have the
same universal numerical bounds. -/
theorem incoming_right_fields_geometry
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ d.incomingRightFields.lam p.1 p.2 ∧
      d.incomingRightFields.lam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -d.incomingRightFields.nu p.1 p.2 ∧
      -d.incomingRightFields.nu p.1 p.2 ≤ 2 / 3 ∧
      (2 / 3 : ℝ) ≤ 1 - 2 * d.incomingRightFields.m p.1 p.2 /
        d.incomingRightFields.r p.1 p.2 ∧
      1 - 2 * d.incomingRightFields.m p.1 p.2 / d.incomingRightFields.r p.1 p.2 ≤ 1 := by
  intro p hp
  obtain ⟨hl0, hl1, _⟩ := (expansions_limit h d).2.2 p hp
  obtain ⟨_, _, hn0, hn1⟩ := right_expansions_geometry h hD d p hp
  obtain ⟨hq0, hq1⟩ := d.mass_geometry h p hp
  exact ⟨hl0, hl1, hn0, hn1, hq0, hq1⟩

/-- Incoming replacement preserves every literal initial datum value.
No continuity convention is imposed on the prescribed function. -/
theorem incoming_right_fields_data_trace
    {alpha₀ : ℝ → ℝ} {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a₀ n v) atTop (𝓝 (alpha₀ v)))
    (d : RadiusLimitData T) :
    ∀ v, 0 < v → d.incomingRightFields.r 0 v = v / 2 ∧
      d.incomingRightFields.alpha 0 v = alpha₀ v :=
  data_trace_limit h hpoint d

end ChristodoulouBV

end
