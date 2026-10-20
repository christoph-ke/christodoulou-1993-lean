module

public import ChristodoulouBV.AreaEstimates.SourceInputsWeakBounds
public import ChristodoulouBV.Existence.BVBasic

/-!
# Every weak source premise for the shared canonical limit

The basic BV limit estimates supply all premises for exactly `d.scalarRightFields`, on the same
shared diagonal subsequence. The common lower expansion constant is `1/3`
and the radius upper constant is `1/2`. No BV axis clause is used.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV.SourceInputsWeak

/-- The canonical limit geometry verifies the outgoing expansion lower premise. -/
theorem canonical_lam_lower
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain, (1 / 3 : ℝ) ≤ d.scalarRightFields.lam p.1 p.2 := fun p hp =>
      (scalar_right_fields_geometry h hD d p hp).1

/-- The canonical limit geometry verifies the incoming expansion upper premise. -/
theorem canonical_nu_upper
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain, d.scalarRightFields.nu p.1 p.2 ≤ -(1 / 3 : ℝ) := by
  intro p hp
  have hn := (scalar_right_fields_geometry h hD d p hp).2.2.1
  linarith only [hn]

/-- The reduced radius primitive gives the universal radius upper premise. -/
theorem canonical_radius_upper
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ u v, (u, v) ∈ globalDomain → d.scalarRightFields.r u v ≤ (1 / 2 : ℝ) * (v - u) := by
  intro u v huv
  exact radius_upper_of_lam_le (transport_limit_is_solution h hD d)
    (fun p hp => (scalar_right_fields_geometry h hD d p hp).2.1) huv

/-- The mass limit verifies both pointwise mass-ratio premises without any BV axis clause. -/
theorem canonical_mass_ratio_bounds
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n))
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      0 ≤ 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 < 1 := by
  intro p hp
  have hm := mass_limit_geometry h d p hp
  exact ⟨hm.2.2.2.1, hm.2.2.2.2.1.trans_lt (by norm_num)⟩

/-- The basic BV estimates verify the outgoing scalar absolute-continuity premise. -/
theorem canonical_scalar_ac_out
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (d.scalarRightFields.phi u) a b := (bv_item3 h hD d).1

/-- The basic BV estimates verify finite scalar variation on every outgoing section. -/
theorem canonical_scalar_bv_out
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ u, BoundedVariationOn (d.scalarRightFields.phi u) {v | (u, v) ∈ globalDomain} := by
  intro u
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((bv_item3 h hD d).2.2.choose_spec.1 u)

/-- The basic BV estimates verify finite invariant variation on every outgoing section. -/
theorem canonical_invariant_bv_out
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ u, BoundedVariationOn (d.scalarRightFields.theta u) {v | (u, v) ∈ globalDomain} := by
  intro u
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((bv_item5 h hD d).choose_spec.1 u)

/-- The basic BV estimates verify the incoming scalar absolute-continuity premise. -/
theorem canonical_scalar_ac_in
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (fun u => d.scalarRightFields.phi u v) a b := (bv_item3 h hD
        d).2.1

/-- The basic BV estimates verify finite scalar variation on every incoming section. -/
theorem canonical_scalar_bv_in
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ v, BoundedVariationOn (fun u => d.scalarRightFields.phi u v)
      {u | (u, v) ∈ globalDomain} := by
  intro v
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((bv_item3 h hD d).2.2.choose_spec.2 v)

/-- The basic BV estimates verify finite invariant variation on every incoming section. -/
theorem canonical_invariant_bv_in
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ v, BoundedVariationOn (fun u => d.scalarRightFields.zeta u v)
      {u | (u, v) ∈ globalDomain} := by
  intro v
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((bv_item5 h hD d).choose_spec.2 v)

end ChristodoulouBV.SourceInputsWeak

end
