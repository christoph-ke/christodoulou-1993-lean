module

public import ChristodoulouBV.AreaEstimates.SourceInputsWeakCanonical
public import ChristodoulouBV.AreaEstimates.SourceInputsWeakCorollaries

/-!
# Source mass-ratio estimates for the partially assembled canonical BV limit

The four source mass-ratio estimates apply before the remaining BV axis
clauses are proved. The majorant constants `15` and `24` are the universal
constants from the basic BV estimates. The accompanying endpoint
integrability statements are used in the BV Stieltjes transport estimates.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV.SourceInputsWeak

/-- The canonical outgoing mass ratio tends to zero using only the basic BV limit estimates. -/
theorem canonical_mass_ratio_tendsto_zero_axis_out
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u v : ℝ} (huv : (u, v) ∈ globalDomain) :
    Tendsto (fun t => 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) (𝓝[>] u) (𝓝 (0 :
      ℝ)) := by
  exact mass_ratio_tendsto_zero_axis_out (transport_limit_is_solution h hD d) (by norm_num : (0 : ℝ)
    < 1 / 3)
    (canonical_lam_lower h hD d)
    ⟨1 / 2, canonical_radius_upper h hD d⟩ (canonical_mass_ratio_bounds h d)
    (canonical_scalar_ac_out h hD d) (canonical_scalar_bv_out h hD d)
    (canonical_invariant_bv_out h hD d) huv

/-- The canonical incoming mass ratio tends to zero using only the basic BV limit estimates. -/
theorem canonical_mass_ratio_tendsto_zero_axis_in_of_half_open_access
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ globalDomain) :
    Tendsto (fun s => 2 * d.scalarRightFields.m s v / d.scalarRightFields.r s v) (𝓝[<] v) (𝓝 (0 :
      ℝ)) := by
  exact mass_ratio_tendsto_zero_axis_in_of_half_open_access (transport_limit_is_solution h hD d) (by
    norm_num : (0 : ℝ) < 1 / 3)
    (canonical_lam_lower h hD d)
    (canonical_nu_upper h hD d) ⟨1 / 2, canonical_radius_upper h hD d⟩ (canonical_mass_ratio_bounds
      h d)
    (canonical_scalar_ac_in h hD d) (canonical_scalar_bv_in h hD d)
    (canonical_invariant_bv_in h hD d) huv haccess

/-- The outgoing canonical source estimate has universal majorant `15 * D.toReal`. -/
theorem canonical_source_mass_ratio_out_majorant
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    (∫ t in u..v, (2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
      d.scalarRightFields.lam u t /
        ((1 - 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) * d.scalarRightFields.r u
          t)) ≤
      (15 * D.toReal) * (eVariationOn (d.scalarRightFields.phi u) (Ioo u v)).toReal := by
  exact source_mass_ratio_out_majorant (transport_limit_is_solution h hD d) (by norm_num : (0 : ℝ) <
    1 / 3)
    (canonical_lam_lower h hD d)
    ⟨1 / 2, canonical_radius_upper h hD d⟩ (canonical_mass_ratio_bounds h d)
    (canonical_scalar_ac_out h hD d) (canonical_scalar_bv_out h hD d)
    (canonical_invariant_bv_out h hD d) ⟨hu, huv⟩
    (fun p hp => (bv_weighted_ratio_bounds h hD d p hp).1)

/-- The incoming canonical source estimate has universal majorant `24 * D.toReal`. -/
theorem canonical_source_mass_ratio_in_majorant
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    -(∫ s in u..v, (2 * d.scalarRightFields.m s v / d.scalarRightFields.r s v) *
      d.scalarRightFields.nu s v /
        ((1 - 2 * d.scalarRightFields.m s v / d.scalarRightFields.r s v) * d.scalarRightFields.r s
          v)) ≤
      (24 * D.toReal) * (eVariationOn (fun s => d.scalarRightFields.phi s v) (Ioo u v)).toReal := by
  exact source_mass_ratio_in_majorant_of_half_open_access (transport_limit_is_solution h hD d) (by
    norm_num : (0 : ℝ) < 1 / 3)
    (canonical_lam_lower h hD d)
    (canonical_nu_upper h hD d) ⟨1 / 2, canonical_radius_upper h hD d⟩ (canonical_mass_ratio_bounds
      h d)
    (canonical_scalar_ac_in h hD d) (canonical_scalar_bv_in h hD d)
    (canonical_invariant_bv_in h hD d) huv
    (fun s hs => ⟨hu.trans hs.1, hs.2⟩)
    (fun s hs => (bv_weighted_ratio_bounds h hD d (s, v) ⟨hu.trans hs.1, hs.2⟩).2)

/-- The outgoing canonical source coefficient is integrable through the axis endpoint. -/
theorem canonical_source_mass_ratio_out_interval_integrable
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    IntervalIntegrable (fun t => (2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
      d.scalarRightFields.lam u t /
        ((1 - 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) * d.scalarRightFields.r u
          t)) volume u v := by
  exact source_mass_ratio_out_interval_integrable (transport_limit_is_solution h hD d) (by norm_num
    : (0 : ℝ) < 1 / 3)
    (canonical_lam_lower h hD d)
    ⟨1 / 2, canonical_radius_upper h hD d⟩ (canonical_mass_ratio_bounds h d)
    (canonical_scalar_ac_out h hD d) (canonical_scalar_bv_out h hD d)
    (canonical_invariant_bv_out h hD d) ⟨hu, huv⟩
    (fun t ht => (bv_weighted_ratio_bounds h hD d (u, t) ⟨hu, ht.1⟩).1)

/-- The incoming canonical source coefficient is integrable through the axis endpoint. -/
theorem canonical_source_mass_ratio_in_interval_integrable
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    IntervalIntegrable (fun s => (2 * d.scalarRightFields.m s v / d.scalarRightFields.r s v) *
      d.scalarRightFields.nu s v /
        ((1 - 2 * d.scalarRightFields.m s v / d.scalarRightFields.r s v) * d.scalarRightFields.r s
          v)) volume u v := by
  exact source_mass_ratio_in_interval_integrable (transport_limit_is_solution h hD d) (by norm_num :
    (0 : ℝ) < 1 / 3)
    (canonical_lam_lower h hD d)
    (canonical_nu_upper h hD d) ⟨1 / 2, canonical_radius_upper h hD d⟩ (canonical_mass_ratio_bounds
      h d)
    (canonical_scalar_ac_in h hD d) (canonical_scalar_bv_in h hD d)
    (canonical_invariant_bv_in h hD d) huv
    (fun s hs => ⟨hu.trans hs.1, hs.2⟩)
    (fun s hs => (bv_weighted_ratio_bounds h hD d (s, v) ⟨hu.trans hs.1, hs.2⟩).2)

end ChristodoulouBV.SourceInputsWeak

end
