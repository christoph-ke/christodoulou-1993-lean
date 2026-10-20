module

public import ChristodoulouBV.Existence.BVStieltjesClose
import Mathlib.Tactic

/-!
# Fixed outgoing edges through the axis endpoint

The scalar flux and logarithmic correction are integrable up to the
excluded axis endpoint. Consequently their pointwise residuals have
finite variation on the whole open edge, and their right tails vanish.
Changing the integration basepoint leaves these variations unchanged.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The outgoing scalar flux is integrable through the excluded axis
endpoint, using scalar BV and the uniform expansion bound. -/
theorem bv_outgoing_scalar_flux_axis_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b : ℝ} (hu : 0 ≤ u) (hub : u < b) :
    IntervalIntegrable (fun t => d.scalarRightFields.lam u t *
      (d.scalarRightFields.theta u t / d.scalarRightFields.r u t)) volume u b := by
  let S := d.scalarRightFields
  have hφ : BoundedVariationOn (S.phi u) (Ioo u b) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans ((bv_scalar_variation h hD d).1 u hu))
  have hp := (bv_density_integrable_and_bound hub.le hφ
    (bv_ae_deriv_phi_out_open h hD d hu)).1
  have hpi : IntegrableOn (fun t => S.theta u t / S.r u t) (Ioo u b) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hub.le).mp hp).mono_set
      Ioo_subset_Ioc_self
  have hm : AEStronglyMeasurable (S.lam u) (volume.restrict (Ioo u b)) := by
    exact bv_area_algebra_aestronglyMeasurable h hD d measurableSet_Ioo
      (c := fun t => (u, t)) (by fun_prop)
      (fun t ht => show (u, t) ∈ globalDomain from ⟨hu, ht.1⟩)
      (q := fun c => c 1) (by fun_prop)
  have hb : ∀ᵐ t ∂volume.restrict (Ioo u b), ‖S.lam u t‖ ≤ (1 / 2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hg := scalar_right_fields_geometry h hD d (u, t) ⟨hu, ht.1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hg.1])]
    exact hg.2.1
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hub.le).mpr
    ((integrableOn_Ioc_iff_integrableOn_Ioo (f := fun t =>
      S.lam u t * (S.theta u t / S.r u t))).mpr (hpi.bdd_mul hm hb))

/-- The outgoing scalar residual is BV on an axis-based open edge.
No value at the axis endpoint is used. -/
theorem bv_outgoing_scalar_residual_axis_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b : ℝ} (hu : 0 ≤ u) (hub : u < b) :
    BoundedVariationOn (bvOutgoingScalarResidual d.scalarRightFields u b) (Ioo u b) := by
  obtain ⟨K, hθ, _⟩ := bv_item5 h hD d
  have hz : BoundedVariationOn (d.scalarRightFields.theta u) (Ioo u b) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ (fun t ht =>
        show (u, t) ∈ globalDomain from ⟨hu, ht.1⟩)).trans (hθ u))
  have hi := bv_outgoing_scalar_flux_axis_integrable h hD d hu hub
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hub.le] at hInt
  exact hz.add (hInt.mono Ioo_subset_Icc_self)

/-- The outgoing logarithmic residual is BV on an axis-based open edge,
with the integrable correction supplied by the weak mass-ratio theorem. -/
theorem bv_outgoing_log_residual_axis_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b : ℝ} (hu : 0 ≤ u) (hub : u < b) :
    BoundedVariationOn (bvOutgoingLogResidual d.scalarRightFields u b) (Ioo u b) := by
  have hl := ((bv_corner_variations_finite h hD d).1 u b hu).2
  have hi := (bv_outgoing_g_bound h hD d hu hub).1
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hub.le] at hInt
  exact hl.add (hInt.mono Ioo_subset_Icc_self)

private theorem variation_integral_change_base
    {f q : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hi : IntervalIntegrable q volume a c) :
    eVariationOn (fun x => f x + ∫ t in b..x, q t) (Ioo a b) =
      eVariationOn (fun x => f x + ∫ t in c..x, q t) (Ioo a b) := by
  have hs (x y : ℝ) (hx : x ∈ Icc a c) (hy : y ∈ Icc a c) :
      IntervalIntegrable q volume x y := by
    apply hi.mono_set
    rw [uIcc_of_le (hab.trans hbc)]
    exact uIcc_subset_Icc hx hy
  have he : EqOn (fun x => f x + ∫ t in b..x, q t)
      (fun x => (f x + ∫ t in c..x, q t) + ∫ t in b..c, q t) (Ioo a b) := by
    intro x hx
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hs b c ⟨hab, hbc⟩ ⟨hab.trans hbc, le_rfl⟩)
      (hs c x ⟨hab.trans hbc, le_rfl⟩ ⟨hx.1.le, hx.2.le.trans hbc⟩)
    linarith only [hh]
  rw [eVariationOn.eq_of_eqOn he, eVariationOn.add_const]

/-- An outgoing scalar edge variation is independent of the upper
integration basepoint. -/
theorem bv_outgoing_scalar_edge_variation_change_base
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) :
    eVariationOn (bvOutgoingScalarResidual d.scalarRightFields a b) (Ioo a b) =
      eVariationOn (bvOutgoingScalarResidual d.scalarRightFields a c) (Ioo a b) :=
  variation_integral_change_base hab.le hbc
    (bv_outgoing_scalar_flux_axis_integrable h hD d ha (hab.trans_le hbc))

/-- An outgoing logarithmic edge variation is independent of the upper
integration basepoint. -/
theorem bv_outgoing_log_edge_variation_change_base
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) :
    eVariationOn (bvOutgoingLogResidual d.scalarRightFields a b) (Ioo a b) =
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields a c) (Ioo a b) :=
  variation_integral_change_base hab.le hbc
    (bv_outgoing_g_bound h hD d ha (hab.trans_le hbc)).1

/-- The amended scalar edge residual on `(a,a+ε)` has vanishing right
tail, even though its integration basepoint moves with `ε`. -/
theorem bv_outgoing_scalar_edge_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε => eVariationOn
      (bvOutgoingScalarResidual d.scalarRightFields a (a + ε)) (Ioo a (a + ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have ht := bv_variation_right_tail_tendsto_zero (lt_add_one a)
    (bv_outgoing_scalar_residual_axis_bv h hD d ha (lt_add_one a))
  have hshift : Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝[>] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, add_zero] using
        (tendsto_const_nhds (x := a)).add
          (continuousWithinAt_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact lt_add_of_pos_right a hε
  apply (ht.comp hshift).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  exact (bv_outgoing_scalar_edge_variation_change_base h hD d ha
    (lt_add_of_pos_right a hε.1) (add_le_add le_rfl hε.2.le)).symm

/-- The logarithmic edge residual on `(a,a+ε)` has vanishing right tail. -/
theorem bv_outgoing_log_edge_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε => eVariationOn
      (bvOutgoingLogResidual d.scalarRightFields a (a + ε)) (Ioo a (a + ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have ht := bv_variation_right_tail_tendsto_zero (lt_add_one a)
    (bv_outgoing_log_residual_axis_bv h hD d ha (lt_add_one a))
  have hshift : Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝[>] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, add_zero] using
        (tendsto_const_nhds (x := a)).add
          (continuousWithinAt_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact lt_add_of_pos_right a hε
  apply (ht.comp hshift).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  exact (bv_outgoing_log_edge_variation_change_base h hD d ha
    (lt_add_of_pos_right a hε.1) (add_le_add le_rfl hε.2.le)).symm

end ChristodoulouBV

end
