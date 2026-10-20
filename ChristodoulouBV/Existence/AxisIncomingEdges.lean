module

public import ChristodoulouBV.Existence.BVStieltjesClose
import Mathlib.Tactic

/-!
# Fixed incoming edges through the axis endpoint

Scalar BV controls the incoming scalar flux through the excluded axis.
The scalar and corrected logarithmic residuals consequently have finite
variation on the whole open terminal edge. Their left tails vanish,
including when the integration basepoint moves with the lower endpoint.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The incoming scalar flux is integrable through the excluded axis
endpoint, by scalar BV and the universal bound on the negative expansion. -/
theorem bv_incoming_scalar_flux_axis_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    IntervalIntegrable (fun t => d.scalarRightFields.nu t v *
      (d.scalarRightFields.zeta t v / d.scalarRightFields.r t v)) volume a v := by
  let S := d.scalarRightFields
  have hφ : BoundedVariationOn (fun t => S.phi t v) (Ioo a v) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ (fun t ht =>
        show t ∈ Ico 0 v from ⟨ha.trans ht.1.le, ht.2⟩)).trans
          ((bv_scalar_variation h hD d).2 v (ha.trans_lt hav)))
  have hp := (bv_density_integrable_and_bound hav.le hφ
    (bv_ae_deriv_phi_in_open h hD d ha)).1
  have hpi : IntegrableOn (fun t => S.zeta t v / S.r t v) (Ioo a v) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).mp hp).mono_set
      Ioo_subset_Ioc_self
  have hm : AEStronglyMeasurable (fun t => S.nu t v)
      (volume.restrict (Ioo a v)) := by
    exact bv_area_algebra_aestronglyMeasurable h hD d measurableSet_Ioo
      (c := fun t => (t, v)) (by fun_prop)
      (fun t ht => show (t, v) ∈ globalDomain from ⟨ha.trans ht.1.le, ht.2⟩)
      (q := fun c => c 2) (by fun_prop)
  have hb : ∀ᵐ t ∂volume.restrict (Ioo a v), ‖S.nu t v‖ ≤ (2 / 3 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hg := scalar_right_fields_geometry h hD d (t, v) ⟨ha.trans ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith only [hg.2.2.1])]
    exact hg.2.2.2.1
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).mpr
    ((integrableOn_Ioc_iff_integrableOn_Ioo (f := fun t =>
      S.nu t v * (S.zeta t v / S.r t v))).mpr (hpi.bdd_mul hm hb))

/-- The incoming scalar residual is BV on an axis-based open terminal
edge. No assigned value at its axis endpoint is used. -/
theorem bv_incoming_scalar_residual_axis_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    BoundedVariationOn (bvIncomingScalarResidual d.scalarRightFields v a)
      (Ioo a v) := by
  obtain ⟨K, _, hζ⟩ := bv_item5 h hD d
  have hz : BoundedVariationOn (fun t => d.scalarRightFields.zeta t v) (Ioo a v) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ (fun t ht =>
        show (t, v) ∈ globalDomain from ⟨ha.trans ht.1.le, ht.2⟩)).trans (hζ v))
  have hi := bv_incoming_scalar_flux_axis_integrable h hD d ha hav
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hav.le] at hInt
  exact hz.add (hInt.mono Ioo_subset_Icc_self)

/-- The incoming logarithmic residual with the corrected `g*` is BV
through the excluded axis endpoint. -/
theorem bv_incoming_log_residual_axis_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    BoundedVariationOn (bvIncomingLogResidual d.scalarRightFields v a)
      (Ioo a v) := by
  have hl := ((bv_corner_variations_finite h hD d).2 a v ha hav).2
  have hi := (bv_incoming_g_bound h hD d ha hav).1
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hav.le] at hInt
  exact hl.add (hInt.mono Ioo_subset_Icc_self)

private theorem variation_integral_change_base
    {f q : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hi : IntervalIntegrable q volume a c) :
    eVariationOn (fun x => f x + ∫ t in b..x, q t) (Ioo b c) =
      eVariationOn (fun x => f x + ∫ t in a..x, q t) (Ioo b c) := by
  have hs (x y : ℝ) (hx : x ∈ Icc a c) (hy : y ∈ Icc a c) :
      IntervalIntegrable q volume x y := by
    apply hi.mono_set
    rw [uIcc_of_le (hab.trans hbc)]
    exact uIcc_subset_Icc hx hy
  have he : EqOn (fun x => f x + ∫ t in b..x, q t)
      (fun x => (f x + ∫ t in a..x, q t) + -(∫ t in a..b, q t)) (Ioo b c) := by
    intro x hx
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hs a b ⟨le_rfl, hab.trans hbc⟩ ⟨hab, hbc⟩)
      (hs b x ⟨hab, hbc⟩ ⟨hab.trans hx.1.le, hx.2.le⟩)
    linarith only [hh]
  rw [eVariationOn.eq_of_eqOn he, eVariationOn.add_const]

/-- Moving the incoming scalar integration basepoint preserves the
variation on the corresponding terminal tail. -/
theorem bv_incoming_scalar_edge_variation_change_base
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b v : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b < v) :
    eVariationOn (bvIncomingScalarResidual d.scalarRightFields v b) (Ioo b v) =
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a) (Ioo b v) :=
  variation_integral_change_base hab hbv.le
    (bv_incoming_scalar_flux_axis_integrable h hD d ha (hab.trans_lt hbv))

/-- Moving the incoming logarithmic integration basepoint preserves
the variation of the corrected residual on the terminal tail. -/
theorem bv_incoming_log_edge_variation_change_base
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b v : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b < v) :
    eVariationOn (bvIncomingLogResidual d.scalarRightFields v b) (Ioo b v) =
      eVariationOn (bvIncomingLogResidual d.scalarRightFields v a) (Ioo b v) :=
  variation_integral_change_base hab hbv.le
    (bv_incoming_g_bound h hD d ha (hab.trans_lt hbv)).1

/-- The incoming scalar fixed-edge residual has a vanishing left tail
even though its lower integration basepoint moves. -/
theorem bv_incoming_scalar_edge_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => eVariationOn
      (bvIncomingScalarResidual d.scalarRightFields a (a - ε)) (Ioo (a - ε) a))
      (𝓝[>] 0) (𝓝 0) := by
  have ht := bv_variation_left_tail_tendsto_zero ha
    (bv_incoming_scalar_residual_axis_bv h hD d (a := 0) le_rfl ha)
  have hshift : Tendsto (fun ε : ℝ => a - ε) (𝓝[>] 0) (𝓝[<] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, sub_zero] using
        (tendsto_const_nhds (x := a)).sub
          (continuousWithinAt_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact sub_lt_self a hε
  apply (ht.comp hshift).congr'
  filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
  exact (bv_incoming_scalar_edge_variation_change_base h hD d le_rfl
    (sub_nonneg.mpr hε.2.le) (sub_lt_self a hε.1)).symm

/-- The corrected incoming logarithmic fixed-edge residual has a
vanishing left tail with a moving integration basepoint. -/
theorem bv_incoming_log_edge_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => eVariationOn
      (bvIncomingLogResidual d.scalarRightFields a (a - ε)) (Ioo (a - ε) a))
      (𝓝[>] 0) (𝓝 0) := by
  have ht := bv_variation_left_tail_tendsto_zero ha
    (bv_incoming_log_residual_axis_bv h hD d (a := 0) le_rfl ha)
  have hshift : Tendsto (fun ε : ℝ => a - ε) (𝓝[>] 0) (𝓝[<] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, sub_zero] using
        (tendsto_const_nhds (x := a)).sub
          (continuousWithinAt_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact sub_lt_self a hε
  apply (ht.comp hshift).congr'
  filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
  exact (bv_incoming_log_edge_variation_change_base h hD d le_rfl
    (sub_nonneg.mpr hε.2.le) (sub_lt_self a hε.1)).symm

end ChristodoulouBV

end
