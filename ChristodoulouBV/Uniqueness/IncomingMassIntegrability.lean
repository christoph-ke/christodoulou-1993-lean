module

public import ChristodoulouBV.Uniqueness.IncomingHardyEndpoint
public import ChristodoulouBV.Uniqueness.IncomingTerminalLinear
import ChristodoulouBV.ForMathlib.BoundedVariation.SliceFacts
import Mathlib.Tactic.FunProp

/-!
# Integrability of the corrected incoming mass coefficient

The BV representative values need only be measurable on the open incoming
ray. The diagonal value is irrelevant for interval integration.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace ChristodoulouBV.Uniqueness

private theorem incoming_coefficient_abs_le
    {z nu r d B c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hd : 0 < d)
    (hnu : c ≤ |nu|) (hr : 0 < r) (hrlower : d * δ ≤ r)
    (hz : |z| ≤ B) :
    |-(z ^ 2 / (nu * r))| ≤ (B / (c * d)) * (|z| / δ) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hz
  have hden : c * d * δ ≤ |nu| * r := by
    calc
      c * d * δ = c * (d * δ) := by ring
      _ ≤ c * r := mul_le_mul_of_nonneg_left hrlower hc.le
      _ ≤ |nu| * r := mul_le_mul_of_nonneg_right hnu hr.le
  have hsq : |z| ^ 2 ≤ B * |z| := by
    calc
      |z| ^ 2 = |z| * |z| := by ring
      _ ≤ B * |z| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have hmul : |z| ^ 2 * (c * d * δ) ≤ B * |z| * (|nu| * r) := by
    calc
      |z| ^ 2 * (c * d * δ) ≤ B * |z| * (c * d * δ) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ B * |z| * (|nu| * r) :=
        mul_le_mul_of_nonneg_left hden (mul_nonneg hB (abs_nonneg _))
  have hnuPos : 0 < |nu| := hc.trans_le hnu
  rw [abs_neg, abs_div, abs_mul, abs_pow, abs_of_pos hr]
  have heq : B / (c * d) * (|z| / δ) =
      B * |z| / ((c * d) * δ) := by ring
  rw [heq]
  exact (div_le_div_iff₀ (mul_pos hnuPos hr)
    (mul_pos (mul_pos hc hd) hδ)).2 (by nlinarith only [hmul])

/-- The homogeneous coefficient is integrable up to the incoming diagonal
because it is bounded by one fixed multiple of `|ζ₂|/(v-u)`. -/
theorem ComparisonData.incomingMassCoefficient_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntervalIntegrable (fun s => incomingMassCoefficient D s v)
      volume u v := by
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have haccess₁ := IsBVSolution.incoming_axis_access_of_triangle hT₁ huv
  have haccess₂ := IsBVSolution.incoming_axis_access_of_triangle hT₂ huv
  obtain ⟨d, _, hd, hrad⟩ := D.h₁.exists_uniform_radius_bounds
  obtain ⟨c, hc, hnuLower⟩ := D.h₂.lam_bounded_below
  let B := max D.h₂.item5.choose 0
  let C := B / (c * d)
  have hC : 0 ≤ C := by dsimp [C, B]; positivity
  have hw := zeta_abs_div_distance_integrable D.h₂ hT₂ huv
  have hwIoo : Integrable (fun s => |D.S₂.zeta s v| / (v - s))
      (volume.restrict (Ioo u v)) := by
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact hw
  have hBVζ : BoundedVariationOn (fun s => D.S₂.zeta s v)
      {s | (s, v) ∈ D.U₂} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (D.h₂.item5.choose_spec.2 v)
  have hBVν : BoundedVariationOn (fun s => D.S₂.nu s v)
      {s | (s, v) ∈ D.U₂} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (D.h₂.item1.choose_spec.2 v)
  have hsub : Ioo u v ⊆ {s | (s, v) ∈ D.U₂} := by
    intro s hs
    exact haccess₂ s ⟨hs.1.le, hs.2⟩
  have hζmeas := hBVζ.measurable_indicator_Ioo hsub
  have hνmeas := hBVν.measurable_indicator_Ioo hsub
  have hrcont : ContinuousOn (fun s => D.S₁.r s v) (Ioo u v) := by
    apply continuousOn_Ioo_of_ac_subintervals
    intro x y hux hxy hyv
    have hseg : inSeg v x y ⊆ D.U₁ := by
      apply IsBVSolution.incoming_seg_subset_of_half_open_access hyv
      intro s hs
      exact haccess₁ s ⟨hux.le.trans hs.1, hs.2⟩
    exact (D.h₁.solution.radius_in_ac_ae hxy hseg).1
  have hrmeas : AEStronglyMeasurable (fun s => D.S₁.r s v)
      (volume.restrict (Ioo u v)) :=
    hrcont.aestronglyMeasurable measurableSet_Ioo
  have hmeas : AEStronglyMeasurable
      (fun s => incomingMassCoefficient D s v)
      (volume.restrict (Ioo u v)) := by
    have hζ : AEStronglyMeasurable
        (fun s => (Ioo u v).indicator (fun t => D.S₂.zeta t v) s)
        (volume.restrict (Ioo u v)) := hζmeas.aestronglyMeasurable
    have hν : AEStronglyMeasurable
        (fun s => (Ioo u v).indicator (fun t => D.S₂.nu t v) s)
        (volume.restrict (Ioo u v)) := hνmeas.aestronglyMeasurable
    have hnum : AEMeasurable
        (fun s => -((Ioo u v).indicator (fun t => D.S₂.zeta t v) s *
          (Ioo u v).indicator (fun t => D.S₂.zeta t v) s))
        (volume.restrict (Ioo u v)) :=
      ((hζ.mul hζ).neg).aemeasurable
    have hden : AEMeasurable
        (fun s => (Ioo u v).indicator (fun t => D.S₂.nu t v) s * D.S₁.r s v)
        (volume.restrict (Ioo u v)) :=
      (hν.mul hrmeas).aemeasurable
    have hq : AEMeasurable
        (fun s =>
          -((Ioo u v).indicator (fun t => D.S₂.zeta t v) s *
            (Ioo u v).indicator (fun t => D.S₂.zeta t v) s) /
          ((Ioo u v).indicator (fun t => D.S₂.nu t v) s * D.S₁.r s v))
        (volume.restrict (Ioo u v)) :=
      measurable_div.comp_aemeasurable (hnum.prodMk hden)
    apply hq.aestronglyMeasurable.congr
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
      simp only [Set.indicator_of_mem hs]
      unfold incomingMassCoefficient
      ring)
  have hbound : ∀ᵐ s ∂volume.restrict (Ioo u v),
      ‖incomingMassCoefficient D s v‖ ≤
        C * (|D.S₂.zeta s v| / (v - s)) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    exact Filter.Eventually.of_forall (fun s hs => by
      have hst : (s, v) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1.trans hs.1.le, hs.2, huv.2.2⟩
      have hp := D.hT hst
      have hnu : c ≤ |D.S₂.nu s v| := by
        have hh := D.h₂.nu_le_neg_lower hc hnuLower hp.2
        rw [abs_of_neg (lt_of_le_of_lt hh (neg_lt_zero.mpr hc))]
        linarith
      have hr := D.h₁.solution.radius_pos (s, v) hp.1
      have hrlower := (hrad s v hp.1).1
      have hz := D.h₂.zeta_abs_le_global_variation_of_triangle hT₂ hst
      have hh := incoming_coefficient_abs_le hc (sub_pos.mpr hs.2) hd
        hnu hr hrlower hz
      simpa only [Real.norm_eq_abs, incomingMassCoefficient, C, B] using hh)
  have hi : Integrable (fun s => incomingMassCoefficient D s v)
      (volume.restrict (Ioo u v)) :=
    Integrable.mono' (hwIoo.const_mul C) hmeas hbound
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
  change Integrable _ (volume.restrict (Ioc u v))
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact hi

/-- The mass difference is bounded and continuous on the open part of each
full incoming characteristic. These facts make the coefficient times mass
difference integrable up to the terminal axis. -/
theorem ComparisonData.incomingMassCoefficient_mul_difference_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntervalIntegrable
      (fun s => incomingMassCoefficient D s v *
        (D.S₁.m s v - D.S₂.m s v)) volume u v := by
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have haccess₁ := IsBVSolution.incoming_axis_access_of_triangle hT₁ huv
  have haccess₂ := IsBVSolution.incoming_axis_access_of_triangle hT₂ huv
  have hmasscont (S : Fields) {U : Set (ℝ × ℝ)}
      (h : IsBVSolution U S) (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
      ContinuousOn (fun s => S.m s v) (Ioo u v) := by
    apply continuousOn_Ioo_of_ac_subintervals
    intro x y hux hxy hyv
    have hseg : inSeg v x y ⊆ U := by
      apply IsBVSolution.incoming_seg_subset_of_half_open_access hyv
      intro s hs
      exact haccess s ⟨hux.le.trans hs.1, hs.2⟩
    exact (h.solution.mass_in_ac_ae hxy hseg).1
  have hycont : ContinuousOn
      (fun s => D.S₁.m s v - D.S₂.m s v) (Ioo u v) :=
    (hmasscont D.S₁ D.h₁ haccess₁).sub
      (hmasscont D.S₂ D.h₂ haccess₂)
  obtain ⟨K₁, _, hK₁⟩ := D.h₁.exists_uniform_radius_upper
  obtain ⟨K₂, _, hK₂⟩ := D.h₂.exists_uniform_radius_upper
  let M := (max K₁ 0 + max K₂ 0) * (v - u) / 2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))
        (sub_nonneg.mpr huv.2.1.le)) (by norm_num)
  have hybound : ∀ s ∈ Ioo u v,
      |D.S₁.m s v - D.S₂.m s v| ≤ M := by
    intro s hs
    have hpt : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1.trans hs.1.le, hs.2, huv.2.2⟩
    have hp := D.hT hpt
    have hm₁ := D.h₁.mass_nonneg hp.1
    have hm₂ := D.h₂.mass_nonneg hp.2
    have hmr₁ := D.h₁.two_mass_lt_radius hp.1
    have hmr₂ := D.h₂.two_mass_lt_radius hp.2
    have hr₁ := hK₁ s v hp.1
    have hr₂ := hK₂ s v hp.2
    have hd : 0 ≤ v - s := sub_nonneg.mpr hs.2.le
    have hupper₁ : D.S₁.r s v ≤ max K₁ 0 * (v - u) := by
      calc
        D.S₁.r s v ≤ K₁ * (v - s) := hr₁
        _ ≤ max K₁ 0 * (v - s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hd
        _ ≤ max K₁ 0 * (v - u) := by
          gcongr
          exact hs.1.le
    have hupper₂ : D.S₂.r s v ≤ max K₂ 0 * (v - u) := by
      calc
        D.S₂.r s v ≤ K₂ * (v - s) := hr₂
        _ ≤ max K₂ 0 * (v - s) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hd
        _ ≤ max K₂ 0 * (v - u) := by
          gcongr
          exact hs.1.le
    have habs := abs_sub (D.S₁.m s v) (D.S₂.m s v)
    have habs' : |D.S₁.m s v - D.S₂.m s v| ≤
        D.S₁.m s v + D.S₂.m s v := by
      simpa only [abs_of_nonneg hm₁, abs_of_nonneg hm₂] using habs
    have hsum : 2 * (D.S₁.m s v + D.S₂.m s v) ≤
        (max K₁ 0 + max K₂ 0) * (v - u) := by
      calc
        2 * (D.S₁.m s v + D.S₂.m s v) =
            2 * D.S₁.m s v + 2 * D.S₂.m s v := by ring
        _ ≤ D.S₁.r s v + D.S₂.r s v := by linarith only [hmr₁, hmr₂]
        _ ≤ max K₁ 0 * (v - u) + max K₂ 0 * (v - u) :=
          add_le_add hupper₁ hupper₂
        _ = (max K₁ 0 + max K₂ 0) * (v - u) := by ring
    have hsum' : D.S₁.m s v + D.S₂.m s v ≤ M := by
      dsimp [M]
      linarith only [hsum]
    exact habs'.trans hsum'
  have hk := D.incomingMassCoefficient_integrable huv
  have hkIoo : Integrable (fun s => incomingMassCoefficient D s v)
      (volume.restrict (Ioo u v)) := by
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).1 hk
  have hmeas : AEStronglyMeasurable
      (fun s => incomingMassCoefficient D s v *
        (D.S₁.m s v - D.S₂.m s v))
      (volume.restrict (Ioo u v)) :=
    hkIoo.aestronglyMeasurable.mul
      (hycont.aestronglyMeasurable measurableSet_Ioo)
  have hbound : ∀ᵐ s ∂volume.restrict (Ioo u v),
      ‖incomingMassCoefficient D s v *
        (D.S₁.m s v - D.S₂.m s v)‖ ≤
      M * ‖incomingMassCoefficient D s v‖ := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs]
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_right (hybound s hs)
          (norm_nonneg (incomingMassCoefficient D s v))))
  have hi : Integrable
      (fun s => incomingMassCoefficient D s v *
        (D.S₁.m s v - D.S₂.m s v))
      (volume.restrict (Ioo u v)) :=
    Integrable.mono' (hkIoo.norm.const_mul M) hmeas hbound
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
  change Integrable _ (volume.restrict (Ioc u v))
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact hi

/-- The forcing in the corrected linear mass equation is integrable on a
complete incoming ray. Its integrability follows from the two frozen mass
densities and the integrable homogeneous term. -/
theorem ComparisonData.incomingMassForcing_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntervalIntegrable (fun s => incomingMassForcing D s v / 2)
      volume u v := by
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have haccess₁ := IsBVSolution.incoming_axis_access_of_triangle hT₁ huv
  have haccess₂ := IsBVSolution.incoming_axis_access_of_triangle hT₂ huv
  have hm₁ := D.h₁.massInDensity_integrable_of_half_open_access
    huv.2.1 haccess₁
  have hm₂ := D.h₂.massInDensity_integrable_of_half_open_access
    huv.2.1 haccess₂
  have hky := D.incomingMassCoefficient_mul_difference_integrable huv
  have hdiff : IntegrableOn
      (fun s => IsBVSolution.massInDensity D.S₁ s v -
        IsBVSolution.massInDensity D.S₂ s v -
        incomingMassCoefficient D s v *
          (D.S₁.m s v - D.S₂.m s v)) (Ioc u v) volume :=
    (hm₁.sub hm₂).sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).1 hky)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
  apply hdiff.congr_fun_ae
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hsne hs
  have hst : (s, v) ∈ triangle D.a D.b :=
    (mem_triangle).2
      ⟨huv.1.trans hs.1.le, lt_of_le_of_ne hs.2 hsne, huv.2.2⟩
  have heq := D.mass_in_difference_linear hst
  linarith only [heq]

end ChristodoulouBV.Uniqueness

end
