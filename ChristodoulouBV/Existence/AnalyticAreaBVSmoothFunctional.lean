module

public import ChristodoulouBV.Existence.AnalyticAreaBVSmooth
public import ChristodoulouBV.Existence.AnalyticAreaBVChartIntegral
public import ChristodoulouBV.AreaEstimates.ScalarAreaJacobian
import Mathlib.Tactic

/-!
# The smooth functionals used in the liminf inequalities

The pointwise section variation is exactly the smooth analytic area
after transverse integration. Both coordinate factors are retained.
These identities transfer the smooth area bounds to the liminf of the
section functionals.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The first ordered map is the source `(φ,α/λ)` map. -/
theorem area_pair_map_phi_alpha_lam (S : Fields) :
    areaPairMap .phiAlphaLam S = sourcePhiAlphaLamMap S := by
  funext p
  change (S.phi p.1 p.2, S.alpha p.1 p.2 * (S.lam p.1 p.2)⁻¹) =
    (S.phi p.1 p.2, S.alpha p.1 p.2 / S.lam p.1 p.2)
  rw [div_eq_mul_inv]

/-- The second ordered map is the source `(λ,φ)` map. -/
theorem area_pair_map_lam_phi (S : Fields) : areaPairMap .lamPhi S = sourceLamPhiMap S := rfl

/-- The third ordered map is the source `(φ,β/ν)` map. -/
theorem area_pair_map_phi_beta_nu (S : Fields) :
    areaPairMap .phiBetaNu S = sourcePhiBetaNuMap S := by
  funext p
  change (S.phi p.1 p.2, S.beta p.1 p.2 * (S.nu p.1 p.2)⁻¹) =
    (S.phi p.1 p.2, S.beta p.1 p.2 / S.nu p.1 p.2)
  rw [div_eq_mul_inv]

/-- The fourth ordered map is the source `(ν,φ)` map. -/
theorem area_pair_map_nu_phi (S : Fields) : areaPairMap .nuPhi S = sourceNuPhiMap S := rfl

/-- Removing the initial characteristic from an open cutoff does not
change smooth analytic area, including on an arbitrary subset. -/
theorem smooth_analytic_area_open_eq_interior (F : ℝ × ℝ → ℝ × ℝ)
    (E : Set (ℝ × ℝ)) (δ a : ℝ) :
    smoothAnalyticArea F (E ∩ areaOpenCutoff δ a) =
      smoothAnalyticArea F (E ∩ areaInteriorCutoff δ a) := by
  apply measure_congr
  have hz : ∀ᵐ p ∂smoothAnalyticArea F, p.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using smooth_analytic_area_initial_edge F
  filter_upwards [hz] with p hp
  apply propext
  constructor
  · rintro ⟨he, ho⟩
    exact ⟨he, ho, lt_of_le_of_ne ho.1 hp.symm⟩
  · rintro ⟨he, ho, _⟩
    exact ⟨he, ho⟩

/-- On a smooth field each area-section functional is the integral of
the absolute Jacobian on its physical open interval. -/
theorem SmoothSolutionBounds.area_section_variation_eq_jacobian_integral
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    areaSectionVariation k S a δ y = ∫⁻ t in areaOpenSection k a δ y,
      ENNReal.ofReal |(fderiv ℝ (areaPairMap k S) (areaBVChartPoint k a δ (y, t))).det| := by
  let z := areaTransverseShift k δ + (a - δ) * (y : ℝ)
  have hL : 0 < a - δ := sub_pos.mpr hδa
  have hz : z ∈ areaTransverseInterval k a δ := by
    change areaTransverseShift k δ < z ∧ z < areaTransverseShift k δ + (a - δ)
    dsimp only [z]
    constructor <;> nlinarith only [hL, y.property.1, y.property.2]
  obtain ⟨hab, hb, hs, hsI⟩ := area_section_geometry k hδ hz
  have hv := h.area_physical_variation_eq_jacobian_integral k hab.le hb hs hsI
  have he : areaSectionVariation k S a δ y =
      eVariationOn (areaPhysicalPrimitive k S z (areaSectionBase k a))
        (Icc (areaSectionLower k δ z) (areaSectionUpper k a δ z)) := by
    cases hki : k.incoming <;>
      simp only [areaSectionVariation, areaSectionLower, areaSectionUpper, areaSectionBase,
        areaTransverseShift, hki, Bool.false_eq_true, ite_false, ite_true, z, zero_add,
        add_comm δ, add_sub_cancel_right]
  rw [he, hv]
  have hj : Ioo (areaSectionLower k δ z) (areaSectionUpper k a δ z) =
      areaOpenSection k a δ y := by
    cases hki : k.incoming <;>
      simp only [areaSectionLower, areaSectionUpper, areaOpenSection, areaTransverseShift,
        hki, Bool.false_eq_true, ite_false, ite_true, z, zero_add, add_comm δ,
        add_sub_cancel_right]
  rw [hj]
  apply lintegral_congr
  intro t
  congr 3
  cases hki : k.incoming <;>
    simp only [areaBVChartPoint, areaTransverseShift, hki,
      Bool.false_eq_true, ite_false, ite_true, z, zero_add]

/-- The corrected smooth weighted pointwise functional is exactly the
smooth analytic area on the open cutoff, for each of the four pairs. -/
theorem smooth_area_coordinate_formula
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    ENNReal.ofReal (a - δ) * ∫⁻ y : Ioo (0 : ℝ) 1,
      areaSectionChartVariation k S a δ y =
        smoothAnalyticArea (areaPairMap k S) (areaOpenCutoff δ a) := by
  have ho := smooth_analytic_area_open_eq_interior (areaPairMap k S) univ δ a
  simp only [univ_inter] at ho
  rw [ho]
  have hf := h.analytic_area_physical_formula k (a := a) hδ (E := univ) MeasurableSet.univ
  rw [area_cutoff_chart_lintegral k hδa] at hf
  simp only [univ_inter, indicator_univ] at hf
  rw [hf]
  apply congrArg (fun v : ℝ≥0∞ => ENNReal.ofReal (a - δ) * v)
  apply lintegral_congr
  intro y
  rw [area_section_chart_variation_eq k S hδ hδa,
    h.area_section_variation_eq_jacobian_integral k hδ hδa y]

end ChristodoulouBV

end
