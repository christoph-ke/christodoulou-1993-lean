module

public import ChristodoulouBV.Existence.AreaSectionLimit
public import ChristodoulouBV.Existence.AnalyticAreaBVLocality
import Mathlib.Tactic

/-!
# Independence of the physical primitive's basepoint

The raw section integrand is integrable on every compact admissible
off-axis section. Changing its anchoring endpoint therefore adds a
constant, which does not affect its local variation measure.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The ordinary part of the raw physical Stieltjes primitive is
integrable on every compact off-axis null section. -/
theorem raw_area_section_q_intervalIntegrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {z A B δ : ℝ} (hab : A ≤ B) (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ t ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1) :
    IntervalIntegrable (fun t => areaSectionQ k
      (areaSectionCoefficients d.rawFields (areaPhysicalPoint k z t))) volume A B := by
  have hm := raw_area_algebra_aestronglyMeasurable h d measurableSet_Icc
    ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).continuousOn hs (area_section_q_continuous k)
  obtain ⟨M, _, hM⟩ := area_section_uniform_bound_with_limit h d hδ
    (area_section_q_continuous k)
  apply (intervalIntegrable_const (a := A) (b := B) (c := M)).mono_fun'
    (hm.mono_set (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Icc A B := by
    rw [uIoc_of_le hab] at ht
    exact Ioc_subset_Icc_self ht
  simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using hM _ (hs ht') (hgap t ht')

/-- The physical integration-by-parts primitive obeys the basepoint
change identity on an admissible compact section. -/
theorem area_physical_primitive_change_base
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {z A B δ b c t : ℝ} (hab : A ≤ B) (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ x ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z x).2 - (areaPhysicalPoint k z x).1)
    (hb : b ∈ Icc A B) (hc : c ∈ Icc A B) (ht : t ∈ Icc A B) :
    areaPhysicalPrimitive k d.rawFields z b t =
      areaPhysicalPrimitive k d.rawFields z c t +
        areaPhysicalPrimitive k d.rawFields z b c := by
  let q := fun x => areaSectionQ k
    (areaSectionCoefficients d.rawFields (areaPhysicalPoint k z x))
  have hi := raw_area_section_q_intervalIntegrable h d k hab hδ hs hgap
  have hsub (x y : ℝ) (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
      IntervalIntegrable q volume x y := by
    apply hi.mono_set
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc hx hy
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hsub b c hb hc)
    (hsub c t hc ht)
  simp only [areaPhysicalPrimitive]
  change _ - ∫ x in b..t, q x =
    (_ - ∫ x in c..t, q x) + (_ - ∫ x in b..c, q x)
  rw [← hsum]
  ring

end ChristodoulouBV

end
