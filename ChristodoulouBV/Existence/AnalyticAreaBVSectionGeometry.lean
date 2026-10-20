module

public import ChristodoulouBV.Existence.AnalyticAreaBVOverlap
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothJets
import Mathlib.Tactic

/-!
# Compact physical sections of an area cutoff

The endpoints and anchoring point are kept in physical coordinates.
Every closed section stays in the global domain, and every open section
stays in its strict interior.
-/

public section

open Set

namespace ChristodoulouBV

/-- Lower endpoint of a physical cutoff section. -/
@[expose] def areaSectionLower (k : AreaSectionPair) (δ z : ℝ) : ℝ :=
  if k.incoming then 0 else z + δ

/-- Upper endpoint of a physical cutoff section. -/
@[expose] def areaSectionUpper (k : AreaSectionPair) (a δ z : ℝ) : ℝ :=
  if k.incoming then z - δ else a

/-- The anchoring endpoint in the physical primitive. -/
@[expose] def areaSectionBase (k : AreaSectionPair) (a : ℝ) : ℝ :=
  if k.incoming then 0 else a

/-- The physical open section is the open interval between its endpoints. -/
theorem areaPhysicalOpenSection_eq_Ioo (k : AreaSectionPair) (a δ z : ℝ) :
    areaPhysicalOpenSection k a δ z =
      Ioo (areaSectionLower k δ z) (areaSectionUpper k a δ z) := by
  cases hki : k.incoming <;>
    simp only [areaPhysicalOpenSection, areaSectionLower, areaSectionUpper, hki,
      Bool.false_eq_true, ite_false, ite_true]

/-- Each admissible physical section is a nondegenerate compact
off-axis interval, with its basepoint at one of the two endpoints. -/
theorem area_section_geometry (k : AreaSectionPair) {a δ z : ℝ} (hδ : 0 < δ)
    (hz : z ∈ areaTransverseInterval k a δ) :
    areaSectionLower k δ z < areaSectionUpper k a δ z ∧
      areaSectionBase k a ∈ Icc (areaSectionLower k δ z) (areaSectionUpper k a δ z) ∧
      MapsTo (areaPhysicalPoint k z)
        (Icc (areaSectionLower k δ z) (areaSectionUpper k a δ z)) globalDomain ∧
      MapsTo (areaPhysicalPoint k z)
        (Ioo (areaSectionLower k δ z) (areaSectionUpper k a δ z)) areaSmoothDomain := by
  cases hki : k.incoming with
  | false =>
    simp only [areaTransverseInterval, areaTransverseShift, hki, Bool.false_eq_true,
      ite_false, zero_add, mem_Ioo] at hz
    simp only [areaSectionLower, areaSectionUpper, areaSectionBase, hki,
      Bool.false_eq_true, ite_false]
    have hza : z + δ < a := by linarith only [hz.2]
    refine ⟨hza, ⟨hza.le, le_rfl⟩, ?_, ?_⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      exact ⟨hz.1.le, by linarith only [ht.1, hδ]⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      exact ⟨hz.1, by linarith only [ht.1, hδ]⟩
  | true =>
    simp only [areaTransverseInterval, areaTransverseShift, hki, ite_true, mem_Ioo] at hz
    simp only [areaSectionLower, areaSectionUpper, areaSectionBase, hki, ite_true]
    have hzw : 0 < z - δ := sub_pos.mpr hz.1
    refine ⟨hzw, ⟨le_rfl, hzw.le⟩, ?_, ?_⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, ite_true]
      exact ⟨ht.1, by linarith only [ht.2, hδ]⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, ite_true]
      exact ⟨ht.1, by linarith only [ht.2, hδ]⟩

/-- The clamped primitive agrees with its unclamped physical primitive
on the whole closed section. -/
theorem area_physical_clamped_eq_on_section (k : AreaSectionPair) (S : Fields)
    (a δ z : ℝ) :
    EqOn (areaPhysicalClampedPrimitive k S a δ z)
      (areaPhysicalPrimitive k S z (areaSectionBase k a))
      (Icc (areaSectionLower k δ z) (areaSectionUpper k a δ z)) := by
  intro t ht
  cases hki : k.incoming with
  | false =>
    simp only [areaSectionLower, areaSectionUpper, hki, Bool.false_eq_true, ite_false] at ht
    simp only [areaPhysicalClampedPrimitive, areaSectionBase, hki, Bool.false_eq_true,
      ite_false, min_eq_right ht.2, max_eq_right ht.1]
  | true =>
    simp only [areaSectionLower, areaSectionUpper, hki, ite_true] at ht
    simp only [areaPhysicalClampedPrimitive, areaSectionBase, hki, ite_true,
      min_eq_right ht.2, max_eq_right ht.1]

end ChristodoulouBV

end
