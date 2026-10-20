module

public import ChristodoulouBV.Existence.BVStieltjesCanonical
import Mathlib.Tactic

/-!
# Canonical variation bounded by the global section kernel

One common transverse exceptional set works for the countable carrier
exhaustion. Every compact interior section is contained in one chart.
Changing the canonical primitive's basepoint changes only a constant.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Changing the canonical primitive's basepoint adds a constant on
each admissible compact physical section. -/
theorem bv_area_physical_primitive_change_base
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {z A B δ b c t : ℝ}
    (hab : A ≤ B) (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ x ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z x).2 - (areaPhysicalPoint k z x).1)
    (hb : b ∈ Icc A B) (hc : c ∈ Icc A B) (ht : t ∈ Icc A B) :
    areaPhysicalPrimitive k d.scalarRightFields z b t =
      areaPhysicalPrimitive k d.scalarRightFields z c t +
        areaPhysicalPrimitive k d.scalarRightFields z b c := by
  let q := fun x => areaSectionQ k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z x))
  have hi := bv_area_algebra_intervalIntegrable h hD d k hab hδ hs hgap
    (area_section_q_continuous k)
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

private theorem section_contained_in_exhaustion (k : AreaSectionPair) {z A B : ℝ}
    (hab : A ≤ B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) areaSmoothDomain) :
    ∃ n, z ∈ areaTransverseInterval k (areaExhaustionUpper n) (areaExhaustionGap n) ∧
      Icc A B ⊆ areaPhysicalOpenSection k (areaExhaustionUpper n) (areaExhaustionGap n) z := by
  have hA := hs ⟨le_rfl, hab⟩
  have hB := hs ⟨hab, le_rfl⟩
  change areaPhysicalPoint k z A ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} at hA
  change areaPhysicalPoint k z B ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} at hB
  rw [← areaInteriorCutoff_iUnion_eq] at hA hB
  obtain ⟨m, hm⟩ := mem_iUnion.mp hA
  obtain ⟨n, hn⟩ := mem_iUnion.mp hB
  have hm' := areaInteriorCutoff_exhaustion_monotone (le_max_left m n) hm
  have hn' := areaInteriorCutoff_exhaustion_monotone (le_max_right m n) hn
  refine ⟨max m n, ?_, ?_⟩
  · cases hki : k.incoming <;>
      simp only [areaPhysicalPoint, areaInteriorCutoff, areaOpenCutoff, hki,
        Bool.false_eq_true, ite_false, ite_true, mem_inter_iff, mem_ofPred_eq] at hm' hn' <;>
      simp only [areaTransverseInterval, areaTransverseShift, hki, Bool.false_eq_true,
        ite_false, ite_true, zero_add, mem_Ioo] <;>
      constructor <;> linarith only [hm'.1.2.1, hm'.1.2.2, hm'.2,
        hn'.1.2.1, hn'.1.2.2, hn'.2]
  · intro t ht
    cases hki : k.incoming <;>
      simp only [areaPhysicalPoint, areaInteriorCutoff, areaOpenCutoff, hki,
        Bool.false_eq_true, ite_false, ite_true, mem_inter_iff, mem_ofPred_eq] at hm' hn' <;>
      simp only [areaPhysicalOpenSection, hki, Bool.false_eq_true, ite_false,
        ite_true, mem_Ioo] <;>
      constructor <;> linarith only [hm'.1.2.1, hm'.1.2.2, hm'.2,
        hn'.1.2.1, hn'.1.2.2, hn'.2, ht.1, ht.2]

/-- For almost every physical transverse coordinate, every compact
interior canonical section has its variation bounded by the actual
global variation-measure kernel. The basepoint and endpoints are universally quantified. -/
theorem bv_area_canonical_variation_le_global_kernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    ∀ᵐ z : ℝ, ∀ A B b : ℝ, A ≤ B → b ∈ Icc A B →
      MapsTo (areaPhysicalPoint k z) (Icc A B) areaSmoothDomain →
        eVariationOn (areaPhysicalPrimitive k d.scalarRightFields z b) (Ioo A B) ≤
          areaBVGlobalSectionKernel h hD d k z (Ioo A B) := by
  have hall : ∀ᵐ z : ℝ, ∀ n : ℕ,
      z ∈ areaTransverseInterval k (areaExhaustionUpper n) (areaExhaustionGap n) →
      ∃ hb : BoundedVariationOn (areaPhysicalClampedPrimitive k d.rawFields
          (areaExhaustionUpper n) (areaExhaustionGap n) z) univ,
        ∃ c : ℝ, EqOn (areaPhysicalPrimitive k d.scalarRightFields z
            (areaSectionBase k (areaExhaustionUpper n)))
          (fun t => (areaPhysicalClampedPrimitive k d.rawFields
            (areaExhaustionUpper n) (areaExhaustionGap n) z).rightLim t + c)
          (areaPhysicalOpenSection k (areaExhaustionUpper n) (areaExhaustionGap n) z) ∧
        areaBVPhysicalKernel h hD d k (area_exhaustion_gap_pos n)
          (area_exhaustion_gap_lt_upper n) z = hb.vectorMeasure.variation :=
    ae_all_iff.mpr fun n => bv_area_canonical_section_eq_rightLim h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)
  filter_upwards [hall] with z hz A B b hab hb hs
  obtain ⟨n, hzI, hsub⟩ := section_contained_in_exhaustion k hab hs
  obtain ⟨hf, c, he, hk⟩ := hz n hzI
  obtain ⟨hLR, hbase, hdom, _⟩ := area_section_geometry k (area_exhaustion_gap_pos n) hzI
  have hgap (t : ℝ) (ht : t ∈ Icc (areaSectionLower k (areaExhaustionGap n) z)
      (areaSectionUpper k (areaExhaustionUpper n) (areaExhaustionGap n) z)) :
      areaExhaustionGap n ≤ (areaPhysicalPoint k z t).2 -
        (areaPhysicalPoint k z t).1 := by
    cases hki : k.incoming <;>
      simp only [areaSectionLower, areaSectionUpper, areaPhysicalPoint, hki,
        Bool.false_eq_true, ite_false, ite_true, mem_Icc] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  have hsub' : Icc A B ⊆ Icc (areaSectionLower k (areaExhaustionGap n) z)
      (areaSectionUpper k (areaExhaustionUpper n) (areaExhaustionGap n) z) := by
    rw [areaPhysicalOpenSection_eq_Ioo] at hsub
    exact hsub.trans Ioo_subset_Icc_self
  have he' : EqOn (areaPhysicalPrimitive k d.scalarRightFields z b)
      (fun t => (areaPhysicalClampedPrimitive k d.rawFields
        (areaExhaustionUpper n) (areaExhaustionGap n) z).rightLim t +
          (c + areaPhysicalPrimitive k d.scalarRightFields z b
            (areaSectionBase k (areaExhaustionUpper n)))) (Ioo A B) := by
    intro t ht
    rw [bv_area_physical_primitive_change_base h hD d k hLR.le
      (area_exhaustion_gap_pos n) hdom hgap (hsub' hb) hbase
      (hsub' ⟨ht.1.le, ht.2.le⟩), he (hsub ⟨ht.1.le, ht.2.le⟩)]
    exact add_assoc _ _ _
  rw [eVariationOn.eq_of_eqOn he', eVariationOn.add_const,
    ← hf.variation_vectorMeasure_Ioo_right, ← hk]
  rw [areaBVGlobalSectionKernel_apply h hD d k z measurableSet_Ioo]
  apply le_iSup_of_le n
  rw [areaBVOpenSectionKernel_apply h hD d k _ _ z measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Icc_self.trans hsub)]

/-- Every canonical interior increment is bounded by the global kernel
on its half-open section. The upper endpoint atom is retained. -/
theorem bv_area_canonical_increment_le_global_kernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    ∀ᵐ z : ℝ, ∀ x y : ℝ, x ≤ y →
      MapsTo (areaPhysicalPoint k z) (Icc x y) areaSmoothDomain →
        ENNReal.ofReal |areaPhysicalPrimitive k d.scalarRightFields z x y| ≤
          areaBVGlobalSectionKernel h hD d k z (Ioc x y) := by
  have hall : ∀ᵐ z : ℝ, ∀ n : ℕ,
      z ∈ areaTransverseInterval k (areaExhaustionUpper n) (areaExhaustionGap n) →
      ∀ x ∈ areaPhysicalOpenSection k (areaExhaustionUpper n) (areaExhaustionGap n) z,
      ∀ y ∈ areaPhysicalOpenSection k (areaExhaustionUpper n) (areaExhaustionGap n) z,
      x ≤ y →
        edist (areaPhysicalPrimitive k d.scalarRightFields z
            (areaSectionBase k (areaExhaustionUpper n)) y)
          (areaPhysicalPrimitive k d.scalarRightFields z
            (areaSectionBase k (areaExhaustionUpper n)) x) ≤
          areaBVPhysicalKernel h hD d k (area_exhaustion_gap_pos n)
            (area_exhaustion_gap_lt_upper n) z (Ioc x y) :=
    ae_all_iff.mpr fun n => bv_area_primitive_increment_le_kernel h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)
  filter_upwards [hall] with z hz x y hxy hs
  obtain ⟨n, hzI, hsub⟩ := section_contained_in_exhaustion k hxy hs
  obtain ⟨hLR, hbase, hdom, _⟩ := area_section_geometry k (area_exhaustion_gap_pos n) hzI
  have hgap (t : ℝ) (ht : t ∈ Icc (areaSectionLower k (areaExhaustionGap n) z)
      (areaSectionUpper k (areaExhaustionUpper n) (areaExhaustionGap n) z)) :
      areaExhaustionGap n ≤ (areaPhysicalPoint k z t).2 -
        (areaPhysicalPoint k z t).1 := by
    cases hki : k.incoming <;>
      simp only [areaSectionLower, areaSectionUpper, areaPhysicalPoint, hki,
        Bool.false_eq_true, ite_false, ite_true, mem_Icc] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  have hsub' : Icc x y ⊆ Icc (areaSectionLower k (areaExhaustionGap n) z)
      (areaSectionUpper k (areaExhaustionUpper n) (areaExhaustionGap n) z) := by
    rw [areaPhysicalOpenSection_eq_Ioo] at hsub
    exact hsub.trans Ioo_subset_Icc_self
  have he := bv_area_physical_primitive_change_base h hD d k hLR.le
    (area_exhaustion_gap_pos n) hdom hgap hbase
    (hsub' ⟨le_rfl, hxy⟩) (hsub' ⟨hxy, le_rfl⟩)
  have hi := hz n hzI x (hsub ⟨le_rfl, hxy⟩) y (hsub ⟨hxy, le_rfl⟩) hxy
  rw [edist_dist, Real.dist_eq, he, add_sub_cancel_right] at hi
  refine hi.trans ?_
  rw [areaBVGlobalSectionKernel_apply h hD d k z measurableSet_Ioc]
  apply le_iSup_of_le n
  rw [areaBVOpenSectionKernel_apply h hD d k _ _ z measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Icc_self.trans hsub)]

/-- Incoming canonical increments beginning at the initial edge are
bounded by the closed global section kernel. Right continuity at zero
retains the correct trace without inserting an artificial initial atom. -/
theorem bv_area_initial_increment_le_global_kernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (hk : k.incoming = true) :
    ∀ᵐ z : ℝ, ∀ y : ℝ, 0 < y → y < z →
      ENNReal.ofReal |areaPhysicalPrimitive k d.scalarRightFields z 0 y| ≤
        areaBVGlobalSectionKernel h hD d k z (Icc 0 y) := by
  filter_upwards [bv_area_canonical_increment_le_global_kernel h hD d k]
    with z hz y hy hyz
  have hs : MapsTo (areaPhysicalPoint k z) (Icc 0 y) globalDomain := by
    intro t ht
    simpa only [areaPhysicalPoint, hk, ite_true] using
      (show (t, z) ∈ globalDomain from ⟨ht.1, ht.2.trans_lt hyz⟩)
  have hgap (t : ℝ) (ht : t ∈ Icc 0 y) :
      z - y ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1 := by
    simpa only [areaPhysicalPoint, hk, ite_true] using sub_le_sub_left ht.2 z
  have hc := bv_area_primitive_right_continuous_Ico h hD d k hy.le
    (show (0 : ℝ) ∈ Icc 0 y from ⟨le_rfl, hy.le⟩) (sub_pos.mpr hyz) hs hgap
    0 ⟨le_rfl, hy⟩
  have hzero : areaPhysicalPrimitive k d.scalarRightFields z 0 0 = 0 := by
    simp only [areaPhysicalPrimitive, intervalIntegral.integral_same, sub_self]
  have ht : Tendsto (fun x => ENNReal.ofReal
      |areaPhysicalPrimitive k d.scalarRightFields z 0 y -
        areaPhysicalPrimitive k d.scalarRightFields z 0 x|)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal |areaPhysicalPrimitive k d.scalarRightFields z 0 y|)) := by
    have hc' : Tendsto (areaPhysicalPrimitive k d.scalarRightFields z 0)
        (𝓝[>] 0) (𝓝 (areaPhysicalPrimitive k d.scalarRightFields z 0 0)) :=
      hc.mono Ioi_subset_Ici_self
    rw [hzero] at hc'
    simpa only [sub_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_const_nhds.sub hc').abs)
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hy] with x hx
  have hi := hz x y hx.2.le (fun t ht => by
    simpa only [areaPhysicalPoint, hk, ite_true] using
      (show (t, z) ∈ areaSmoothDomain from ⟨hx.1.trans_le ht.1, ht.2.trans_lt hyz⟩))
  have he := bv_area_physical_primitive_change_base h hD d k hy.le
    (sub_pos.mpr hyz) hs hgap ⟨le_rfl, hy.le⟩ ⟨hx.1.le, hx.2.le⟩ ⟨hy.le, le_rfl⟩
  have he' : areaPhysicalPrimitive k d.scalarRightFields z 0 y -
      areaPhysicalPrimitive k d.scalarRightFields z 0 x =
        areaPhysicalPrimitive k d.scalarRightFields z x y := by
    linarith only [he]
  rw [he']
  exact hi.trans (measure_mono (Ioc_subset_Icc_self.trans
    (Icc_subset_Icc hx.1.le le_rfl)))

/-- A closed incoming-section carrier bound for arbitrary nonnegative
endpoints. This includes initial and shifted logarithmic rectangles. -/
theorem bv_area_incoming_increment_le_global_kernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (hk : k.incoming = true) :
    ∀ᵐ z : ℝ, ∀ x y : ℝ, 0 ≤ x → x ≤ y → y < z →
      ENNReal.ofReal |areaPhysicalPrimitive k d.scalarRightFields z x y| ≤
        areaBVGlobalSectionKernel h hD d k z (Icc x y) := by
  filter_upwards [bv_area_initial_increment_le_global_kernel h hD d k hk,
    bv_area_canonical_increment_le_global_kernel h hD d k] with z hinit hinter x y hx hxy hyz
  by_cases hx0 : x = 0
  · subst x
    by_cases hy0 : y = 0
    · subst y
      simp only [areaPhysicalPrimitive, intervalIntegral.integral_same, sub_self, abs_zero,
        ENNReal.ofReal_zero, zero_le]
    · exact hinit y (lt_of_le_of_ne hxy (Ne.symm hy0)) hyz
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hi := hinter x y hxy (fun t ht => by
      simpa only [areaPhysicalPoint, hk, ite_true] using
        (show (t, z) ∈ areaSmoothDomain from ⟨hxpos.trans_le ht.1, ht.2.trans_lt hyz⟩))
    exact hi.trans (measure_mono Ioc_subset_Icc_self)

end ChristodoulouBV

end
