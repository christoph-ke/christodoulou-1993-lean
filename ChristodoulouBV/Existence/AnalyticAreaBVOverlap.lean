module

public import ChristodoulouBV.Existence.AnalyticAreaBVPhysical
public import ChristodoulouBV.Existence.AnalyticAreaBVPrimitive
import Mathlib.Tactic

/-!
# Agreement of the physical section measures on overlaps

Cutoff-dependent constant extension is used only locally. On an overlap
the unclamped primitives differ by their anchoring constant, so their
variation measures agree on the common open section.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The open section at a fixed physical transverse coordinate. -/
@[expose] def areaPhysicalOpenSection (k : AreaSectionPair) (a δ z : ℝ) : Set ℝ :=
  if k.incoming then Ioo 0 (z - δ) else Ioo (z + δ) a

/-- Two clamped outgoing primitives differ by a constant on their
common open section. The constant is the ordinary basepoint change. -/
theorem area_physical_clamped_outgoing_overlap
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) (hki : k.incoming = false)
    {a δ a' δ' z : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (hz : z ∈ areaTransverseInterval k a δ)
    (hz' : z ∈ areaTransverseInterval k a' δ') :
    EqOn (areaPhysicalClampedPrimitive k d.rawFields a δ z)
      (fun t => areaPhysicalClampedPrimitive k d.rawFields a' δ' z t +
        areaPhysicalPrimitive k d.rawFields z a a')
      (Ioo (max (z + δ) (z + δ')) (min a a')) := by
  simp only [areaTransverseInterval, areaTransverseShift, hki,
    Bool.false_eq_true, ite_false, zero_add, mem_Ioo] at hz hz'
  let A := min (z + δ) (z + δ')
  let B := max a a'
  have hza : z + δ < a := by linarith only [hz.2]
  have hza' : z + δ' < a' := by linarith only [hz'.2]
  have hAa : A ≤ a := (min_le_left _ _).trans hza.le
  have hAa' : A ≤ a' := (min_le_right _ _).trans hza'.le
  have hBA : A ≤ B := hAa.trans (le_max_left _ _)
  have hδm : 0 < min δ δ' := lt_min hδ hδ'
  have hAgap : z + min δ δ' ≤ A := by
    apply le_min
    · linarith only [min_le_left δ δ']
    · linarith only [min_le_right δ δ']
  have hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain := by
    intro t ht
    simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
    exact ⟨hz.1.le, by linarith only [ht.1, hAgap, hδm]⟩
  have hgap : ∀ t ∈ Icc A B,
      min δ δ' ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1 := by
    intro t ht
    simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
    linarith only [ht.1, hAgap]
  intro t ht
  have htA : A ≤ t := (min_le_left _ _).trans
    ((le_max_left _ _).trans ht.1.le)
  have htB : t ≤ B := ht.2.le.trans ((min_le_left _ _).trans (le_max_left _ _))
  have hbase := area_physical_primitive_change_base h d k hBA hδm hs hgap
    ⟨hAa, le_max_left _ _⟩ ⟨hAa', le_max_right _ _⟩ ⟨htA, htB⟩
  have hlt : z + δ < t := (le_max_left _ _).trans_lt ht.1
  have hlt' : z + δ' < t := (le_max_right _ _).trans_lt ht.1
  have hta : t < a := ht.2.trans_le (min_le_left _ _)
  have hta' : t < a' := ht.2.trans_le (min_le_right _ _)
  simp only [areaPhysicalClampedPrimitive, hki, Bool.false_eq_true, ite_false,
    min_eq_right hta.le, min_eq_right hta'.le, max_eq_right hlt.le,
    max_eq_right hlt'.le]
  exact hbase

/-- The two physical variation kernels agree on the intersection of
their open sections whenever both transverse coordinates are admissible. -/
theorem areaBVPhysicalKernel_restrict_overlap
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ a' δ' z : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hδ' : 0 < δ') (hδa' : δ' < a')
    (hz : z ∈ areaTransverseInterval k a δ)
    (hz' : z ∈ areaTransverseInterval k a' δ') :
    (areaBVPhysicalKernel h hD d k hδ hδa z).restrict
        (areaPhysicalOpenSection k a δ z ∩ areaPhysicalOpenSection k a' δ' z) =
      (areaBVPhysicalKernel h hD d k hδ' hδa' z).restrict
        (areaPhysicalOpenSection k a δ z ∩ areaPhysicalOpenSection k a' δ' z) := by
  obtain ⟨hf, he⟩ := areaBVPhysicalKernel_eq_variation h hD d k hδ hδa hz
  obtain ⟨hg, he'⟩ := areaBVPhysicalKernel_eq_variation h hD d k hδ' hδa' hz'
  rw [he, he']
  cases hki : k.incoming with
  | false =>
    simp only [areaPhysicalOpenSection, hki, Bool.false_eq_true, ite_false, Ioo_inter_Ioo]
    exact variation_measure_restrict_Ioo_eq_of_eqOn_add_const hf hg
      (area_physical_clamped_outgoing_overlap h d k hki hδ hδ' hz hz')
  | true =>
    simp only [areaPhysicalOpenSection, hki, ite_true, Ioo_inter_Ioo, max_self]
    apply variation_measure_restrict_Ioo_eq_of_eqOn_add_const hf hg (c := 0)
    intro t ht
    have hta : t ≤ z - δ := ht.2.le.trans (min_le_left _ _)
    have hta' : t ≤ z - δ' := ht.2.le.trans (min_le_right _ _)
    simp only [areaPhysicalClampedPrimitive, hki, ite_true, min_eq_right hta,
      min_eq_right hta', max_eq_right ht.1.le, add_zero]

end ChristodoulouBV

end
