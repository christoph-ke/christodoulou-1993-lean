module

public import ChristodoulouBV.Existence.AnalyticAreaBVCharts
import Mathlib.Tactic

/-!
# Coverage of the source cutoffs by the two unit charts

Each open unit square maps onto the strict interior cutoff. The closed
source cutoff differs only on its three coordinate boundary lines.
No assertion that those lines have zero BV area is made.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The open parameter square for the two source area charts. -/
@[expose] def areaUnitSquare : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

/-- The three boundary lines omitted by the open unit charts. -/
@[expose] def areaCutoffBoundary (δ a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 = 0 ∨ p.2 = a ∨ p.2 - p.1 = δ}

/-- Each literal unit-square coordinate map covers exactly the strict
interior of the corresponding off-axis cutoff. -/
theorem areaUnitMap_image (k : AreaSectionPair) {a δ : ℝ}
    (_hδ : 0 < δ) (hδa : δ < a) :
    areaUnitMap k a δ '' areaUnitSquare = areaInteriorCutoff δ a := by
  let L := a - δ
  have hL : 0 < L := sub_pos.mpr hδa
  apply Subset.antisymm
  · rintro p ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    cases hki : k.incoming with
    | false =>
      simp only [areaUnitMap, hki, Bool.false_eq_true, ite_false]
      have hu : 0 < L * y := mul_pos hL hy.1
      have hv : 0 < L * (1 - y) * x := mul_pos (mul_pos hL (sub_pos.mpr hy.2)) hx.1
      have hg : 0 < L * (1 - y) * (1 - x) :=
        mul_pos (mul_pos hL (sub_pos.mpr hy.2)) (sub_pos.mpr hx.2)
      change ((0 ≤ L * y ∧ a - L * (1 - y) * x < a ∧
        δ < a - L * (1 - y) * x - L * y) ∧ 0 < L * y)
      refine ⟨⟨hu.le, by linarith only [hv], ?_⟩, hu⟩
      dsimp only [L] at hg ⊢
      nlinarith only [hg]
    | true =>
      simp only [areaUnitMap, hki, ite_true]
      have hu : 0 < L * x * y := mul_pos (mul_pos hL hx.1) hy.1
      have hv : L * y < L := (mul_lt_mul_of_pos_left hy.2 hL).trans_eq (mul_one L)
      have hg : 0 < L * y * (1 - x) := mul_pos (mul_pos hL hy.1) (sub_pos.mpr hx.2)
      change ((0 ≤ L * x * y ∧ δ + L * y < a ∧
        δ < δ + L * y - L * x * y) ∧ 0 < L * x * y)
      refine ⟨⟨hu.le, ?_, by nlinarith only [hg]⟩, hu⟩
      dsimp only [L] at hv ⊢
      linarith only [hv]
  · intro p hp
    obtain ⟨⟨hu, hva, hgap⟩, hu'⟩ := hp
    change 0 < p.1 at hu'
    cases hki : k.incoming with
    | false =>
      have hden : 0 < L - p.1 := by dsimp only [L]; linarith only [hgap, hva]
      have hy0 : 0 < p.1 / L := div_pos hu' hL
      have hy1 : p.1 / L < 1 := (div_lt_one hL).mpr (by linarith only [hden])
      have hx0 : 0 < (a - p.2) / (L - p.1) := div_pos (sub_pos.mpr hva) hden
      have hx1 : (a - p.2) / (L - p.1) < 1 := (div_lt_one hden).mpr (by
        dsimp only [L]
        linarith only [hgap])
      refine ⟨((a - p.2) / (L - p.1), p.1 / L), ⟨⟨hx0, hx1⟩, hy0, hy1⟩, ?_⟩
      simp only [areaUnitMap, hki, Bool.false_eq_true, ite_false]
      apply Prod.ext
      · change L * (p.1 / L) = p.1
        exact mul_div_cancel₀ _ hL.ne'
      · change a - L * (1 - p.1 / L) * ((a - p.2) / (L - p.1)) = p.2
        have he : L * (1 - p.1 / L) = L - p.1 := by
          field_simp
        rw [he, mul_div_cancel₀ _ hden.ne']
        ring
    | true =>
      have hden : 0 < p.2 - δ := by linarith only [hgap, hu']
      have hy0 : 0 < (p.2 - δ) / L := div_pos hden hL
      have hy1 : (p.2 - δ) / L < 1 := (div_lt_one hL).mpr (by
        dsimp only [L]
        linarith only [hva])
      have hx0 : 0 < p.1 / (p.2 - δ) := div_pos hu' hden
      have hx1 : p.1 / (p.2 - δ) < 1 := (div_lt_one hden).mpr (by linarith only [hgap])
      refine ⟨(p.1 / (p.2 - δ), (p.2 - δ) / L), ⟨⟨hx0, hx1⟩, hy0, hy1⟩, ?_⟩
      simp only [areaUnitMap, hki, ite_true]
      apply Prod.ext
      · change L * (p.1 / (p.2 - δ)) * ((p.2 - δ) / L) = p.1
        field_simp
      · change δ + L * ((p.2 - δ) / L) = p.2
        rw [mul_div_cancel₀ _ hL.ne']
        ring

/-- The closed source cutoff is covered by either unit chart together
with its three explicitly named boundary lines. -/
theorem areaClosedCutoff_subset_chart_union_boundary (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaClosedCutoff δ a ⊆ areaUnitMap k a δ '' areaUnitSquare ∪ areaCutoffBoundary δ a := by
  rw [areaUnitMap_image k hδ hδa]
  intro p hp
  by_cases hu : p.1 = 0
  · exact Or.inr (Or.inl hu)
  by_cases hv : p.2 = a
  · exact Or.inr (Or.inr (Or.inl hv))
  by_cases hg : p.2 - p.1 = δ
  · exact Or.inr (Or.inr (Or.inr hg))
  exact Or.inl ⟨⟨hp.1.1, lt_of_le_of_ne hp.2.1 hv,
    lt_of_le_of_ne hp.2.2 (fun he => hg he.symm)⟩,
    lt_of_le_of_ne hp.1.1 (fun he => hu he.symm)⟩

/-- The source truncation geometry: the radius is bounded below by
`δ/3`, each chart covers the cutoff up to its boundary, and both
absolute Jacobians have the corrected coordinate weights. -/
theorem s6_truncation
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    (∀ p ∈ areaClosedCutoff δ a, δ / 3 ≤ d.rawFields.r p.1 p.2) ∧
      areaClosedCutoff δ a ⊆ areaUnitMap k a δ '' areaUnitSquare ∪ areaCutoffBoundary δ a ∧
      ∀ p ∈ areaUnitSquare, |(fderiv ℝ (areaUnitMap k a δ) p).det| =
        if k.incoming then (a - δ) ^ 2 * p.2 else (a - δ) ^ 2 * (1 - p.2) := by
  refine ⟨?_, areaClosedCutoff_subset_chart_union_boundary k hδ hδa, ?_⟩
  · intro p hp
    exact (div_le_div_of_nonneg_right hp.2.2 (by norm_num : (0 : ℝ) ≤ 3)).trans
      (d.radius_lower h hp.1)
  · intro p hp
    exact areaUnitMap_abs_det k a δ p.1 hp.2

end ChristodoulouBV

end
