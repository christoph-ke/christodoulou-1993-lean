module

public import ChristodoulouBV.Existence.AreaSectionLimitRectangle
import Mathlib.Tactic

/-!
# Uniform transverse distances of the raw area fields

The constants below come directly from the mixed primitive majorant
`9/δ`. They apply to either ordering of the endpoints and are uniform
over every off-axis section.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Uniform transverse distances for the two raw outgoing fields. -/
theorem raw_outgoing_fields_transverse_dist
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {u w v δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hgu : δ ≤ v - u) (hgw : δ ≤ v - w) :
    dist (d.rawFields.lam u v) (d.rawFields.lam w v) ≤ (9 / δ) * dist u w ∧
    dist (d.rawFields.alpha u v) (d.rawFields.alpha w v) ≤
      ((9 / δ) * (6 * D.toReal + C)) * dist u w := by
  have hmem (t : ℝ) (ht : t ∈ Icc (min u w) (max u w)) :
      (t, v) ∈ globalDomain ∧ δ ≤ v - t := by
    have hlo : 0 ≤ t := (le_min hu hw).trans ht.1
    have hhi : t ≤ v - δ := ht.2.trans (max_le (by linarith only [hgu])
      (by linarith only [hgw]))
    exact ⟨⟨hlo, by linarith only [hhi, hδ]⟩, by linarith only [hhi]⟩
  have hseg (x y : ℝ) (hx : x ∈ Icc (min u w) (max u w))
      (hy : y ∈ Icc (min u w) (max u w)) (_hxy : x ≤ y) :
      inSeg v x y ⊆ globalDomain := by
    rintro ⟨t, s⟩ ⟨ht, rfl⟩
    exact (hmem t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩).1
  have hbound (t : ℝ) (ht : t ∈ Icc (min u w) (max u w)) :
      |IsBVSolution.radiusCoeff d.rawFields t v| ≤ 9 / δ :=
    d.raw_radius_coeff_bound h (hmem t ht).1 hδ (hmem t ht).2
  have huI : u ∈ Icc (min u w) (max u w) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hwI : w ∈ Icc (min u w) (max u w) := ⟨min_le_right _ _, le_max_right _ _⟩
  constructor
  · exact dist_le_of_interval_primitives
      (fun x y hx hy hxy => (raw_expansion_primitive_limit h d).1 v x y hxy
        (hseg x y hx hy hxy)) hbound huI hwI
  · apply dist_le_of_interval_primitives
      (fun x y hx hy hxy => (raw_alpha_beta_transport_limit h d).1 v x y hxy
        (hseg x y hx hy hxy)) ?_ huI hwI
    intro t ht
    rw [abs_mul]
    exact mul_le_mul (hbound t ht) (d.scalar_amplitude h (hmem t ht).1)
      (abs_nonneg _) (div_nonneg (by norm_num) hδ.le)

/-- Uniform transverse distances for the two raw incoming fields. -/
theorem raw_incoming_fields_transverse_dist
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {u v w δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u)
    (hgv : δ ≤ v - u) (hgw : δ ≤ w - u) :
    dist (d.rawFields.nu u v) (d.rawFields.nu u w) ≤ (9 / δ) * dist v w ∧
    dist (d.rawFields.beta u v) (d.rawFields.beta u w) ≤
      ((9 / δ) * (6 * D.toReal + C)) * dist v w := by
  have hmem (t : ℝ) (ht : t ∈ Icc (min v w) (max v w)) :
      (u, t) ∈ globalDomain ∧ δ ≤ t - u := by
    have hlo : u + δ ≤ t := (le_min (by linarith only [hgv])
      (by linarith only [hgw])).trans ht.1
    exact ⟨⟨hu, by linarith only [hlo, hδ]⟩, by linarith only [hlo]⟩
  have hseg (x y : ℝ) (hx : x ∈ Icc (min v w) (max v w))
      (hy : y ∈ Icc (min v w) (max v w)) (_hxy : x ≤ y) :
      outSeg u x y ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact (hmem t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩).1
  have hbound (t : ℝ) (ht : t ∈ Icc (min v w) (max v w)) :
      |IsBVSolution.radiusCoeff d.rawFields u t| ≤ 9 / δ :=
    d.raw_radius_coeff_bound h (hmem t ht).1 hδ (hmem t ht).2
  have hvI : v ∈ Icc (min v w) (max v w) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hwI : w ∈ Icc (min v w) (max v w) := ⟨min_le_right _ _, le_max_right _ _⟩
  constructor
  · exact dist_le_of_interval_primitives
      (fun x y hx hy hxy => (raw_expansion_primitive_limit h d).2 u x y hxy
        (hseg x y hx hy hxy)) hbound hvI hwI
  · apply dist_le_of_interval_primitives
      (fun x y hx hy hxy => (raw_alpha_beta_transport_limit h d).2 u x y hxy
        (hseg x y hx hy hxy)) ?_ hvI hwI
    intro t ht
    rw [abs_mul]
    exact mul_le_mul (hbound t ht) (d.scalar_amplitude h (hmem t ht).1)
      (abs_nonneg _) (div_nonneg (by norm_num) hδ.le)

end ChristodoulouBV

end
