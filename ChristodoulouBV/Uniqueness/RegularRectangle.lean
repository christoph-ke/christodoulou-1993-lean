module

public import ChristodoulouBV.Uniqueness.RegularRectangleCoefficients
public import ChristodoulouBV.Uniqueness.RegularRectangleComparison
public import ChristodoulouBV.Uniqueness.RegularRectangleVolterraBound

/-!
# Characteristic comparison on a regular rectangle

Equal primary fields on a past face identify its primitive densities almost
everywhere, without choosing values at exceptional points.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Equality of the two primary fields on the past outgoing face identifies
its two primitive densities almost everywhere. -/
theorem regular_rectangle_outgoing_boundary_data
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hface : ∀ v ∈ Icc v₀ v₁,
      S₁.r u₀ v = S₂.r u₀ v ∧ S₁.phi u₀ v = S₂.phi u₀ v) :
    ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v := by
  have hs₁ := regularRectangle_outSeg_subset hR₁ ⟨le_rfl, hu⟩
  have hs₂ := regularRectangle_outSeg_subset hR₂ ⟨le_rfl, hu⟩
  have hlam := IntervalPrimitive.same_primitive_ae_of_eqOn hv
    (fun x y h₀ hxy hy =>
      h₁.solution.radius_out u₀ x y hxy
        ((outSeg_subsegment h₀ hxy hy).trans hs₁))
    (fun x y h₀ hxy hy =>
      h₂.solution.radius_out u₀ x y hxy
        ((outSeg_subsegment h₀ hxy hy).trans hs₂))
    (fun v hv => (hface v hv).1)
  have halpha := IntervalPrimitive.same_primitive_ae_of_eqOn hv
    (fun x y h₀ hxy hy =>
      h₁.solution.scalar_radius_out u₀ x y hxy
        ((outSeg_subsegment h₀ hxy hy).trans hs₁))
    (fun x y h₀ hxy hy =>
      h₂.solution.scalar_radius_out u₀ x y hxy
        ((outSeg_subsegment h₀ hxy hy).trans hs₂))
    (fun v hv => by
      obtain ⟨hr, hphi⟩ := hface v hv
      rw [hr, hphi])
  filter_upwards [hlam, halpha] with v hLam hAlpha hv
  exact ⟨hLam hv, hAlpha hv⟩

/-- Equality of the two primary fields on the past incoming face identifies
its two primitive densities almost everywhere. -/
theorem regular_rectangle_incoming_boundary_data
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hface : ∀ u ∈ Icc u₀ u₁,
      S₁.r u v₀ = S₂.r u v₀ ∧ S₁.phi u v₀ = S₂.phi u v₀) :
    ∀ᵐ u ∂volume, u ∈ Icc u₀ u₁ →
      S₁.nu u v₀ = S₂.nu u v₀ ∧
      S₁.beta u v₀ = S₂.beta u v₀ := by
  have hs₁ := regularRectangle_inSeg_subset hR₁ ⟨le_rfl, hv⟩
  have hs₂ := regularRectangle_inSeg_subset hR₂ ⟨le_rfl, hv⟩
  have hnu := IntervalPrimitive.same_primitive_ae_of_eqOn hu
    (fun x y h₀ hxy hy =>
      h₁.solution.radius_in v₀ x y hxy
        ((inSeg_subsegment h₀ hxy hy).trans hs₁))
    (fun x y h₀ hxy hy =>
      h₂.solution.radius_in v₀ x y hxy
        ((inSeg_subsegment h₀ hxy hy).trans hs₂))
    (fun u hu => (hface u hu).1)
  have hbeta := IntervalPrimitive.same_primitive_ae_of_eqOn hu
    (fun x y h₀ hxy hy =>
      h₁.solution.scalar_radius_in v₀ x y hxy
        ((inSeg_subsegment h₀ hxy hy).trans hs₁))
    (fun x y h₀ hxy hy =>
      h₂.solution.scalar_radius_in v₀ x y hxy
        ((inSeg_subsegment h₀ hxy hy).trans hs₂))
    (fun u hu => by
      obtain ⟨hr, hphi⟩ := hface u hu
      rw [hr, hphi])
  filter_upwards [hnu, hbeta] with u hNu hBeta hu
  exact ⟨hNu hu, hBeta hu⟩

/-- Equal primary fields on both past faces give the conditional Volterra
boundary data and the common lower-corner values. -/
theorem regular_rectangle_boundary_data
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hout : ∀ v ∈ Icc v₀ v₁,
      S₁.r u₀ v = S₂.r u₀ v ∧
      S₁.phi u₀ v = S₂.phi u₀ v ∧
      S₁.m u₀ v = S₂.m u₀ v)
    (hin : ∀ u ∈ Icc u₀ u₁,
      S₁.r u v₀ = S₂.r u v₀ ∧
      S₁.phi u v₀ = S₂.phi u v₀ ∧
      S₁.m u v₀ = S₂.m u v₀) :
    (S₁.r u₀ v₀ = S₂.r u₀ v₀ ∧
      S₁.r u₀ v₀ * S₁.phi u₀ v₀ =
        S₂.r u₀ v₀ * S₂.phi u₀ v₀ ∧
      S₁.m u₀ v₀ = S₂.m u₀ v₀) ∧
    (∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v) ∧
    (∀ᵐ u ∂volume, u ∈ Icc u₀ u₁ →
      S₁.nu u v₀ = S₂.nu u v₀ ∧
      S₁.beta u v₀ = S₂.beta u v₀) := by
  have hcorner := hout v₀ ⟨le_rfl, hv⟩
  refine ⟨⟨hcorner.1, ?_, hcorner.2.2⟩, ?_, ?_⟩
  · rw [hcorner.1, hcorner.2.1]
  · exact regular_rectangle_outgoing_boundary_data h₁ h₂ hu hv hR₁ hR₂
      (fun v hv => ⟨(hout v hv).1, (hout v hv).2.1⟩)
  · exact regular_rectangle_incoming_boundary_data h₁ h₂ hu hv hR₁ hR₂
      (fun u hu => ⟨(hin u hu).1, (hin u hu).2.1⟩)

/-- Characteristic uniqueness on a nondegenerate regular rectangle: common
corner radius, scalar-radius, and mass, together with the source-level a.e.
past-face densities, determine the three primary fields everywhere. -/
theorem regular_rectangle_unique
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hr₀ : S₁.r u₀ v₀ = S₂.r u₀ v₀)
    (hψ₀ : S₁.r u₀ v₀ * S₁.phi u₀ v₀ =
      S₂.r u₀ v₀ * S₂.phi u₀ v₀)
    (hm₀ : S₁.m u₀ v₀ = S₂.m u₀ v₀)
    (hV : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v)
    (hU : ∀ᵐ u ∂volume, u ∈ Icc u₀ u₁ →
      S₁.nu u v₀ = S₂.nu u v₀ ∧
      S₁.beta u v₀ = S₂.beta u v₀) :
    ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      S₁.r u v = S₂.r u v ∧
      S₁.phi u v = S₂.phi u v ∧
      S₁.m u v = S₂.m u v := by
  have hsep : u₁ < v₀ := by
    have hp : (u₁, v₀) ∈ U₁ :=
      hR₁ ⟨⟨hu.le, le_rfl⟩, ⟨le_rfl, hv.le⟩⟩
    exact (h₁.solution.development.1 hp).2
  let P : Set ℝ := {v | v ∈ Icc v₀ v₁ →
    S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v}
  let Q : Set ℝ := {u | u ∈ Icc u₀ u₁ →
    S₁.nu u v₀ = S₂.nu u v₀ ∧
      S₁.beta u v₀ = S₂.beta u v₀}
  have hP : ∀ᵐ v : ℝ ∂volume, v ∈ P := hV
  have hQ : ∀ᵐ u : ℝ ∂volume, u ∈ Q := hU
  obtain ⟨M, hM, hineq⟩ := regular_rectangle_volterra_bound
    h₁ h₂ hu.le hv.le hsep hR₁ hR₂ hr₀ hψ₀ hm₀ hV
  obtain ⟨B, hB, hFB⟩ := regularDifference_bounded
    h₁ h₂ hu.le hv.le hsep hR₁ hR₂
  have hFint := regularDifference_intervalIntegrable
    h₁ h₂ hu.le hv.le hR₁ hR₂
  have hFu : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      IntervalIntegrable (fun s => regularDifference S₁ S₂ s v)
        volume u₀ u := by
    intro u hu' v hv'
    apply (hFint.2 v hv').mono_set
    rw [uIcc_of_le hu.le, uIcc_of_le hu'.1]
    exact Icc_subset_Icc le_rfl hu'.2
  have hFv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      IntervalIntegrable (regularDifference S₁ S₂ u)
        volume v₀ v := by
    intro u hu' v hv'
    apply (hFint.1 u hu').mono_set
    rw [uIcc_of_le hv.le, uIcc_of_le hv'.1]
    exact Icc_subset_Icc le_rfl hv'.2
  have hZero := eq_zero_of_le_two_variable_volterra_ae_both
    hu.le hv.le hM hB hP hQ
    (fun u hu' v hv' => regularDifference_nonneg S₁ S₂ u v)
    hFB hFu hFv
    (fun u hu' v hv' huQ hvP =>
      hineq u hu' v hv' (hvP hv') (huQ hu'))
  have hEqGood : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      u ∈ Q → v ∈ P →
      S₁.r u v = S₂.r u v ∧
      S₁.phi u v = S₂.phi u v ∧
      S₁.m u v = S₂.m u v := by
    intro u hu' v hv' huQ hvP
    have hz := hZero u hu' v hv' huQ hvP
    obtain ⟨hr, hphi, hm, _, _, _, _⟩ :=
      regularDifference_components S₁ S₂ u v
    have heq (x y : ℝ) (hxy : |x - y| ≤ regularDifference S₁ S₂ u v) :
        x = y := by
      have hzero : |x - y| = 0 :=
        le_antisymm (by simpa only [hz] using hxy) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
    exact ⟨heq _ _ hr, heq _ _ hphi, heq _ _ hm⟩
  have hcont₁ := regular_rectangle_slice_continuity
    h₁ hu.le hv.le hR₁
  have hcont₂ := regular_rectangle_slice_continuity
    h₂ hu.le hv.le hR₂
  intro u hu' v hv'
  have hr := regular_rectangle_eq_of_ae_parameters hu hv hP hQ
    (fun v hv' => (hcont₁.2 v hv').1)
    (fun v hv' => (hcont₂.2 v hv').1)
    (fun u hu' => (hcont₁.1 u hu').1)
    (fun u hu' => (hcont₂.1 u hu').1)
    (fun u hu' v hv' huQ hvP => (hEqGood u hu' v hv' huQ hvP).1)
  have hphi := regular_rectangle_eq_of_ae_parameters hu hv hP hQ
    (fun v hv' => (hcont₁.2 v hv').2.1)
    (fun v hv' => (hcont₂.2 v hv').2.1)
    (fun u hu' => (hcont₁.1 u hu').2.1)
    (fun u hu' => (hcont₂.1 u hu').2.1)
    (fun u hu' v hv' huQ hvP => (hEqGood u hu' v hv' huQ hvP).2.1)
  have hm := regular_rectangle_eq_of_ae_parameters hu hv hP hQ
    (fun v hv' => (hcont₁.2 v hv').2.2)
    (fun v hv' => (hcont₂.2 v hv').2.2)
    (fun u hu' => (hcont₁.1 u hu').2.2)
    (fun u hu' => (hcont₂.1 u hu').2.2)
    (fun u hu' v hv' huQ hvP => (hEqGood u hu' v hv' huQ hvP).2.2)
  exact ⟨hr u hu' v hv', hphi u hu' v hv', hm u hu' v hv'⟩

end ChristodoulouBV.Uniqueness

end
