module

public import ChristodoulouBV.Uniqueness.RegularRectangleBounds

/-!
# Regular coefficients on a characteristic rectangle

The radius and mass gap have positive minima on each fixed off-axis
rectangle. The frozen transport densities then have uniform finite bounds.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- The regular mixed coefficient is bounded by the inverse radius and gap
minima and the expansion amplitudes. -/
theorem regular_radiusCoeff_abs_le
    {μ lam nu g r ρ δ C : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hρ : 0 < ρ) (hr : ρ ≤ r)
    (hδ : 0 < δ) (hg : δ ≤ g)
    (hC : 0 ≤ C) (hlam : |lam| ≤ C) (hnu : |nu| ≤ C) :
    |μ * lam * nu / (g * r)| ≤ C ^ 2 / (δ * ρ) := by
  have hrpos : 0 < r := hρ.trans_le hr
  have hgpos : 0 < g := hδ.trans_le hg
  have hden : 0 < g * r := mul_pos hgpos hrpos
  have hdenLow : δ * ρ ≤ g * r :=
    mul_le_mul hg hr hρ.le hgpos.le
  have hprod : |lam| * |nu| ≤ C ^ 2 := by
    rw [pow_two]
    exact (mul_le_mul_of_nonneg_right hlam (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnu hC)
  have hnum : μ * |lam| * |nu| ≤ C ^ 2 := by
    calc
      μ * |lam| * |nu| ≤ 1 * |lam| * |nu| := by
        have h := mul_le_mul_of_nonneg_right hμ1 (abs_nonneg lam)
        exact mul_le_mul_of_nonneg_right h (abs_nonneg nu)
      _ = |lam| * |nu| := by ring
      _ ≤ C ^ 2 := hprod
  have hdenLowPos : 0 < δ * ρ := mul_pos hδ hρ
  have hdiv : μ * |lam| * |nu| / (g * r) ≤ C ^ 2 / (δ * ρ) := by
    apply (div_le_div_iff₀ hden hdenLowPos).2
    calc
      (μ * |lam| * |nu|) * (δ * ρ) ≤ C ^ 2 * (δ * ρ) :=
        mul_le_mul_of_nonneg_right hnum hdenLowPos.le
      _ ≤ C ^ 2 * (g * r) :=
        mul_le_mul_of_nonneg_left hdenLow (sq_nonneg C)
  have habs : |μ * lam * nu / (g * r)| =
      μ * |lam| * |nu| / (g * r) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hμ0,
      abs_of_pos hden]
  rw [habs]
  exact hdiv

/-- On a closed off-axis rectangle the pair has finite uniform bounds for
all frozen regular transport coefficients. The bound belongs to this fixed
rectangle and pair. -/
theorem regular_rectangle_coefficients
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂) :
    ∃ ρ δ c C : ℝ, 0 < ρ ∧ 0 < δ ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        ∀ S : Fields, (S = S₁ ∨ S = S₂) →
          ρ ≤ S.r u v ∧ δ ≤ 1 - 2 * S.m u v / S.r u v ∧
          c ≤ S.lam u v ∧ S.nu u v ≤ -c ∧
          |S.lam u v| ≤ C ∧ |S.nu u v| ≤ C ∧
          |S.phi u v| ≤ C ∧
          |S.alpha u v| ≤ C ∧ |S.beta u v| ≤ C ∧
          |IsBVSolution.radiusCoeff S u v| ≤ C ∧
          |IsBVSolution.massV S u v| ≤ C ∧
          |IsBVSolution.massInDensity S u v| ≤ C := by
  obtain ⟨ρ, δ, c, C₀, hρ, hδ, hc, hC₀, hfield⟩ :=
    regular_rectangle_basic_bounds h₁ h₂ hu hv hsep hR₁ hR₂
  let K : ℝ := C₀ ^ 2 / (δ * ρ)
  let H : ℝ := C₀ ^ 2 / (2 * c)
  let C : ℝ := 1 + C₀ + C₀ ^ 2 + K + H
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith [sq_nonneg C₀]
  refine ⟨ρ, δ, c, C, hρ, hδ, hc, hC, ?_⟩
  intro u hu' v hv' S hS
  obtain ⟨hr, hgap, hlam, hnu, hLamAbs, hNuAbs,
    hphi, htheta, hzeta⟩ := hfield u hu' v hv' S hS
  have hμ : 0 ≤ 2 * S.m u v / S.r u v ∧
      2 * S.m u v / S.r u v < 1 := by
    rcases hS with rfl | rfl
    · exact h₁.mass_ratio_bounds (hR₁ ⟨hu', hv'⟩)
    · exact h₂.mass_ratio_bounds (hR₂ ⟨hu', hv'⟩)
  have hgap0 : 0 ≤ 1 - 2 * S.m u v / S.r u v := by linarith [hμ.2]
  have hgap1 : 1 - 2 * S.m u v / S.r u v ≤ 1 := by linarith [hμ.1]
  have hLamPos : 0 < S.lam u v := hc.trans_le hlam
  have hNuNeg : S.nu u v < 0 := lt_of_le_of_lt hnu (neg_lt_zero.mpr hc)
  have hLamDen : c ≤ |S.lam u v| := by rwa [abs_of_pos hLamPos]
  have hNuDen : c ≤ |S.nu u v| := by
    rw [abs_of_neg hNuNeg]
    linarith
  have hAlpha : |S.alpha u v| ≤ C₀ + C₀ ^ 2 := by
    have heq : S.alpha u v =
        S.theta u v + S.lam u v * S.phi u v := by
      dsimp [Fields.theta]; ring
    rw [heq]
    exact regular_scalar_density_abs_le hC₀ htheta hLamAbs hphi
  have hBeta : |S.beta u v| ≤ C₀ + C₀ ^ 2 := by
    have heq : S.beta u v =
        S.zeta u v + S.nu u v * S.phi u v := by
      dsimp [Fields.zeta]; ring
    rw [heq]
    exact regular_scalar_density_abs_le hC₀ hzeta hNuAbs hphi
  have hRadius : |IsBVSolution.radiusCoeff S u v| ≤ K := by
    change
      |(2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)| ≤ K
    exact regular_radiusCoeff_abs_le hμ.1 hμ.2.le hρ hr hδ hgap
      hC₀ hLamAbs hNuAbs
  have hMassV : |IsBVSolution.massV S u v| ≤ H := by
    change |(1 - 2 * S.m u v / S.r u v) *
      S.theta u v ^ 2 / (2 * S.lam u v)| ≤ H
    exact regular_mass_density_abs_le hgap0 hgap1 hc hLamDen hC₀ htheta
  have hMassIn : |IsBVSolution.massInDensity S u v| ≤ H := by
    change |(1 - 2 * S.m u v / S.r u v) *
      S.zeta u v ^ 2 / (2 * S.nu u v)| ≤ H
    exact regular_mass_density_abs_le hgap0 hgap1 hc hNuDen hC₀ hzeta
  refine ⟨hr, hgap, hlam, hnu, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp [C]; linarith [sq_nonneg C₀]

/-- All three nonlinear transport densities are interval integrable in
their characteristic directions on the closed rectangle. -/
theorem regular_rectangle_transport_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    (∀ u ∈ Icc u₀ u₁,
      IntervalIntegrable (IsBVSolution.massV S u) volume v₀ v₁ ∧
      IntervalIntegrable (IsBVSolution.radiusCoeff S u) volume v₀ v₁ ∧
      IntervalIntegrable (fun v => IsBVSolution.radiusCoeff S u v *
        S.phi u v) volume v₀ v₁) ∧
    (∀ v ∈ Icc v₀ v₁,
      IntervalIntegrable (fun u => IsBVSolution.massInDensity S u v)
        volume u₀ u₁ ∧
      IntervalIntegrable (fun u => IsBVSolution.radiusCoeff S u v)
        volume u₀ u₁ ∧
      IntervalIntegrable (fun u => IsBVSolution.radiusCoeff S u v *
        S.phi u v) volume u₀ u₁) := by
  constructor
  · intro u hu'
    have hs := regularRectangle_outSeg_subset hR hu'
    have hmass : IntervalIntegrable (IsBVSolution.massV S u) volume v₀ v₁ := by
      change IntervalIntegrable
        (fun v => (1 - 2 * S.m u v / S.r u v) *
          S.theta u v ^ 2 / (2 * S.lam u v)) volume v₀ v₁
      exact (h.solution.mass_out u v₀ v₁ hv hs).1
    have hcoeff : IntervalIntegrable (IsBVSolution.radiusCoeff S u)
        volume v₀ v₁ := by
      change IntervalIntegrable
        (fun v => (2 * S.m u v / S.r u v) *
          S.lam u v * S.nu u v /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v)) volume v₀ v₁
      exact (h.solution.nu_out u v₀ v₁ hv hs).1
    have hscalar : IntervalIntegrable
        (fun v => IsBVSolution.radiusCoeff S u v * S.phi u v)
        volume v₀ v₁ := by
      change IntervalIntegrable
        (fun v => ((2 * S.m u v / S.r u v) *
          S.lam u v * S.nu u v /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v)) *
          S.phi u v) volume v₀ v₁
      exact (h.solution.beta_out u v₀ v₁ hv hs).1
    exact ⟨hmass, hcoeff, hscalar⟩
  · intro v hv'
    have hs := regularRectangle_inSeg_subset hR hv'
    have hmass : IntervalIntegrable
        (fun u => IsBVSolution.massInDensity S u v) volume u₀ u₁ := by
      change IntervalIntegrable
        (fun u => (1 - 2 * S.m u v / S.r u v) *
          S.zeta u v ^ 2 / (2 * S.nu u v)) volume u₀ u₁
      exact (h.solution.mass_in v u₀ u₁ hu hs).1
    have hcoeff : IntervalIntegrable
        (fun u => IsBVSolution.radiusCoeff S u v) volume u₀ u₁ := by
      change IntervalIntegrable
        (fun u => (2 * S.m u v / S.r u v) *
          S.lam u v * S.nu u v /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v)) volume u₀ u₁
      exact (h.solution.lam_in v u₀ u₁ hu hs).1
    have hscalar : IntervalIntegrable
        (fun u => IsBVSolution.radiusCoeff S u v * S.phi u v)
        volume u₀ u₁ := by
      change IntervalIntegrable
        (fun u => ((2 * S.m u v / S.r u v) *
          S.lam u v * S.nu u v /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v)) *
          S.phi u v) volume u₀ u₁
      exact (h.solution.alpha_in v u₀ u₁ hu hs).1
    exact ⟨hmass, hcoeff, hscalar⟩

end ChristodoulouBV.Uniqueness

end
