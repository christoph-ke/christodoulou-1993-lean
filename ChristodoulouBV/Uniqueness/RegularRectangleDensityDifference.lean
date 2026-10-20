module

public import ChristodoulouBV.Uniqueness.RegularRectangleDifferenceAlgebra

/-!
# Lipschitz bounds for the regular characteristic densities

The constants belong to one fixed pair of solutions and one fixed
positive-radius rectangle. The bounds hold for the actual BV representatives.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- The three nonlinear characteristic densities have a common local
Lipschitz bound in the seven-field difference on a regular rectangle. -/
theorem regular_rectangle_density_difference
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        |IsBVSolution.massV S₁ u v -
          IsBVSolution.massV S₂ u v| ≤
          K * regularDifference S₁ S₂ u v ∧
        |IsBVSolution.massInDensity S₁ u v -
          IsBVSolution.massInDensity S₂ u v| ≤
          K * regularDifference S₁ S₂ u v ∧
        |IsBVSolution.radiusCoeff S₁ u v -
          IsBVSolution.radiusCoeff S₂ u v| ≤
          K * regularDifference S₁ S₂ u v ∧
        |IsBVSolution.radiusCoeff S₁ u v * S₁.phi u v -
          IsBVSolution.radiusCoeff S₂ u v * S₂.phi u v| ≤
          K * regularDifference S₁ S₂ u v := by
  obtain ⟨ρ, δ, c, C, hρ, hδ, hc, hC, hbound⟩ :=
    regular_rectangle_coefficients h₁ h₂ hu hv hsep hR₁ hR₂
  let T := C + C ^ 2
  let Kμ := 3 / ρ
  let Kθ := 1 + 2 * C
  let Km := ((2 * T * Kθ + T ^ 2 * Kμ) / (2 * c)) +
    T ^ 2 * 2 / (2 * c) ^ 2
  let Kr := C * ((1 / δ) * (1 / ρ + C / ρ ^ 2) +
    (C / ρ) * (Kμ / δ + Kμ / δ ^ 2)) +
    (1 / δ) * (C / ρ)
  let Ks := C * Kr + C
  let K := 1 + Km + Kr + Ks
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hKμ : 0 ≤ Kμ := by dsimp [Kμ]; positivity
  have hKθ : 0 ≤ Kθ := by dsimp [Kθ]; positivity
  have hKm : 0 ≤ Km := by dsimp [Km]; positivity
  have hKr : 0 ≤ Kr := by dsimp [Kr]; positivity
  have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
  have hK : 0 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro u hu' v hv'
  let F := regularDifference S₁ S₂ u v
  have hF : 0 ≤ F := regularDifference_nonneg S₁ S₂ u v
  obtain ⟨hdr, hdphi, hdm, hdlam, hdnu, hdalpha, hdbeta⟩ :=
    regularDifference_components S₁ S₂ u v
  have hb₁ := hbound u hu' v hv' S₁ (Or.inl rfl)
  have hb₂ := hbound u hu' v hv' S₂ (Or.inr rfl)
  obtain ⟨hr₁, hg₁, hlam₁, hnu₁, hlamAbs₁, hnuAbs₁,
    hphi₁, halpha₁, hbeta₁, hcoeff₁, _, _⟩ := hb₁
  obtain ⟨hr₂, hg₂, hlam₂, hnu₂, hlamAbs₂, hnuAbs₂,
    hphi₂, halpha₂, hbeta₂, hcoeff₂, _, _⟩ := hb₂
  have hμ₁ := h₁.mass_ratio_bounds (hR₁ ⟨hu', hv'⟩)
  have hμ₂ := h₂.mass_ratio_bounds (hR₂ ⟨hu', hv'⟩)
  have hμdiff : |2 * S₁.m u v / S₁.r u v -
      2 * S₂.m u v / S₂.r u v| ≤ Kμ * F := by
    have hh := regular_mass_ratio_difference_le (m₁ := S₁.m u v)
      hρ hr₁ hr₂ hμ₂.1 hμ₂.2.le
    have hsum : 2 * |S₁.m u v - S₂.m u v| +
        |S₁.r u v - S₂.r u v| ≤ 3 * F := by
      dsimp [F] at hdr hdm ⊢
      linarith
    calc
      |2 * S₁.m u v / S₁.r u v -
          2 * S₂.m u v / S₂.r u v| ≤
          (2 * |S₁.m u v - S₂.m u v| +
            |S₁.r u v - S₂.r u v|) / ρ := hh
      _ ≤ (3 * F) / ρ := div_le_div_of_nonneg_right hsum hρ.le
      _ = Kμ * F := by dsimp [Kμ]; ring
  have hgdiff : |(1 - 2 * S₁.m u v / S₁.r u v) -
      (1 - 2 * S₂.m u v / S₂.r u v)| ≤ Kμ * F := by
    have heq : (1 - 2 * S₁.m u v / S₁.r u v) -
        (1 - 2 * S₂.m u v / S₂.r u v) =
        -(2 * S₁.m u v / S₁.r u v -
          2 * S₂.m u v / S₂.r u v) := by ring
    rw [heq, abs_neg]
    exact hμdiff
  have hg₁0 : 0 ≤ 1 - 2 * S₁.m u v / S₁.r u v := by linarith [hμ₁.2]
  have hg₂0 : 0 ≤ 1 - 2 * S₂.m u v / S₂.r u v := by linarith [hμ₂.2]
  have hg₁1 : 1 - 2 * S₁.m u v / S₁.r u v ≤ 1 := by linarith [hμ₁.1]
  have hg₂1 : 1 - 2 * S₂.m u v / S₂.r u v ≤ 1 := by linarith [hμ₂.1]
  have hθ₁ : |S₁.theta u v| ≤ T := by
    change |S₁.alpha u v - S₁.lam u v * S₁.phi u v| ≤ T
    exact regular_amplitude_abs_le hC halpha₁ hlamAbs₁ hphi₁
  have hθ₂ : |S₂.theta u v| ≤ T := by
    change |S₂.alpha u v - S₂.lam u v * S₂.phi u v| ≤ T
    exact regular_amplitude_abs_le hC halpha₂ hlamAbs₂ hphi₂
  have hζ₁ : |S₁.zeta u v| ≤ T := by
    change |S₁.beta u v - S₁.nu u v * S₁.phi u v| ≤ T
    exact regular_amplitude_abs_le hC hbeta₁ hnuAbs₁ hphi₁
  have hζ₂ : |S₂.zeta u v| ≤ T := by
    change |S₂.beta u v - S₂.nu u v * S₂.phi u v| ≤ T
    exact regular_amplitude_abs_le hC hbeta₂ hnuAbs₂ hphi₂
  have hθdiff : |S₁.theta u v - S₂.theta u v| ≤ Kθ * F := by
    change |(S₁.alpha u v - S₁.lam u v * S₁.phi u v) -
      (S₂.alpha u v - S₂.lam u v * S₂.phi u v)| ≤ Kθ * F
    exact regular_amplitude_lipschitz hC hF hlamAbs₁ hphi₂
      hdalpha hdlam hdphi
  have hζdiff : |S₁.zeta u v - S₂.zeta u v| ≤ Kθ * F := by
    change |(S₁.beta u v - S₁.nu u v * S₁.phi u v) -
      (S₂.beta u v - S₂.nu u v * S₂.phi u v)| ≤ Kθ * F
    exact regular_amplitude_lipschitz hC hF hnuAbs₁ hphi₂
      hdbeta hdnu hdphi
  have hmassV : |IsBVSolution.massV S₁ u v -
      IsBVSolution.massV S₂ u v| ≤ Km * F := by
    change |(1 - 2 * S₁.m u v / S₁.r u v) *
      S₁.theta u v ^ 2 / (2 * S₁.lam u v) -
      (1 - 2 * S₂.m u v / S₂.r u v) *
      S₂.theta u v ^ 2 / (2 * S₂.lam u v)| ≤ Km * F
    simpa only [Km, mul_one] using regular_mass_density_lipschitz
      hc hT hKμ hKθ (by norm_num : (0 : ℝ) ≤ 1) hF
      hg₁0 hg₁1 hg₂0 hg₂1 hlam₁ hlam₂
      hθ₁ hθ₂ hgdiff hθdiff
      (by simpa only [one_mul] using hdlam)
  have hmassIn : |IsBVSolution.massInDensity S₁ u v -
      IsBVSolution.massInDensity S₂ u v| ≤ Km * F := by
    have hq₁ : c ≤ -S₁.nu u v := by linarith
    have hq₂ : c ≤ -S₂.nu u v := by linarith
    have hqdiff : |-S₁.nu u v - -S₂.nu u v| ≤ F := by
      have heq : -S₁.nu u v - -S₂.nu u v =
          -(S₁.nu u v - S₂.nu u v) := by ring
      rwa [heq, abs_neg]
    have hh := regular_mass_density_lipschitz hc hT hKμ hKθ
      (by norm_num : (0 : ℝ) ≤ 1) hF
      hg₁0 hg₁1 hg₂0 hg₂1 hq₁ hq₂
      hζ₁ hζ₂ hgdiff hζdiff
      (by simpa only [one_mul] using hqdiff)
    change |(1 - 2 * S₁.m u v / S₁.r u v) *
      S₁.zeta u v ^ 2 / (2 * S₁.nu u v) -
      (1 - 2 * S₂.m u v / S₂.r u v) *
      S₂.zeta u v ^ 2 / (2 * S₂.nu u v)| ≤ Km * F
    have hform₁ : (1 - 2 * S₁.m u v / S₁.r u v) *
      S₁.zeta u v ^ 2 / (2 * S₁.nu u v) =
      -((1 - 2 * S₁.m u v / S₁.r u v) *
        S₁.zeta u v ^ 2 / (2 * -S₁.nu u v)) := by ring
    have hform₂ : (1 - 2 * S₂.m u v / S₂.r u v) *
      S₂.zeta u v ^ 2 / (2 * S₂.nu u v) =
      -((1 - 2 * S₂.m u v / S₂.r u v) *
        S₂.zeta u v ^ 2 / (2 * -S₂.nu u v)) := by ring
    rw [hform₁, hform₂]
    have habs (a b : ℝ) : |-a - -b| = |a - b| := by
      have heq : -a - -b = -(a - b) := by ring
      rw [heq, abs_neg]
    rw [habs]
    simpa only [Km, mul_one] using hh
  have hcoeff : |IsBVSolution.radiusCoeff S₁ u v -
      IsBVSolution.radiusCoeff S₂ u v| ≤ Kr * F := by
    change |(2 * S₁.m u v / S₁.r u v) * S₁.lam u v * S₁.nu u v /
        ((1 - 2 * S₁.m u v / S₁.r u v) * S₁.r u v) -
      (2 * S₂.m u v / S₂.r u v) * S₂.lam u v * S₂.nu u v /
        ((1 - 2 * S₂.m u v / S₂.r u v) * S₂.r u v)| ≤ Kr * F
    simpa only [Kr, Kμ] using regular_radius_coefficient_lipschitz
      hρ hδ hC hKμ hF hμ₁.1 hμ₁.2.le hμ₂.1 hμ₂.2.le
      hg₁ hg₂ hr₁ hr₂ hlamAbs₁ hlamAbs₂ hnuAbs₁ hnuAbs₂
      hμdiff hgdiff hdr hdlam hdnu
  have hscalar : |IsBVSolution.radiusCoeff S₁ u v * S₁.phi u v -
      IsBVSolution.radiusCoeff S₂ u v * S₂.phi u v| ≤ Ks * F := by
    have hh := regular_product_lipschitz
      hC hC hKr (by norm_num : (0 : ℝ) ≤ 1) hF
      hcoeff₁ hphi₂ hcoeff (by simpa only [one_mul] using hdphi)
    convert hh using 1
    dsimp [Ks]
    ring
  have hKmK : Km ≤ K := by dsimp [K]; linarith
  have hKrK : Kr ≤ K := by dsimp [K]; linarith
  have hKsK : Ks ≤ K := by dsimp [K]; linarith
  exact ⟨hmassV.trans (mul_le_mul_of_nonneg_right hKmK hF),
    hmassIn.trans (mul_le_mul_of_nonneg_right hKmK hF),
    hcoeff.trans (mul_le_mul_of_nonneg_right hKrK hF),
    hscalar.trans (mul_le_mul_of_nonneg_right hKsK hF)⟩

end ChristodoulouBV.Uniqueness

end
