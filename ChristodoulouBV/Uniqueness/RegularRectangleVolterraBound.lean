module

public import ChristodoulouBV.Uniqueness.RegularRectangleBoundary

/-!
# Seven-field Volterra comparison on a regular rectangle

The characteristic integral identities yield a homogeneous two-variable
inequality at parameters where both past-face density equalities hold.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace ChristodoulouBV.Uniqueness

/-- Separate continuity extends equality from a product of two conull
parameter sets to a nondegenerate closed rectangle. -/
theorem regular_rectangle_eq_of_ae_parameters
    {f g : ℝ → ℝ → ℝ} {u₀ u₁ v₀ v₁ : ℝ}
    {P Q : Set ℝ}
    (hu : u₀ < u₁) (hv : v₀ < v₁)
    (hP : ∀ᵐ v : ℝ ∂volume, v ∈ P)
    (hQ : ∀ᵐ u : ℝ ∂volume, u ∈ Q)
    (hfu : ∀ v ∈ Icc v₀ v₁,
      ContinuousOn (fun u => f u v) (Icc u₀ u₁))
    (hgu : ∀ v ∈ Icc v₀ v₁,
      ContinuousOn (fun u => g u v) (Icc u₀ u₁))
    (hfv : ∀ u ∈ Icc u₀ u₁,
      ContinuousOn (f u) (Icc v₀ v₁))
    (hgv : ∀ u ∈ Icc u₀ u₁,
      ContinuousOn (g u) (Icc v₀ v₁))
    (heq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      u ∈ Q → v ∈ P → f u v = g u v) :
    ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      f u v = g u v := by
  have hgoodV : ∀ v ∈ Icc v₀ v₁, v ∈ P →
      ∀ u ∈ Icc u₀ u₁, f u v = g u v := by
    intro v hv' hvP
    apply Measure.eqOn_Icc_of_ae_eq (μ := volume) (ne_of_lt hu) ?_
      (hfu v hv') (hgu v hv')
    change ∀ᵐ u ∂volume.restrict (Icc u₀ u₁), f u v = g u v
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hQ] with u huQ hu'
    exact heq u hu' v hv' huQ hvP
  intro u hu' v hv'
  have hface : ∀ᵐ t ∂volume, t ∈ Icc v₀ v₁ → f u t = g u t := by
    filter_upwards [hP] with t htP ht
    exact hgoodV t ht htP u hu'
  have heqOn := Measure.eqOn_Icc_of_ae_eq (μ := volume)
    (ne_of_lt hv) (by
      change ∀ᵐ t ∂volume.restrict (Icc v₀ v₁), f u t = g u t
      rw [ae_restrict_iff' measurableSet_Icc]
      exact hface) (hfv u hu') (hgv u hu')
  exact heqOn hv'

/-- On a regular rectangle, equal corner data and a.e. equal boundary
densities give the homogeneous Volterra inequality at good parameters. -/
theorem regular_rectangle_volterra_bound
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hr₀ : S₁.r u₀ v₀ = S₂.r u₀ v₀)
    (hψ₀ : S₁.r u₀ v₀ * S₁.phi u₀ v₀ =
      S₂.r u₀ v₀ * S₂.phi u₀ v₀)
    (hm₀ : S₁.m u₀ v₀ = S₂.m u₀ v₀)
    (hV : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        (S₁.lam u₀ v = S₂.lam u₀ v ∧
          S₁.alpha u₀ v = S₂.alpha u₀ v) →
        (S₁.nu u v₀ = S₂.nu u v₀ ∧
          S₁.beta u v₀ = S₂.beta u v₀) →
        regularDifference S₁ S₂ u v ≤
          M * (∫ s in u₀..u, regularDifference S₁ S₂ s v) +
          M * (∫ t in v₀..v, regularDifference S₁ S₂ u t) := by
  obtain ⟨ρ, δ, c, C, hρ, hδ, hc, hC, hbound⟩ :=
    regular_rectangle_coefficients h₁ h₂ hu hv hsep hR₁ hR₂
  obtain ⟨K, hK, hdensity⟩ :=
    regular_rectangle_density_difference h₁ h₂ hu hv hsep hR₁ hR₂
  have hprimary := regular_rectangle_outgoing_primary_face h₁ h₂ hu hv
    hR₁ hR₂ hr₀ hψ₀ hV
  have hmass := regular_rectangle_outgoing_mass_face h₁ h₂ hu hv
    hsep hR₁ hR₂ hm₀ hprimary hV
  have hFint := regularDifference_intervalIntegrable h₁ h₂ hu hv hR₁ hR₂
  let A := 1 + (1 + C) / ρ + 3 * K
  let B := 2 * K
  let M := 1 + A + B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; linarith
  refine ⟨M, hM, ?_⟩
  intro u hu' v hv' hVpoint hUpoint
  let Iu := ∫ s in u₀..u, regularDifference S₁ S₂ s v
  let Iv := ∫ t in v₀..v, regularDifference S₁ S₂ u t
  have hIu : 0 ≤ Iu := by
    dsimp [Iu]
    apply intervalIntegral.integral_nonneg hu'.1
    intro s hs
    exact regularDifference_nonneg S₁ S₂ s v
  have hIv : 0 ≤ Iv := by
    dsimp [Iv]
    apply intervalIntegral.integral_nonneg hv'.1
    intro t ht
    exact regularDifference_nonneg S₁ S₂ u t
  have hFu : IntervalIntegrable
      (fun s => regularDifference S₁ S₂ s v) volume u₀ u := by
    apply (hFint.2 v hv').mono_set
    rw [uIcc_of_le hu, uIcc_of_le hu'.1]
    exact Icc_subset_Icc le_rfl hu'.2
  have hFv : IntervalIntegrable
      (regularDifference S₁ S₂ u) volume v₀ v := by
    apply (hFint.1 u hu').mono_set
    rw [uIcc_of_le hv, uIcc_of_le hv'.1]
    exact Icc_subset_Icc le_rfl hv'.2
  have hsIn₁ := regularRectangle_inSeg_subset hR₁ hv'
  have hsIn₂ := regularRectangle_inSeg_subset hR₂ hv'
  have hsOut₁ := regularRectangle_outSeg_subset hR₁ hu'
  have hsOut₂ := regularRectangle_outSeg_subset hR₂ hu'
  have hsi₁ : inSeg v u₀ u ⊆ U₁ :=
    (inSeg_subsegment le_rfl hu'.1 hu'.2).trans hsIn₁
  have hsi₂ : inSeg v u₀ u ⊆ U₂ :=
    (inSeg_subsegment le_rfl hu'.1 hu'.2).trans hsIn₂
  have hso₁ : outSeg u v₀ v ⊆ U₁ :=
    (outSeg_subsegment le_rfl hv'.1 hv'.2).trans hsOut₁
  have hso₂ : outSeg u v₀ v ⊆ U₂ :=
    (outSeg_subsegment le_rfl hv'.1 hv'.2).trans hsOut₂
  have hr : |S₁.r u v - S₂.r u v| ≤ Iu := by
    have hh := regular_primitive_difference_le hu'.1
      (by norm_num : (0 : ℝ) ≤ 1) (hprimary v hv').1
      (h₁.solution.radius_in v u₀ u hu'.1 hsi₁)
      (h₂.solution.radius_in v u₀ u hu'.1 hsi₂) hFu
      (fun s hs => by
        simpa only [one_mul] using
          (regularDifference_components S₁ S₂ s v).2.2.2.2.1)
    simpa only [Iu, one_mul] using hh
  have hψ : |S₁.r u v * S₁.phi u v -
      S₂.r u v * S₂.phi u v| ≤ Iu := by
    have hh := regular_primitive_difference_le hu'.1
      (by norm_num : (0 : ℝ) ≤ 1) (hprimary v hv').2
      (h₁.solution.scalar_radius_in v u₀ u hu'.1 hsi₁)
      (h₂.solution.scalar_radius_in v u₀ u hu'.1 hsi₂) hFu
      (fun s hs => by
        simpa only [one_mul] using
          (regularDifference_components S₁ S₂ s v).2.2.2.2.2.2)
    simpa only [Iu, one_mul] using hh
  have hm : |S₁.m u v - S₂.m u v| ≤ K * Iu := by
    have hh := regular_primitive_difference_le hu'.1 hK
      (hmass v hv')
      (show IntervalPrimitive (fun s => S₁.m s v)
          (fun s => IsBVSolution.massInDensity S₁ s v) u₀ u from
        h₁.solution.mass_in v u₀ u hu'.1 hsi₁)
      (show IntervalPrimitive (fun s => S₂.m s v)
          (fun s => IsBVSolution.massInDensity S₂ s v) u₀ u from
        h₂.solution.mass_in v u₀ u hu'.1 hsi₂)
      hFu (fun s hs => (hdensity s ⟨hs.1, hs.2.trans hu'.2⟩ v hv').2.1)
    exact hh
  have hlam : |S₁.lam u v - S₂.lam u v| ≤ K * Iu := by
    have hh := regular_primitive_difference_le hu'.1 hK hVpoint.1
      (show IntervalPrimitive (fun s => S₁.lam s v)
          (fun s => IsBVSolution.radiusCoeff S₁ s v) u₀ u from
        h₁.solution.lam_in v u₀ u hu'.1 hsi₁)
      (show IntervalPrimitive (fun s => S₂.lam s v)
          (fun s => IsBVSolution.radiusCoeff S₂ s v) u₀ u from
        h₂.solution.lam_in v u₀ u hu'.1 hsi₂)
      hFu (fun s hs => (hdensity s ⟨hs.1, hs.2.trans hu'.2⟩ v hv').2.2.1)
    exact hh
  have halpha : |S₁.alpha u v - S₂.alpha u v| ≤ K * Iu := by
    have hh := regular_primitive_difference_le hu'.1 hK hVpoint.2
      (show IntervalPrimitive (fun s => S₁.alpha s v)
          (fun s => IsBVSolution.radiusCoeff S₁ s v * S₁.phi s v) u₀ u from
        h₁.solution.alpha_in v u₀ u hu'.1 hsi₁)
      (show IntervalPrimitive (fun s => S₂.alpha s v)
          (fun s => IsBVSolution.radiusCoeff S₂ s v * S₂.phi s v) u₀ u from
        h₂.solution.alpha_in v u₀ u hu'.1 hsi₂)
      hFu (fun s hs => (hdensity s ⟨hs.1, hs.2.trans hu'.2⟩ v hv').2.2.2)
    exact hh
  have hnu : |S₁.nu u v - S₂.nu u v| ≤ K * Iv := by
    have hh := regular_primitive_difference_le hv'.1 hK hUpoint.1
      (h₁.solution.nu_out u v₀ v hv'.1 hso₁)
      (h₂.solution.nu_out u v₀ v hv'.1 hso₂)
      hFv (fun t ht =>
        (hdensity u hu' t ⟨ht.1, ht.2.trans hv'.2⟩).2.2.1)
    exact hh
  have hbeta : |S₁.beta u v - S₂.beta u v| ≤ K * Iv := by
    have hh := regular_primitive_difference_le hv'.1 hK hUpoint.2
      (h₁.solution.beta_out u v₀ v hv'.1 hso₁)
      (h₂.solution.beta_out u v₀ v hv'.1 hso₂)
      hFv (fun t ht =>
        (hdensity u hu' t ⟨ht.1, ht.2.trans hv'.2⟩).2.2.2)
    exact hh
  have hphi : |S₁.phi u v - S₂.phi u v| ≤
      ((1 + C) / ρ) * Iu := by
    have hbr := (hbound u hu' v hv' S₁ (Or.inl rfl)).1
    have hbphi := (hbound u hu' v hv' S₂ (Or.inr rfl)).2.2.2.2.2.2.1
    have hh := regular_scalar_of_radius_scalar_difference_le
      (r₂ := S₂.r u v) (φ₁ := S₁.phi u v) hρ hbr hC hbphi
    calc
      |S₁.phi u v - S₂.phi u v| ≤
          (|S₁.r u v * S₁.phi u v -
              S₂.r u v * S₂.phi u v| +
            C * |S₁.r u v - S₂.r u v|) / ρ := hh
      _ ≤ (Iu + C * Iu) / ρ :=
        div_le_div_of_nonneg_right
          (add_le_add hψ (mul_le_mul_of_nonneg_left hr hC)) hρ.le
      _ = ((1 + C) / ρ) * Iu := by ring
  have hsum : regularDifference S₁ S₂ u v ≤ A * Iu + B * Iv := by
    dsimp [regularDifference, A, B]
    linarith
  have hMA : A ≤ M := by dsimp [M]; linarith
  have hMB : B ≤ M := by dsimp [M]; linarith
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_right hMA hIu)
    (mul_le_mul_of_nonneg_right hMB hIv))

end ChristodoulouBV.Uniqueness

end
