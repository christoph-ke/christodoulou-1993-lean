module

public import ChristodoulouBV.Uniqueness.RegularRectangleDensityDifference

/-!
# Past-face data on a regular characteristic rectangle

Equality of primitive densities is used only almost everywhere. Their
continuous primitives are then identified at every point of each face.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- Equal initial values and almost-everywhere equal densities give equal
primitives at every point of an ordered interval. -/
theorem regular_same_primitive_of_ae
    {f₁ f₂ g₁ g₂ : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hinit : f₁ a = f₂ a)
    (hprim₁ : ∀ t ∈ Icc a b, IntervalPrimitive f₁ g₁ a t)
    (hprim₂ : ∀ t ∈ Icc a b, IntervalPrimitive f₂ g₂ a t)
    (hgae : ∀ᵐ s ∂volume, s ∈ Icc a b → g₁ s = g₂ s) :
    ∀ t ∈ Icc a b, f₁ t = f₂ t := by
  intro t ht
  have hp₁ := (hprim₁ t ht).2
  have hp₂ := (hprim₂ t ht).2
  have hint : (∫ s in a..t, g₁ s) = ∫ s in a..t, g₂ s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgae] with s hs hst
    have hsab : s ∈ Icc a b := by
      rw [uIoc_of_le ht.1] at hst
      exact ⟨hst.1.le, hst.2.trans ht.2⟩
    exact hs hsab
  linarith

/-- A difference of ordered primitives is bounded by the integral of a
pointwise density majorant. -/
theorem regular_primitive_difference_le
    {f₁ f₂ g₁ g₂ F : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b) (_hK : 0 ≤ K)
    (hinit : f₁ a = f₂ a)
    (hprim₁ : IntervalPrimitive f₁ g₁ a b)
    (hprim₂ : IntervalPrimitive f₂ g₂ a b)
    (hF : IntervalIntegrable F volume a b)
    (hbound : ∀ s ∈ Icc a b, |g₁ s - g₂ s| ≤ K * F s) :
    |f₁ b - f₂ b| ≤ K * ∫ s in a..b, F s := by
  have hform : f₁ b - f₂ b = ∫ s in a..b, g₁ s - g₂ s := by
    rw [intervalIntegral.integral_sub hprim₁.1 hprim₂.1]
    linarith [hprim₁.2, hprim₂.2]
  rw [hform]
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc a b →
      ‖g₁ s - g₂ s‖ ≤ K * F s :=
    Filter.Eventually.of_forall (fun s hs => by
      simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1.le, hs.2⟩)
  have h := intervalIntegral.norm_integral_le_of_norm_le hab hmaj
    (hF.const_mul K)
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using h

/-- The a.e. outgoing boundary densities and the corner data determine
radius and scalar-radius pointwise on the past outgoing face. -/
theorem regular_rectangle_outgoing_primary_face
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hr₀ : S₁.r u₀ v₀ = S₂.r u₀ v₀)
    (hψ₀ : S₁.r u₀ v₀ * S₁.phi u₀ v₀ =
      S₂.r u₀ v₀ * S₂.phi u₀ v₀)
    (hdata : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v) :
    ∀ v ∈ Icc v₀ v₁,
      S₁.r u₀ v = S₂.r u₀ v ∧
      S₁.r u₀ v * S₁.phi u₀ v =
        S₂.r u₀ v * S₂.phi u₀ v := by
  have hs₁ := regularRectangle_outSeg_subset hR₁ ⟨le_rfl, hu⟩
  have hs₂ := regularRectangle_outSeg_subset hR₂ ⟨le_rfl, hu⟩
  have hlam : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v := by
    filter_upwards [hdata] with v hv hv'
    exact (hv hv').1
  have halpha : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.alpha u₀ v = S₂.alpha u₀ v := by
    filter_upwards [hdata] with v hv hv'
    exact (hv hv').2
  have hr := regular_same_primitive_of_ae hv hr₀
    (fun t ht => h₁.solution.radius_out u₀ v₀ t ht.1
      ((outSeg_subsegment le_rfl ht.1 ht.2).trans hs₁))
    (fun t ht => h₂.solution.radius_out u₀ v₀ t ht.1
      ((outSeg_subsegment le_rfl ht.1 ht.2).trans hs₂)) hlam
  have hψ := regular_same_primitive_of_ae hv hψ₀
    (fun t ht => h₁.solution.scalar_radius_out u₀ v₀ t ht.1
      ((outSeg_subsegment le_rfl ht.1 ht.2).trans hs₁))
    (fun t ht => h₂.solution.scalar_radius_out u₀ v₀ t ht.1
      ((outSeg_subsegment le_rfl ht.1 ht.2).trans hs₂)) halpha
  exact fun v hv' => ⟨hr v hv', hψ v hv'⟩

/-- The a.e. incoming boundary densities and corner data determine radius
and scalar-radius pointwise on the past incoming face. -/
theorem regular_rectangle_incoming_primary_face
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hr₀ : S₁.r u₀ v₀ = S₂.r u₀ v₀)
    (hψ₀ : S₁.r u₀ v₀ * S₁.phi u₀ v₀ =
      S₂.r u₀ v₀ * S₂.phi u₀ v₀)
    (hdata : ∀ᵐ u ∂volume, u ∈ Icc u₀ u₁ →
      S₁.nu u v₀ = S₂.nu u v₀ ∧
      S₁.beta u v₀ = S₂.beta u v₀) :
    ∀ u ∈ Icc u₀ u₁,
      S₁.r u v₀ = S₂.r u v₀ ∧
      S₁.r u v₀ * S₁.phi u v₀ =
        S₂.r u v₀ * S₂.phi u v₀ := by
  have hs₁ := regularRectangle_inSeg_subset hR₁ ⟨le_rfl, hv⟩
  have hs₂ := regularRectangle_inSeg_subset hR₂ ⟨le_rfl, hv⟩
  have hnu : ∀ᵐ u ∂volume, u ∈ Icc u₀ u₁ →
      S₁.nu u v₀ = S₂.nu u v₀ := by
    filter_upwards [hdata] with u hu hu'
    exact (hu hu').1
  have hbeta : ∀ᵐ u ∂volume, u ∈ Icc u₀ u₁ →
      S₁.beta u v₀ = S₂.beta u v₀ := by
    filter_upwards [hdata] with u hu hu'
    exact (hu hu').2
  have hr := regular_same_primitive_of_ae hu hr₀
    (fun t ht => h₁.solution.radius_in v₀ u₀ t ht.1
      ((inSeg_subsegment le_rfl ht.1 ht.2).trans hs₁))
    (fun t ht => h₂.solution.radius_in v₀ u₀ t ht.1
      ((inSeg_subsegment le_rfl ht.1 ht.2).trans hs₂)) hnu
  have hψ := regular_same_primitive_of_ae hu hψ₀
    (fun t ht => h₁.solution.scalar_radius_in v₀ u₀ t ht.1
      ((inSeg_subsegment le_rfl ht.1 ht.2).trans hs₁))
    (fun t ht => h₂.solution.scalar_radius_in v₀ u₀ t ht.1
      ((inSeg_subsegment le_rfl ht.1 ht.2).trans hs₂)) hbeta
  exact fun u hu' => ⟨hr u hu', hψ u hu'⟩

/-- Equal radius and scalar-radius on a positive-radius face give equal
scalar fields there. -/
theorem regular_rectangle_phi_of_radius_scalar
    {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁)
    {u v : ℝ} (huv : (u, v) ∈ U₁)
    (hr : S₁.r u v = S₂.r u v)
    (hψ : S₁.r u v * S₁.phi u v =
      S₂.r u v * S₂.phi u v) :
    S₁.phi u v = S₂.phi u v := by
  have hrne : S₁.r u v ≠ 0 :=
    (h₁.solution.radius_pos (u, v) huv).ne'
  rw [← hr] at hψ
  exact (mul_left_cancel₀ hrne hψ)

/-- Equal corner mass, radius, scalar-radius, and outgoing primitive
densities determine the mass pointwise on the past outgoing face. -/
theorem regular_rectangle_outgoing_mass_face
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂)
    (hm₀ : S₁.m u₀ v₀ = S₂.m u₀ v₀)
    (hface : ∀ v ∈ Icc v₀ v₁,
      S₁.r u₀ v = S₂.r u₀ v ∧
      S₁.r u₀ v * S₁.phi u₀ v =
        S₂.r u₀ v * S₂.phi u₀ v)
    (hdata : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      S₁.lam u₀ v = S₂.lam u₀ v ∧
      S₁.alpha u₀ v = S₂.alpha u₀ v) :
    ∀ v ∈ Icc v₀ v₁, S₁.m u₀ v = S₂.m u₀ v := by
  let z : ℝ → ℝ := fun v => S₁.m u₀ v - S₂.m u₀ v
  let k : ℝ → ℝ := fun v =>
    -(S₁.theta u₀ v * S₁.theta u₀ v *
      (S₁.r u₀ v)⁻¹ * (S₁.lam u₀ v)⁻¹)
  have hs₁ := regularRectangle_outSeg_subset hR₁ ⟨le_rfl, hu⟩
  have hs₂ := regularRectangle_outSeg_subset hR₂ ⟨le_rfl, hu⟩
  have hprim₁ (t : ℝ) (ht : t ∈ Icc v₀ v₁) :
      IntervalPrimitive (S₁.m u₀) (IsBVSolution.massV S₁ u₀) v₀ t := by
    change IntervalPrimitive (S₁.m u₀)
      (fun s => (1 - 2 * S₁.m u₀ s / S₁.r u₀ s) *
        S₁.theta u₀ s ^ 2 / (2 * S₁.lam u₀ s)) v₀ t
    exact h₁.solution.mass_out u₀ v₀ t ht.1
      ((outSeg_subsegment le_rfl ht.1 ht.2).trans hs₁)
  have hprim₂ (t : ℝ) (ht : t ∈ Icc v₀ v₁) :
      IntervalPrimitive (S₂.m u₀) (IsBVSolution.massV S₂ u₀) v₀ t := by
    change IntervalPrimitive (S₂.m u₀)
      (fun s => (1 - 2 * S₂.m u₀ s / S₂.r u₀ s) *
        S₂.theta u₀ s ^ 2 / (2 * S₂.lam u₀ s)) v₀ t
    exact h₂.solution.mass_out u₀ v₀ t ht.1
      ((outSeg_subsegment le_rfl ht.1 ht.2).trans hs₂)
  have hmassInt₁ := (hprim₁ v₁ ⟨hv, le_rfl⟩).1
  have hmassInt₂ := (hprim₂ v₁ ⟨hv, le_rfl⟩).1
  have hmassDiff : ∀ᵐ v ∂volume, v ∈ Icc v₀ v₁ →
      IsBVSolution.massV S₁ u₀ v -
        IsBVSolution.massV S₂ u₀ v = k v * z v := by
    filter_upwards [hdata] with v hd hv'
    have hpoint₁ : (u₀, v) ∈ U₁ := hR₁ ⟨⟨le_rfl, hu⟩, hv'⟩
    have hr := (hface v hv').1
    have hφ := regular_rectangle_phi_of_radius_scalar h₁ hpoint₁ hr
      (hface v hv').2
    have hθ : S₁.theta u₀ v = S₂.theta u₀ v := by
      dsimp [Fields.theta]
      rw [hd hv' |>.2, hd hv' |>.1, hφ]
    have hrne : S₁.r u₀ v ≠ 0 :=
      (h₁.solution.radius_pos (u₀, v) hpoint₁).ne'
    have hlne : S₁.lam u₀ v ≠ 0 :=
      (h₁.solution.lam_pos (u₀, v) hpoint₁).ne'
    dsimp [IsBVSolution.massV, k, z]
    rw [hd hv' |>.1, hθ, ← hr]
    field_simp
    ring
  have hpoint : (u₀, v₁) ∈ U₁ :=
    hR₁ ⟨⟨le_rfl, hu⟩, ⟨hv, le_rfl⟩⟩
  have hu0v0 : u₀ < v₀ := hu.trans_lt hsep
  have hk : IntervalIntegrable k volume v₀ v₁ := by
    have hh := IsBVSolution.barrier_coefficient_integrable
      h₁.solution.development h₁ hpoint hu0v0 hv le_rfl
    convert hh.neg using 1
  have hkz : IntervalIntegrable (fun v => k v * z v)
      volume v₀ v₁ := by
    apply (hmassInt₁.sub hmassInt₂).congr_ae
    change ∀ᵐ v ∂volume.restrict (uIoc v₀ v₁),
      IsBVSolution.massV S₁ u₀ v -
        IsBVSolution.massV S₂ u₀ v = k v * z v
    rw [uIoc_of_le hv]
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hmassDiff] with v hdiff hv'
    exact hdiff ⟨hv'.1.le, hv'.2⟩
  have hy (t : ℝ) (ht : t ∈ Icc v₀ v₁) :
      z t - z v₀ = ∫ s in v₀..t, (k s * z s + (0 : ℝ)) := by
    have hp₁ := (hprim₁ t ht).2
    have hp₂ := (hprim₂ t ht).2
    have hsub : (∫ s in v₀..t,
        IsBVSolution.massV S₁ u₀ s -
          IsBVSolution.massV S₂ u₀ s) =
        ∫ s in v₀..t, k s * z s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hmassDiff] with s hs hst
      have hsrect : s ∈ Icc v₀ v₁ := by
        rw [uIoc_of_le ht.1] at hst
        exact ⟨hst.1.le, hst.2.trans ht.2⟩
      exact hs hsrect
    have hlin := intervalIntegral.integral_sub
      (hprim₁ t ht).1 (hprim₂ t ht).1
    dsimp [z]
    simp only [add_zero]
    rw [← hsub, hlin]
    linarith [hp₁, hp₂]
  intro v hv'
  have hform := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    hv hk intervalIntegrable_const hkz hy hv'
  have hz₀ : z v₀ = 0 := sub_eq_zero.mpr hm₀
  have hz : z v = 0 := by
    simpa only [hz₀, mul_zero, intervalIntegral.integral_zero,
      add_zero] using hform
  exact sub_eq_zero.mp hz

end ChristodoulouBV.Uniqueness

end
