module

public import ChristodoulouBV.Existence.BVStieltjesRepresentatives
public import ChristodoulouBV.Existence.BVBasic
import Mathlib.Tactic

/-!
# Mixed scalar calculus for the canonical BV limit

The mixed scalar densities are absolutely continuous in the transverse
coordinate. Their derivatives are the ordinary parts of the four
Stieltjes area primitives. These identities follow from the already
proved canonical null primitives, without differentiating a BV jump.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- An absolutely continuous function with the indicated a.e. density
satisfies the exact frozen interval primitive, including both endpoints. -/
theorem IntervalPrimitive.of_ac_ae {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOnInterval F a b)
    (he : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv F t = f t) :
    IntervalPrimitive F f a b := by
  have he' : ∀ᵐ t ∂volume, t ∈ uIoc a b → deriv F t = f t := by
    filter_upwards [he] with t ht htI
    exact ht (by rw [uIoc_of_le hab] at htI; exact Ioc_subset_Icc_self htI)
  refine ⟨hF.intervalIntegrable_deriv.congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).mpr he'), ?_⟩
  rw [← hF.integral_deriv_eq_sub]
  exact intervalIntegral.integral_congr_ae he'

private theorem scalar_deriv_of_radius_primitives
    {r φ l α : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφ : AbsolutelyContinuousOnInterval φ a b)
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hrd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv r t = l t)
    (hψd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv (fun s => r s * φ s) t = α t)
    (hr0 : ∀ t ∈ Icc a b, r t ≠ 0) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → deriv φ t = (α t - l t * φ t) / r t := by
  filter_upwards [hrd, hψd, hr.ae_deriv_mul hφ] with t hrt hψt hpt ht
  have hp := hpt (by simpa only [uIcc_of_le hab] using ht)
  rw [hψt ht, hrt ht] at hp
  apply (eq_div_iff (hr0 t ht)).mpr
  linarith only [hp]

/-- The canonical scalar's outgoing a.e. derivative follows from its
radius and scalar-radius primitives and the proved scalar AC clause. -/
theorem bv_ae_deriv_phi_out
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (d.scalarRightFields.phi u) t =
        d.scalarRightFields.theta u t / d.scalarRightFields.r u t := by
  have H := transport_limit_is_solution h hD d
  have hr := H.radius_out_ac_ae hab hs
  have hψ := H.scalar_radius_out_ac_ae hab hs
  exact scalar_deriv_of_radius_primitives hab
    ((scalar_limit_absolute_continuity h hD d).1 u a b hab hs) hr.1 hr.2 hψ.2
    (fun t ht => (H.radius_pos (u, t) (hs ⟨rfl, ht⟩)).ne')

/-- The canonical scalar's incoming a.e. derivative follows from the
symmetric two null primitives. -/
theorem bv_ae_deriv_phi_in
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (fun s => d.scalarRightFields.phi s v) t =
        d.scalarRightFields.zeta t v / d.scalarRightFields.r t v := by
  have H := transport_limit_is_solution h hD d
  have hr := H.radius_in_ac_ae hab hs
  have hψ := H.scalar_radius_in_ac_ae hab hs
  exact scalar_deriv_of_radius_primitives hab
    ((scalar_limit_absolute_continuity h hD d).2 v a b hab hs) hr.1 hr.2 hψ.2
    (fun t ht => (H.radius_pos (t, v) (hs ⟨ht, rfl⟩)).ne')

/-- On an outgoing canonical section, the incoming scalar density has
the mixed scalar derivative almost everywhere. -/
theorem bv_outgoing_mixed_scalar_density
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    AbsolutelyContinuousOnInterval
      (fun v => d.scalarRightFields.zeta u v / d.scalarRightFields.r u v) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b →
        deriv (fun v => d.scalarRightFields.zeta u v / d.scalarRightFields.r u v) v =
          areaSectionP (areaSectionCoefficients d.scalarRightFields (u, v)) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have ha : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  have hc : 0 < (a - u) / 3 := div_pos (sub_pos.mpr ha.2) (by norm_num)
  have hr (t : ℝ) (ht : t ∈ Icc a b) : (a - u) / 3 ≤ S.r u t :=
    (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 u) (by norm_num)).trans
      (d.radius_lower h (p := (u, t)) (hs ⟨rfl, ht⟩))
  have hsub (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      outSeg u x y ⊆ globalDomain := (outSeg_subsegment hax hxy hyb).trans hs
  have hφ : AbsolutelyContinuousOnInterval (S.phi u) a b :=
    (scalar_limit_absolute_continuity h hD d).1 u a b hab hs
  obtain ⟨hfac, hfd⟩ := mixed_scalar_density_of_primitives hab hc hr hφ
    (fun x y hax hxy hyb => H.radius_out u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => H.scalar_radius_out u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => H.nu_out u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => H.beta_out u x y hxy (hsub x y hax hxy hyb))
  refine ⟨hfac, ?_⟩
  filter_upwards [hfd] with t ht hti
  change deriv (fun v => (S.beta u v - S.nu u v * S.phi u v) / S.r u v) t = _
  rw [ht hti]
  change -(S.lam u t * (S.beta u t - S.nu u t * S.phi u t) +
    S.nu u t * (S.alpha u t - S.lam u t * S.phi u t)) / S.r u t ^ 2 =
    -(S.lam u t * (S.beta u t - S.nu u t * S.phi u t) +
    S.nu u t * (S.alpha u t - S.lam u t * S.phi u t)) * (S.r u t)⁻¹ ^ 2
  rw [div_eq_mul_inv, inv_pow]

/-- On an incoming canonical section, the outgoing scalar density has
the symmetric mixed scalar derivative almost everywhere. -/
theorem bv_incoming_mixed_scalar_density
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    AbsolutelyContinuousOnInterval
      (fun u => d.scalarRightFields.theta u v / d.scalarRightFields.r u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun u => d.scalarRightFields.theta u v / d.scalarRightFields.r u v) u =
          areaSectionP (areaSectionCoefficients d.scalarRightFields (u, v)) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hb : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
  have hc : 0 < (v - b) / 3 := div_pos (sub_pos.mpr hb.2) (by norm_num)
  have hr (t : ℝ) (ht : t ∈ Icc a b) : (v - b) / 3 ≤ S.r t v :=
    (div_le_div_of_nonneg_right (sub_le_sub_left ht.2 v) (by norm_num)).trans
      (d.radius_lower h (p := (t, v)) (hs ⟨ht, rfl⟩))
  have hsub (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      inSeg v x y ⊆ globalDomain := (inSeg_subsegment hax hxy hyb).trans hs
  have hφ : AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b :=
    (scalar_limit_absolute_continuity h hD d).2 v a b hab hs
  obtain ⟨hfac, hfd⟩ := mixed_scalar_density_of_primitives hab hc hr hφ
    (fun x y hax hxy hyb => H.radius_in v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => H.scalar_radius_in v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => H.lam_in v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => H.alpha_in v x y hxy (hsub x y hax hxy hyb))
  refine ⟨hfac, ?_⟩
  filter_upwards [hfd] with t ht hti
  change deriv (fun u => (S.alpha u v - S.lam u v * S.phi u v) / S.r u v) t = _
  rw [ht hti]
  change -(S.nu t v * (S.alpha t v - S.lam t v * S.phi t v) +
    S.lam t v * (S.beta t v - S.nu t v * S.phi t v)) / S.r t v ^ 2 =
    -(S.lam t v * (S.beta t v - S.nu t v * S.phi t v) +
    S.nu t v * (S.alpha t v - S.lam t v * S.phi t v)) * (S.r t v)⁻¹ ^ 2
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- The incoming scalar residual is an outgoing absolutely continuous
primitive. This is the cancellation underlying the β--ν rectangle. -/
theorem bv_zeta_out_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    IntervalPrimitive (d.scalarRightFields.zeta u)
      (fun v => -d.scalarRightFields.nu u v *
        (d.scalarRightFields.theta u v / d.scalarRightFields.r u v)) a b := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  obtain ⟨hn, hnd⟩ := H.nu_out_ac_ae hab hs
  obtain ⟨hβ, hβd⟩ := H.beta_out_ac_ae hab hs
  have hφ : AbsolutelyContinuousOnInterval (S.phi u) a b :=
    (scalar_limit_absolute_continuity h hD d).1 u a b hab hs
  apply IntervalPrimitive.of_ac_ae hab (hβ.fun_sub (hn.fun_mul hφ))
  filter_upwards [hβd, hnd, bv_ae_deriv_phi_out h hD d hab hs,
    hn.ae_deriv_mul hφ, hβ.ae_differentiableAt, (hn.fun_mul hφ).ae_differentiableAt]
    with t hβt hnt hφt hnφt hβdiff hnφdiff ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  change deriv (fun v => S.beta u v - S.nu u v * S.phi u v) t = _
  rw [deriv_fun_sub (hβdiff htu) (hnφdiff htu), hnφt htu,
    hβt ht, hnt ht, hφt ht]
  ring

/-- The outgoing scalar residual is the symmetric incoming primitive. -/
theorem bv_theta_in_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    IntervalPrimitive (fun u => d.scalarRightFields.theta u v)
      (fun u => -d.scalarRightFields.lam u v *
        (d.scalarRightFields.zeta u v / d.scalarRightFields.r u v)) a b := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  obtain ⟨hl, hld⟩ := H.lam_in_ac_ae hab hs
  obtain ⟨hα, hαd⟩ := H.alpha_in_ac_ae hab hs
  have hφ : AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b :=
    (scalar_limit_absolute_continuity h hD d).2 v a b hab hs
  apply IntervalPrimitive.of_ac_ae hab (hα.fun_sub (hl.fun_mul hφ))
  filter_upwards [hαd, hld, bv_ae_deriv_phi_in h hD d hab hs,
    hl.ae_deriv_mul hφ, hα.ae_differentiableAt, (hl.fun_mul hφ).ae_differentiableAt]
    with t hαt hlt hφt hlφt hαdiff hlφdiff ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  change deriv (fun u => S.alpha u v - S.lam u v * S.phi u v) t = _
  rw [deriv_fun_sub (hαdiff htu) (hlφdiff htu), hlφt htu,
    hαt ht, hlt ht, hφt ht]
  ring

/-- The ordinary correction in the incoming ν--φ area primitive is
the outgoing derivative of the incoming scalar flux. -/
theorem bv_incoming_scalar_flux_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    IntervalPrimitive
      (fun v => d.scalarRightFields.nu u v *
        (d.scalarRightFields.zeta u v / d.scalarRightFields.r u v))
      (fun v => areaSectionQ .nuPhi (areaSectionCoefficients d.scalarRightFields (u, v)))
      a b := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  obtain ⟨hn, hnd⟩ := H.nu_out_ac_ae hab hs
  obtain ⟨hf, hfd⟩ := bv_outgoing_mixed_scalar_density h hD d hab hs
  apply IntervalPrimitive.of_ac_ae hab (hn.fun_mul hf)
  filter_upwards [hn.ae_deriv_mul hf, hnd, hfd] with t hprod hnt hft ht
  rw [hprod (by simpa only [uIcc_of_le hab] using ht), hnt ht, hft ht]
  change _ * _ + _ * _ =
    S.nu u t * areaSectionP (areaSectionCoefficients S (u, t)) +
      ((S.beta u t - S.nu u t * S.phi u t) * (S.r u t)⁻¹) *
        IsBVSolution.radiusCoeff S u t
  simp only [Fields.zeta, div_eq_mul_inv]
  ring

/-- The ordinary correction in the outgoing λ--φ area primitive is
the incoming derivative of the outgoing scalar flux. -/
theorem bv_outgoing_scalar_flux_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    IntervalPrimitive
      (fun u => d.scalarRightFields.lam u v *
        (d.scalarRightFields.theta u v / d.scalarRightFields.r u v))
      (fun u => areaSectionQ .lamPhi (areaSectionCoefficients d.scalarRightFields (u, v)))
      a b := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  obtain ⟨hl, hld⟩ := H.lam_in_ac_ae hab hs
  obtain ⟨hf, hfd⟩ := bv_incoming_mixed_scalar_density h hD d hab hs
  apply IntervalPrimitive.of_ac_ae hab (hl.fun_mul hf)
  filter_upwards [hl.ae_deriv_mul hf, hld, hfd] with t hprod hlt hft ht
  rw [hprod (by simpa only [uIcc_of_le hab] using ht), hlt ht, hft ht]
  change _ * _ + _ * _ =
    S.lam t v * areaSectionP (areaSectionCoefficients S (t, v)) +
      ((S.alpha t v - S.lam t v * S.phi t v) * (S.r t v)⁻¹) *
        IsBVSolution.radiusCoeff S t v
  simp only [Fields.theta, div_eq_mul_inv]
  ring

end ChristodoulouBV

end
