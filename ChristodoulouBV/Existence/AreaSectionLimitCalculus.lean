module

public import ChristodoulouBV.Existence.AreaSectionLimitCore
public import ChristodoulouBV.BVSolution.PrimitiveCalculus
import Mathlib.Tactic

/-!
# The a.e. mixed scalar density on the actual limit sections

The cancellation of the mixed radius coefficient proves the weak scalar
identity from the frozen primitives. In particular it supplies the
derivative density used in the concrete area primitives without assuming
classical differentiability at a BV jump.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The mixed scalar identity follows from the four interval primitives
and scalar absolute continuity on a section, with an a.e. derivative.
The mixed radius coefficient cancels in the product rule. -/
theorem mixed_scalar_density_of_primitives
    {r l n α β φ ρ : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hr : ∀ t ∈ Icc a b, c ≤ r t)
    (hφ : AbsolutelyContinuousOnInterval φ a b)
    (hR : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive r l x y)
    (hΨ : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      IntervalPrimitive (fun t => r t * φ t) α x y)
    (hN : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive n ρ x y)
    (hB : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      IntervalPrimitive β (fun t => ρ t * φ t) x y) :
    AbsolutelyContinuousOnInterval (fun t => (β t - n t * φ t) / r t) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun t => (β t - n t * φ t) / r t) t =
          -(l t * (β t - n t * φ t) + n t * (α t - l t * φ t)) / r t ^ 2 := by
  obtain ⟨hRac, hRd⟩ := IntervalPrimitive.ac_ae_of_subsegments hab hR
  obtain ⟨hΨac, hΨd⟩ := IntervalPrimitive.ac_ae_of_subsegments hab hΨ
  obtain ⟨hNac, hNd⟩ := IntervalPrimitive.ac_ae_of_subsegments hab hN
  obtain ⟨hBac, hBd⟩ := IntervalPrimitive.ac_ae_of_subsegments hab hB
  have hnum := hBac.fun_sub (hNac.fun_mul hφ)
  obtain ⟨hfac, hfd⟩ := hnum.div_and_ae_deriv hRac hc (by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (hr t ht).trans (le_abs_self _))
  refine ⟨hfac, ?_⟩
  filter_upwards [hRd, hΨd, hNd, hBd, hRac.ae_deriv_mul hφ,
    hNac.ae_deriv_mul hφ, hfd, hBac.ae_differentiableAt,
    (hNac.fun_mul hφ).ae_differentiableAt] with t hrt hψt hnt hβt hrφ hnφ hft hβdiff hnφdiff ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  have hr0 : r t ≠ 0 := (hc.trans_le (hr t ht)).ne'
  have hφd : deriv φ t = (α t - l t * φ t) / r t := by
    have hid := hrφ htu
    rw [hψt ht, hrt ht] at hid
    exact (eq_div_iff hr0).mpr (by linarith only [hid])
  rw [hft htu, deriv_fun_sub (hβdiff htu) (hnφdiff htu), hnφ htu,
    hβt ht, hnt ht, hrt ht, hφd]
  field_simp
  ring

/-- On every outgoing raw limit section, `ζ/r` is absolutely continuous
in `v` and has the mixed scalar density used by Lemma 6.1 almost
everywhere. The initial outgoing section is included. -/
theorem raw_outgoing_mixed_scalar_density
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    AbsolutelyContinuousOnInterval
      (fun v => d.rawFields.zeta u v / d.rawFields.r u v) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b →
        deriv (fun v => d.rawFields.zeta u v / d.rawFields.r u v) v =
          areaSectionP (areaSectionCoefficients d.rawFields (u, v)) := by
  have ha : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  have hc : 0 < (a - u) / 3 := div_pos (sub_pos.mpr ha.2) (by norm_num)
  have hr (t : ℝ) (ht : t ∈ Icc a b) : (a - u) / 3 ≤ d.rawFields.r u t :=
    (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 u) (by norm_num)).trans
      (d.radius_lower h (p := (u, t)) (hs ⟨rfl, ht⟩))
  have hsub (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      outSeg u x y ⊆ globalDomain := (outSeg_subsegment hax hxy hyb).trans hs
  have hR := (radius_primitive_limit h hD d).1
  have hΨ := (s6_scalar_primitive h hD d).1
  have hN := (raw_expansion_primitive_limit h d).2
  have hB := (raw_alpha_beta_transport_limit h d).2
  have hφ := (scalar_limit_absolute_continuity h hD d).1 u a b hab hs
  obtain ⟨hfac, hfd⟩ := mixed_scalar_density_of_primitives hab hc hr hφ
    (fun x y hax hxy hyb => hR u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => hΨ u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => hN u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => hB u x y hxy (hsub x y hax hxy hyb))
  refine ⟨hfac, ?_⟩
  filter_upwards [hfd] with t ht hti
  change deriv (fun v => (d.rawFields.beta u v -
    d.rawFields.nu u v * d.rawFields.phi u v) / d.rawFields.r u v) t = _
  rw [ht hti]
  change -(d.rawFields.lam u t *
    (d.rawFields.beta u t - d.rawFields.nu u t * d.rawFields.phi u t) +
    d.rawFields.nu u t *
    (d.rawFields.alpha u t - d.rawFields.lam u t * d.rawFields.phi u t)) /
      d.rawFields.r u t ^ 2 =
    -(d.rawFields.lam u t *
    (d.rawFields.beta u t - d.rawFields.nu u t * d.rawFields.phi u t) +
    d.rawFields.nu u t *
    (d.rawFields.alpha u t - d.rawFields.lam u t * d.rawFields.phi u t)) *
      (d.rawFields.r u t)⁻¹ ^ 2
  rw [div_eq_mul_inv, inv_pow]

/-- On every incoming raw limit section, `θ/r` is absolutely continuous
in `u` with the same symmetric mixed scalar density almost everywhere. -/
theorem raw_incoming_mixed_scalar_density
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    AbsolutelyContinuousOnInterval
      (fun u => d.rawFields.theta u v / d.rawFields.r u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun u => d.rawFields.theta u v / d.rawFields.r u v) u =
          areaSectionP (areaSectionCoefficients d.rawFields (u, v)) := by
  have hb : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
  have hc : 0 < (v - b) / 3 := div_pos (sub_pos.mpr hb.2) (by norm_num)
  have hr (t : ℝ) (ht : t ∈ Icc a b) : (v - b) / 3 ≤ d.rawFields.r t v :=
    (div_le_div_of_nonneg_right (sub_le_sub_left ht.2 v) (by norm_num)).trans
      (d.radius_lower h (p := (t, v)) (hs ⟨ht, rfl⟩))
  have hsub (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      inSeg v x y ⊆ globalDomain := (inSeg_subsegment hax hxy hyb).trans hs
  have hR := (radius_primitive_limit h hD d).2
  have hΨ := (s6_scalar_primitive h hD d).2
  have hN := (raw_expansion_primitive_limit h d).1
  have hB := (raw_alpha_beta_transport_limit h d).1
  have hφ := (scalar_limit_absolute_continuity h hD d).2 v a b hab hs
  obtain ⟨hfac, hfd⟩ := mixed_scalar_density_of_primitives hab hc hr hφ
    (fun x y hax hxy hyb => hR v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => hΨ v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => hN v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => hB v x y hxy (hsub x y hax hxy hyb))
  refine ⟨hfac, ?_⟩
  filter_upwards [hfd] with t ht hti
  change deriv (fun u => (d.rawFields.alpha u v -
    d.rawFields.lam u v * d.rawFields.phi u v) / d.rawFields.r u v) t = _
  rw [ht hti]
  change -(d.rawFields.nu t v *
    (d.rawFields.alpha t v - d.rawFields.lam t v * d.rawFields.phi t v) +
    d.rawFields.lam t v *
    (d.rawFields.beta t v - d.rawFields.nu t v * d.rawFields.phi t v)) /
      d.rawFields.r t v ^ 2 =
    -(d.rawFields.lam t v *
    (d.rawFields.beta t v - d.rawFields.nu t v * d.rawFields.phi t v) +
    d.rawFields.nu t v *
    (d.rawFields.alpha t v - d.rawFields.lam t v * d.rawFields.phi t v)) *
      (d.rawFields.r t v)⁻¹ ^ 2
  rw [div_eq_mul_inv, inv_pow]
  ring

end ChristodoulouBV

end
