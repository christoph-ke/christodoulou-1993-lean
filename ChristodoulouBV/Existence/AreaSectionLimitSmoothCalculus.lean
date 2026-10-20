module

public import ChristodoulouBV.Existence.AreaSectionLimitCalculus
public import ChristodoulouBV.Existence.AreaSectionLimitMeasureCore
import Mathlib.Tactic

/-!
# Mixed scalar densities for the original smooth sequence

The same primitive calculation used for the raw limit applies to every
smooth approximant. Its quantitative derivative bound therefore comes
from the uniform algebraic coefficient bounds.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem scalar_ac_of_primitives
    {r φ l α : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hr : ∀ t ∈ Icc a b, c ≤ r t)
    (hR : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive r l x y)
    (hΨ : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      IntervalPrimitive (fun t => r t * φ t) α x y) :
    AbsolutelyContinuousOnInterval φ a b := by
  have hRac := (IntervalPrimitive.ac_ae_of_subsegments hab hR).1
  have hΨac := (IntervalPrimitive.ac_ae_of_subsegments hab hΨ).1
  have hφac := (hΨac.div_and_ae_deriv hRac hc (fun t ht =>
    (hr t (by simpa only [uIcc_of_le hab] using ht)).trans (le_abs_self _))).1
  apply hφac.congr
  intro t ht
  have hr0 : r t ≠ 0 := (hc.trans_le (hr t (by simpa only [uIcc_of_le hab] using ht))).ne'
  field_simp

/-- The original smooth outgoing scalar density has the same mixed
derivative as the raw limiting density, almost everywhere on a closed
section, including `u=0`. -/
theorem SmoothSolutionBounds.outgoing_mixed_scalar_density
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    AbsolutelyContinuousOnInterval (fun v => S.zeta u v / S.r u v) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b → deriv (fun v => S.zeta u v / S.r u v) v =
        areaSectionP (areaSectionCoefficients S (u, v)) := by
  have ha : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  have hc : 0 < (a - u) / 3 := div_pos (sub_pos.mpr ha.2) (by norm_num)
  have hr (t : ℝ) (ht : t ∈ Icc a b) : (a - u) / 3 ≤ S.r u t :=
    (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 u) (by norm_num)).trans
      (h.radius_lower (p := (u, t)) (hs ⟨rfl, ht⟩))
  have hsub (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      outSeg u x y ⊆ globalDomain := (outSeg_subsegment hax hxy hyb).trans hs
  have hR := fun x y hax hxy hyb => h.solution.solution.radius_out u x y hxy (hsub x y hax hxy hyb)
  have hΨ := fun x y hax hxy hyb =>
    h.solution.solution.scalar_radius_out u x y hxy (hsub x y hax hxy hyb)
  have hφ := scalar_ac_of_primitives hab hc hr hR hΨ
  obtain ⟨hfac, hfd⟩ := mixed_scalar_density_of_primitives hab hc hr hφ hR hΨ
    (fun x y hax hxy hyb => h.solution.solution.nu_out u x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => h.solution.solution.beta_out u x y hxy (hsub x y hax hxy hyb))
  refine ⟨hfac, ?_⟩
  filter_upwards [hfd] with t ht hti
  change deriv (fun v => (S.beta u v - S.nu u v * S.phi u v) / S.r u v) t = _
  rw [ht hti]
  change -(S.lam u t * (S.beta u t - S.nu u t * S.phi u t) +
    S.nu u t * (S.alpha u t - S.lam u t * S.phi u t)) / S.r u t ^ 2 =
    -(S.lam u t * (S.beta u t - S.nu u t * S.phi u t) +
    S.nu u t * (S.alpha u t - S.lam u t * S.phi u t)) * (S.r u t)⁻¹ ^ 2
  rw [div_eq_mul_inv, inv_pow]

/-- The symmetric incoming mixed scalar density for every smooth
approximant. -/
theorem SmoothSolutionBounds.incoming_mixed_scalar_density
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    AbsolutelyContinuousOnInterval (fun u => S.theta u v / S.r u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b → deriv (fun u => S.theta u v / S.r u v) u =
        areaSectionP (areaSectionCoefficients S (u, v)) := by
  have hb : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
  have hc : 0 < (v - b) / 3 := div_pos (sub_pos.mpr hb.2) (by norm_num)
  have hr (t : ℝ) (ht : t ∈ Icc a b) : (v - b) / 3 ≤ S.r t v :=
    (div_le_div_of_nonneg_right (sub_le_sub_left ht.2 v) (by norm_num)).trans
      (h.radius_lower (p := (t, v)) (hs ⟨ht, rfl⟩))
  have hsub (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      inSeg v x y ⊆ globalDomain := (inSeg_subsegment hax hxy hyb).trans hs
  have hR := fun x y hax hxy hyb => h.solution.solution.radius_in v x y hxy (hsub x y hax hxy hyb)
  have hΨ := fun x y hax hxy hyb =>
    h.solution.solution.scalar_radius_in v x y hxy (hsub x y hax hxy hyb)
  have hφ := scalar_ac_of_primitives hab hc hr hR hΨ
  obtain ⟨hfac, hfd⟩ := mixed_scalar_density_of_primitives hab hc hr hφ hR hΨ
    (fun x y hax hxy hyb => h.solution.solution.lam_in v x y hxy (hsub x y hax hxy hyb))
    (fun x y hax hxy hyb => h.solution.solution.alpha_in v x y hxy (hsub x y hax hxy hyb))
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

end ChristodoulouBV

end
