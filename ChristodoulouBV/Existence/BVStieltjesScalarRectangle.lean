module

public import ChristodoulouBV.Existence.BVStieltjesRectangle
public import ChristodoulouBV.Existence.BVStieltjesMeasurable
import Mathlib.Tactic

/-!
# Scalar Stieltjes rectangle identities for the canonical limit

The endpoints are arbitrary points of the rectangle. The ordinary
correction is jointly integrable by the canonical off-axis majorants.
The identities therefore retain the right-continuous values at jumps.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The ν--φ area primitive in scalar-flux notation. -/
theorem area_physical_primitive_nu_phi (S : Fields) (w c x : ℝ) :
    areaPhysicalPrimitive .nuPhi S w c x =
      S.nu x w * (S.theta x w / S.r x w) -
        S.nu c w * (S.theta c w / S.r c w) -
          ∫ t in c..x, areaSectionQ .nuPhi (areaSectionCoefficients S (t, w)) := by
  change ((S.alpha x w - S.lam x w * S.phi x w) * (S.r x w)⁻¹) * S.nu x w -
    ((S.alpha c w - S.lam c w * S.phi c w) * (S.r c w)⁻¹) * S.nu c w -
    (∫ t in c..x, areaSectionQ .nuPhi (areaSectionCoefficients S (t, w))) = _
  simp only [Fields.theta, div_eq_mul_inv]
  ring

/-- The λ--φ area primitive in symmetric scalar-flux notation. -/
theorem area_physical_primitive_lam_phi (S : Fields) (w c x : ℝ) :
    areaPhysicalPrimitive .lamPhi S w c x =
      S.lam w x * (S.zeta w x / S.r w x) -
        S.lam w c * (S.zeta w c / S.r w c) -
          ∫ t in c..x, areaSectionQ .lamPhi (areaSectionCoefficients S (w, t)) := by
  change ((S.beta w x - S.nu w x * S.phi w x) * (S.r w x)⁻¹) * S.lam w x -
    ((S.beta w c - S.nu w c * S.phi w c) * (S.r w c)⁻¹) * S.lam w c -
    (∫ t in c..x, areaSectionQ .lamPhi (areaSectionCoefficients S (w, t))) = _
  simp only [Fields.zeta, div_eq_mul_inv]
  ring

/-- The exact incoming scalar rectangle identity for the canonical
fields. No exceptional endpoint set occurs in this statement. -/
theorem bv_beta_rectangle_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {x₁ x₂ v b : ℝ}
    (hx₁ : 0 ≤ x₁) (hxx : x₁ ≤ x₂) (hxv : x₂ < v) (hvb : v ≤ b) :
    let S := d.scalarRightFields
    (S.zeta x₂ v - S.zeta x₁ v +
        ∫ x in x₁..x₂, S.nu x v * (S.zeta x v / S.r x v)) -
      (S.zeta x₂ b - S.zeta x₁ b +
        ∫ x in x₁..x₂, S.nu x b * (S.zeta x b / S.r x b)) =
      ∫ w in v..b, areaPhysicalPrimitive .nuPhi S w x₁ x₂ := by
  let S := d.scalarRightFields
  have hsout (x : ℝ) (hx : x ∈ Icc x₁ x₂) : outSeg x v b ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨hx₁.trans hx.1, hx.2.trans_lt (hxv.trans_le ht.1)⟩
  have hsin (w : ℝ) (hw : v ≤ w) : inSeg w x₁ x₂ ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨hs, rfl⟩
    exact ⟨hx₁.trans hs.1, hs.2.trans_lt (hxv.trans_le hw)⟩
  have hrect : MapsTo (fun p : ℝ × ℝ => areaPhysicalPoint .nuPhi p.1 p.2)
      (Icc v b ×ˢ Icc x₁ x₂) globalDomain := by
    intro p hp
    exact ⟨hx₁.trans hp.2.1, hp.2.2.trans_lt (hxv.trans_le hp.1.1)⟩
  have hgap (p : ℝ × ℝ) (hp : p ∈ Icc v b ×ˢ Icc x₁ x₂) :
      v - x₂ ≤ (areaPhysicalPoint .nuPhi p.1 p.2).2 -
        (areaPhysicalPoint .nuPhi p.1 p.2).1 := by
    change v - x₂ ≤ p.1 - p.2
    exact sub_le_sub hp.1.1 hp.2.2
  have hU (x : ℝ) (hx : x ∈ Icc x₁ x₂) :=
    bv_zeta_out_primitive h hD d hvb (hsout x hx)
  have hH (x : ℝ) (hx : x ∈ Icc x₁ x₂) :=
    bv_incoming_scalar_flux_primitive h hD d hvb (hsout x hx)
  let flux := fun c : Fin 9 → ℝ => c 2 * ((c 5 - c 2 * c 3) * c 0)
  have hcflux : Continuous flux := by fun_prop
  have hHi (w : ℝ) (hw : v ≤ w) : IntervalIntegrable
      (fun x => S.nu x w * (S.zeta x w / S.r x w)) volume x₁ x₂ := by
    have hi := bv_area_algebra_intervalIntegrable h hD d .nuPhi hxx
      (sub_pos.mpr hxv) (fun x hx => hsin w hw ⟨hx, rfl⟩)
      (fun x hx => by
        change v - x₂ ≤ w - x
        exact sub_le_sub hw hx.2) hcflux
    change IntervalIntegrable
      (fun x => S.nu x w * ((S.beta x w - S.nu x w * S.phi x w) * (S.r x w)⁻¹))
      volume x₁ x₂ at hi
    simpa only [Fields.zeta, div_eq_mul_inv] using hi
  have hQi := bv_area_algebra_integrable_rectangle h hD d .nuPhi
    (sub_pos.mpr hxv) hrect hgap (area_section_q_continuous .nuPhi)
  have he := stieltjes_rectangle_increment hvb hxx
    (U := fun w x => S.zeta x w)
    (G := fun w x => S.nu x w * (S.theta x w / S.r x w))
    (H := fun w x => S.nu x w * (S.zeta x w / S.r x w))
    (Q := fun w x => areaSectionQ .nuPhi (areaSectionCoefficients S (x, w)))
    (by simpa only [neg_mul, intervalIntegral.integral_neg] using
      (hU x₁ ⟨le_rfl, hxx⟩).2)
    (by simpa only [neg_mul, intervalIntegral.integral_neg] using
      (hU x₂ ⟨hxx, le_rfl⟩).2)
    (fun x hx => (hH x hx).2)
    (by
      convert (hU x₁ ⟨le_rfl, hxx⟩).1.neg using 1
      funext w
      simp only [Pi.neg_apply, neg_mul, neg_neg, S])
    (by
      convert (hU x₂ ⟨hxx, le_rfl⟩).1.neg using 1
      funext w
      simp only [Pi.neg_apply, neg_mul, neg_neg, S])
    (hHi v le_rfl) (hHi b hvb) hQi
  simpa only [area_physical_primitive_nu_phi] using he

/-- The exact outgoing scalar rectangle identity, including the
initial edge when the lower transverse coordinate is zero. -/
theorem bv_alpha_rectangle_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u₁ u₂ x₁ x₂ : ℝ}
    (hu₁ : 0 ≤ u₁) (huu : u₁ ≤ u₂) (hux : u₂ < x₁) (hxx : x₁ ≤ x₂) :
    let S := d.scalarRightFields
    (S.theta u₁ x₂ - S.theta u₁ x₁ +
        ∫ x in x₁..x₂, S.lam u₁ x * (S.theta u₁ x / S.r u₁ x)) -
      (S.theta u₂ x₂ - S.theta u₂ x₁ +
        ∫ x in x₁..x₂, S.lam u₂ x * (S.theta u₂ x / S.r u₂ x)) =
      ∫ w in u₁..u₂, areaPhysicalPrimitive .lamPhi S w x₁ x₂ := by
  let S := d.scalarRightFields
  have hsin (x : ℝ) (hx : x ∈ Icc x₁ x₂) : inSeg x u₁ u₂ ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨hs, rfl⟩
    exact ⟨hu₁.trans hs.1, hs.2.trans_lt (hux.trans_le hx.1)⟩
  have hsout (w : ℝ) (hw : w ≤ u₂) (hw0 : 0 ≤ w) :
      outSeg w x₁ x₂ ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨hw0, hw.trans_lt (hux.trans_le ht.1)⟩
  have hrect : MapsTo (fun p : ℝ × ℝ => areaPhysicalPoint .lamPhi p.1 p.2)
      (Icc u₁ u₂ ×ˢ Icc x₁ x₂) globalDomain := by
    intro p hp
    exact ⟨hu₁.trans hp.1.1, hp.1.2.trans_lt (hux.trans_le hp.2.1)⟩
  have hgap (p : ℝ × ℝ) (hp : p ∈ Icc u₁ u₂ ×ˢ Icc x₁ x₂) :
      x₁ - u₂ ≤ (areaPhysicalPoint .lamPhi p.1 p.2).2 -
        (areaPhysicalPoint .lamPhi p.1 p.2).1 := by
    change x₁ - u₂ ≤ p.2 - p.1
    exact sub_le_sub hp.2.1 hp.1.2
  have hU (x : ℝ) (hx : x ∈ Icc x₁ x₂) :=
    bv_theta_in_primitive h hD d huu (hsin x hx)
  have hH (x : ℝ) (hx : x ∈ Icc x₁ x₂) :=
    bv_outgoing_scalar_flux_primitive h hD d huu (hsin x hx)
  let flux := fun c : Fin 9 → ℝ => c 1 * ((c 4 - c 1 * c 3) * c 0)
  have hcflux : Continuous flux := by fun_prop
  have hHi (w : ℝ) (hw : w ∈ Icc u₁ u₂) : IntervalIntegrable
      (fun x => S.lam w x * (S.theta w x / S.r w x)) volume x₁ x₂ := by
    have hi := bv_area_algebra_intervalIntegrable h hD d .lamPhi hxx
      (sub_pos.mpr hux) (fun x hx => hsout w hw.2 (hu₁.trans hw.1) ⟨rfl, hx⟩)
      (fun x hx => by
        change x₁ - u₂ ≤ x - w
        exact sub_le_sub hx.1 hw.2) hcflux
    change IntervalIntegrable
      (fun x => S.lam w x * ((S.alpha w x - S.lam w x * S.phi w x) * (S.r w x)⁻¹))
      volume x₁ x₂ at hi
    simpa only [Fields.theta, div_eq_mul_inv] using hi
  have hQi := bv_area_algebra_integrable_rectangle h hD d .lamPhi
    (sub_pos.mpr hux) hrect hgap (area_section_q_continuous .lamPhi)
  have he := stieltjes_rectangle_increment huu hxx
    (U := fun w x => S.theta w x)
    (G := fun w x => S.lam w x * (S.zeta w x / S.r w x))
    (H := fun w x => S.lam w x * (S.theta w x / S.r w x))
    (Q := fun w x => areaSectionQ .lamPhi (areaSectionCoefficients S (w, x)))
    (by simpa only [neg_mul, intervalIntegral.integral_neg] using
      (hU x₁ ⟨le_rfl, hxx⟩).2)
    (by simpa only [neg_mul, intervalIntegral.integral_neg] using
      (hU x₂ ⟨hxx, le_rfl⟩).2)
    (fun x hx => (hH x hx).2)
    (by
      convert (hU x₁ ⟨le_rfl, hxx⟩).1.neg using 1
      funext w
      simp only [Pi.neg_apply, neg_mul, neg_neg, S])
    (by
      convert (hU x₂ ⟨hxx, le_rfl⟩).1.neg using 1
      funext w
      simp only [Pi.neg_apply, neg_mul, neg_neg, S])
    (hHi u₁ ⟨le_rfl, huu⟩) (hHi u₂ ⟨huu, le_rfl⟩) hQi
  simpa only [area_physical_primitive_lam_phi] using he

end ChristodoulouBV

end
