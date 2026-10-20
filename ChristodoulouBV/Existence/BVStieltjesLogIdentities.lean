module

public import ChristodoulouBV.Existence.BVStieltjesLogRectangle
public import ChristodoulouBV.Existence.BVStieltjesLogNormalization
public import ChristodoulouBV.Existence.BVStieltjesTransverse
import Mathlib.Tactic

/-!
# Exact canonical logarithmic rectangle identities

These identities keep all canonical endpoint values. Their area primitives
have the complementary section orientation required by (6.8a) and (6.11a).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The incoming-section log-area primitive in physical field notation. -/
theorem bv_area_physical_primitive_phi_beta_nu (S : Fields) (z a b : ℝ) :
    areaPhysicalPrimitive .phiBetaNu S z a b =
      S.theta b z / S.r b z * (S.beta b z / S.nu b z) -
        S.theta a z / S.r a z * (S.beta a z / S.nu a z) -
          ∫ t in a..b, areaSectionQ .phiBetaNu (areaSectionCoefficients S (t, z)) := by
  change ((S.alpha b z - S.lam b z * S.phi b z) * (S.r b z)⁻¹) *
    (S.beta b z * (S.nu b z)⁻¹) -
    ((S.alpha a z - S.lam a z * S.phi a z) * (S.r a z)⁻¹) *
    (S.beta a z * (S.nu a z)⁻¹) - _ = _
  simp only [Fields.theta, div_eq_mul_inv]
  rfl

/-- The outgoing-section log-area primitive in physical field notation. -/
theorem bv_area_physical_primitive_phi_alpha_lam (S : Fields) (z a b : ℝ) :
    areaPhysicalPrimitive .phiAlphaLam S z a b =
      S.zeta z b / S.r z b * (S.alpha z b / S.lam z b) -
        S.zeta z a / S.r z a * (S.alpha z a / S.lam z a) -
          ∫ t in a..b, areaSectionQ .phiAlphaLam (areaSectionCoefficients S (z, t)) := by
  change ((S.beta z b - S.nu z b * S.phi z b) * (S.r z b)⁻¹) *
    (S.alpha z b * (S.lam z b)⁻¹) -
    ((S.beta z a - S.nu z a * S.phi z a) * (S.r z a)⁻¹) *
    (S.alpha z a * (S.lam z a)⁻¹) - _ = _
  simp only [Fields.zeta, div_eq_mul_inv]
  rfl

private theorem outgoing_algebra_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u x y : ℝ} (hu : 0 ≤ u) (hux : u < x) (hxy : x ≤ y)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    IntervalIntegrable (fun t => q (areaSectionCoefficients d.scalarRightFields (u, t)))
      volume x y :=
  bv_area_algebra_intervalIntegrable h hD d .lamPhi hxy (sub_pos.mpr hux)
    (fun _ ht => ⟨hu, hux.trans_le ht.1⟩)
    (fun _ ht => sub_le_sub_right ht.1 u) hq

private theorem incoming_algebra_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyv : y < v)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    IntervalIntegrable (fun t => q (areaSectionCoefficients d.scalarRightFields (t, v)))
      volume x y :=
  bv_area_algebra_intervalIntegrable h hD d .nuPhi hxy (sub_pos.mpr hyv)
    (fun _ ht => ⟨hx.trans ht.1, ht.2.trans_lt hyv⟩)
    (fun _ ht => sub_le_sub_left ht.2 v) hq

/-- The exact outgoing logarithmic rectangle identity, with the
initial edge allowed. The area primitive is incoming in `u`. -/
theorem bv_outgoing_log_rectangle_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u₀ u x y : ℝ}
    (hu₀ : 0 ≤ u₀) (huu : u₀ ≤ u) (hux : u < x) (hxy : x ≤ y) :
    let S := d.scalarRightFields
    (Real.log (S.lam u y) - Real.log (S.lam u x) +
        ∫ t in x..y, bvOutgoingLogCoefficient S u t) -
      (Real.log (S.lam u₀ y) - Real.log (S.lam u₀ x) +
        ∫ t in x..y, bvOutgoingLogCoefficient S u₀ t) =
      -(∫ t in x..y, areaPhysicalPrimitive .phiBetaNu S t u₀ u) := by
  dsimp only
  let S := d.scalarRightFields
  have hsin (t : ℝ) (ht : x ≤ t) : inSeg t u₀ u ⊆ globalDomain := by
    rintro ⟨w, s⟩ ⟨hw, rfl⟩
    exact ⟨hu₀.trans hw.1, hw.2.trans_lt (hux.trans_le ht)⟩
  have hsout (w : ℝ) (hw : w ∈ Icc u₀ u) : outSeg w x y ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨hu₀.trans hw.1, hw.2.trans_lt (hux.trans_le ht.1)⟩
  let qW := fun c : Fin 9 → ℝ => (c 4 - c 1 * c 3) * c 0 * c 3
  let qV := fun c : Fin 9 → ℝ => (c 4 - c 1 * c 3) * c 0 * (c 5 * c 8)
  have hW : Continuous qW := by fun_prop
  have hV : Continuous qV := by fun_prop
  have hWi (w : ℝ) (hw : w ∈ Icc u₀ u) : IntervalIntegrable
      (fun t => S.theta w t / S.r w t * S.phi w t) volume x y := by
    have hi := outgoing_algebra_integrable h hD d (hu₀.trans hw.1)
      (hw.2.trans_lt hux) hxy hW
    change IntervalIntegrable (fun t => S.theta w t * (S.r w t)⁻¹ * S.phi w t)
      volume x y at hi
    simpa only [div_eq_mul_inv] using hi
  have hVi (w : ℝ) (hw : w ∈ Icc u₀ u) : IntervalIntegrable
      (fun t => S.theta w t / S.r w t * (S.beta w t / S.nu w t)) volume x y := by
    have hi := outgoing_algebra_integrable h hD d (hu₀.trans hw.1)
      (hw.2.trans_lt hux) hxy hV
    change IntervalIntegrable (fun t => S.theta w t * (S.r w t)⁻¹ *
      (S.beta w t * (S.nu w t)⁻¹)) volume x y at hi
    simpa only [div_eq_mul_inv] using hi
  have hrect : MapsTo (fun p : ℝ × ℝ => areaPhysicalPoint .lamPhi p.1 p.2)
      (Icc u₀ u ×ˢ Icc x y) globalDomain := by
    intro p hp
    exact ⟨hu₀.trans hp.1.1, hp.1.2.trans_lt (hux.trans_le hp.2.1)⟩
  have hgap (p : ℝ × ℝ) (hp : p ∈ Icc u₀ u ×ˢ Icc x y) :
      x - u ≤ (areaPhysicalPoint .lamPhi p.1 p.2).2 -
        (areaPhysicalPoint .lamPhi p.1 p.2).1 := sub_le_sub hp.2.1 hp.1.2
  have hQ := bv_area_algebra_integrable_rectangle h hD d .lamPhi
    (sub_pos.mpr hux) hrect hgap (area_section_q_continuous .phiBetaNu)
  have hH := bv_area_algebra_integrable_rectangle h hD d .lamPhi
    (sub_pos.mpr hux) hrect hgap (bv_log_square_algebra_continuous true)
  have he := stieltjes_log_rectangle_increment huu hxy
    (U := fun w t => Real.log (S.lam w t) - Real.log (1 - 2 * S.m w t / S.r w t))
    (K := fun w t => S.zeta w t ^ 2 / (S.r w t * S.nu w t))
    (W := fun w t => S.theta w t / S.r w t * S.phi w t)
    (V := fun w t => S.theta w t / S.r w t * (S.beta w t / S.nu w t))
    (Q := fun w t => areaSectionQ .phiBetaNu (areaSectionCoefficients S (w, t)))
    (H := fun w t => bvLogSquareAlgebra true (areaSectionCoefficients S (w, t)))
    (bv_log_normalized_lam_in h hD d huu (hsin x le_rfl)).2
    (bv_log_normalized_lam_in h hD d huu (hsin y hxy)).2
    (fun w hw => (bv_incoming_square_flux_primitive h hD d hxy (hsout w hw)).2)
    (fun t ht => (bv_log_scalar_product_in_primitive h hD d huu (hsin t ht.1)).2)
    (bv_log_normalized_lam_in h hD d huu (hsin x le_rfl)).1
    (bv_log_normalized_lam_in h hD d huu (hsin y hxy)).1
    (hWi u₀ ⟨le_rfl, huu⟩) (hWi u ⟨huu, le_rfl⟩)
    (hVi u₀ ⟨le_rfl, huu⟩) (hVi u ⟨huu, le_rfl⟩) hQ hH
  rw [bv_outgoing_log_increment_normalized h hD d (hu₀.trans huu) hux hxy,
    bv_outgoing_log_increment_normalized h hD d hu₀ (huu.trans_lt hux) hxy]
  simpa only [bv_area_physical_primitive_phi_beta_nu] using he

/-- The exact incoming logarithmic rectangle identity with the corrected
incoming coefficient. Its area primitive is outgoing in `v`. -/
theorem bv_incoming_log_rectangle_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {x y v b : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyv : y < v) (hvb : v ≤ b) :
    let S := d.scalarRightFields
    (Real.log (-S.nu y v) - Real.log (-S.nu x v) +
        ∫ t in x..y, bvIncomingLogCoefficient S t v) -
      (Real.log (-S.nu y b) - Real.log (-S.nu x b) +
        ∫ t in x..y, bvIncomingLogCoefficient S t b) =
      ∫ t in x..y, areaPhysicalPrimitive .phiAlphaLam S t v b := by
  dsimp only
  let S := d.scalarRightFields
  have hsout (t : ℝ) (ht : t ≤ y) (ht0 : 0 ≤ t) : outSeg t v b ⊆ globalDomain := by
    rintro ⟨s, w⟩ ⟨rfl, hw⟩
    exact ⟨ht0, ht.trans_lt (hyv.trans_le hw.1)⟩
  have hsin (w : ℝ) (hw : w ∈ Icc v b) : inSeg w x y ⊆ globalDomain := by
    rintro ⟨t, s⟩ ⟨ht, rfl⟩
    exact ⟨hx.trans ht.1, ht.2.trans_lt (hyv.trans_le hw.1)⟩
  let qW := fun c : Fin 9 → ℝ => (c 5 - c 2 * c 3) * c 0 * c 3
  let qV := fun c : Fin 9 → ℝ => (c 5 - c 2 * c 3) * c 0 * (c 4 * c 7)
  have hW : Continuous qW := by fun_prop
  have hV : Continuous qV := by fun_prop
  have hWi (w : ℝ) (hw : w ∈ Icc v b) : IntervalIntegrable
      (fun t => S.zeta t w / S.r t w * S.phi t w) volume x y := by
    have hi := incoming_algebra_integrable h hD d hx hxy (hyv.trans_le hw.1) hW
    change IntervalIntegrable (fun t => S.zeta t w * (S.r t w)⁻¹ * S.phi t w)
      volume x y at hi
    simpa only [div_eq_mul_inv] using hi
  have hVi (w : ℝ) (hw : w ∈ Icc v b) : IntervalIntegrable
      (fun t => S.zeta t w / S.r t w * (S.alpha t w / S.lam t w)) volume x y := by
    have hi := incoming_algebra_integrable h hD d hx hxy (hyv.trans_le hw.1) hV
    change IntervalIntegrable (fun t => S.zeta t w * (S.r t w)⁻¹ *
      (S.alpha t w * (S.lam t w)⁻¹)) volume x y at hi
    simpa only [div_eq_mul_inv] using hi
  have hrect : MapsTo (fun p : ℝ × ℝ => areaPhysicalPoint .nuPhi p.1 p.2)
      (Icc v b ×ˢ Icc x y) globalDomain := by
    intro p hp
    exact ⟨hx.trans hp.2.1, hp.2.2.trans_lt (hyv.trans_le hp.1.1)⟩
  have hgap (p : ℝ × ℝ) (hp : p ∈ Icc v b ×ˢ Icc x y) :
      v - y ≤ (areaPhysicalPoint .nuPhi p.1 p.2).2 -
        (areaPhysicalPoint .nuPhi p.1 p.2).1 := sub_le_sub hp.1.1 hp.2.2
  have hQ := bv_area_algebra_integrable_rectangle h hD d .nuPhi
    (sub_pos.mpr hyv) hrect hgap (area_section_q_continuous .phiAlphaLam)
  have hH := bv_area_algebra_integrable_rectangle h hD d .nuPhi
    (sub_pos.mpr hyv) hrect hgap (bv_log_square_algebra_continuous false)
  have he := stieltjes_log_rectangle_increment hvb hxy
    (U := fun w t => Real.log (-S.nu t w) - Real.log (1 - 2 * S.m t w / S.r t w))
    (K := fun w t => S.theta t w ^ 2 / (S.r t w * S.lam t w))
    (W := fun w t => S.zeta t w / S.r t w * S.phi t w)
    (V := fun w t => S.zeta t w / S.r t w * (S.alpha t w / S.lam t w))
    (Q := fun w t => areaSectionQ .phiAlphaLam (areaSectionCoefficients S (t, w)))
    (H := fun w t => bvLogSquareAlgebra false (areaSectionCoefficients S (t, w)))
    (bv_log_normalized_nu_out h hD d hvb (hsout x hxy hx)).2
    (bv_log_normalized_nu_out h hD d hvb (hsout y le_rfl (hx.trans hxy))).2
    (fun w hw => (bv_outgoing_square_flux_primitive h hD d hxy (hsin w hw)).2)
    (fun t ht => (bv_log_scalar_product_out_primitive h hD d hvb
      (hsout t ht.2 (hx.trans ht.1))).2)
    (bv_log_normalized_nu_out h hD d hvb (hsout x hxy hx)).1
    (bv_log_normalized_nu_out h hD d hvb (hsout y le_rfl (hx.trans hxy))).1
    (hWi v ⟨le_rfl, hvb⟩) (hWi b ⟨hvb, le_rfl⟩)
    (hVi v ⟨le_rfl, hvb⟩) (hVi b ⟨hvb, le_rfl⟩) hQ hH
  rw [bv_incoming_log_increment_normalized h hD d hx hxy hyv,
    bv_incoming_log_increment_normalized h hD d hx hxy (hyv.trans_le hvb)]
  have he' :
      ((Real.log (-S.nu y b) - Real.log (1 - 2 * S.m y b / S.r y b)) -
        (Real.log (-S.nu x b) - Real.log (1 - 2 * S.m x b / S.r x b)) +
        ∫ t in x..y, S.zeta t b / S.r t b * S.phi t b -
          S.zeta t b / S.r t b * (S.alpha t b / S.lam t b)) -
      ((Real.log (-S.nu y v) - Real.log (1 - 2 * S.m y v / S.r y v)) -
        (Real.log (-S.nu x v) - Real.log (1 - 2 * S.m x v / S.r x v)) +
        ∫ t in x..y, S.zeta t v / S.r t v * S.phi t v -
          S.zeta t v / S.r t v * (S.alpha t v / S.lam t v)) =
      -(∫ t in x..y, areaPhysicalPrimitive .phiAlphaLam S t v b) := by
    simpa only [bv_area_physical_primitive_phi_alpha_lam] using he
  linarith only [he']

end ChristodoulouBV

end
