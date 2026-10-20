module

public import ChristodoulouBV.Existence.BVStieltjesLogResidual
import Mathlib.Tactic

/-!
# Normalization of logarithmic residual increments

The ordinary mass-gap primitive moves the mass-ratio part of `g` into
the logarithmic potential. This keeps the remaining endpoint product in
the same orientation as the analytic area carrier.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Increments of the outgoing logarithmic residual with a right basepoint. -/
theorem bv_outgoing_log_residual_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b x y : ℝ} (hu : 0 ≤ u) (hux : u < x)
    (hxy : x ≤ y) (hyb : y ≤ b) :
    bvOutgoingLogResidual d.scalarRightFields u b y -
      bvOutgoingLogResidual d.scalarRightFields u b x =
      Real.log (d.scalarRightFields.lam u y) - Real.log (d.scalarRightFields.lam u x) +
        ∫ t in x..y, bvOutgoingLogCoefficient d.scalarRightFields u t := by
  have hi := intervalIntegral.integral_interval_sub_left
    (bv_outgoing_log_coefficient_integrable h hD d hu (hux.trans_le hxy) hyb).symm
    (bv_outgoing_log_coefficient_integrable h hD d hu hux (hxy.trans hyb)).symm
  dsimp only [bvOutgoingLogResidual]
  linarith only [hi]

/-- Increments of the corrected incoming logarithmic residual with a left basepoint. -/
theorem bv_incoming_log_residual_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a x y : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hxy : x ≤ y) (hyv : y < v) :
    bvIncomingLogResidual d.scalarRightFields v a y -
      bvIncomingLogResidual d.scalarRightFields v a x =
      Real.log (-d.scalarRightFields.nu y v) - Real.log (-d.scalarRightFields.nu x v) +
        ∫ t in x..y, bvIncomingLogCoefficient d.scalarRightFields t v := by
  have hi := intervalIntegral.integral_interval_sub_left
    (bv_incoming_log_coefficient_integrable h hD d ha (hax.trans hxy) hyv)
    (bv_incoming_log_coefficient_integrable h hD d ha hax (hxy.trans_lt hyv))
  dsimp only [bvIncomingLogResidual]
  linarith only [hi]

/-- The outgoing residual increment in normalized-potential form.
The remaining product is `φᵥ (φ - β/ν)`, so the area is incoming in `u`. -/
theorem bv_outgoing_log_increment_normalized
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u x y : ℝ} (hu : 0 ≤ u) (hux : u < x) (hxy : x ≤ y) :
    let S := d.scalarRightFields
    Real.log (S.lam u y) - Real.log (S.lam u x) +
        (∫ t in x..y, bvOutgoingLogCoefficient S u t) =
      (Real.log (S.lam u y) - Real.log (1 - 2 * S.m u y / S.r u y)) -
        (Real.log (S.lam u x) - Real.log (1 - 2 * S.m u x / S.r u x)) +
        ∫ t in x..y, S.theta u t / S.r u t * S.phi u t -
          S.theta u t / S.r u t * (S.beta u t / S.nu u t) := by
  let S := d.scalarRightFields
  have hs : outSeg u x y ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨hu, hux.trans_le ht.1⟩
  have hg := bv_log_mass_gap_out h hD d hxy hs
  let W := fun t => S.theta u t / S.r u t * S.phi u t -
    S.theta u t / S.r u t * (S.beta u t / S.nu u t)
  have hp : IntervalPrimitive (fun t => Real.log (1 - 2 * S.m u t / S.r u t))
      (fun t => W t - bvOutgoingLogCoefficient S u t) x y := by
    apply IntervalPrimitive.of_ac_ae hxy hg.1
    filter_upwards [hg.2] with t ht htI
    rw [ht htI]
    dsimp only [S]
    have hl : S.lam u t ≠ 0 :=
      (limit_signs_conformal h hD d (u, t) (hs ⟨rfl, htI⟩)).2.1.ne'
    have hn : S.nu u t ≠ 0 :=
      (limit_signs_conformal h hD d (u, t) (hs ⟨rfl, htI⟩)).2.2.1.ne
    dsimp only [W, S, bvOutgoingLogCoefficient, sourceLogCorrection, Fields.zeta]
    dsimp only [S] at hl hn
    field_simp [hl, hn]
    ring
  have hgi := bv_outgoing_log_coefficient_integrable h hD d hu hux hxy
  have hWi : IntervalIntegrable W volume x y := by
    convert hp.1.add hgi using 1
    funext t
    ring
  have he := hp.2
  rw [intervalIntegral.integral_sub hWi hgi] at he
  change _ = _ + ∫ t in x..y, W t
  linarith only [he]

/-- The incoming normalized form uses the corrected negative sign of
`f*`; its area endpoint product is outgoing in `v`. -/
theorem bv_incoming_log_increment_normalized
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyv : y < v) :
    let S := d.scalarRightFields
    Real.log (-S.nu y v) - Real.log (-S.nu x v) +
        (∫ t in x..y, bvIncomingLogCoefficient S t v) =
      (Real.log (-S.nu y v) - Real.log (1 - 2 * S.m y v / S.r y v)) -
        (Real.log (-S.nu x v) - Real.log (1 - 2 * S.m x v / S.r x v)) +
        ∫ t in x..y, S.zeta t v / S.r t v * S.phi t v -
          S.zeta t v / S.r t v * (S.alpha t v / S.lam t v) := by
  let S := d.scalarRightFields
  have hs : inSeg v x y ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨ht, rfl⟩
    exact ⟨hx.trans ht.1, ht.2.trans_lt hyv⟩
  have hg := bv_log_mass_gap_in h hD d hxy hs
  let W := fun t => S.zeta t v / S.r t v * S.phi t v -
    S.zeta t v / S.r t v * (S.alpha t v / S.lam t v)
  have hp : IntervalPrimitive (fun t => Real.log (1 - 2 * S.m t v / S.r t v))
      (fun t => W t - bvIncomingLogCoefficient S t v) x y := by
    apply IntervalPrimitive.of_ac_ae hxy hg.1
    filter_upwards [hg.2] with t ht htI
    rw [ht htI]
    dsimp only [S]
    have hl : S.lam t v ≠ 0 :=
      (limit_signs_conformal h hD d (t, v) (hs ⟨htI, rfl⟩)).2.1.ne'
    have hn : S.nu t v ≠ 0 :=
      (limit_signs_conformal h hD d (t, v) (hs ⟨htI, rfl⟩)).2.2.1.ne
    dsimp only [W, S, bvIncomingLogCoefficient, sourceLogCorrectionStar, Fields.theta]
    dsimp only [S] at hl hn
    field_simp [hl, hn]
    ring
  have hgi := bv_incoming_log_coefficient_integrable h hD d hx hxy hyv
  have hWi : IntervalIntegrable W volume x y := by
    convert hp.1.add hgi using 1
    funext t
    ring
  have he := hp.2
  rw [intervalIntegral.integral_sub hWi hgi] at he
  change _ = _ + ∫ t in x..y, W t
  linarith only [he]

end ChristodoulouBV

end
