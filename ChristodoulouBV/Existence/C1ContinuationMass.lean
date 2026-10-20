module

public import ChristodoulouBV.Existence.C1ContinuationSlice
public import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import Mathlib.Tactic

/-!
# Mass ratio from outgoing slice variation

The mass primitive, monotonicity of the radius, and the scalar amplitude
bound give the local estimate needed at the terminal corner.
-/

public section

open Set MeasureTheory
open scoped ENNReal Interval

namespace ChristodoulouBV

/-- On a unit C¹ development the mass ratio on an outgoing slice is at
most `15D` times the quotient variation on that same slice. -/
theorem s6_mass_ratio_le_outgoing_variation_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S) {u v : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo u 1) :
    ENNReal.ofReal (2 * S.m u v / S.r u v) ≤
      ENNReal.ofReal (15 * (sourceD S).toReal) *
        eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u 1) := by
  let T := scalarShift S (-S.phi 0 0)
  have HT : IsC1Solution (developmentWithInitialEdge 1) T := H.scalarShift _
  have hrT : ∀ w ∈ Ioo (0 : ℝ) 1, T.r 0 w = w / 2 := hr
  have hcenter : T.phi 0 0 = 0 := by simp only [T, scalarShift, add_neg_cancel]
  have hbootT : s4_bootstrap T := hboot
  have hDT : sourceD T = sourceD S := sourceD_scalarShift H hr _ (by norm_num)
  let M : ℝ := 15 * (sourceD S).toReal
  have hM : 0 ≤ M := by positivity
  have hamp {t : ℝ} (ht : t ∈ Ioo u 1) : |S.theta u t / S.lam u t| ≤ M := by
    have h := source_theta_div_lam_le_sourceD HT hrT hcenter hbootT
      (p := (u, t)) ⟨hu.1.le, ht.1, ht.2⟩
    rw [hDT] at h
    dsimp only [T] at h
    rw [scalarShift_theta] at h
    exact h
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hp : (u, v) ∈ developmentWithInitialEdge 1 := ⟨hu.1.le, hv.1, hv.2⟩
  have hrv : 0 < S.r u v := H.solution.radius_pos (u, v) hp
  let F : ℝ → ℝ := fun t => 2 * IsBVSolution.massV S u t / S.r u v
  have hIntegral : (∫ t in Ioo u v, F t) = 2 * S.m u v / S.r u v := by
    dsimp [F]
    rw [integral_div, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hv.1.le, hBV.mass_out_integral_from_axis hp]
  have hpoint (t : ℝ) (ht : t ∈ Ioo u v) :
      ‖F t‖ₑ ≤ ENNReal.ofReal M * ENNReal.ofReal (|S.theta u t| / S.r u t) := by
    have htU : (u, t) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, ht.1, ht.2.trans hv.2⟩
    have hrt : 0 < S.r u t := H.solution.radius_pos (u, t) htU
    have hlam : 0 < S.lam u t := H.solution.lam_pos (u, t) htU
    have hmu := hBV.mass_ratio_bounds htU
    have hrad : S.r u t ≤ S.r u v :=
      Uniqueness.radius_monotone_on_outgoing_of_c1 H hu.1.le ht.1 ht.2.le hv.2
    have hmass : 0 ≤ IsBVSolution.massV S u t := by
      change 0 ≤ (1 - 2 * S.m u t / S.r u t) * S.theta u t ^ 2 / (2 * S.lam u t)
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hmu.2.le) (sq_nonneg _))
        (mul_nonneg (by norm_num) hlam.le)
    have hF : 0 ≤ F t := div_nonneg (mul_nonneg (by norm_num) hmass) hrv.le
    have hnum : 2 * IsBVSolution.massV S u t ≤ M * |S.theta u t| := by
      calc
        2 * IsBVSolution.massV S u t =
            (1 - 2 * S.m u t / S.r u t) * (S.theta u t ^ 2 / S.lam u t) := by
          change 2 * ((1 - 2 * S.m u t / S.r u t) * S.theta u t ^ 2 /
            (2 * S.lam u t)) = _
          ring
        _ ≤ 1 * (S.theta u t ^ 2 / S.lam u t) :=
          mul_le_mul_of_nonneg_right (by linarith only [hmu.1])
            (div_nonneg (sq_nonneg _) hlam.le)
        _ = |S.theta u t / S.lam u t| * |S.theta u t| := by
          rw [one_mul, abs_div, abs_of_pos hlam, div_mul_eq_mul_div,
            ← sq, sq_abs]
        _ ≤ M * |S.theta u t| := mul_le_mul_of_nonneg_right
          (hamp ⟨ht.1, ht.2.trans hv.2⟩) (abs_nonneg _)
    have hreal : F t ≤ M * (|S.theta u t| / S.r u t) := by
      calc
        F t ≤ M * |S.theta u t| / S.r u v := div_le_div_of_nonneg_right hnum hrv.le
        _ ≤ M * |S.theta u t| / S.r u t :=
          div_le_div_of_nonneg_left (mul_nonneg hM (abs_nonneg _)) hrt hrad
        _ = _ := mul_div_assoc _ _ _
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hF]
    simpa only [ENNReal.ofReal_mul hM] using ENNReal.ofReal_le_ofReal hreal
  calc
    ENNReal.ofReal (2 * S.m u v / S.r u v) = ‖∫ t in Ioo u v, F t‖ₑ := by
      rw [hIntegral, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hBV.mass_ratio_bounds hp).1]
    _ ≤ ∫⁻ t in Ioo u v, ‖F t‖ₑ := enorm_integral_le_lintegral_enorm F
    _ ≤ ∫⁻ t in Ioo u v,
        ENNReal.ofReal M * ENNReal.ofReal (|S.theta u t| / S.r u t) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hpoint t ht
    _ = ENNReal.ofReal M *
        (∫⁻ t in Ioo u v, ENNReal.ofReal (|S.theta u t| / S.r u t)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M *
        (∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t)) := by
      gcongr
      exact hv.2.le
    _ ≤ _ := by
      gcongr
      exact (lemma4_1 H).1 u hu

/-- The local mass-ratio estimate in physical coordinates. Its coefficient
uses the original datum and is independent of the cutoff. -/
theorem s6_finite_cutoff_mass_ratio_le_variation
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {a u v : ℝ} (ha : 0 < a) (haB : a < B)
    (hu : u ∈ Ioo (0 : ℝ) a) (hv : v ∈ Ioo u a) :
    ENNReal.ofReal (2 * S.m u v / S.r u v) ≤
      ENNReal.ofReal (15 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) *
        eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u a) := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨HT, htrace, hDT⟩ := s6_scale ha (haB.trans hBb) H hdata
  have hboot := (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have huUnit : u / a ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hu.1 ha, (div_lt_one ha).mpr hu.2⟩
  have hvUnit : v / a ∈ Ioo (u / a) 1 :=
    ⟨div_lt_div_of_pos_right hv.1 ha, (div_lt_one ha).mpr hv.2⟩
  have h := s6_mass_ratio_le_outgoing_variation_unit HT
    (fun w hw => (htrace w hw).1) hboot huUnit hvUnit
  have hq : eVariationOn (fun t => T.alpha (u / a) t / T.lam (u / a) t)
      (Ioo (u / a) 1) =
        eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u a) := by
    simpa only [T, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_div_cancel₀ _ ha.ne', mul_one] using
      (e1_variation_scale_Ioo (fun t => S.alpha u t / S.lam u t)
        (a := u / a) (b := 1) ha)
  have hratio : 2 * T.m (u / a) (v / a) / T.r (u / a) (v / a) =
      2 * S.m u v / S.r u v := by
    simp only [T, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_div_cancel₀ _ ha.ne']
    field_simp
  rw [hq, hratio] at h
  have hDfinite : eVariationOn alpha₀ (Ioi (0 : ℝ)) ≠ ∞ :=
    ne_top_of_lt (hD.trans (ENNReal.ofReal_lt_top))
  exact h.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hDfinite hDT) (by norm_num))) bot_le)

end ChristodoulouBV

end
