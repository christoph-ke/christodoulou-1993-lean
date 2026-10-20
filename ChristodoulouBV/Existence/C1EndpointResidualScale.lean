module

public import ChristodoulouBV.Existence.C1EndpointCutoff
public import ChristodoulouBV.AreaEstimates.LogTransportCore
public import ChristodoulouBV.AreaEstimates.LogTransportInitialResidual
import Mathlib.Tactic

/-!
# The initial outgoing residual under scalar shifts and dilation

These identities transfer the Section 4 initial residual estimate from a
centered, unit-scaled cutoff back to the endpoint family.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- Constant scalar shifts leave the full outgoing logarithmic residual fixed. -/
theorem sourceOutgoingLogResidual_scalarShift (S : Fields) (c u v : ℝ) :
    sourceOutgoingLogResidual (scalarShift S c) u v =
      sourceOutgoingLogResidual S u v := by
  simp only [sourceOutgoingLogResidual, sourceLogCorrection,
    Fields.theta, Fields.zeta, scalarShift]
  ring

/-- The outgoing residual has weight one under dilation of both null
coordinates. This identity is used only where the radius and mass gap are
nonzero, as guaranteed by a C¹ development. -/
theorem sourceOutgoingLogResidual_rescaled_initial
    (S : Fields) {a v : ℝ} (ha : 0 < a)
    (hr : S.r 0 (a * v) ≠ 0) :
    sourceOutgoingLogResidual (Uniqueness.rescaledFields S 0 a) 0 v =
      a * sourceOutgoingLogResidual S 0 (a * v) := by
  have hderiv :
      deriv (fun t => Real.log ((Uniqueness.rescaledFields S 0 a).lam 0 t)) v =
        a * deriv (fun t => Real.log (S.lam 0 t)) (a * v) := by
    simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_zero, smul_eq_mul] using
      (deriv_comp_mul_left a (fun t => Real.log (S.lam 0 t)) v)
  simp only [sourceOutgoingLogResidual, sourceLogCorrection,
    Fields.theta, Fields.zeta, Uniqueness.rescaledFields,
    Uniqueness.affineCoordinate, zero_add, mul_zero] at *
  rw [hderiv]
  field_simp [ha.ne', hr]

/-- The outgoing alpha-lambda residual in (4.4b). -/
@[expose] noncomputable def sourceOutgoingAlphaResidual (S : Fields) (u v : ℝ) : ℝ :=
  deriv (S.alpha u) v - deriv (S.lam u) v * S.phi u v

/-- The alpha-lambda residual has weight one under dilation. -/
theorem sourceOutgoingAlphaResidual_rescaled
    (S : Fields) {a u v : ℝ} (_ha : 0 < a) :
    sourceOutgoingAlphaResidual (Uniqueness.rescaledFields S 0 a) u v =
      a * sourceOutgoingAlphaResidual S (a * u) (a * v) := by
  have hAlpha :
      deriv ((Uniqueness.rescaledFields S 0 a).alpha u) v =
        a * deriv (S.alpha (a * u)) (a * v) := by
    simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, smul_eq_mul] using
      (deriv_comp_mul_left a (S.alpha (a * u)) v)
  have hLam :
      deriv ((Uniqueness.rescaledFields S 0 a).lam u) v =
        a * deriv (S.lam (a * u)) (a * v) := by
    simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, smul_eq_mul] using
      (deriv_comp_mul_left a (S.lam (a * u)) v)
  change deriv ((Uniqueness.rescaledFields S 0 a).alpha u) v -
      deriv ((Uniqueness.rescaledFields S 0 a).lam u) v *
        (Uniqueness.rescaledFields S 0 a).phi u v =
    a * (deriv (S.alpha (a * u)) (a * v) -
      deriv (S.lam (a * u)) (a * v) * S.phi (a * u) (a * v))
  rw [hAlpha, hLam]
  simp only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
    zero_add]
  ring

/-- A constant scalar shift leaves the alpha-lambda residual fixed wherever
the two outgoing derivatives exist. -/
theorem sourceOutgoingAlphaResidual_scalarShift
    (S : Fields) (c u v : ℝ)
    (hAlpha : DifferentiableAt ℝ (S.alpha u) v)
    (hLam : DifferentiableAt ℝ (S.lam u) v) :
    sourceOutgoingAlphaResidual (scalarShift S c) u v =
      sourceOutgoingAlphaResidual S u v := by
  have hDeriv : deriv (fun t => S.alpha u t + c * S.lam u t) v =
      deriv (S.alpha u) v + c * deriv (S.lam u) v := by
    change deriv ((S.alpha u) + fun t => c * S.lam u t) v = _
    rw [deriv_add hAlpha (hLam.const_mul c), deriv_const_mul_field]
  simp only [sourceOutgoingAlphaResidual, scalarShift, hDeriv]
  ring

/-- The full outgoing logarithmic residual has the same weight at every
interior point of a dilated development. -/
theorem sourceOutgoingLogResidual_rescaled
    (S : Fields) {a u v : ℝ} (ha : 0 < a)
    (hr : S.r (a * u) (a * v) ≠ 0) :
    sourceOutgoingLogResidual (Uniqueness.rescaledFields S 0 a) u v =
      a * sourceOutgoingLogResidual S (a * u) (a * v) := by
  have hderiv :
      deriv (fun t => Real.log
        ((Uniqueness.rescaledFields S 0 a).lam u t)) v =
        a * deriv (fun t => Real.log (S.lam (a * u) t)) (a * v) := by
    simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, smul_eq_mul] using
      (deriv_comp_mul_left a
        (fun t => Real.log (S.lam (a * u) t)) v)
  simp only [sourceOutgoingLogResidual, sourceLogCorrection,
    Fields.theta, Fields.zeta, Uniqueness.rescaledFields,
    Uniqueness.affineCoordinate, zero_add] at *
  rw [hderiv]
  field_simp [ha.ne', hr]

/-- On a strict finite cutoff, the complete initial logarithmic residual is
integrable. The bound is supplied by the centered Section 4 estimate and is
independent of the cutoff. -/
theorem s6_initial_residual_cutoff_packet
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Set.Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Set.Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) (haB : a < B) :
    IntervalIntegrable (fun v => |sourceOutgoingLogResidual S 0 v|)
      volume 0 a ∧
    (∫ v in (0 : ℝ)..a, |sourceOutgoingLogResidual S 0 v|) ≤
      108 * (eVariationOn alpha₀ (Set.Ioi (0 : ℝ))).toReal ^ 2 := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨Q, HQ, hcenter, hrQ, hInv, _, _, _, _⟩ :=
    s6_centered_finite_cutoff_area_bounds hB hBb H hdata hD ha haB
  have hbootT :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have hbootQ : s4_bootstrap Q := by
    rw [← hInv] at hbootT
    simpa only [s4_bootstrap, scalarShift] using hbootT
  have hQI := initial_log_residual_integrable HQ hrQ hcenter hbootQ
  have hTI : IntervalIntegrable
      (fun v => |sourceOutgoingLogResidual T 0 v|) volume 0 1 := by
    apply (intervalIntegrable_congr_uIoo (a := (0 : ℝ)) (b := 1)
      (f := fun v => |sourceOutgoingLogResidual T 0 v|)
      (g := fun v => |sourceOutgoingLogResidual Q 0 v|) ?_).2 hQI
    intro v hv
    change scalarShift Q ((Uniqueness.rescaledFields S 0 a).phi 0 0) = T at hInv
    change |sourceOutgoingLogResidual T 0 v| =
      |sourceOutgoingLogResidual Q 0 v|
    rw [← hInv, sourceOutgoingLogResidual_scalarShift]
  have hScaled : IntervalIntegrable
      (fun v => a * |sourceOutgoingLogResidual S 0 (a * v)|)
      volume 0 1 := by
    apply (intervalIntegrable_congr_uIoo (a := (0 : ℝ)) (b := 1)
      (f := fun v => a * |sourceOutgoingLogResidual S 0 (a * v)|)
      (g := fun v => |sourceOutgoingLogResidual T 0 v|) ?_).2 hTI
    intro v hv
    have hv' : v ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hv
    have hav : a * v ∈ Set.Ioo (0 : ℝ) b := by
      constructor
      · exact mul_pos ha hv'.1
      · calc
          a * v < a := by nlinarith [hv'.2]
          _ < b := (haB.trans hBb)
    have hr : S.r 0 (a * v) ≠ 0 :=
      ne_of_gt (H.solution.radius_pos (0, a * v)
        ⟨le_rfl, hav.1, hav.2⟩)
    change a * |sourceOutgoingLogResidual S 0 (a * v)| =
      |sourceOutgoingLogResidual (Uniqueness.rescaledFields S 0 a) 0 v|
    rw [sourceOutgoingLogResidual_rescaled_initial S ha hr,
      abs_mul, abs_of_pos ha]
  have hComp : IntervalIntegrable
      (fun v => |sourceOutgoingLogResidual S 0 (a * v)|)
      volume 0 1 := by
    have hfun : (fun v => (a * |sourceOutgoingLogResidual S 0 (a * v)|) / a) =
        (fun v => |sourceOutgoingLogResidual S 0 (a * v)|) := by
      funext v
      field_simp [ha.ne']
    simpa only [hfun] using hScaled.div_const a
  have hIff := (IntervalIntegrable.comp_mul_left_iff
    (f := fun v => |sourceOutgoingLogResidual S 0 v|)
    (a := (0 : ℝ)) (b := a) (c := a) ha.ne')
  have hS := hIff.mp (by simpa only [zero_div, div_self ha.ne'] using hComp)
  refine ⟨hS, ?_⟩
  have hQbound := initial_log_residual HQ hrQ hcenter hbootQ
  have hQT : (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual Q 0 v|) =
      ∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual T 0 v| := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
    intro v hv
    change scalarShift Q ((Uniqueness.rescaledFields S 0 a).phi 0 0) = T at hInv
    change |sourceOutgoingLogResidual Q 0 v| =
      |sourceOutgoingLogResidual T 0 v|
    rw [← hInv, sourceOutgoingLogResidual_scalarShift]
  have hTS : (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual T 0 v|) =
      ∫ v in (0 : ℝ)..1,
        a * |sourceOutgoingLogResidual S 0 (a * v)| := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
    intro v hv
    have hav : a * v ∈ Set.Ioo (0 : ℝ) b := by
      constructor
      · exact mul_pos ha hv.1
      · calc
          a * v < a * 1 := mul_lt_mul_of_pos_left hv.2 ha
          _ = a := mul_one a
          _ < b := haB.trans hBb
    have hr : S.r 0 (a * v) ≠ 0 :=
      ne_of_gt (H.solution.radius_pos (0, a * v)
        ⟨le_rfl, hav.1, hav.2⟩)
    change |sourceOutgoingLogResidual (Uniqueness.rescaledFields S 0 a) 0 v| =
      a * |sourceOutgoingLogResidual S 0 (a * v)|
    rw [sourceOutgoingLogResidual_rescaled_initial S ha hr,
      abs_mul, abs_of_pos ha]
  have hsub : (∫ v in (0 : ℝ)..1,
      a * |sourceOutgoingLogResidual S 0 (a * v)|) =
      ∫ v in (0 : ℝ)..a, |sourceOutgoingLogResidual S 0 v| := by
    calc
      (∫ v in (0 : ℝ)..1,
          a * |sourceOutgoingLogResidual S 0 (a * v)|) =
          a * ∫ v in (0 : ℝ)..1,
            |sourceOutgoingLogResidual S 0 (a * v)| :=
        intervalIntegral.integral_const_mul _ _
      _ = ∫ v in (0 : ℝ)..a, |sourceOutgoingLogResidual S 0 v| := by
        simpa only [smul_eq_mul, mul_zero, mul_one] using
          (intervalIntegral.smul_integral_comp_mul_left
            (f := fun v => |sourceOutgoingLogResidual S 0 v|)
            (a := (0 : ℝ)) (b := 1) a)
  have hTdata := (s6_scale ha (haB.trans hBb) H hdata).2.2
  have hDQt : sourceD Q = sourceD T := by
    change scalarShift Q ((Uniqueness.rescaledFields S 0 a).phi 0 0) = T at hInv
    rw [← hInv, sourceD_scalarShift HQ hrQ _ (by norm_num)]
  have hDtop : eVariationOn alpha₀ (Set.Ioi (0 : ℝ)) ≠ ∞ := by
    have hE : s4Epsilon0 ≠ ∞ := by norm_num [s4Epsilon0]
    exact ne_top_of_le_ne_top hE (hD.le.trans epsilonChosen_le_s4)
  have hDreal : (sourceD Q).toReal ≤
      (eVariationOn alpha₀ (Set.Ioi (0 : ℝ))).toReal := by
    rw [hDQt]
    exact ENNReal.toReal_mono hDtop hTdata
  have hQnonneg : 0 ≤ (sourceD Q).toReal := ENNReal.toReal_nonneg
  have hDnonneg : 0 ≤ (eVariationOn alpha₀ (Set.Ioi (0 : ℝ))).toReal :=
    ENNReal.toReal_nonneg
  rw [← hsub, ← hTS, ← hQT]
  nlinarith

/-- Integrability alone, as used by the endpoint exhaustion argument. -/
theorem s6_initial_residual_integrable_cutoff
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Set.Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Set.Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) (haB : a < B) :
    IntervalIntegrable (fun v => |sourceOutgoingLogResidual S 0 v|)
      volume 0 a :=
  (s6_initial_residual_cutoff_packet hB hBb H hdata hD ha haB).1

end ChristodoulouBV

end
