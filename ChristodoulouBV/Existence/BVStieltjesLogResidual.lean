module

public import ChristodoulouBV.Existence.BVStieltjesLogCalculus
public import ChristodoulouBV.Existence.BVStieltjesMeasurable
public import ChristodoulouBV.AreaEstimates.LogTransportCore
import Mathlib.Tactic

/-!
# Canonical logarithmic Stieltjes residuals

The incoming coefficient uses the negative sign of `f*` fixed by the sign correction described in ERRATA.md, ERR-23.
Both residuals have finite variation on fixed compact off-axis edges.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The outgoing coefficient `g = f - μ λ / ((1-μ)r)`. -/
@[expose] noncomputable def bvOutgoingLogCoefficient (S : Fields) (u v : ℝ) : ℝ :=
  sourceLogCorrection S u v - (2 * S.m u v / S.r u v) * S.lam u v /
    ((1 - 2 * S.m u v / S.r u v) * S.r u v)

/-- The incoming coefficient with the corrected sign `g* = -f* - μν/((1-μ)r)`. -/
@[expose] noncomputable def bvIncomingLogCoefficient (S : Fields) (u v : ℝ) : ℝ :=
  -sourceLogCorrectionStar S u v - (2 * S.m u v / S.r u v) * S.nu u v /
    ((1 - 2 * S.m u v / S.r u v) * S.r u v)

/-- A pointwise primitive of `d log λ + g dv`. -/
@[expose] noncomputable def bvOutgoingLogResidual (S : Fields) (u a x : ℝ) : ℝ :=
  Real.log (S.lam u x) + ∫ t in a..x, bvOutgoingLogCoefficient S u t

/-- A pointwise primitive of the sign-corrected `d log |ν| + g* du`. -/
@[expose] noncomputable def bvIncomingLogResidual (S : Fields) (v a x : ℝ) : ℝ :=
  Real.log (-S.nu x v) + ∫ t in a..x, bvIncomingLogCoefficient S t v

/-- The outgoing coefficient as a continuous polynomial in the area coefficients. -/
@[expose] def bvOutgoingLogAlgebra (c : Fin 9 → ℝ) : ℝ :=
  (c 4 - c 1 * c 3) * c 0 *
    ((c 4 - c 1 * c 3) * c 7 - (c 5 - c 2 * c 3) * c 8) - c 6 * c 8

/-- The corrected incoming coefficient in the same coefficient coordinates. -/
@[expose] def bvIncomingLogAlgebra (c : Fin 9 → ℝ) : ℝ :=
  -(c 5 - c 2 * c 3) * c 0 *
    ((c 4 - c 1 * c 3) * c 7 - (c 5 - c 2 * c 3) * c 8) - c 6 * c 7

/-- Both algebraic coefficient formulas are continuous. -/
theorem bv_log_algebras_continuous :
    Continuous bvOutgoingLogAlgebra ∧ Continuous bvIncomingLogAlgebra := by
  constructor
  · unfold bvOutgoingLogAlgebra
    fun_prop
  · unfold bvIncomingLogAlgebra
    fun_prop

/-- The algebraic formulas equal the actual source logarithmic coefficients
at every canonical domain point. -/
theorem bv_log_coefficients_eq_algebra
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    bvOutgoingLogCoefficient d.scalarRightFields p.1 p.2 =
      bvOutgoingLogAlgebra (areaSectionCoefficients d.scalarRightFields p) ∧
    bvIncomingLogCoefficient d.scalarRightFields p.1 p.2 =
      bvIncomingLogAlgebra (areaSectionCoefficients d.scalarRightFields p) := by
  let S := d.scalarRightFields
  have hl : S.lam p.1 p.2 ≠ 0 := (limit_signs_conformal h hD d p hp).2.1.ne'
  have hn : S.nu p.1 p.2 ≠ 0 := (limit_signs_conformal h hD d p hp).2.2.1.ne
  have hr : S.r p.1 p.2 ≠ 0 := (limit_signs_conformal h hD d p hp).1.ne'
  have hg : 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≠ 0 :=
    (limit_signs_conformal h hD d p hp).2.2.2.1.ne'
  have hgr : S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0 := by
    intro he
    apply hg
    have heq : 2 * S.m p.1 p.2 / S.r p.1 p.2 = 1 :=
      (div_eq_one_iff_eq hr).mpr (by linarith only [he])
    rw [heq, sub_self]
  constructor
  · change S.theta p.1 p.2 / S.r p.1 p.2 *
        (S.theta p.1 p.2 / S.lam p.1 p.2 - S.zeta p.1 p.2 / S.nu p.1 p.2) -
        (2 * S.m p.1 p.2 / S.r p.1 p.2) * S.lam p.1 p.2 /
          ((1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2) =
      S.theta p.1 p.2 * (S.r p.1 p.2)⁻¹ *
        (S.theta p.1 p.2 * (S.lam p.1 p.2)⁻¹ -
          S.zeta p.1 p.2 * (S.nu p.1 p.2)⁻¹) -
        IsBVSolution.radiusCoeff S p.1 p.2 * (S.nu p.1 p.2)⁻¹
    dsimp only [IsBVSolution.radiusCoeff]
    field_simp [hr, hl, hn, hg, hgr]
  · change -(S.zeta p.1 p.2 / S.r p.1 p.2 *
        (S.theta p.1 p.2 / S.lam p.1 p.2 - S.zeta p.1 p.2 / S.nu p.1 p.2)) -
        (2 * S.m p.1 p.2 / S.r p.1 p.2) * S.nu p.1 p.2 /
          ((1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2) =
      -S.zeta p.1 p.2 * (S.r p.1 p.2)⁻¹ *
        (S.theta p.1 p.2 * (S.lam p.1 p.2)⁻¹ -
          S.zeta p.1 p.2 * (S.nu p.1 p.2)⁻¹) -
        IsBVSolution.radiusCoeff S p.1 p.2 * (S.lam p.1 p.2)⁻¹
    dsimp only [IsBVSolution.radiusCoeff]
    field_simp [hr, hl, hn, hg, hgr]

/-- The outgoing log coefficient is integrable on every compact outgoing section. -/
theorem bv_outgoing_log_coefficient_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hu : 0 ≤ u) (hua : u < a) (hab : a ≤ b) :
    IntervalIntegrable (bvOutgoingLogCoefficient d.scalarRightFields u) volume a b := by
  have hi := bv_area_algebra_intervalIntegrable h hD d .lamPhi hab (sub_pos.mpr hua)
    (fun t ht => show (u, t) ∈ globalDomain from ⟨hu, hua.trans_le ht.1⟩)
    (fun t ht => show a - u ≤ t - u from sub_le_sub_right ht.1 u)
    bv_log_algebras_continuous.1
  apply hi.congr
  intro t ht
  rw [uIoc_of_le hab] at ht
  exact (bv_log_coefficients_eq_algebra h hD d
    (show (u, t) ∈ globalDomain from ⟨hu, hua.trans_le ht.1.le⟩)).1.symm

/-- The corrected incoming log coefficient is integrable on compact incoming sections. -/
theorem bv_incoming_log_coefficient_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b < v) :
    IntervalIntegrable (fun t => bvIncomingLogCoefficient d.scalarRightFields t v)
      volume a b := by
  have hi := bv_area_algebra_intervalIntegrable h hD d .nuPhi hab (sub_pos.mpr hbv)
    (fun t ht => show (t, v) ∈ globalDomain from ⟨ha.trans ht.1, ht.2.trans_lt hbv⟩)
    (fun t ht => show v - b ≤ v - t from sub_le_sub_left ht.2 v)
    bv_log_algebras_continuous.2
  apply hi.congr
  intro t ht
  rw [uIoc_of_le hab] at ht
  exact (bv_log_coefficients_eq_algebra h hD d
    (show (t, v) ∈ globalDomain from ⟨ha.trans ht.1.le, ht.2.trans_lt hbv⟩)).2.symm

/-- Fixed outgoing logarithmic residuals have finite variation on compact off-axis edges. -/
theorem bv_outgoing_log_residual_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hu : 0 ≤ u) (hua : u < a) (hab : a ≤ b) :
    BoundedVariationOn (bvOutgoingLogResidual d.scalarRightFields u b) (Icc a b) := by
  have hv := (right_expansions_variation h hD d).1 u hu
  have hfinite : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  have hb : BoundedVariationOn (d.scalarRightFields.lam u) (Icc a b) :=
    ne_top_of_le_ne_top hfinite ((eVariationOn.mono _
      (fun t ht => hua.trans_le ht.1)).trans hv)
  have hlog : BoundedVariationOn (fun t => Real.log (d.scalarRightFields.lam u t))
      (Icc a b) :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb)
      (eVariationOn.log_comp_le (by norm_num : (0 : ℝ) < 1 / 3)
        (fun t ht => (scalar_right_fields_geometry h hD d (u, t)
          ⟨hu, hua.trans_le ht.1⟩).1))
  have hi := bv_outgoing_log_coefficient_integrable h hD d hu hua hab
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hab] at hInt
  exact hlog.add hInt

/-- Fixed incoming logarithmic residuals have finite variation, with the corrected sign. -/
theorem bv_incoming_log_residual_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b < v) :
    BoundedVariationOn (bvIncomingLogResidual d.scalarRightFields v a) (Icc a b) := by
  have hv := (right_expansions_variation h hD d).2 v (ha.trans_lt (hab.trans_lt hbv))
  have hfinite : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  have hbν : BoundedVariationOn (fun t => d.scalarRightFields.nu t v) (Icc a b) :=
    ne_top_of_le_ne_top hfinite ((eVariationOn.mono _
      (fun t ht => show t ∈ Ico 0 v from ⟨ha.trans ht.1, ht.2.trans_lt hbv⟩)).trans hv)
  have hb := hbν.neg
  have hlog : BoundedVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v))
      (Icc a b) :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb)
      (eVariationOn.log_comp_le (by norm_num : (0 : ℝ) < 1 / 3)
        (fun t ht => (scalar_right_fields_geometry h hD d (t, v)
          ⟨ha.trans ht.1, ht.2.trans_lt hbv⟩).2.2.1))
  have hi := bv_incoming_log_coefficient_integrable h hD d ha hab hbv
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hab] at hInt
  exact hlog.add hInt

end ChristodoulouBV

end
