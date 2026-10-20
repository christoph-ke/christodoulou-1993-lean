module

public import Mathlib
public import ChristodoulouBV.Frozen.FieldsTheta
public import ChristodoulouBV.Frozen.FieldsZeta
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The initial X and Y integrals

Continuous extensions of the two regularized scalar amplitudes give uniform
linear bounds for the outgoing and incoming integrals in Section 6.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV.C1Solution

/-- Continuous regularized amplitudes give uniform linear bounds for both
Section 6 integrals. The endpoint values of the raw quotients are immaterial. -/
theorem xy_integral_bound_of_continuous_rates {b : ℝ} (_hb : 0 < b)
    (S : Fields) (Xrate Yrate : ℝ × ℝ → ℝ)
    (hXcont : ContinuousOn Xrate (closedCoordTriangle 0 b))
    (hYcont : ContinuousOn Yrate (closedCoordTriangle 0 b))
    (hXeq : ∀ p ∈ developmentWithInitialEdge b,
      Xrate p = |S.theta p.1 p.2| / S.r p.1 p.2)
    (hYeq : ∀ p ∈ developmentWithInitialEdge b,
      Yrate p = |S.zeta p.1 p.2| / S.r p.1 p.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → t < b →
      (∀ u, 0 < u → u < t →
        IntervalIntegrable (fun w => |S.theta u w| / S.r u w) volume u t ∧
        |∫ w in u..t, |S.theta u w| / S.r u w| ≤ C * t) ∧
      (∀ v, 0 < v → v < t →
        IntervalIntegrable (fun w => |S.zeta w v| / S.r w v) volume 0 v ∧
        |∫ w in (0 : ℝ)..v, |S.zeta w v| / S.r w v| ≤ C * t) := by
  obtain ⟨Cx, hCx⟩ := (isCompact_closedCoordTriangle 0 b).exists_bound_of_continuousOn
    hXcont
  obtain ⟨Cy, hCy⟩ := (isCompact_closedCoordTriangle 0 b).exists_bound_of_continuousOn
    hYcont
  let C := max 0 (max Cx Cy)
  have hC : 0 ≤ C := le_max_left _ _
  have hCxC : Cx ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCyC : Cy ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro t ht htB
  constructor
  · intro u hu hut
    have hutle : u ≤ t := hut.le
    have hslice : ContinuousOn (fun w => Xrate (u, w)) (Icc u t) := by
      apply hXcont.comp (continuous_const.prodMk continuous_id).continuousOn
      intro w hw
      exact ⟨hu.le, hw.1, hw.2.trans htB.le⟩
    have hInt : IntervalIntegrable (fun w => Xrate (u, w)) volume u t :=
      hslice.intervalIntegrable_of_Icc hutle
    have hEq : EqOn (fun w => Xrate (u, w))
        (fun w => |S.theta u w| / S.r u w) (uIoo u t) := by
      intro w hw
      rw [uIoo_of_le hutle] at hw
      exact hXeq (u, w) ⟨hu.le, hw.1, hw.2.trans htB⟩
    have hInt' := hInt.congr_uIoo hEq
    have hEqInt : (∫ w in u..t, Xrate (u, w)) =
        (∫ w in u..t, |S.theta u w| / S.r u w) :=
      intervalIntegral.integral_congr_Ioo_of_le hutle
        (hEq.mono (by rw [uIoo_of_le hutle]))
    have hbound : ∀ w ∈ Icc u t, |Xrate (u, w)| ≤ C := by
      intro w hw
      have hK : (u, w) ∈ closedCoordTriangle 0 b :=
        ⟨hu.le, hw.1, hw.2.trans htB.le⟩
      have h := (hCx (u, w) hK).trans hCxC
      simpa only [Real.norm_eq_abs] using h
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := t) (C := C) (f := fun w => Xrate (u, w)) (by
        intro w hw
        rw [uIoc_of_le hutle] at hw
        simpa only [Real.norm_eq_abs] using hbound w ⟨hw.1.le, hw.2⟩)
    have hupper : |∫ w in u..t, Xrate (u, w)| ≤ C * (t - u) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hutle)] using hnorm
    refine ⟨hInt', ?_⟩
    rw [← hEqInt]
    nlinarith [mul_nonneg hC hu.le]
  · intro v hv hvt
    have hvle : (0 : ℝ) ≤ v := hv.le
    have hslice : ContinuousOn (fun w => Yrate (w, v)) (Icc 0 v) := by
      apply hYcont.comp (continuous_id.prodMk continuous_const).continuousOn
      intro w hw
      exact ⟨hw.1, hw.2, hvt.le.trans htB.le⟩
    have hInt : IntervalIntegrable (fun w => Yrate (w, v)) volume 0 v :=
      hslice.intervalIntegrable_of_Icc hvle
    have hEq : EqOn (fun w => Yrate (w, v))
        (fun w => |S.zeta w v| / S.r w v) (uIoo 0 v) := by
      intro w hw
      rw [uIoo_of_le hvle] at hw
      exact hYeq (w, v) ⟨hw.1.le, hw.2, hvt.trans htB⟩
    have hInt' := hInt.congr_uIoo hEq
    have hEqInt : (∫ w in (0 : ℝ)..v, Yrate (w, v)) =
        (∫ w in (0 : ℝ)..v, |S.zeta w v| / S.r w v) :=
      intervalIntegral.integral_congr_Ioo_of_le hvle
        (hEq.mono (by rw [uIoo_of_le hvle]))
    have hbound : ∀ w ∈ Icc 0 v, |Yrate (w, v)| ≤ C := by
      intro w hw
      have hK : (w, v) ∈ closedCoordTriangle 0 b :=
        ⟨hw.1, hw.2, hvt.le.trans htB.le⟩
      have h := (hCy (w, v) hK).trans hCyC
      simpa only [Real.norm_eq_abs] using h
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := v) (C := C) (f := fun w => Yrate (w, v)) (by
        intro w hw
        rw [uIoc_of_le hvle] at hw
        simpa only [Real.norm_eq_abs] using hbound w ⟨hw.1.le, hw.2⟩)
    have hupper : |∫ w in (0 : ℝ)..v, Yrate (w, v)| ≤ C * v := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hvle] using hnorm
    refine ⟨hInt', ?_⟩
    rw [← hEqInt]
    exact hupper.trans (mul_le_mul_of_nonneg_left hvt.le hC)

/-- The outgoing and incoming Section 6 integrals are uniformly small near the
initial corner whenever their regularized amplitudes extend continuously. -/
theorem xy_integrals_uniformly_small_of_continuous_rates {b : ℝ} (hb : 0 < b)
    (S : Fields) (Xrate Yrate : ℝ × ℝ → ℝ)
    (hXcont : ContinuousOn Xrate (closedCoordTriangle 0 b))
    (hYcont : ContinuousOn Yrate (closedCoordTriangle 0 b))
    (hXeq : ∀ p ∈ developmentWithInitialEdge b,
      Xrate p = |S.theta p.1 p.2| / S.r p.1 p.2)
    (hYeq : ∀ p ∈ developmentWithInitialEdge b,
      Yrate p = |S.zeta p.1 p.2| / S.r p.1 p.2) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      (∀ u, 0 < u → u < t →
        |∫ w in u..t, |S.theta u w| / S.r u w| < ε) ∧
      (∀ v, 0 < v → v < t →
        |∫ w in (0 : ℝ)..v, |S.zeta w v| / S.r w v| < ε) := by
  obtain ⟨C, hC, hbound⟩ := xy_integral_bound_of_continuous_rates hb S Xrate
    Yrate hXcont hYcont hXeq hYeq
  intro ε hε
  let δ := min b (ε / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := lt_min hb (div_pos hε hC1)
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have htB : t < b := htδ.trans_le (min_le_left _ _)
  have htSmall : (C + 1) * t < ε := by
    have h := mul_lt_mul_of_pos_left (htδ.trans_le (min_le_right _ _)) hC1
    calc
      (C + 1) * t < (C + 1) * (ε / (C + 1)) := h
      _ = ε := by field_simp
  obtain ⟨hX, hY⟩ := hbound t ht htB
  constructor
  · intro u hu hut
    have hle := (hX u hu hut).2
    nlinarith
  · intro v hv hvt
    have hle := (hY v hv hvt).2
    nlinarith

end ChristodoulouBV.C1Solution

end
