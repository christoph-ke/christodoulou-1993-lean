module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsNormalized
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsProducts
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Rational coefficients on a closed coordinate triangle

Uniform cubic value and quadratic jet expansions provide a first jet for a
cubic-over-square quotient. This module assembles the regular products that
occur after that removable quotient, with a common complementary denominator.
-/

public section

open Set

namespace intervalIntegral

/-- Common regularity and axis data for a cubic numerator, a linearly
vanishing denominator, and the regular factors of a rational coefficient.
The three uniform expansions are the abstract interface supplied by a
Volterra calculation. -/
structure CubicRationalTriangleBox (a b c : ℝ) where
  /-- The cubic numerator. -/
  J : ℝ × ℝ → ℝ
  /-- The linearly vanishing denominator. -/
  r : ℝ × ℝ → ℝ
  /-- The normalized denominator. -/
  ρ : ℝ × ℝ → ℝ
  /-- The positive regular weight. -/
  w : ℝ × ℝ → ℝ
  /-- The second regular factor. -/
  z : ℝ × ℝ → ℝ
  /-- The linearly vanishing source factor. -/
  H : ℝ × ℝ → ℝ
  /-- The axis slope used in the cubic expansion. -/
  h : ℝ × ℝ → ℝ
  /-- The numerator has continuous first jets. -/
  J_c1 : ContDiffOn ℝ 1 J (closedCoordTriangle a b)
  /-- The denominator has continuous first jets. -/
  r_c1 : ContDiffOn ℝ 1 r (closedCoordTriangle a b)
  /-- The normalized denominator is continuous. -/
  ρ_cont : ContinuousOn ρ (closedCoordTriangle a b)
  /-- The first regular factor has continuous first jets. -/
  w_c1 : ContDiffOn ℝ 1 w (closedCoordTriangle a b)
  /-- The second regular factor has continuous first jets. -/
  z_c1 : ContDiffOn ℝ 1 z (closedCoordTriangle a b)
  /-- The source factor has continuous first jets. -/
  H_c1 : ContDiffOn ℝ 1 H (closedCoordTriangle a b)
  /-- The axis slope is continuous. -/
  h_cont : ContinuousOn h (closedCoordTriangle a b)
  /-- The normalized denominator has a common positive lower bound. -/
  ρ_lower : ∀ p ∈ closedCoordTriangle a b, c ≤ ρ p
  /-- The positive weight also has the common lower bound. -/
  w_lower : ∀ p ∈ closedCoordTriangle a b, c ≤ w p
  /-- Factorization of the denominator by the coordinate gap. -/
  r_factor : ∀ p ∈ closedCoordTriangle a b,
    r p = (p.2 - p.1) * ρ p
  /-- The numerator vanishes on the diagonal. -/
  J_diag : ∀ u ∈ Icc a b, J (u, u) = 0
  /-- The source factor vanishes on the diagonal. -/
  H_diag : ∀ u ∈ Icc a b, H (u, u) = 0
  /-- The normalized radius has the diagonal value of the weight. -/
  ρ_diag : ∀ u ∈ Icc a b, ρ (u, u) = w (u, u)
  /-- The regular factors have opposite diagonal values. -/
  z_diag : ∀ u ∈ Icc a b, z (u, u) = -w (u, u)
  /-- The denominator's horizontal diagonal derivative. -/
  r_u_diag : ∀ u ∈ Icc a b,
    (fderivWithin ℝ r (closedCoordTriangle a b) (u, u)) (1, 0) = -w (u, u)
  /-- The denominator's vertical diagonal derivative. -/
  r_v_diag : ∀ u ∈ Icc a b,
    (fderivWithin ℝ r (closedCoordTriangle a b) (u, u)) (0, 1) = w (u, u)
  /-- Uniform cubic numerator expansion along the whole diagonal. -/
  J_axis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
      |J (u, v) - (w (u, u) * h (u, u) ^ 2 / 12) * (v - u) ^ 3| ≤
        ε * (v - u) ^ 3
  /-- Uniform horizontal numerator-jet expansion. -/
  J_u_axis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
      |(fderivWithin ℝ J (closedCoordTriangle a b) (u, v)) (1, 0) -
        (-(w (u, u) * h (u, u) ^ 2 / 4)) * (v - u) ^ 2| ≤
          ε * (v - u) ^ 2
  /-- Uniform vertical numerator-jet expansion. -/
  J_v_axis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
      |(fderivWithin ℝ J (closedCoordTriangle a b) (u, v)) (0, 1) -
        (w (u, u) * h (u, u) ^ 2 / 4) * (v - u) ^ 2| ≤
          ε * (v - u) ^ 2

/-- The normalized axis coefficient for the numerator. -/
@[expose] noncomputable def CubicRationalTriangleBox.valueAxis
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) : ℝ := B.w p * B.h p ^ 2 / 12

/-- The normalized horizontal axis coefficient for the numerator jet. -/
@[expose] noncomputable def CubicRationalTriangleBox.horizontalAxis
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) : ℝ := -(B.w p * B.h p ^ 2 / 4)

/-- The normalized vertical axis coefficient for the numerator jet. -/
@[expose] noncomputable def CubicRationalTriangleBox.verticalAxis
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) : ℝ := B.w p * B.h p ^ 2 / 4

/-- The cubic-over-square quotient has a continuous relative first jet on
the closed triangle. The jet formula uses only continuous normalized
quotients and differentiates the original quotient only off the diagonal. -/
theorem CubicRationalTriangleBox.squaredQuotient_hasJet
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) :
    let K := closedCoordTriangle a b
    let U := gapPowerQuotient 3 B.J B.valueAxis
    let V := normalizedCoordinateJet 2
      (fderivWithin ℝ B.J K) B.horizontalAxis B.verticalAxis
    ContDiffOn ℝ 1 (cubicSquaredQuotient B.J B.r) K ∧
      ∀ p ∈ K,
        fderivWithin ℝ (cubicSquaredQuotient B.J B.r) K p =
          cubicSquaredQuotientJet U B.ρ V
            (fderivWithin ℝ B.r K) p := by
  have hC₀ : ContinuousOn B.valueAxis (closedCoordTriangle a b) := by
    exact (B.w_c1.continuousOn.mul (B.h_cont.pow 2)).div_const 12
  have hCᵤ : ContinuousOn B.horizontalAxis (closedCoordTriangle a b) := by
    exact ((B.w_c1.continuousOn.mul (B.h_cont.pow 2)).div_const 4).neg
  have hCᵥ : ContinuousOn B.verticalAxis (closedCoordTriangle a b) := by
    exact (B.w_c1.continuousOn.mul (B.h_cont.pow 2)).div_const 4
  exact cubicSquaredQuotient_hasJet_of_uniform_axis hab
    B.J_c1 B.r_c1 B.ρ_cont hC₀ hCᵤ hCᵥ
    B.ρ_lower hc B.r_factor B.J_diag B.J_axis B.J_u_axis B.J_v_axis

/-- The two coordinate jets of the cubic-over-square quotient on the
diagonal are opposite, with magnitude given by the cubic axis coefficient
divided by the positive weight. -/
theorem CubicRationalTriangleBox.squaredQuotient_axis_coordinates
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ (cubicSquaredQuotient B.J B.r)
      (closedCoordTriangle a b) (u, u)) (1, 0) =
        -(B.h (u, u) ^ 2 / (12 * B.w (u, u))) ∧
    (fderivWithin ℝ (cubicSquaredQuotient B.J B.r)
      (closedCoordTriangle a b) (u, u)) (0, 1) =
        B.h (u, u) ^ 2 / (12 * B.w (u, u)) := by
  let K := closedCoordTriangle a b
  let U := gapPowerQuotient 3 B.J B.valueAxis
  let V := normalizedCoordinateJet 2
    (fderivWithin ℝ B.J K) B.horizontalAxis B.verticalAxis
  have hU : U (u, u) = B.w (u, u) * B.h (u, u) ^ 2 / 12 := by
    simp [U, gapPowerQuotient, CubicRationalTriangleBox.valueAxis]
  have hVu : V (u, u) (1, 0) =
      -(B.w (u, u) * B.h (u, u) ^ 2 / 4) := by
    simp [V, normalizedCoordinateJet, gapPowerQuotient,
      coordinateLinearJet_apply, CubicRationalTriangleBox.horizontalAxis]
  have hVv : V (u, u) (0, 1) =
      B.w (u, u) * B.h (u, u) ^ 2 / 4 := by
    simp [V, normalizedCoordinateJet, gapPowerQuotient,
      coordinateLinearJet_apply, CubicRationalTriangleBox.verticalAxis]
  have hA := (B.squaredQuotient_hasJet hab hc).2
    (u, u) ⟨hu.1, le_rfl, hu.2⟩
  rw [hA]
  exact cubicSquaredQuotientJet_axis
    (ne_of_gt (hc.trans_le (B.w_lower (u, u) ⟨hu.1, le_rfl, hu.2⟩)))
    (B.ρ_diag u hu) hU hVu hVv (B.r_u_diag u hu) (B.r_v_diag u hu)

/-- A positive complement of the cubic-over-linear quotient extends across
the diagonal, where that quotient is zero. -/
theorem CubicRationalTriangleBox.complement_ne_zero
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε) :
    ∀ p ∈ closedCoordTriangle a b,
      1 - cubicLinearQuotient B.J B.r p ≠ 0 := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · have h := hoff p hp hstrict
    exact ne_of_gt (by linarith)
  · have hzero : cubicLinearQuotient B.J B.r p = 0 := by
      simp [cubicLinearQuotient, hstrict]
    simp [hzero]

/-- The four removable rational quantities have continuous first jets
under one common denominator gap. -/
theorem CubicRationalTriangleBox.contDiffOn_coefficients
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε) :
    ContDiffOn ℝ 1 (cubicSquaredQuotient B.J B.r)
      (closedCoordTriangle a b) ∧
    ContDiffOn ℝ 1 (cubicLinearQuotient B.J B.r)
      (closedCoordTriangle a b) ∧
    ContDiffOn ℝ 1 (rationalCubicCoefficient B.J B.r B.w B.z)
      (closedCoordTriangle a b) ∧
    ContDiffOn ℝ 1 (rationalCubicSource B.J B.r B.w B.z B.H)
      (closedCoordTriangle a b) := by
  have hA := (B.squaredQuotient_hasJet hab hc).1
  have hμ := contDiffOn_cubicLinearQuotient hA B.r_c1 hc
    B.ρ_lower B.r_factor
  have hden := B.complement_ne_zero hε hoff
  have hK := contDiffOn_rationalCubicCoefficient hA hμ
    B.w_c1 B.z_c1 hden
  have hQ := contDiffOn_rationalCubicSource hK B.H_c1 B.w_c1
    (fun p hp => ne_of_gt (hc.trans_le (B.w_lower p hp)))
  exact ⟨hA, hμ, hK, hQ⟩

/-- The diagonal derivative of the cubic-over-linear quotient vanishes. -/
theorem CubicRationalTriangleBox.linearQuotient_diag_jet
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) {u : ℝ} (hu : u ∈ Icc a b) :
    fderivWithin ℝ (cubicLinearQuotient B.J B.r)
      (closedCoordTriangle a b) (u, u) = 0 := by
  exact fderivWithin_cubicLinearQuotient_diag hab hu
    (B.squaredQuotient_hasJet hab hc).1 B.r_c1 hc B.ρ_lower B.r_factor

/-- The two coordinate derivatives of the rational cubic coefficient on
the diagonal have opposite signs and the factor (1/12). -/
theorem CubicRationalTriangleBox.coefficient_axis_coordinates
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ (rationalCubicCoefficient B.J B.r B.w B.z)
      (closedCoordTriangle a b) (u, u)) (1, 0) =
        B.w (u, u) * B.h (u, u) ^ 2 / 12 ∧
    (fderivWithin ℝ (rationalCubicCoefficient B.J B.r B.w B.z)
      (closedCoordTriangle a b) (u, u)) (0, 1) =
        -(B.w (u, u) * B.h (u, u) ^ 2 / 12) := by
  let K := closedCoordTriangle a b
  let U := gapPowerQuotient 3 B.J B.valueAxis
  let V := normalizedCoordinateJet 2
    (fderivWithin ℝ B.J K) B.horizontalAxis B.verticalAxis
  have hA := B.squaredQuotient_hasJet hab hc
  have hμ := contDiffOn_cubicLinearQuotient hA.1 B.r_c1 hc
    B.ρ_lower B.r_factor
  have hden := B.complement_ne_zero hε hoff
  have hU : U (u, u) = B.w (u, u) * B.h (u, u) ^ 2 / 12 := by
    simp [U, gapPowerQuotient, CubicRationalTriangleBox.valueAxis]
  have hVu : V (u, u) (1, 0) =
      -(B.w (u, u) * B.h (u, u) ^ 2 / 4) := by
    simp [V, normalizedCoordinateJet, gapPowerQuotient,
      coordinateLinearJet_apply, CubicRationalTriangleBox.horizontalAxis]
  have hVv : V (u, u) (0, 1) =
      B.w (u, u) * B.h (u, u) ^ 2 / 4 := by
    simp [V, normalizedCoordinateJet, gapPowerQuotient,
      coordinateLinearJet_apply, CubicRationalTriangleBox.verticalAxis]
  exact rationalCubicCoefficient_axis_coordinates hab hu hA.1 hμ
    B.w_c1 B.z_c1 hden (hA.2 (u, u) ⟨hu.1, le_rfl, hu.2⟩)
    (ne_of_gt (hc.trans_le (B.w_lower (u, u) ⟨hu.1, le_rfl, hu.2⟩)))
    rfl (B.z_diag u hu) (B.ρ_diag u hu) hU hVu hVv
    (B.r_u_diag u hu) (B.r_v_diag u hu)

/-- The rational source and its full first jet vanish on the diagonal. -/
theorem CubicRationalTriangleBox.source_diag_jet
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε)
    {u : ℝ} (hu : u ∈ Icc a b) :
    rationalCubicSource B.J B.r B.w B.z B.H (u, u) = 0 ∧
      fderivWithin ℝ (rationalCubicSource B.J B.r B.w B.z B.H)
        (closedCoordTriangle a b) (u, u) = 0 := by
  have hC := B.contDiffOn_coefficients hab hc hε hoff
  exact rationalCubicSource_diag_jet hab hu hC.2.2.1 B.H_c1 B.w_c1
    (fun p hp => ne_of_gt (hc.trans_le (B.w_lower p hp))) (B.H_diag u hu)

/-- The Fréchet quotient rule for real-valued functions on a normed real
space, in scalar form convenient for coordinate evaluations. -/
theorem fderiv_div_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hgne : g x ≠ 0) :
    fderiv ℝ (fun y => f y / g y) x =
      (1 / g x) • fderiv ℝ f x -
        (f x / g x ^ 2) • fderiv ℝ g x := by
  have hginv := (hasFDerivAt_inv hgne).comp x hg.hasFDerivAt
  have hmul := hf.hasFDerivAt.mul hginv
  change fderiv ℝ (f * ((fun y : ℝ => y⁻¹) ∘ g)) x = _
  rw [hmul.fderiv]
  ext e
  simp only [add_apply, sub_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  field_simp [hgne]
  ring

/-- At an interior off-diagonal point, the relative first jet of a cubic
over linear quotient is the ordinary quotient-rule jet. -/
theorem CubicRationalTriangleBox.linearQuotient_jet_interior
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ interior (closedCoordTriangle a b)) :
    fderivWithin ℝ (cubicLinearQuotient B.J B.r)
      (closedCoordTriangle a b) p =
        (1 / B.r p) • fderivWithin ℝ B.J (closedCoordTriangle a b) p -
          (B.J p / B.r p ^ 2) •
            fderivWithin ℝ B.r (closedCoordTriangle a b) p := by
  let K := closedCoordTriangle a b
  have hp' : p ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hp
  have hpK : p ∈ K := interior_subset hp
  have hnhds : K ∈ nhds p := mem_interior_iff_mem_nhds.mp hp
  have hrne : B.r p ≠ 0 := by
    rw [B.r_factor p hpK]
    exact mul_ne_zero (sub_ne_zero.mpr hp'.2.1.ne')
      (ne_of_gt (hc.trans_le (B.ρ_lower p hpK)))
  have hJa : DifferentiableAt ℝ B.J p :=
    ((B.J_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hra : DifferentiableAt ℝ B.r p :=
    ((B.r_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hevent : cubicLinearQuotient B.J B.r =ᶠ[nhds p]
      (fun q => B.J q / B.r q) := by
    filter_upwards [isOpen_interior.mem_nhds hp] with q hq
    have hq' : q ∈ openCoordTriangle a b := by
      simpa only [K, interior_closedCoordTriangle] using hq
    simp [cubicLinearQuotient, hq'.2.1]
  have hleft : fderivWithin ℝ (cubicLinearQuotient B.J B.r) K p =
      fderiv ℝ (cubicLinearQuotient B.J B.r) p :=
    fderivWithin_of_mem_nhds hnhds
  have hJrw : fderivWithin ℝ B.J K p = fderiv ℝ B.J p :=
    fderivWithin_of_mem_nhds hnhds
  have hrrw : fderivWithin ℝ B.r K p = fderiv ℝ B.r p :=
    fderivWithin_of_mem_nhds hnhds
  rw [hleft, hJrw, hrrw]
  rw [hevent.fderiv_eq, fderiv_div_real hJa hra hrne]

/-- At an interior off-diagonal point, the relative first jet of the
cubic-over-square quotient is its ordinary squared-quotient jet. -/
theorem CubicRationalTriangleBox.squaredQuotient_jet_interior
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ interior (closedCoordTriangle a b)) :
    fderivWithin ℝ (cubicSquaredQuotient B.J B.r)
      (closedCoordTriangle a b) p =
        (1 / B.r p ^ 2) • fderivWithin ℝ B.J (closedCoordTriangle a b) p -
          (2 * B.J p / B.r p ^ 3) •
            fderivWithin ℝ B.r (closedCoordTriangle a b) p := by
  let K := closedCoordTriangle a b
  have hp' : p ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hp
  have hpK : p ∈ K := interior_subset hp
  have hnhds : K ∈ nhds p := mem_interior_iff_mem_nhds.mp hp
  have hrne : B.r p ≠ 0 := by
    rw [B.r_factor p hpK]
    exact mul_ne_zero (sub_ne_zero.mpr hp'.2.1.ne')
      (ne_of_gt (hc.trans_le (B.ρ_lower p hpK)))
  have hJa : DifferentiableAt ℝ B.J p :=
    ((B.J_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hra : DifferentiableAt ℝ B.r p :=
    ((B.r_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hevent : cubicSquaredQuotient B.J B.r =ᶠ[nhds p]
      (fun q => B.J q / B.r q ^ 2) := by
    filter_upwards [isOpen_interior.mem_nhds hp] with q hq
    have hq' : q ∈ openCoordTriangle a b := by
      simpa only [K, interior_closedCoordTriangle] using hq
    simp [cubicSquaredQuotient, hq'.2.1]
  have hleft : fderivWithin ℝ (cubicSquaredQuotient B.J B.r) K p =
      fderiv ℝ (cubicSquaredQuotient B.J B.r) p :=
    fderivWithin_of_mem_nhds hnhds
  have hJrw : fderivWithin ℝ B.J K p = fderiv ℝ B.J p :=
    fderivWithin_of_mem_nhds hnhds
  have hrrw : fderivWithin ℝ B.r K p = fderiv ℝ B.r p :=
    fderivWithin_of_mem_nhds hnhds
  rw [hleft, hJrw, hrrw]
  rw [hevent.fderiv_eq, fderiv_div_sq hJa hra hrne]

end intervalIntegral

end
