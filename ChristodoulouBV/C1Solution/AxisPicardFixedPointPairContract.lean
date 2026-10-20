module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairDistance
import Mathlib.Tactic

/-! # Contractive coordinate distance for the axis Picard update -/

public section

noncomputable section

namespace ChristodoulouBV.AxisPicard

/-- All three updated first jets contract in coordinate distance with the
explicit coefficient `7 Cstar T`. -/
theorem Box.picardJets_coordinateDistance_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.picardJets D hab hM hsmall).coordinateDistance
      (y.picardJets D hab hM hsmall) ≤
      7 * (numericalLedger M).Cstar M * (b - a) *
        x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let T := b - a
  let Z := x.1.coordinateDistance y.1
  let C := B.Cstar M
  have hT : 0 ≤ T := sub_nonneg.mpr hab.le
  have hZ : 0 ≤ Z := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hcoef := B.coefficients_le_Cstar hM
  have hTsmall : T ≤ 1 / 100 := by
    have h := B.coefficient_mul_width_le hab hM hsmall hcoef.1
    simpa only [one_mul] using h
  have hT2 : T ^ 2 ≤ T := by
    nlinarith only [mul_nonneg hT (by linarith : 0 ≤ (1 : ℝ) - T)]
  have hT3 : T ^ 3 ≤ T := by
    have h2 := mul_le_mul_of_nonneg_left hT2 hT
    nlinarith only [h2, hT2]
  have hK0 : B.KΔ₀ * T * Z ≤ C * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef.2.2.2.2.2.2.2.1 hT) hZ
  have hK1 : B.KΔ₁ * T * Z ≤ C * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef.2.2.2.2.2.2.2.2.1 hT) hZ
  have hQ0 : B.QΔ₀ * T * Z ≤ C * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef.2.2.2.2.2.2.2.2.2.1 hT) hZ
  have hQ1 : B.QΔ₁ * T * Z ≤ C * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef.2.2.2.2.2.2.2.2.2.2.1 hT) hZ
  have hK0pos : 0 ≤ B.KΔ₀ := B.nonneg.2.2.2.2.2.1
  have hQ0pos : 0 ≤ B.QΔ₀ := B.nonneg.2.2.2.2.2.2.2.1
  have hQ1pos : 0 ≤ B.QΔ₁ := B.nonneg.2.2.2.2.2.2.2.2
  have hK0sq : B.KΔ₀ * T ^ 2 * Z ≤ B.KΔ₀ * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT2 hK0pos) hZ
  have hQ0cu : B.QΔ₀ * T ^ 3 * Z ≤ B.QΔ₀ * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT3 hQ0pos) hZ
  have hQ0sq : B.QΔ₀ * T ^ 2 * Z ≤ B.QΔ₀ * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT2 hQ0pos) hZ
  have hQ1sq : B.QΔ₁ * T ^ 2 * Z ≤ B.QΔ₁ * T * Z := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT2 hQ1pos) hZ
  have hLam := x.picard_lam_coordinateDistance_bound D y hab hM hsmall
  have hNu := x.picard_nu_coordinateDistance_bound D y hab hM hsmall
  have hh := x.picard_h_coordinateDistance_bound D y hab hM hsmall
  dsimp only [B, T, Z, C] at *
  have hLam' : (x.picardJets D hab hM hsmall).1.coordinateDistance
      (y.picardJets D hab hM hsmall).1 ≤ 7 * C * T * Z := by
    nlinarith [hLam, hK0sq, hK0, hK1]
  have hNu' : (x.picardJets D hab hM hsmall).2.1.coordinateDistance
      (y.picardJets D hab hM hsmall).2.1 ≤ 7 * C * T * Z := by
    have hTsq : 2 * T ^ 2 ≤ T := by
      nlinarith only [mul_nonneg hT (by linarith : 0 ≤ (1 / 2 : ℝ) - T)]
    have hK0sq' : 2 * B.KΔ₀ * T ^ 2 * Z ≤ B.KΔ₀ * T * Z := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTsq hK0pos) hZ
      nlinarith only [h]
    nlinarith [hNu, hK0sq', hK0, hK1]
  have hh' : (x.picardJets D hab hM hsmall).2.2.coordinateDistance
      (y.picardJets D hab hM hsmall).2.2 ≤ 7 * C * T * Z := by
    have hCTZ : 0 ≤ C * T * Z :=
      mul_nonneg (mul_nonneg (by linarith only [hcoef.1]) hT) hZ
    calc
      _ ≤ B.QΔ₀ * T ^ 3 * Z +
          2 * (B.QΔ₀ + B.QΔ₁) * T ^ 2 * Z := hh
      _ ≤ B.QΔ₀ * T * Z +
          2 * (B.QΔ₀ + B.QΔ₁) * T * Z := by
            nlinarith only [hQ0cu, hQ0sq, hQ1sq]
      _ ≤ 5 * C * T * Z := by nlinarith only [hQ0, hQ1]
      _ ≤ 7 * C * T * Z := by nlinarith only [hCTZ]
  change max ((x.picardJets D hab hM hsmall).1.coordinateDistance
      (y.picardJets D hab hM hsmall).1)
      (max ((x.picardJets D hab hM hsmall).2.1.coordinateDistance
        (y.picardJets D hab hM hsmall).2.1)
        ((x.picardJets D hab hM hsmall).2.2.coordinateDistance
          (y.picardJets D hab hM hsmall).2.2)) ≤ _
  exact max_le hLam' (max_le hNu' hh')

end ChristodoulouBV.AxisPicard

end
