module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointComplement
import all ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxVolterraPair
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxSourceQuotient
import Mathlib.Tactic

/-!
# The full two-input rational coefficient box for axis Picard inputs

The Volterra pair, numerical mass margin, regular factors, and weighted
source factor provide every field of the established full rational pair box.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Two boxed Picard inputs at the explicit lifetime supply the full common
rational coefficient box, with no independent coefficient assumptions. -/
def Box.toCubicRationalFullPairBox {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    intervalIntegral.CubicRationalFullPairBox a b (1 / 4) := by
  let hsize : b - a ≤ 1 :=
    (numerical_lifetime_bounds hM (sub_pos.mpr hab) hsmall).1
  let B := x.toCubicRationalPairBox y hab hM hsize
  have hBw₁ : B.first.w = x.1.1.extendValue := by dsimp only [B]; rfl
  have hBw₂ : B.second.w = y.1.1.extendValue := by dsimp only [B]; rfl
  have hBz₁ : B.first.z = x.1.2.1.extendValue := by dsimp only [B]; rfl
  have hBz₂ : B.second.z = y.1.2.1.extendValue := by dsimp only [B]; rfl
  have hBH₁ : B.first.H = x.1.toTriple.meanError := by dsimp only [B]; rfl
  have hBH₂ : B.second.H = y.1.toTriple.meanError := by dsimp only [B]; rfl
  have hBD : B.D = x.1.coordinateDistance y.1 := by dsimp only [B]; rfl
  let H₁ := intervalIntegral.weightedDiagonalErrorDerivativeCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M)
  let HΔ₀ := intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient
    (1 / 4) (3 / 4) (2 * M)
  let HΔ₁ := intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M)
  have hH₁ : 0 ≤ H₁ := by
    dsimp [H₁, intervalIntegral.weightedDiagonalErrorDerivativeCoefficient]
    positivity
  have hHΔ₀ : 0 ≤ HΔ₀ := by
    dsimp [HΔ₀, intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient]
    positivity
  have hHΔ₁ : 0 ≤ HΔ₁ := by
    dsimp [HΔ₁, intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient,
      intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient]
    positivity
  refine {
    pair := B
    ε := 3 / 4
    ε_pos := by norm_num
    complement_first := ?_
    complement_second := ?_
    C := 3 / 4
    V := 3 / 4
    L := 2 * M
    H₀ := 2 * M
    H₁ := H₁
    HΔ₀ := HΔ₀
    HΔ₁ := HΔ₁
    C_nonneg := by norm_num
    V_nonneg := by norm_num
    L_nonneg := by linarith only [hM]
    H₀_nonneg := by linarith only [hM]
    H₁_nonneg := hH₁
    HΔ₀_nonneg := hHΔ₀
    HΔ₁_nonneg := hHΔ₁
    regular_bound := ?_
    regular_jet_bound := ?_
    regular_sub_bound := ?_
    regular_jet_sub_bound := ?_
    source_bound := ?_
    source_jet_bound := ?_
    source_sub_bound := ?_
    source_jet_sub_bound := ?_
  }
  · intro p hp
    exact (x.pair_complement_bounds y hab hM hsmall hp).1
  · intro p hp
    exact (x.pair_complement_bounds y hab hM hsmall hp).2
  · intro p hp
    rw [hBw₁, hBw₂, hBz₁, hBz₂]
    have hxw := x.lam_value_bounds hp
    have hyw := y.lam_value_bounds hp
    exact ⟨⟨by rw [abs_of_nonneg (by linarith only [hxw.1])]; exact hxw.2,
      by rw [abs_of_nonneg (by linarith only [hyw.1])]; exact hyw.2⟩,
      ⟨x.nu_value_bound hp, y.nu_value_bound hp⟩⟩
  · intro p hp e he
    rw [hBw₁, hBw₂, hBz₁, hBz₂]
    rcases he with rfl | rfl
    · have hxw := x.lam_coordinate_bound hp (0 : Fin 2)
      have hyw := y.lam_coordinate_bound hp (0 : Fin 2)
      have hxz := x.nu_coordinate_bound hp (0 : Fin 2)
      have hyz := y.nu_coordinate_bound hp (0 : Fin 2)
      simp only [coordinateDirection, ↓reduceIte] at hxw hyw hxz hyz
      rw [x.lam_fderivWithin hab hp, y.lam_fderivWithin hab hp,
        x.nu_fderivWithin hab hp, y.nu_fderivWithin hab hp]
      exact ⟨⟨hxw, hyw⟩, ⟨hxz, hyz⟩⟩
    · have hxw := x.lam_coordinate_bound hp (1 : Fin 2)
      have hyw := y.lam_coordinate_bound hp (1 : Fin 2)
      have hxz := x.nu_coordinate_bound hp (1 : Fin 2)
      have hyz := y.nu_coordinate_bound hp (1 : Fin 2)
      simp only [coordinateDirection, Fin.isValue] at hxw hyw hxz hyz
      rw [x.lam_fderivWithin hab hp, y.lam_fderivWithin hab hp,
        x.nu_fderivWithin hab hp, y.nu_fderivWithin hab hp]
      exact ⟨⟨hxw, hyw⟩, ⟨hxz, hyz⟩⟩
  · intro p hp
    rw [hBw₁, hBw₂, hBz₁, hBz₂, hBD]
    have h := (x.input_difference_bounds y hab.le hp).1
    exact ⟨h.1, h.2.1⟩
  · intro p hp e he
    rw [hBw₁, hBw₂, hBz₁, hBz₂, hBD]
    rcases he with rfl | rfl
    · have h := (x.input_difference_bounds y hab.le hp).2 (0 : Fin 2)
      rw [x.lam_fderivWithin hab hp, y.lam_fderivWithin hab hp,
        x.nu_fderivWithin hab hp, y.nu_fderivWithin hab hp]
      simpa [coordinateDirection] using ⟨h.1, h.2.1⟩
    · have h := (x.input_difference_bounds y hab.le hp).2 (1 : Fin 2)
      rw [x.lam_fderivWithin hab hp, y.lam_fderivWithin hab hp,
        x.nu_fderivWithin hab hp, y.nu_fderivWithin hab hp]
      simpa [coordinateDirection] using ⟨h.1, h.2.1⟩
  · intro p hp
    rw [hBH₁, hBH₂]
    exact ⟨(x.meanError_bounds hab hM hsize hp).1,
      (y.meanError_bounds hab hM hsize hp).1⟩
  · intro p hp e he
    rw [hBH₁, hBH₂]
    rcases he with rfl | rfl
    · exact ⟨(x.meanError_bounds hab hM hsize hp).2.1,
        (y.meanError_bounds hab hM hsize hp).2.1⟩
    · exact ⟨(x.meanError_bounds hab hM hsize hp).2.2,
        (y.meanError_bounds hab hM hsize hp).2.2⟩
  · intro p hp
    rw [hBH₁, hBH₂, hBD]
    exact (x.meanError_difference_bounds y hab hM hsize hp).1
  · intro p hp e he
    rw [hBH₁, hBH₂, hBD]
    rcases he with rfl | rfl
    · exact (x.meanError_difference_bounds y hab hM hsize hp).2.1
    · exact (x.meanError_difference_bounds y hab hM hsize hp).2.2

end ChristodoulouBV.AxisPicard

end
