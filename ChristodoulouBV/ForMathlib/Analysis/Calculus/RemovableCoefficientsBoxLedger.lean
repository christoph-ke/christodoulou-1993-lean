module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxFactors
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Function-level value ledger for rational cubic coefficients

The common box's cubic quotient, regular product, and complementary
reciprocal bounds assemble through the scalar three-factor ledger.
-/

public section

open Set

namespace intervalIntegral

/-- The rational cubic coefficients have a common linear value bound and a
linear two-input difference bound, with the three exact product terms. -/
theorem CubicRationalFullPairBox.coefficient_value_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    let A₀ := B.pair.J₀ / c ^ 2
    let AΔ₀ := B.pair.JΔ₀ / c ^ 2 + 2 * B.pair.J₀ / c ^ 3
    let W₀ := B.C * B.V
    let WΔ₀ := B.C + B.V
    let Z₀ := B.ε⁻¹
    let ZΔ₀ := (B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2) / B.ε ^ 2
    ∀ p ∈ closedCoordTriangle a b,
      |rationalCubicCoefficient B.pair.first.J B.pair.first.r
        B.pair.first.w B.pair.first.z p| ≤ A₀ * W₀ * Z₀ * (p.2 - p.1) ∧
      |rationalCubicCoefficient B.pair.second.J B.pair.second.r
        B.pair.second.w B.pair.second.z p| ≤ A₀ * W₀ * Z₀ * (p.2 - p.1) ∧
      |rationalCubicCoefficient B.pair.first.J B.pair.first.r
          B.pair.first.w B.pair.first.z p -
        rationalCubicCoefficient B.pair.second.J B.pair.second.r
          B.pair.second.w B.pair.second.z p| ≤
            (AΔ₀ * W₀ * Z₀ + A₀ * WΔ₀ * Z₀ +
              A₀ * W₀ * ZΔ₀) * (p.2 - p.1) * B.pair.D := by
  dsimp only
  intro p hp
  let d := p.2 - p.1
  let A₀ := B.pair.J₀ / c ^ 2
  let AΔ₀ := B.pair.JΔ₀ / c ^ 2 + 2 * B.pair.J₀ / c ^ 3
  let W₀ := B.C * B.V
  let WΔ₀ := B.C + B.V
  let Z₀ := B.ε⁻¹
  let ZΔ₀ := (B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2) / B.ε ^ 2
  let A₁ := cubicSquaredQuotient B.pair.first.J B.pair.first.r p
  let A₂ := cubicSquaredQuotient B.pair.second.J B.pair.second.r p
  let W₁ := B.pair.first.regularProduct p
  let W₂ := B.pair.second.regularProduct p
  let Z₁ := B.pair.first.inverseComplement p
  let Z₂ := B.pair.second.inverseComplement p
  have hd : 0 ≤ d := sub_nonneg.mpr hp.2.1
  have hdle : d ≤ 1 := by
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    dsimp [d]
    linarith [B.pair.width_le_one]
  have hA := B.pair.squaredQuotient_value_bounds hc p hp
  have hW := B.regularProduct_bounds p hp (1, 0) (by simp)
  have hWd := (B.regularProduct_sub_bounds p hp (1, 0) (by simp)).1
  have hZ := B.inverseComplement_bounds hab hc p hp (1, 0) (by simp)
  have hZd := (B.inverseComplement_sub_bounds hab hc p hp (1, 0) (by simp)).1
  have hJ0 := B.pair.J₀_nonneg
  have hJd0 := B.pair.JΔ₀_nonneg
  have hC := B.C_nonneg
  have hV := B.V_nonneg
  have hε := B.ε_pos
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hAΔ₀ : 0 ≤ AΔ₀ := by dsimp [AΔ₀]; positivity
  have hW₀ : 0 ≤ W₀ := mul_nonneg B.C_nonneg B.V_nonneg
  have hWΔ₀ : 0 ≤ WΔ₀ := add_nonneg B.C_nonneg B.V_nonneg
  have hZΔ₀ : 0 ≤ ZΔ₀ := by dsimp [ZΔ₀]; positivity
  have hK₁ : |rationalCubicCoefficient B.pair.first.J B.pair.first.r
      B.pair.first.w B.pair.first.z p| ≤ A₀ * W₀ * Z₀ * d := by
    change |A₁ * (W₁ * Z₁)| ≤ _
    rw [abs_mul, abs_mul]
    calc
      |A₁| * (|W₁| * |Z₁|) ≤ (A₀ * d) * (W₀ * Z₀) := by
        gcongr
        · exact hA.1
        · exact hW.1
        · exact hZ.1
      _ = _ := by ring
  have hK₂ : |rationalCubicCoefficient B.pair.second.J B.pair.second.r
      B.pair.second.w B.pair.second.z p| ≤ A₀ * W₀ * Z₀ * d := by
    change |A₂ * (W₂ * Z₂)| ≤ _
    rw [abs_mul, abs_mul]
    calc
      |A₂| * (|W₂| * |Z₂|) ≤ (A₀ * d) * (W₀ * Z₀) := by
        gcongr
        · exact hA.2.1
        · exact hW.2.1
        · exact hZ.2.1
      _ = _ := by ring
  have hKΔ := abs_triple_mul_sub_le_of_gap_bounds
    hd hdle B.pair.D_nonneg hA₀ hAΔ₀ hW₀ hWΔ₀ hZΔ₀
    hA.2.1 hA.2.2 hW.1 hW.2.1 hWd hZ.1 hZd
  have hKΔ' : |rationalCubicCoefficient B.pair.first.J B.pair.first.r
        B.pair.first.w B.pair.first.z p -
      rationalCubicCoefficient B.pair.second.J B.pair.second.r
        B.pair.second.w B.pair.second.z p| ≤
        (AΔ₀ * W₀ * Z₀ + A₀ * WΔ₀ * Z₀ +
          A₀ * W₀ * ZΔ₀) * d * B.pair.D := by
    convert hKΔ using 1
    simp only [rationalCubicCoefficient,
      CubicRationalTriangleBox.regularProduct,
      CubicRationalTriangleBox.inverseComplement, div_eq_mul_inv]
    ring
  exact ⟨hK₁, hK₂, hKΔ'⟩

end intervalIntegral

end
