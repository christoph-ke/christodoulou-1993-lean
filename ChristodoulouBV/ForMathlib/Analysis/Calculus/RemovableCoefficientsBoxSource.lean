module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxLedgerJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsSourceQuotient
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quadratic source products from rational cubic coefficients

The rational coefficient and the linearly vanishing source factor form a
quadratic numerator. Its value and first-jet bounds are the inputs for the
final uniformly positive quotient.
-/

public section

open Set

namespace intervalIntegral

/-- Linear value-bound coefficient for the rational cubic factor. -/
@[expose] noncomputable def CubicRationalFullPairBox.coefficientValueBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  (B.pair.J₀ / c ^ 2) * (B.C * B.V) * B.ε⁻¹

/-- Uniform coordinate-jet bound for the rational cubic factor. -/
@[expose] noncomputable def CubicRationalFullPairBox.coefficientJetBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  let A₀ := B.pair.J₀ / c ^ 2
  let A₁ := B.pair.J₁ / c ^ 2 + 2 * B.pair.J₀ * B.pair.R₁ / c ^ 3
  let W₀ := B.C * B.V
  let W₁ := B.L * (B.C + B.V)
  let Z₀ := B.ε⁻¹
  let Z₁ := (B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2) / B.ε ^ 2
  A₁ * W₀ * Z₀ + A₀ * W₁ * Z₀ + A₀ * W₀ * Z₁

/-- Linear difference-bound coefficient for the rational cubic factor. -/
@[expose] noncomputable def CubicRationalFullPairBox.coefficientValueSubBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  let A₀ := B.pair.J₀ / c ^ 2
  let AΔ₀ := B.pair.JΔ₀ / c ^ 2 + 2 * B.pair.J₀ / c ^ 3
  let W₀ := B.C * B.V
  let WΔ₀ := B.C + B.V
  let Z₀ := B.ε⁻¹
  let ZΔ₀ := (B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2) / B.ε ^ 2
  AΔ₀ * W₀ * Z₀ + A₀ * WΔ₀ * Z₀ + A₀ * W₀ * ZΔ₀

/-- Nine-term coordinate-jet difference coefficient for the rational cubic
factor. -/
@[expose] noncomputable def CubicRationalFullPairBox.coefficientJetSubBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  let A₀ := B.pair.J₀ / c ^ 2
  let A₁ := B.pair.J₁ / c ^ 2 + 2 * B.pair.J₀ * B.pair.R₁ / c ^ 3
  let AΔ₀ := B.pair.JΔ₀ / c ^ 2 + 2 * B.pair.J₀ / c ^ 3
  let AΔ₁ := B.pair.JΔ₁ / c ^ 2 + 2 * B.pair.J₁ / c ^ 3 +
    2 * B.pair.JΔ₀ * B.pair.R₁ / c ^ 3 +
    2 * B.pair.J₀ * B.pair.RΔ / c ^ 3 +
    6 * B.pair.J₀ * B.pair.R₁ / c ^ 4
  let W₀ := B.C * B.V
  let W₁ := B.L * (B.C + B.V)
  let WΔ₀ := B.C + B.V
  let WΔ₁ := B.C + B.V + 2 * B.L
  let μ₁ := B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2
  let μΔ₀ := B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2
  let μΔ₁ := B.pair.JΔ₁ / c + B.pair.J₁ / c ^ 2 +
    B.pair.JΔ₀ * B.pair.R₁ / c ^ 2 +
    B.pair.J₀ * B.pair.RΔ / c ^ 2 +
    2 * B.pair.J₀ * B.pair.R₁ / c ^ 3
  let Z₀ := B.ε⁻¹
  let Z₁ := μ₁ / B.ε ^ 2
  let ZΔ₀ := μΔ₀ / B.ε ^ 2
  let ZΔ₁ := μΔ₁ / B.ε ^ 2 + 2 * μ₁ * μΔ₀ / B.ε ^ 3
  AΔ₁ * W₀ * Z₀ + A₁ * WΔ₀ * Z₀ + A₁ * W₀ * ZΔ₀ +
    AΔ₀ * W₁ * Z₀ + A₀ * WΔ₁ * Z₀ + A₀ * W₁ * ZΔ₀ +
    AΔ₀ * W₀ * Z₁ + A₀ * WΔ₀ * Z₁ + A₀ * W₀ * ZΔ₁

/-- The quadratic numerator of the rational source quotient. -/
@[expose] noncomputable def CubicRationalTriangleBox.sourceNumerator
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) : ℝ :=
  -(rationalCubicCoefficient B.J B.r B.w B.z p * B.H p)

/-- The product-rule coordinate-jet expression for the quadratic source
numerator. -/
@[expose] noncomputable def CubicRationalTriangleBox.sourceNumeratorJet
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p e : ℝ × ℝ) : ℝ :=
  -((fderivWithin ℝ
      (rationalCubicCoefficient B.J B.r B.w B.z)
      (closedCoordTriangle a b) p) e * B.H p +
    rationalCubicCoefficient B.J B.r B.w B.z p *
      (fderivWithin ℝ B.H (closedCoordTriangle a b) p) e)

/-- The source numerators inherit quadratic value bounds and the exact
two-term quadratic difference bound. -/
theorem CubicRationalFullPairBox.sourceNumerator_value_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |B.pair.first.sourceNumerator p| ≤
        (B.coefficientValueBound * B.H₀) * (p.2 - p.1) ^ 2 ∧
      |B.pair.second.sourceNumerator p| ≤
        (B.coefficientValueBound * B.H₀) * (p.2 - p.1) ^ 2 ∧
      |B.pair.first.sourceNumerator p -
        B.pair.second.sourceNumerator p| ≤
          (B.coefficientValueSubBound * B.H₀ +
            B.coefficientValueBound * B.HΔ₀) *
            (p.2 - p.1) ^ 2 * B.pair.D := by
  intro p hp
  let d := p.2 - p.1
  have hd : 0 ≤ d := sub_nonneg.mpr hp.2.1
  have hK := B.coefficient_value_bounds hab hc p hp
  have hH := B.source_bound p hp
  have hK₀ : 0 ≤ B.coefficientValueBound := by
    have hJ0 := B.pair.J₀_nonneg
    have hC := B.C_nonneg
    have hV := B.V_nonneg
    have hε := B.ε_pos
    dsimp [CubicRationalFullPairBox.coefficientValueBound]
    positivity
  have hKΔ₀ : 0 ≤ B.coefficientValueSubBound := by
    have hJ0 := B.pair.J₀_nonneg
    have hJd := B.pair.JΔ₀_nonneg
    have hC := B.C_nonneg
    have hV := B.V_nonneg
    have hε := B.ε_pos
    dsimp [CubicRationalFullPairBox.coefficientValueSubBound]
    positivity
  have hP₁ : |B.pair.first.sourceNumerator p| ≤
      (B.coefficientValueBound * B.H₀) * d ^ 2 := by
    rw [CubicRationalTriangleBox.sourceNumerator, abs_neg, abs_mul]
    calc
      _ ≤ (B.coefficientValueBound * d) * (B.H₀ * d) := by
        gcongr
        · exact hK.1
        · exact hH.1
      _ = _ := by ring
  have hP₂ : |B.pair.second.sourceNumerator p| ≤
      (B.coefficientValueBound * B.H₀) * d ^ 2 := by
    rw [CubicRationalTriangleBox.sourceNumerator, abs_neg, abs_mul]
    calc
      _ ≤ (B.coefficientValueBound * d) * (B.H₀ * d) := by
        gcongr
        · exact hK.2.1
        · exact hH.2
      _ = _ := by ring
  have hPΔ := abs_mul_sub_mul_le_of_linear_gap_bounds
    hd B.pair.D_nonneg hK₀ hKΔ₀
    hK.2.1 hK.2.2 hH.1 (B.source_sub_bound p hp)
  have hPΔ' : |B.pair.first.sourceNumerator p -
      B.pair.second.sourceNumerator p| ≤
        (B.coefficientValueSubBound * B.H₀ +
          B.coefficientValueBound * B.HΔ₀) * d ^ 2 * B.pair.D := by
    convert hPΔ using 1
    simp only [CubicRationalTriangleBox.sourceNumerator,
      neg_sub_neg]
    exact abs_sub_comm _ _
  exact ⟨hP₁, hP₂, hPΔ'⟩

/-- The quadratic source numerator has linear coordinate jets, and its
two-input jet difference has the four product-rule terms. -/
theorem CubicRationalFullPairBox.sourceNumerator_jet_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |B.pair.first.sourceNumeratorJet p e| ≤
          (B.coefficientJetBound * B.H₀ +
            B.coefficientValueBound * B.H₁) * (p.2 - p.1) ∧
        |B.pair.second.sourceNumeratorJet p e| ≤
          (B.coefficientJetBound * B.H₀ +
            B.coefficientValueBound * B.H₁) * (p.2 - p.1) ∧
        |B.pair.first.sourceNumeratorJet p e -
          B.pair.second.sourceNumeratorJet p e| ≤
            (B.coefficientJetSubBound * B.H₀ +
              B.coefficientJetBound * B.HΔ₀ +
              B.coefficientValueSubBound * B.H₁ +
              B.coefficientValueBound * B.HΔ₁) *
                (p.2 - p.1) * B.pair.D := by
  intro p hp e he
  let d := p.2 - p.1
  have hd : 0 ≤ d := sub_nonneg.mpr hp.2.1
  have hK := B.coefficient_value_bounds hab hc p hp
  have hKi := B.coefficient_jet_bounds hab hc p hp e he
  have hH := B.source_bound p hp
  have hHi := B.source_jet_bound p hp e he
  have hK₀ : 0 ≤ B.coefficientValueBound := by
    have hJ0 := B.pair.J₀_nonneg
    have hC := B.C_nonneg
    have hV := B.V_nonneg
    have hε := B.ε_pos
    dsimp [CubicRationalFullPairBox.coefficientValueBound]
    positivity
  have hKΔ₀ : 0 ≤ B.coefficientValueSubBound := by
    have hJ0 := B.pair.J₀_nonneg
    have hJd := B.pair.JΔ₀_nonneg
    have hC := B.C_nonneg
    have hV := B.V_nonneg
    have hε := B.ε_pos
    dsimp [CubicRationalFullPairBox.coefficientValueSubBound]
    positivity
  have hK₁ : 0 ≤ B.coefficientJetBound := by
    have hJ0 := B.pair.J₀_nonneg
    have hJ1 := B.pair.J₁_nonneg
    have hR1 := B.pair.R₁_nonneg
    have hC := B.C_nonneg
    have hV := B.V_nonneg
    have hL := B.L_nonneg
    have hε := B.ε_pos
    dsimp [CubicRationalFullPairBox.coefficientJetBound]
    positivity
  have hPjet (k ki h hi : ℝ)
      (hk : |k| ≤ B.coefficientValueBound * d)
      (hki : |ki| ≤ B.coefficientJetBound)
      (hh : |h| ≤ B.H₀ * d)
      (hhi : |hi| ≤ B.H₁) :
      |-(ki * h + k * hi)| ≤
        (B.coefficientJetBound * B.H₀ +
          B.coefficientValueBound * B.H₁) * d := by
    rw [abs_neg]
    calc
      _ ≤ |ki * h| + |k * hi| := abs_add_le _ _
      _ ≤ B.coefficientJetBound * (B.H₀ * d) +
          (B.coefficientValueBound * d) * B.H₁ := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul hki hh (abs_nonneg _) hK₁)
          (mul_le_mul hk hhi (abs_nonneg _)
            (mul_nonneg hK₀ hd))
      _ = _ := by ring
  have hP₁ : |B.pair.first.sourceNumeratorJet p e| ≤
      (B.coefficientJetBound * B.H₀ +
        B.coefficientValueBound * B.H₁) * d := by
    change |-((
      (fderivWithin ℝ
        (rationalCubicCoefficient B.pair.first.J B.pair.first.r
          B.pair.first.w B.pair.first.z)
        (closedCoordTriangle a b) p) e * B.pair.first.H p) +
      rationalCubicCoefficient B.pair.first.J B.pair.first.r
        B.pair.first.w B.pair.first.z p *
          (fderivWithin ℝ B.pair.first.H
            (closedCoordTriangle a b) p) e)| ≤ _
    exact hPjet _ _ _ _ hK.1 hKi.1 hH.1 hHi.1
  have hP₂ : |B.pair.second.sourceNumeratorJet p e| ≤
      (B.coefficientJetBound * B.H₀ +
        B.coefficientValueBound * B.H₁) * d := by
    change |-((
      (fderivWithin ℝ
        (rationalCubicCoefficient B.pair.second.J B.pair.second.r
          B.pair.second.w B.pair.second.z)
        (closedCoordTriangle a b) p) e * B.pair.second.H p) +
      rationalCubicCoefficient B.pair.second.J B.pair.second.r
        B.pair.second.w B.pair.second.z p *
          (fderivWithin ℝ B.pair.second.H
            (closedCoordTriangle a b) p) e)| ≤ _
    exact hPjet _ _ _ _ hK.2.1 hKi.2.1 hH.2 hHi.2
  have hPΔ := abs_productJet_sub_le_of_linear_gap_bounds
    hd B.pair.D_nonneg hK₀ hKΔ₀
    hK.2.1 hK.2.2 hKi.2.1 hKi.2.2
    hH.1 (B.source_sub_bound p hp)
    hHi.1 (B.source_jet_sub_bound p hp e he)
  have hPΔ' : |B.pair.first.sourceNumeratorJet p e -
      B.pair.second.sourceNumeratorJet p e| ≤
        (B.coefficientJetSubBound * B.H₀ +
          B.coefficientJetBound * B.HΔ₀ +
          B.coefficientValueSubBound * B.H₁ +
          B.coefficientValueBound * B.HΔ₁) * d * B.pair.D := by
    convert hPΔ using 1
    · simp only [CubicRationalTriangleBox.sourceNumeratorJet,
        neg_sub_neg]
      exact abs_sub_comm _ _
    · rfl
  exact ⟨hP₁, hP₂, hPΔ'⟩

end intervalIntegral

end
