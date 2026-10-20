module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxLedger
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Coordinate-jet ledger for rational cubic coefficients

The scalar nine-term three-factor estimate controls the two-input first
jet. Continuity extends the interior calculation to the closed triangle.
-/

public section

open Set

namespace intervalIntegral

/-- The first-jet value bound and nine-term two-input difference bound
for rational cubic coefficients hold at every interior point. -/
theorem CubicRationalFullPairBox.coefficient_jet_interior_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
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
    ∀ p ∈ interior (closedCoordTriangle a b),
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ
          (rationalCubicCoefficient B.pair.first.J B.pair.first.r
            B.pair.first.w B.pair.first.z)
          (closedCoordTriangle a b) p) e| ≤
          A₁ * W₀ * Z₀ + A₀ * W₁ * Z₀ + A₀ * W₀ * Z₁ ∧
        |(fderivWithin ℝ
          (rationalCubicCoefficient B.pair.second.J B.pair.second.r
            B.pair.second.w B.pair.second.z)
          (closedCoordTriangle a b) p) e| ≤
          A₁ * W₀ * Z₀ + A₀ * W₁ * Z₀ + A₀ * W₀ * Z₁ ∧
        |(fderivWithin ℝ
            (rationalCubicCoefficient B.pair.first.J B.pair.first.r
              B.pair.first.w B.pair.first.z)
            (closedCoordTriangle a b) p) e -
          (fderivWithin ℝ
            (rationalCubicCoefficient B.pair.second.J B.pair.second.r
              B.pair.second.w B.pair.second.z)
            (closedCoordTriangle a b) p) e| ≤
          (AΔ₁ * W₀ * Z₀ + A₁ * WΔ₀ * Z₀ + A₁ * W₀ * ZΔ₀ +
            AΔ₀ * W₁ * Z₀ + A₀ * WΔ₁ * Z₀ + A₀ * W₁ * ZΔ₀ +
            AΔ₀ * W₀ * Z₁ + A₀ * WΔ₀ * Z₁ + A₀ * W₀ * ZΔ₁) *
            B.pair.D := by
  dsimp only
  intro p hp e he
  let d := p.2 - p.1
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
  let a₁ := cubicSquaredQuotient B.pair.first.J B.pair.first.r p
  let a₂ := cubicSquaredQuotient B.pair.second.J B.pair.second.r p
  let ai₁ := (fderivWithin ℝ
    (cubicSquaredQuotient B.pair.first.J B.pair.first.r)
    (closedCoordTriangle a b) p) e
  let ai₂ := (fderivWithin ℝ
    (cubicSquaredQuotient B.pair.second.J B.pair.second.r)
    (closedCoordTriangle a b) p) e
  let w₁ := B.pair.first.regularProduct p
  let w₂ := B.pair.second.regularProduct p
  let wi₁ := B.pair.first.regularProductJet p e
  let wi₂ := B.pair.second.regularProductJet p e
  let z₁ := B.pair.first.inverseComplement p
  let z₂ := B.pair.second.inverseComplement p
  let zi₁ := B.pair.first.inverseComplementJet p e
  let zi₂ := B.pair.second.inverseComplementJet p e
  have hpK : p ∈ closedCoordTriangle a b := interior_subset hp
  have hstrict : p.1 < p.2 := by
    have hp' : p ∈ openCoordTriangle a b := by
      simpa only [interior_closedCoordTriangle] using hp
    exact hp'.2.1
  have hd : 0 ≤ d := sub_nonneg.mpr hstrict.le
  have hdle : d ≤ 1 := by
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hpK
    dsimp [d]
    linarith [B.pair.width_le_one]
  have hA := B.pair.squaredQuotient_value_bounds hc p hpK
  have hAi := B.pair.squaredQuotient_jet_bounds hab hc p hpK e he
  have hAid := B.pair.squaredQuotient_jet_sub_bound hab hc p hpK e he
  have hW := B.regularProduct_bounds p hpK e he
  have hWd := B.regularProduct_sub_bounds p hpK e he
  have hZ := B.inverseComplement_bounds hab hc p hpK e he
  have hZd := B.inverseComplement_sub_bounds hab hc p hpK e he
  have hJ0 := B.pair.J₀_nonneg
  have hJ1 := B.pair.J₁_nonneg
  have hJd0 := B.pair.JΔ₀_nonneg
  have hJd1 := B.pair.JΔ₁_nonneg
  have hR1 := B.pair.R₁_nonneg
  have hRd := B.pair.RΔ_nonneg
  have hC := B.C_nonneg
  have hV := B.V_nonneg
  have hL := B.L_nonneg
  have hε := B.ε_pos
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hAΔ₀ : 0 ≤ AΔ₀ := by dsimp [AΔ₀]; positivity
  have hAΔ₁ : 0 ≤ AΔ₁ := by dsimp [AΔ₁]; positivity
  have hW₀ : 0 ≤ W₀ := by dsimp [W₀]; positivity
  have hW₁ : 0 ≤ W₁ := by dsimp [W₁]; positivity
  have hWΔ₀ : 0 ≤ WΔ₀ := by dsimp [WΔ₀]; positivity
  have hWΔ₁ : 0 ≤ WΔ₁ := by dsimp [WΔ₁]; positivity
  have hμ₁ : 0 ≤ μ₁ := by dsimp [μ₁]; positivity
  have hμΔ₀ : 0 ≤ μΔ₀ := by dsimp [μΔ₀]; positivity
  have hμΔ₁ : 0 ≤ μΔ₁ := by dsimp [μΔ₁]; positivity
  have hZ₁ : 0 ≤ Z₁ := by dsimp [Z₁]; positivity
  have hZΔ₀ : 0 ≤ ZΔ₀ := by dsimp [ZΔ₀]; positivity
  have hZΔ₁ : 0 ≤ ZΔ₁ := by dsimp [ZΔ₁]; positivity
  have ha₁ : |a₁| ≤ A₀ * d := hA.1
  have ha₂ : |a₂| ≤ A₀ * d := hA.2.1
  have had : |a₁ - a₂| ≤ AΔ₀ * d * B.pair.D := hA.2.2
  have hai₁ : |ai₁| ≤ A₁ := hAi.1
  have hai₂ : |ai₂| ≤ A₁ := hAi.2
  have haid : |ai₁ - ai₂| ≤ AΔ₁ * B.pair.D := hAid
  have hw₁ : |w₁| ≤ W₀ := hW.1
  have hw₂ : |w₂| ≤ W₀ := hW.2.1
  have hwd : |w₁ - w₂| ≤ WΔ₀ * B.pair.D := hWd.1
  have hwi₁ : |wi₁| ≤ W₁ := hW.2.2.1
  have hwi₂ : |wi₂| ≤ W₁ := hW.2.2.2
  have hwid : |wi₁ - wi₂| ≤ WΔ₁ * B.pair.D := hWd.2
  have hz₁ : |z₁| ≤ Z₀ := hZ.1
  have hzd : |z₁ - z₂| ≤ ZΔ₀ * d ^ 2 * B.pair.D := hZd.1
  have hzi₁ : |zi₁| ≤ Z₁ * d := hZ.2.2.1
  have hzid : |zi₁ - zi₂| ≤ ZΔ₁ * d * B.pair.D := hZd.2
  have hfirst := abs_tripleProductJet_le
    hA₀ hW₀ hA₁ hW₁
    (ha₁.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdle hA₀))
    hai₁ hw₁ hwi₁ hz₁
    (hzi₁.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdle hZ₁))
  have hsecond := abs_tripleProductJet_le
    hA₀ hW₀ hA₁ hW₁
    (ha₂.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdle hA₀))
    hai₂ hw₂ hwi₂ hZ.2.1
    (hZ.2.2.2.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hdle hZ₁))
  have hdiff := abs_tripleProductJet_sub_le_of_gap_bounds
    hd hdle B.pair.D_nonneg
    hA₀ hA₁ hAΔ₀ hAΔ₁ hW₀ hW₁ hWΔ₀ hWΔ₁
    hZ₁ hZΔ₀ hZΔ₁ ha₂ had hai₂ haid
    hw₁ hw₂ hwd hwi₁ hwi₂ hwid hz₁ hzd hzi₁ hzid
  have hformula₁ :
      (fderivWithin ℝ
        (rationalCubicCoefficient B.pair.first.J B.pair.first.r
          B.pair.first.w B.pair.first.z)
        (closedCoordTriangle a b) p) e =
          ai₁ * w₁ * z₁ + a₁ * wi₁ * z₁ + a₁ * w₁ * zi₁ := by
    convert B.pair.first.coefficient_jet_interior hab hc B.ε_pos
      (fun q hq _ => by linarith [B.complement_first q hq]) hp e using 1
    dsimp [a₁, ai₁, w₁, wi₁, z₁, zi₁,
      CubicRationalTriangleBox.regularProduct,
      CubicRationalTriangleBox.regularProductJet,
      CubicRationalTriangleBox.inverseComplement,
      CubicRationalTriangleBox.inverseComplementJet]
  have hformula₂ :
      (fderivWithin ℝ
        (rationalCubicCoefficient B.pair.second.J B.pair.second.r
          B.pair.second.w B.pair.second.z)
        (closedCoordTriangle a b) p) e =
          ai₂ * w₂ * z₂ + a₂ * wi₂ * z₂ + a₂ * w₂ * zi₂ := by
    convert B.pair.second.coefficient_jet_interior hab hc B.ε_pos
      (fun q hq _ => by linarith [B.complement_second q hq]) hp e using 1
    dsimp [a₂, ai₂, w₂, wi₂, z₂, zi₂,
      CubicRationalTriangleBox.regularProduct,
      CubicRationalTriangleBox.regularProductJet,
      CubicRationalTriangleBox.inverseComplement,
      CubicRationalTriangleBox.inverseComplementJet]
  rw [hformula₁, hformula₂]
  exact ⟨by simpa only [mul_one] using hfirst,
    by simpa only [mul_one] using hsecond, hdiff⟩

/-- The first-jet value bound and nine-term two-input difference bound
extend to the entire closed triangle, including its diagonal. -/
theorem CubicRationalFullPairBox.coefficient_jet_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
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
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ
          (rationalCubicCoefficient B.pair.first.J B.pair.first.r
            B.pair.first.w B.pair.first.z)
          (closedCoordTriangle a b) p) e| ≤
          A₁ * W₀ * Z₀ + A₀ * W₁ * Z₀ + A₀ * W₀ * Z₁ ∧
        |(fderivWithin ℝ
          (rationalCubicCoefficient B.pair.second.J B.pair.second.r
            B.pair.second.w B.pair.second.z)
          (closedCoordTriangle a b) p) e| ≤
          A₁ * W₀ * Z₀ + A₀ * W₁ * Z₀ + A₀ * W₀ * Z₁ ∧
        |(fderivWithin ℝ
            (rationalCubicCoefficient B.pair.first.J B.pair.first.r
              B.pair.first.w B.pair.first.z)
            (closedCoordTriangle a b) p) e -
          (fderivWithin ℝ
            (rationalCubicCoefficient B.pair.second.J B.pair.second.r
              B.pair.second.w B.pair.second.z)
            (closedCoordTriangle a b) p) e| ≤
          (AΔ₁ * W₀ * Z₀ + A₁ * WΔ₀ * Z₀ + A₁ * W₀ * ZΔ₀ +
            AΔ₀ * W₁ * Z₀ + A₀ * WΔ₁ * Z₀ + A₀ * W₁ * ZΔ₀ +
            AΔ₀ * W₀ * Z₁ + A₀ * WΔ₀ * Z₁ + A₀ * W₀ * ZΔ₁) *
            B.pair.D := by
  dsimp only
  intro p hp e he
  let K := closedCoordTriangle a b
  have hC₁ := (B.pair.first.contDiffOn_coefficients hab hc B.ε_pos
    (fun q hq _ => by linarith [B.complement_first q hq])).2.2.1
  have hC₂ := (B.pair.second.contDiffOn_coefficients hab hc B.ε_pos
    (fun q hq _ => by linarith [B.complement_second q hq])).2.2.1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont₁ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (rationalCubicCoefficient B.pair.first.J B.pair.first.r
          B.pair.first.w B.pair.first.z) K q) e) K :=
    (hC₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hcont₂ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (rationalCubicCoefficient B.pair.second.J B.pair.second.r
          B.pair.second.w B.pair.second.z) K q) e) K :=
    (hC₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hInt := B.coefficient_jet_interior_bounds hab hc
  dsimp only at hInt
  have hfirst := le_on_closedCoordTriangle_of_interior hab
    hcont₁.abs continuousOn_const (fun q hq => (hInt q hq e he).1) p hp
  have hsecond := le_on_closedCoordTriangle_of_interior hab
    hcont₂.abs continuousOn_const (fun q hq => (hInt q hq e he).2.1) p hp
  have hdiff := le_on_closedCoordTriangle_of_interior hab
    (hcont₁.sub hcont₂).abs continuousOn_const
    (fun q hq => (hInt q hq e he).2.2) p hp
  exact ⟨hfirst, hsecond, hdiff⟩

end intervalIntegral

end
