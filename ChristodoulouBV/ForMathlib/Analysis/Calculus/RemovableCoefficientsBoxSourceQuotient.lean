module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxSource
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quotient bounds for quadratic rational sources

The last coefficient is the quadratic source product divided by the
uniformly positive regular weight. Its value estimates are direct
applications of the scalar quadratic quotient ledger.
-/

public section

open Set

namespace intervalIntegral

/-- Quadratic value-bound coefficient for the source numerator. -/
@[expose] noncomputable def CubicRationalFullPairBox.sourceProductValueBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  B.coefficientValueBound * B.H₀

/-- Linear coordinate-jet bound for the source numerator. -/
@[expose] noncomputable def CubicRationalFullPairBox.sourceProductJetBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  B.coefficientJetBound * B.H₀ + B.coefficientValueBound * B.H₁

/-- Quadratic value-difference coefficient for the source numerator. -/
@[expose] noncomputable def CubicRationalFullPairBox.sourceProductValueSubBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  B.coefficientValueSubBound * B.H₀ +
    B.coefficientValueBound * B.HΔ₀

/-- Linear coordinate-jet difference coefficient for the source
numerator. -/
@[expose] noncomputable def CubicRationalFullPairBox.sourceProductJetSubBound
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) : ℝ :=
  B.coefficientJetSubBound * B.H₀ +
    B.coefficientJetBound * B.HΔ₀ +
    B.coefficientValueSubBound * B.H₁ +
    B.coefficientValueBound * B.HΔ₁

/-- The rational source is its quadratic source numerator divided by the
positive regular weight. -/
theorem CubicRationalTriangleBox.source_eq_numerator_div
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) :
    rationalCubicSource B.J B.r B.w B.z B.H p =
      B.sourceNumerator p / B.w p := by
  simp only [rationalCubicSource,
    CubicRationalTriangleBox.sourceNumerator, div_eq_mul_inv]
  ring

/-- The final rational source satisfies quadratic value bounds and a
quadratic two-input difference estimate on the whole closed triangle. -/
theorem CubicRationalFullPairBox.source_value_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |rationalCubicSource B.pair.first.J B.pair.first.r
        B.pair.first.w B.pair.first.z B.pair.first.H p| ≤
          (B.sourceProductValueBound / c) * (p.2 - p.1) ^ 2 ∧
      |rationalCubicSource B.pair.second.J B.pair.second.r
        B.pair.second.w B.pair.second.z B.pair.second.H p| ≤
          (B.sourceProductValueBound / c) * (p.2 - p.1) ^ 2 ∧
      |rationalCubicSource B.pair.first.J B.pair.first.r
          B.pair.first.w B.pair.first.z B.pair.first.H p -
        rationalCubicSource B.pair.second.J B.pair.second.r
          B.pair.second.w B.pair.second.z B.pair.second.H p| ≤
            (B.sourceProductValueSubBound / c +
              B.sourceProductValueBound / c ^ 2) *
              (p.2 - p.1) ^ 2 * B.pair.D := by
  intro p hp
  have hP := B.sourceNumerator_value_bounds hab hc p hp
  have hw₁ := B.pair.first.w_lower p hp
  have hw₂ := B.pair.second.w_lower p hp
  have hwd := (B.regular_sub_bound p hp).1
  rw [B.pair.first.source_eq_numerator_div,
    B.pair.second.source_eq_numerator_div]
  have h₁ := abs_div_le_of_quadratic_gap_bound hc hw₁ hP.1
  have h₂ := abs_div_le_of_quadratic_gap_bound hc hw₂ hP.2.1
  have hΔ := abs_div_sub_div_le_of_quadratic_gap_bounds
    hc hw₁ hw₂ hwd hP.2.1 hP.2.2
  exact ⟨h₁, h₂, hΔ⟩

/-- On the interior, the rational source coordinate jet is the ordinary
quotient-rule expression for its quadratic numerator and positive weight. -/
theorem CubicRationalTriangleBox.sourceQuotientJet_interior
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε)
    {p : ℝ × ℝ} (hp : p ∈ interior (closedCoordTriangle a b))
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (rationalCubicSource B.J B.r B.w B.z B.H)
      (closedCoordTriangle a b) p) e =
        B.sourceNumeratorJet p e / B.w p -
          B.sourceNumerator p *
            (fderivWithin ℝ B.w (closedCoordTriangle a b) p) e /
              B.w p ^ 2 := by
  rw [B.source_jet_interior hab hc hε hoff hp e]
  simp only [CubicRationalTriangleBox.sourceNumerator,
    CubicRationalTriangleBox.sourceNumeratorJet]
  ring

/-- The final rational source has linear first-jet value bounds and the
five-term two-input derivative difference bound on the closed triangle. -/
theorem CubicRationalFullPairBox.source_jet_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ
          (rationalCubicSource B.pair.first.J B.pair.first.r
            B.pair.first.w B.pair.first.z B.pair.first.H)
          (closedCoordTriangle a b) p) e| ≤
            (B.sourceProductJetBound / c +
              B.sourceProductValueBound * B.L / c ^ 2) *
                (p.2 - p.1) ∧
        |(fderivWithin ℝ
          (rationalCubicSource B.pair.second.J B.pair.second.r
            B.pair.second.w B.pair.second.z B.pair.second.H)
          (closedCoordTriangle a b) p) e| ≤
            (B.sourceProductJetBound / c +
              B.sourceProductValueBound * B.L / c ^ 2) *
                (p.2 - p.1) ∧
        |(fderivWithin ℝ
            (rationalCubicSource B.pair.first.J B.pair.first.r
              B.pair.first.w B.pair.first.z B.pair.first.H)
            (closedCoordTriangle a b) p) e -
          (fderivWithin ℝ
            (rationalCubicSource B.pair.second.J B.pair.second.r
              B.pair.second.w B.pair.second.z B.pair.second.H)
            (closedCoordTriangle a b) p) e| ≤
              (B.sourceProductJetSubBound / c +
                B.sourceProductJetBound / c ^ 2 +
                B.sourceProductValueSubBound * B.L / c ^ 2 +
                B.sourceProductValueBound / c ^ 2 +
                2 * B.sourceProductValueBound * B.L / c ^ 3) *
                  (p.2 - p.1) * B.pair.D := by
  let K := closedCoordTriangle a b
  have hQ₁ := (B.pair.first.contDiffOn_coefficients hab hc B.ε_pos
    (fun q hq _ => by linarith [B.complement_first q hq])).2.2.2
  have hQ₂ := (B.pair.second.contDiffOn_coefficients hab hc B.ε_pos
    (fun q hq _ => by linarith [B.complement_second q hq])).2.2.2
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  intro p hp e he
  have hJ0 := B.pair.J₀_nonneg
  have hJ1 := B.pair.J₁_nonneg
  have hJd0 := B.pair.JΔ₀_nonneg
  have hJd1 := B.pair.JΔ₁_nonneg
  have hR1 := B.pair.R₁_nonneg
  have hRd := B.pair.RΔ_nonneg
  have hC := B.C_nonneg
  have hV := B.V_nonneg
  have hL := B.L_nonneg
  have hH0 := B.H₀_nonneg
  have hH1 := B.H₁_nonneg
  have hHd0 := B.HΔ₀_nonneg
  have hHd1 := B.HΔ₁_nonneg
  have hε := B.ε_pos
  have hP₀ : 0 ≤ B.sourceProductValueBound := by
    dsimp [CubicRationalFullPairBox.sourceProductValueBound,
      CubicRationalFullPairBox.coefficientValueBound]
    positivity
  have hP₁ : 0 ≤ B.sourceProductJetBound := by
    dsimp [CubicRationalFullPairBox.sourceProductJetBound,
      CubicRationalFullPairBox.coefficientJetBound,
      CubicRationalFullPairBox.coefficientValueBound]
    positivity
  have hPΔ₀ : 0 ≤ B.sourceProductValueSubBound := by
    dsimp [CubicRationalFullPairBox.sourceProductValueSubBound,
      CubicRationalFullPairBox.coefficientValueSubBound,
      CubicRationalFullPairBox.coefficientValueBound]
    positivity
  have hPΔ₁ : 0 ≤ B.sourceProductJetSubBound := by
    dsimp [CubicRationalFullPairBox.sourceProductJetSubBound,
      CubicRationalFullPairBox.coefficientJetSubBound,
      CubicRationalFullPairBox.coefficientJetBound,
      CubicRationalFullPairBox.coefficientValueSubBound,
      CubicRationalFullPairBox.coefficientValueBound]
    positivity
  have hcont₁ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (rationalCubicSource B.pair.first.J B.pair.first.r
          B.pair.first.w B.pair.first.z B.pair.first.H) K q) e) K :=
    (hQ₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hcont₂ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (rationalCubicSource B.pair.second.J B.pair.second.r
          B.pair.second.w B.pair.second.z B.pair.second.H) K q) e) K :=
    (hQ₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hbound₁ : ContinuousOn
      (fun q : ℝ × ℝ =>
        (B.sourceProductJetBound / c +
          B.sourceProductValueBound * B.L / c ^ 2) * (q.2 - q.1)) K := by fun_prop
  have hboundΔ : ContinuousOn
      (fun q : ℝ × ℝ =>
        (B.sourceProductJetSubBound / c +
          B.sourceProductJetBound / c ^ 2 +
          B.sourceProductValueSubBound * B.L / c ^ 2 +
          B.sourceProductValueBound / c ^ 2 +
          2 * B.sourceProductValueBound * B.L / c ^ 3) *
            (q.2 - q.1) * B.pair.D) K := by fun_prop
  have hfirst := le_on_closedCoordTriangle_of_interior hab
    hcont₁.abs hbound₁ (by
      intro q hq
      have hqK : q ∈ K := interior_subset hq
      have hq' : q ∈ openCoordTriangle a b := by
        simpa only [K, interior_closedCoordTriangle] using hq
      have hd : 0 ≤ q.2 - q.1 := sub_nonneg.mpr hq'.2.1.le
      have hdle : q.2 - q.1 ≤ 1 := by
        have hcoord : a ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ b := hqK
        linarith [B.pair.width_le_one]
      have hP := B.sourceNumerator_value_bounds hab hc q hqK
      have hPi := B.sourceNumerator_jet_bounds hab hc q hqK e he
      rw [B.pair.first.sourceQuotientJet_interior hab hc B.ε_pos
        (fun t ht _ => by linarith [B.complement_first t ht]) hq e]
      exact abs_quotientJet_le_of_quadratic_gap_bounds hc hd hdle
        hP₀ (B.pair.first.w_lower q hqK) hP.1 hPi.1
          (B.regular_jet_bound q hqK e he).1.1) p hp
  have hsecond := le_on_closedCoordTriangle_of_interior hab
    hcont₂.abs hbound₁ (by
      intro q hq
      have hqK : q ∈ K := interior_subset hq
      have hq' : q ∈ openCoordTriangle a b := by
        simpa only [K, interior_closedCoordTriangle] using hq
      have hd : 0 ≤ q.2 - q.1 := sub_nonneg.mpr hq'.2.1.le
      have hdle : q.2 - q.1 ≤ 1 := by
        have hcoord : a ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ b := hqK
        linarith [B.pair.width_le_one]
      have hP := B.sourceNumerator_value_bounds hab hc q hqK
      have hPi := B.sourceNumerator_jet_bounds hab hc q hqK e he
      rw [B.pair.second.sourceQuotientJet_interior hab hc B.ε_pos
        (fun t ht _ => by linarith [B.complement_second t ht]) hq e]
      exact abs_quotientJet_le_of_quadratic_gap_bounds hc hd hdle
        hP₀ (B.pair.second.w_lower q hqK) hP.2.1 hPi.2.1
          (B.regular_jet_bound q hqK e he).1.2) p hp
  have hdiff := le_on_closedCoordTriangle_of_interior hab
    (hcont₁.sub hcont₂).abs hboundΔ (by
      intro q hq
      have hqK : q ∈ K := interior_subset hq
      have hq' : q ∈ openCoordTriangle a b := by
        simpa only [K, interior_closedCoordTriangle] using hq
      have hd : 0 ≤ q.2 - q.1 := sub_nonneg.mpr hq'.2.1.le
      have hdle : q.2 - q.1 ≤ 1 := by
        have hcoord : a ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ b := hqK
        linarith [B.pair.width_le_one]
      have hP := B.sourceNumerator_value_bounds hab hc q hqK
      have hPi := B.sourceNumerator_jet_bounds hab hc q hqK e he
      simp only [Pi.sub_apply]
      rw [B.pair.first.sourceQuotientJet_interior hab hc B.ε_pos
          (fun t ht _ => by linarith [B.complement_first t ht]) hq e,
        B.pair.second.sourceQuotientJet_interior hab hc B.ε_pos
          (fun t ht _ => by linarith [B.complement_second t ht]) hq e]
      simpa only [mul_one] using abs_quotientJet_sub_le_of_quadratic_gap_bounds
        hc hd hdle B.pair.D_nonneg hP₀ hP₁ hPΔ₀ hPΔ₁
        B.L_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
        (B.pair.first.w_lower q hqK)
        (B.pair.second.w_lower q hqK)
        (B.regular_sub_bound q hqK).1
        hP.2.1 hP.2.2 hPi.2.1 hPi.2.2
        (B.regular_jet_bound q hqK e he).1.1
        (B.regular_jet_bound q hqK e he).1.2
        (by simpa only [one_mul] using
          (B.regular_jet_sub_bound q hqK e he).1)) p hp
  exact ⟨hfirst, hsecond, hdiff⟩

end intervalIntegral

end
