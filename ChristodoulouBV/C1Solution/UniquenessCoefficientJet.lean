module

public import ChristodoulouBV.C1Solution.UniquenessRegularProductJetDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing jet of the canonical mixed coefficient

The reciprocal mass gap and the three regular factors have a product-rule
jet on the full closed triangle, including the axis.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The outgoing jet of the reciprocal mass gap is the usual reciprocal
derivative wherever the gap is nonzero. -/
theorem inverse_one_sub_vertical_jet
    {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hu : UniqueDiffWithinAt ℝ K p) {μ : ℝ × ℝ → ℝ}
    (hμ : DifferentiableWithinAt ℝ μ K p) (hne : 1 - μ p ≠ 0) :
    (fderivWithin ℝ (fun q => (1 - μ q)⁻¹) K p) (0, 1) =
      (fderivWithin ℝ μ K p) (0, 1) / (1 - μ p) ^ 2 := by
  let g : ℝ × ℝ → ℝ := fun q => 1 - μ q
  have hg : DifferentiableWithinAt ℝ g K p := hμ.const_sub 1
  have hi : (fderivWithin ℝ (fun q => (g q)⁻¹) K p) (0, 1) =
      - (fderivWithin ℝ g K p) (0, 1) / (g p) ^ 2 := by
    have hc := fderivWithin_comp p (s := K) (t := Set.univ)
      (g := fun x : ℝ => x⁻¹) (differentiableAt_inv hne).differentiableWithinAt
      hg (by intro q hq; trivial) hu
    change fderivWithin ℝ (fun q => (g q)⁻¹) K p = _ at hc
    rw [hc, fderivWithin_univ, fderiv_inv]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  rw [hi]
  simp only [g, fderivWithin_const_sub hu, neg_apply, neg_neg]

/-- The three-factor product rule for an outgoing coordinate derivative. -/
theorem triple_product_vertical_jet
    {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hu : UniqueDiffWithinAt ℝ K p) {a w z : ℝ × ℝ → ℝ}
    (ha : DifferentiableWithinAt ℝ a K p)
    (hw : DifferentiableWithinAt ℝ w K p)
    (hz : DifferentiableWithinAt ℝ z K p) :
    (fderivWithin ℝ (fun q => a q * w q * z q) K p) (0, 1) =
      (fderivWithin ℝ a K p) (0, 1) * w p * z p +
      a p * (fderivWithin ℝ w K p) (0, 1) * z p +
      a p * w p * (fderivWithin ℝ z K p) (0, 1) := by
  have h₁ := fderivWithin_fun_mul hu (ha.mul hw) hz
  have h₂ := fderivWithin_fun_mul hu ha hw
  change fderivWithin ℝ (a * w) K p = _ at h₂
  change fderivWithin ℝ (fun q => a q * w q * z q) K p = _ at h₁
  rw [h₁, h₂]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- The canonical mixed coefficient has the nine-term ledger's underlying
three-factor outgoing jet, with its reciprocal factor written explicitly. -/
theorem canonical_mixed_coefficient_vertical_jet_eq
    {b T : ℝ} (hT : 0 < T) (hTb : T < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hgap : ∀ q ∈ closedCoordTriangle 0 T,
      0 < 1 - canonicalMassRatio b S q)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    (fderivWithin ℝ (canonicalMixedCoefficient b S)
      (closedCoordTriangle 0 T) p) (0, 1) =
      (fderivWithin ℝ (canonicalMassOverRadiusSq b S)
        (closedCoordTriangle 0 T) p) (0, 1) *
          (S.lam p.1 p.2 * S.nu p.1 p.2) *
          (1 - canonicalMassRatio b S p)⁻¹ +
      canonicalMassOverRadiusSq b S p *
        (fderivWithin ℝ
          (fun q : ℝ × ℝ => S.lam q.1 q.2 * S.nu q.1 q.2)
          (closedCoordTriangle 0 T) p) (0, 1) *
          (1 - canonicalMassRatio b S p)⁻¹ +
      canonicalMassOverRadiusSq b S p *
        (S.lam p.1 p.2 * S.nu p.1 p.2) *
          ((fderivWithin ℝ (canonicalMassRatio b S)
            (closedCoordTriangle 0 T) p) (0, 1) /
              (1 - canonicalMassRatio b S p) ^ 2) := by
  let K := closedCoordTriangle 0 T
  let a := canonicalMassOverRadiusSq b S
  let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2 * S.nu q.1 q.2
  let μ := canonicalMassRatio b S
  let z : ℝ × ℝ → ℝ := fun q => (1 - μ q)⁻¹
  have hu : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hT)) p hp
  have ha : DifferentiableWithinAt ℝ a K p :=
    ((canonicalMassOverRadiusSq_contDiffOn hT hTb H).differentiableOn
      (by norm_num)) p hp
  have hw : DifferentiableWithinAt ℝ w K p := by
    have hf := five_fields_contDiffOn hT hTb H
    exact ((hf.1.mul hf.2.1).differentiableOn (by norm_num)) p hp
  have hμ : DifferentiableWithinAt ℝ μ K p :=
    ((canonicalMassRatio_contDiffOn hT hTb H).differentiableOn
      (by norm_num)) p hp
  have hne : 1 - μ p ≠ 0 := ne_of_gt (hgap p hp)
  have hz : DifferentiableWithinAt ℝ z K p :=
    (hμ.const_sub 1).inv hne
  have hjet := triple_product_vertical_jet hu ha hw hz
  have hzinv := inverse_one_sub_vertical_jet hu hμ hne
  change (fderivWithin ℝ (fun q => a q * w q * z q) K p) (0, 1) = _ at hjet
  have hEq : canonicalMixedCoefficient b S =
      (fun q => a q * w q * z q) := by
    funext q
    simp only [canonicalMixedCoefficient, a, w, z, μ, div_eq_mul_inv]
    ring
  rw [hEq, hjet, hzinv]

end ChristodoulouBV.C1Solution

end
