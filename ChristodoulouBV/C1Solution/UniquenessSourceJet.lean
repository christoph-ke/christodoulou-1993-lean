module

public import ChristodoulouBV.C1Solution.UniquenessCoefficientJetBound
public import ChristodoulouBV.C1Solution.UniquenessFinal
public import ChristodoulouBV.C1Solution.UniquenessBoxes
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing jet of the canonical quotient source

The source is the negative product of the mixed coefficient and the
regular source factor divided by `λ`. Its outgoing jet has the four
product and quotient terms used by the uniqueness ledger.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The outgoing derivative of the reciprocal of a nonzero real field. -/
theorem inverse_vertical_jet
    {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hu : UniqueDiffWithinAt ℝ K p) {f : ℝ × ℝ → ℝ}
    (hf : DifferentiableWithinAt ℝ f K p) (hne : f p ≠ 0) :
    (fderivWithin ℝ (fun q => (f q)⁻¹) K p) (0, 1) =
      -(fderivWithin ℝ f K p) (0, 1) / (f p) ^ 2 := by
  have hc := fderivWithin_comp p (s := K) (t := Set.univ)
    (g := fun x : ℝ => x⁻¹) (differentiableAt_inv hne).differentiableWithinAt
    hf (by intro q hq; trivial) hu
  change fderivWithin ℝ (fun q => (f q)⁻¹) K p = _ at hc
  rw [hc, fderivWithin_univ, fderiv_inv]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- The outgoing quotient rule for a negative two-factor numerator. -/
theorem negative_product_quotient_vertical_jet
    {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hu : UniqueDiffWithinAt ℝ K p)
    {k h lam : ℝ × ℝ → ℝ}
    (hk : DifferentiableWithinAt ℝ k K p)
    (hh : DifferentiableWithinAt ℝ h K p)
    (hlam : DifferentiableWithinAt ℝ lam K p)
    (hne : lam p ≠ 0) :
    (fderivWithin ℝ (fun q => -(k q * h q) / lam q) K p) (0, 1) =
      -((fderivWithin ℝ k K p) (0, 1) * h p +
        k p * (fderivWithin ℝ h K p) (0, 1)) / lam p +
        (k p * h p) * (fderivWithin ℝ lam K p) (0, 1) / lam p ^ 2 := by
  let z : ℝ × ℝ → ℝ := fun q => (lam q)⁻¹
  have hz : DifferentiableWithinAt ℝ z K p := hlam.inv hne
  have htriple := triple_product_vertical_jet hu hk hh hz
  have hinv := inverse_vertical_jet hu hlam hne
  have heq : (fun q => -(k q * h q) / lam q) =
      (fun q => -(k q * h q * z q)) := by
    funext q
    simp only [div_eq_mul_inv, z]
    ring
  rw [heq, fderivWithin_fun_neg hu]
  simp only [neg_apply]
  rw [htriple, hinv]
  simp only [div_eq_mul_inv]
  ring

/-- On the entire closed triangle, the outgoing quotient-source jet is
the product-rule expression fed to the scalar source ledger. -/
theorem canonical_quotient_source_vertical_jet_eq
    {b T : ℝ} (hT : 0 < T) (hTb : T < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    (fderivWithin ℝ (canonicalQuotientSource b S)
      (closedCoordTriangle 0 T) p) (0, 1) =
      -((fderivWithin ℝ (canonicalMixedCoefficient b S)
          (closedCoordTriangle 0 T) p) (0, 1) *
          canonicalSourceFactor S p +
        canonicalMixedCoefficient b S p *
          (fderivWithin ℝ (canonicalSourceFactor S)
            (closedCoordTriangle 0 T) p) (0, 1)) /
          S.lam p.1 p.2 +
      (canonicalMixedCoefficient b S p * canonicalSourceFactor S p) *
        (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
          (closedCoordTriangle 0 T) p) (0, 1) /
          (S.lam p.1 p.2) ^ 2 := by
  let K := closedCoordTriangle 0 T
  let k := canonicalMixedCoefficient b S
  let h := canonicalSourceFactor S
  let lam : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  have hu : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hT)) p hp
  have hk : DifferentiableWithinAt ℝ k K p :=
    ((canonicalMixedCoefficient_contDiffOn hT hTb H).differentiableOn
      (by norm_num)) p hp
  have hh : DifferentiableWithinAt ℝ h K p :=
    (((canonical_source_factor_box_inputs hT hTb H).1).differentiableOn
      (by norm_num)) p hp
  have hlam : DifferentiableWithinAt ℝ lam K p :=
    (((five_fields_contDiffOn hT hTb H).1).differentiableOn
      (by norm_num)) p hp
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hT hTb H
  have hne : lam p ≠ 0 := ne_of_gt (hc.trans_le (hcl p hp))
  have heq : canonicalQuotientSource b S =
      (fun q => -(k q * h q) / lam q) := by
    funext q
    simp only [canonicalQuotientSource, canonicalSourceFactor, k, h, lam]
    ring
  rw [heq]
  exact negative_product_quotient_vertical_jet hu hk hh hlam hne

end ChristodoulouBV.C1Solution

end
