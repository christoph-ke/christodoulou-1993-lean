module

public import ChristodoulouBV.C1Solution.Uniqueness
public import ChristodoulouBV.C1Solution.UniquenessLedger
public import ChristodoulouBV.C1Solution.UniquenessSlice
public import ChristodoulouBV.C1Solution.UniquenessBounds
import ChristodoulouBV.C1Solution.ExtractionRemovable
import ChristodoulouBV.C1Solution.ExtractionJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Equations for the outgoing quotient on a closed triangle

The quotient `h = α / λ` obeys an incoming equation with the removable
mixed coefficient. This identifies the source coefficient used in the
unrestricted uniqueness calculation, including on the regular axis.
-/

public section

open Set
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- The incoming source for the outgoing quotient `h = α / λ`, formed from
the canonical removable coefficient and the actual closed-triangle scalar. -/
@[expose] noncomputable def canonicalQuotientSource
    (b : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  canonicalMixedCoefficient b S p *
    (S.phi p.1 p.2 - outgoingQuotient S p) / S.lam p.1 p.2

/-- The source of the outgoing quotient has a continuous first jet on every
smaller closed triangle. -/
theorem canonicalQuotientSource_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalQuotientSource b S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hK := canonicalMixedCoefficient_contDiffOn hB hBb H
  have hphi := (five_fields_contDiffOn hB hBb H).2.2.1
  have hh := alpha_div_lam_contDiffOn hB hBb H
  have hlam := (five_fields_contDiffOn hB hBb H).1
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  change ContDiffOn ℝ 1
    (fun p => canonicalMixedCoefficient b S p *
      (S.phi p.1 p.2 - outgoingQuotient S p) / S.lam p.1 p.2) K
  exact (hK.mul (hphi.sub hh)).div hlam
    (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))

/-- On the whole closed triangle, including the axis, the incoming
relative derivative of `h = α / λ` equals its canonical source. -/
theorem outgoingQuotient_horizontal_jet {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (outgoingQuotient S)
      (closedCoordTriangle 0 B) p) (1, 0) =
      canonicalQuotientSource b S p := by
  let K := closedCoordTriangle 0 B
  let lam : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let alpha : ℝ × ℝ → ℝ := fun q => S.alpha q.1 q.2
  let h := outgoingQuotient S
  have hunique : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)) p hp
  have hlamC1 := (five_fields_contDiffOn hB hBb H).1
  have hhC1 := alpha_div_lam_contDiffOn hB hBb H
  have hlamDiff := hlamC1.differentiableOn (by norm_num) p hp
  have hhDiff := hhC1.differentiableOn (by norm_num) p hp
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hlamPos : 0 < lam p := hc.trans_le (hcl p hp)
  have heq : EqOn (fun q => h q * lam q) alpha K := by
    intro q hq
    have hqpos : lam q ≠ 0 := ne_of_gt (hc.trans_le (hcl q hq))
    change S.alpha q.1 q.2 / S.lam q.1 q.2 * S.lam q.1 q.2 =
      S.alpha q.1 q.2
    exact div_mul_cancel₀ _ hqpos
  have hjet := fderivWithin_congr' (𝕜 := ℝ) heq hp
  have hprod :
      (fderivWithin ℝ (fun q => h q * lam q) K p) (1, 0) =
        (fderivWithin ℝ h K p) (1, 0) * lam p +
          h p * (fderivWithin ℝ lam K p) (1, 0) := by
    have hmul := fderivWithin_fun_mul hunique hhDiff hlamDiff
    have hmul' := congrArg
      (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hmul
    simp only [add_apply, smul_apply, smul_eq_mul] at hmul'
    change (fderivWithin ℝ (fun q => h q * lam q) K p) (1, 0) =
      h p * (fderivWithin ℝ lam K p) (1, 0) +
        lam p * (fderivWithin ℝ h K p) (1, 0) at hmul'
    calc
      _ = h p * (fderivWithin ℝ lam K p) (1, 0) +
          lam p * (fderivWithin ℝ h K p) (1, 0) := hmul'
      _ = _ := by ring
  obtain ⟨hlamJet, _, halphaJet, _⟩ := four_mixed_coordinate_jets hB hBb H hp
  have heqn :
      (fderivWithin ℝ h K p) (1, 0) * lam p +
        h p * canonicalMixedCoefficient b S p =
          canonicalMixedCoefficient b S p * S.phi p.1 p.2 := by
    have hjetVal := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hjet
    rw [hprod] at hjetVal
    change (fderivWithin ℝ h K p) (1, 0) * lam p +
      h p * (fderivWithin ℝ lam K p) (1, 0) =
        (fderivWithin ℝ alpha K p) (1, 0) at hjetVal
    rw [hlamJet, halphaJet] at hjetVal
    exact hjetVal
  change (fderivWithin ℝ h K p) (1, 0) =
    canonicalMixedCoefficient b S p *
      (S.phi p.1 p.2 - h p) / lam p
  apply (eq_div_iff hlamPos.ne').2
  linear_combination heqn

/-- The incoming expansion on an outgoing ray is determined by its regular
axis value and the canonical mixed coefficient. -/
theorem nu_eq_neg_lam_axis_add_integral {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    S.nu u v = -S.lam u u +
      ∫ t in u..v, canonicalMixedCoefficient b S (u, t) := by
  have hFTC := integral_vertical_jet_eq_sub hB
    (five_fields_contDiffOn hB hBb H).2.1 hu huv hv
  have hintegral :
      (∫ t in u..v,
        (fderivWithin ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2)
          (closedCoordTriangle 0 B) (u, t)) (0, 1)) =
      ∫ t in u..v, canonicalMixedCoefficient b S (u, t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le huv] at ht
    have hp : (u, t) ∈ closedCoordTriangle 0 B := by
      change 0 ≤ u ∧ u ≤ t ∧ t ≤ B
      exact ⟨hu, ht.1, ht.2.trans hv⟩
    exact (four_mixed_coordinate_jets (p := (u, t)) hB hBb H hp).2.1
  rw [hintegral] at hFTC
  have haxis := nu_eq_neg_lam_axis hB hBb H
    (show u ∈ Icc 0 B from ⟨hu, huv.trans hv⟩)
  rw [haxis] at hFTC
  linarith only [hFTC]

end ChristodoulouBV.C1Solution

end
