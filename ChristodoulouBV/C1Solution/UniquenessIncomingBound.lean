module

public import ChristodoulouBV.C1Solution.UniquenessCoefficientPointwise
public import ChristodoulouBV.C1Solution.UniquenessCanonicalLedger
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing-ray control of the incoming expansion

The pointwise value difference of the mixed coefficient closes a scalar
Gronwall inequality for `|Δν(u,v)|` on each outgoing ray. Taking the moving
supremum then gives the incoming bound needed by the four-term ledger.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- A uniform bound on every point of a moving outgoing slice bounds its
compact moving supremum. -/
theorem movingSliceSup_le_of_slice_bound {T : ℝ} (_hT : 0 ≤ T)
    {f : ℝ × ℝ → ℝ} {u M : ℝ} (hu : u ∈ Icc 0 T)
    (hbound : ∀ v ∈ Icc u T, f (u, v) ≤ M) :
    movingSliceSup T f ⟨u, hu⟩ ≤ M := by
  let R : Set ℝ := ((fun t : Icc (0 : ℝ) 1 =>
    f (u, u + (T - u) * t.1)) '' Set.univ)
  have hR : R.Nonempty := by
    refine ⟨f (u, u), ⟨⟨0, by norm_num⟩, Set.mem_univ _, ?_⟩⟩
    simp
  change sSup R ≤ M
  apply csSup_le hR
  intro y hy
  obtain ⟨t, _, rfl⟩ := hy
  have hgap : 0 ≤ T - u := sub_nonneg.mpr hu.2
  have hfirst : 0 ≤ (T - u) * t.1 := mul_nonneg hgap t.2.1
  have hlast : 0 ≤ (T - u) * (1 - t.1) :=
    mul_nonneg hgap (sub_nonneg.mpr t.2.2)
  apply hbound
  constructor
  · linarith only [hfirst]
  · nlinarith only [hlast]

/-- The incoming expansion difference at a point is bounded by the
outgoing four-field difference on its ray, with the exact scalar Gronwall
factor from the audited ledger. -/
theorem canonical_incoming_component_le_outgoing_difference
    {b₁ b₂ T c C Bv V L ε : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hε : 0 < ε)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hnu₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₁.nu p.1 p.2| ≤ V)
    (hnu₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₂.nu p.1 p.2| ≤ V)
    (hgap₁ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    let ℓ := canonicalVerticalLedger B C Bv V L ε
    |S₁.nu u v - S₂.nu u v| ≤
      (2 * Real.exp ℓ.Kd - 1) * outgoingDifference T hT.le S₁ S₂ u := by
  dsimp only
  let K := closedCoordTriangle 0 T
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let ℓ := canonicalVerticalLedger B C Bv V L ε
  let D := outgoingDifference T hT.le S₁ S₂ u
  let n : ℝ → ℝ := fun t => |S₁.nu u t - S₂.nu u t|
  have huI : u ∈ Icc 0 T := ⟨hu, huv.trans hv⟩
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂ huI
  have hKd : 0 ≤ ℓ.Kd := (CanonicalVerticalLedger.nonneg B hc hC hBv hV hL hε).1
  have hpathcont : ContinuousOn (fun t : ℝ => (u, t)) (Icc u v) := by fun_prop
  have hpathmap : Set.MapsTo (fun t : ℝ => (u, t)) (Icc u v) K := by
    intro t ht
    exact ⟨hu, ht.1, ht.2.trans hv⟩
  have hνcont₁ : ContinuousOn (fun t => S₁.nu u t) (Icc u v) :=
    ((five_fields_contDiffOn hT hT₁ H₁).2.1.continuousOn).comp
      hpathcont hpathmap
  have hνcont₂ : ContinuousOn (fun t => S₂.nu u t) (Icc u v) :=
    ((five_fields_contDiffOn hT hT₂ H₂).2.1.continuousOn).comp
      hpathcont hpathmap
  have hncont : ContinuousOn n (Icc u v) := (hνcont₁.sub hνcont₂).abs
  have hKcont₁ : ContinuousOn (fun t => canonicalMixedCoefficient b₁ S₁ (u, t))
      (Icc u v) :=
    (canonicalMixedCoefficient_continuousOn hT hT₁ H₁).comp
      hpathcont hpathmap
  have hKcont₂ : ContinuousOn (fun t => canonicalMixedCoefficient b₂ S₂ (u, t))
      (Icc u v) :=
    (canonicalMixedCoefficient_continuousOn hT hT₂ H₂).comp
      hpathcont hpathmap
  have hKpoint (t : ℝ) (ht : t ∈ Icc u v) :
      |canonicalMixedCoefficient b₁ S₁ (u, t) -
        canonicalMixedCoefficient b₂ S₂ (u, t)| ≤
        ℓ.Kd * (D + n t) := by
    have hp : (u, t) ∈ K := ⟨hu, ht.1, ht.2.trans hv⟩
    have hraw := canonical_mixed_coefficient_value_sub_le_pointwise
      hT hTwidth hT₁ hT₂ hc hC hBv hV hε H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
      hgap₁ hgap₂ hp
    have hraw' : |canonicalMixedCoefficient b₁ S₁ (u, t) -
        canonicalMixedCoefficient b₂ S₂ (u, t)| ≤
          ℓ.Kd * (t - u) * (D + n t) := by
      convert hraw using 1; rfl
    have hgap : t - u ≤ 1 := by linarith only [hu, ht.2, hv, hTwidth]
    have hfac : 0 ≤ ℓ.Kd * (D + n t) :=
      mul_nonneg hKd (add_nonneg hD (abs_nonneg _))
    calc
      _ ≤ ℓ.Kd * (t - u) * (D + n t) := hraw'
      _ = (t - u) * (ℓ.Kd * (D + n t)) := by ring
      _ ≤ 1 * (ℓ.Kd * (D + n t)) :=
        mul_le_mul_of_nonneg_right hgap hfac
      _ = _ := by ring
  have hineq : ∀ t ∈ Icc u v,
      n t ≤ D + ℓ.Kd * ∫ s in u..t, (D + n s) := by
    intro t ht
    have hν₁ := nu_eq_neg_lam_axis_add_integral hT hT₁ H₁
      hu ht.1 (ht.2.trans hv)
    have hν₂ := nu_eq_neg_lam_axis_add_integral hT hT₂ H₂
      hu ht.1 (ht.2.trans hv)
    have hlamaxis := (outgoing_components_le_difference
      hT hT₁ hT₂ H₁ H₂ hu le_rfl (huv.trans hv)).1
    have hKint₁' : IntervalIntegrable
        (fun s => canonicalMixedCoefficient b₁ S₁ (u, s)) volume u t :=
      (hKcont₁.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hKint₂' : IntervalIntegrable
        (fun s => canonicalMixedCoefficient b₂ S₂ (u, s)) volume u t :=
      (hKcont₂.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hnint : IntervalIntegrable (fun s => D + n s) volume u t :=
      (continuousOn_const.add
        (hncont.mono (Icc_subset_Icc_right ht.2))).intervalIntegrable_of_Icc ht.1
    have hKsubint := hKint₁'.sub hKint₂'
    have hKabsint := hKsubint.abs
    have hmajorint := hnint.const_mul ℓ.Kd
    have hInt : |(∫ s in u..t, canonicalMixedCoefficient b₁ S₁ (u, s)) -
        (∫ s in u..t, canonicalMixedCoefficient b₂ S₂ (u, s))| ≤
        ℓ.Kd * ∫ s in u..t, (D + n s) := by
      rw [← intervalIntegral.integral_sub hKint₁' hKint₂']
      calc
        _ ≤ ∫ s in u..t,
            |canonicalMixedCoefficient b₁ S₁ (u, s) -
              canonicalMixedCoefficient b₂ S₂ (u, s)| :=
          intervalIntegral.abs_integral_le_integral_abs ht.1
        _ ≤ ∫ s in u..t, ℓ.Kd * (D + n s) := by
          apply intervalIntegral.integral_mono_on ht.1 hKabsint hmajorint
          intro s hs
          exact hKpoint s ⟨hs.1, hs.2.trans ht.2⟩
        _ = ℓ.Kd * ∫ s in u..t, (D + n s) := by
          rw [intervalIntegral.integral_const_mul]
    change |S₁.nu u t - S₂.nu u t| ≤ _
    rw [hν₁, hν₂]
    have htriangle := abs_add_le
      (-(S₁.lam u u - S₂.lam u u))
      ((∫ s in u..t, canonicalMixedCoefficient b₁ S₁ (u, s)) -
        (∫ s in u..t, canonicalMixedCoefficient b₂ S₂ (u, s)))
    have heq : (-S₁.lam u u + ∫ s in u..t, canonicalMixedCoefficient b₁ S₁ (u, s)) -
        (-S₂.lam u u + ∫ s in u..t, canonicalMixedCoefficient b₂ S₂ (u, s)) =
        -(S₁.lam u u - S₂.lam u u) +
          ((∫ s in u..t, canonicalMixedCoefficient b₁ S₁ (u, s)) -
           (∫ s in u..t, canonicalMixedCoefficient b₂ S₂ (u, s))) := by ring
    rw [heq]
    rw [abs_neg] at htriangle
    linarith only [htriangle, hlamaxis, hInt]
  have hgron := outgoing_nu_bound_of_volterra huv
    (show (1 : ℝ) ≤ 1 by norm_num)
    (by linarith only [hu, hv, hTwidth])
    hD hKd hncont (by
      intro t ht
      simpa only [mul_one] using hineq t ht)
  simpa only [n, one_pow, mul_one] using hgron

/-- The moving incoming seminorm is controlled by the moving outgoing
seminorm with the same scalar Gronwall factor. -/
theorem canonical_incoming_difference_le_outgoing_difference
    {b₁ b₂ T c C Bv V L ε : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hε : 0 < ε)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hnu₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₁.nu p.1 p.2| ≤ V)
    (hnu₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₂.nu p.1 p.2| ≤ V)
    (hgap₁ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    let ℓ := canonicalVerticalLedger B C Bv V L ε
    incomingDifference T hT.le S₁ S₂ u ≤
      (2 * Real.exp ℓ.Kd - 1) * outgoingDifference T hT.le S₁ S₂ u := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let ℓ := canonicalVerticalLedger B C Bv V L ε
  let M := (2 * Real.exp ℓ.Kd - 1) * outgoingDifference T hT.le S₁ S₂ u
  have hslice : ∀ v ∈ Icc u T,
      incomingDifferenceSummand S₁ S₂ (u, v) ≤ M := by
    intro v hv
    change |S₁.nu u v - S₂.nu u v| ≤ M
    exact canonical_incoming_component_le_outgoing_difference
      hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
      hgap₁ hgap₂ hu.1 hv.1 hv.2
  have hsup := movingSliceSup_le_of_slice_bound hT.le hu hslice
  change movingSliceSup T (incomingDifferenceSummand S₁ S₂) ⟨u, hu⟩ ≤ M at hsup
  change movingSliceSupReal T hT.le (incomingDifferenceSummand S₁ S₂) u ≤ M
  rw [movingSliceSupReal, Set.projIcc_of_mem hT.le hu]
  exact hsup

end ChristodoulouBV.C1Solution

end
