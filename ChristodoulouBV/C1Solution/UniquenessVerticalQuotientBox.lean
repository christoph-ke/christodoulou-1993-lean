module

public import ChristodoulouBV.C1Solution.UniquenessVerticalQuotients
import ChristodoulouBV.C1Solution.UniquenessMassRatioDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The canonical outgoing mass and radius as a vertical pair box

This instantiation uses the moving fixed-ray seminorm. It does not require
differences of incoming first jets.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- Coordinate inequalities supplied by membership in a closed triangle. -/
theorem closed_triangle_coordinates {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
  simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using hp

/-- Two frozen C¹ solutions give a vertical-only cubic rational pair box on
a closed triangle of width at most one. Its distance is the moving outgoing
four-field difference. -/
@[expose] noncomputable def canonicalVerticalPairBox
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv) :
    intervalIntegral.CubicRationalVerticalPairBox 0 T c := by
  let K := closedCoordTriangle 0 T
  let j₀ := C * Bv ^ 2
  let jΔ := Bv ^ 2 + 2 * C * Bv *
    ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))
  let k₀ := j₀ / c
  let kΔ := jΔ / c + j₀ / c ^ 2
  let J₀ := j₀ / 3
  let JΔ := jΔ / 3 + j₀ * kΔ / 6
  let Jv := j₀ + k₀ * J₀
  let JΔv := jΔ + kΔ * J₀ + k₀ * JΔ
  let X₁ := canonicalCubicRationalTriangleBox hT hT₁ H₁
    (fun p hp => (hweight₁ p hp).1)
  let X₂ := canonicalCubicRationalTriangleBox hT hT₂ H₂
    (fun p hp => (hweight₂ p hp).1)
  let D := outgoingDifference T hT.le S₁ S₂
  have hlam₁ := (five_fields_contDiffOn hT hT₁ H₁).1
  have hlam₂ := (five_fields_contDiffOn hT hT₂ H₂).1
  have hw₁ : ContinuousOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2) K :=
    hlam₁.continuousOn
  have hw₂ : ContinuousOn (fun p : ℝ × ℝ => S₂.lam p.1 p.2) K :=
    hlam₂.continuousOn
  refine {
    first := X₁
    second := X₂
    J₀ := J₀
    Jv := Jv
    JΔ := JΔ
    JΔv := JΔv
    Rv := C
    RΔv := 1
    D := D
    D_continuous := (continuous_outgoing_and_incoming_difference
      hT hT₁ hT₂ H₁ H₂).1
    D_nonneg := fun u hu => outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂ hu
    bounds_nonneg := ?_
    J_bound := ?_
    J_vertical_bound := ?_
    J_sub_bound := ?_
    J_vertical_sub_bound := ?_
    r_sub_bound := ?_
    r_vertical_bound := ?_
    r_vertical_sub_bound := ?_ }
  · dsimp [J₀, Jv, JΔ, JΔv, j₀, jΔ, k₀, kΔ]
    exact ⟨by positivity, by positivity, by positivity,
      by positivity, hC, by norm_num⟩
  · intro p hp
    rcases p with ⟨u, v⟩
    have hcoord : 0 ≤ u ∧ u ≤ v ∧ v ≤ T := closed_triangle_coordinates hp
    have h₁ := canonical_mass_numerator_nonneg_le hT hT₁ hc hBv
      H₁ hweight₁ hhvertical₁ hcoord.1 hcoord.2.1 hcoord.2.2
    have h₂ := canonical_mass_numerator_nonneg_le hT hT₂ hc hBv
      H₂ hweight₂ hhvertical₂ hcoord.1 hcoord.2.1 hcoord.2.2
    change |canonicalMassNumerator b₁ S₁ (u, v)| ≤ J₀ * (v - u) ^ 3 ∧
      |canonicalMassNumerator b₂ S₂ (u, v)| ≤ J₀ * (v - u) ^ 3
    exact ⟨by rw [abs_of_nonneg h₁.1]; exact h₁.2,
      by rw [abs_of_nonneg h₂.1]; exact h₂.2⟩
  · intro p hp
    rcases p with ⟨u, v⟩
    have hcoord : 0 ≤ u ∧ u ≤ v ∧ v ≤ T := closed_triangle_coordinates hp
    change |(fderivWithin ℝ (canonicalMassNumerator b₁ S₁) K (u, v)) (0, 1)| ≤
        Jv * (v - u) ^ 2 ∧
      |(fderivWithin ℝ (canonicalMassNumerator b₂ S₂) K (u, v)) (0, 1)| ≤
        Jv * (v - u) ^ 2
    exact ⟨canonical_mass_numerator_vertical_jet_abs_le
        hT hTwidth hT₁ hc hBv H₁ hweight₁ hhvertical₁
        hcoord.1 hcoord.2.1 hcoord.2.2,
      canonical_mass_numerator_vertical_jet_abs_le
        hT hTwidth hT₂ hc hBv H₂ hweight₂ hhvertical₂
        hcoord.1 hcoord.2.1 hcoord.2.2⟩
  · intro p hp
    rcases p with ⟨u, v⟩
    have hcoord : 0 ≤ u ∧ u ≤ v ∧ v ≤ T := closed_triangle_coordinates hp
    change |canonicalMassNumerator b₁ S₁ (u, v) -
      canonicalMassNumerator b₂ S₂ (u, v)| ≤ JΔ * (v - u) ^ 3 * D u
    exact canonical_mass_numerator_sub_le_difference
      hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂
      hcoord.1 hcoord.2.1 hcoord.2.2
  · intro p hp
    rcases p with ⟨u, v⟩
    have hcoord : 0 ≤ u ∧ u ≤ v ∧ v ≤ T := closed_triangle_coordinates hp
    change |(fderivWithin ℝ (canonicalMassNumerator b₁ S₁) K (u, v)) (0, 1) -
      (fderivWithin ℝ (canonicalMassNumerator b₂ S₂) K (u, v)) (0, 1)| ≤
      JΔv * (v - u) ^ 2 * D u
    exact canonical_mass_numerator_vertical_jet_sub_le_difference
      hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂
      hcoord.1 hcoord.2.1 hcoord.2.2
  · intro p hp
    rcases p with ⟨u, v⟩
    have hcoord : 0 ≤ u ∧ u ≤ v ∧ v ≤ T := closed_triangle_coordinates hp
    change |canonicalRadius S₁ (u, v) - canonicalRadius S₂ (u, v)| ≤
      (v - u) * D u
    have hwdiff : ∀ t ∈ Icc u v,
        |S₁.lam u t - S₂.lam u t| ≤ D u := by
      intro t ht
      exact (outgoing_components_le_difference hT hT₁ hT₂ H₁ H₂
        hcoord.1 ht.1 (ht.2.trans hcoord.2.2)).1
    have h := intervalIntegral.abs_weightedDiagonalRadius_sub_le_on_ray
      hw₁ hw₂ hcoord.1 hcoord.2.1 hcoord.2.2 hwdiff
    simpa only [canonicalRadius, mul_comm] using h
  · intro p hp
    have hjet₁ := canonicalRadius_vertical_jet hT hT₁ H₁ hp
    have hjet₂ := canonicalRadius_vertical_jet hT hT₂ H₂ hp
    change |(fderivWithin ℝ (canonicalRadius S₁) K p) (0, 1)| ≤ C ∧
      |(fderivWithin ℝ (canonicalRadius S₂) K p) (0, 1)| ≤ C
    rw [hjet₁, hjet₂]
    exact ⟨by rw [abs_of_nonneg (hc.le.trans (hweight₁ p hp).1)];
                 exact (hweight₁ p hp).2,
      by rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)];
         exact (hweight₂ p hp).2⟩
  · intro p hp
    have hcoord : 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T :=
      closed_triangle_coordinates hp
    have hjet₁ := canonicalRadius_vertical_jet hT hT₁ H₁ hp
    have hjet₂ := canonicalRadius_vertical_jet hT hT₂ H₂ hp
    change |(fderivWithin ℝ (canonicalRadius S₁) K p) (0, 1) -
      (fderivWithin ℝ (canonicalRadius S₂) K p) (0, 1)| ≤ 1 * D p.1
    rw [hjet₁, hjet₂, one_mul]
    exact (outgoing_components_le_difference hT hT₁ hT₂ H₁ H₂
      hcoord.1 hcoord.2.1 hcoord.2.2).1

end ChristodoulouBV.C1Solution

end
