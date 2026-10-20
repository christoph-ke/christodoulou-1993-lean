module

public import ChristodoulouBV.C1Solution.UniquenessVerticalMean
public import ChristodoulouBV.C1Solution.UniquenessSlice
public import ChristodoulouBV.C1Solution.UniquenessBoxIdentities
import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Moving outgoing differences for canonical C¹ solutions

The four-field outgoing seminorm uses values and outgoing jets of `λ`
and `h=α/λ`. The incoming expansion has a separate moving supremum.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The four terms in the outgoing uniqueness seminorm. -/
@[expose] noncomputable def outgoingDifferenceSummand (B : ℝ)
    (S₁ S₂ : Fields) (p : ℝ × ℝ) : ℝ :=
  |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| +
  |outgoingQuotient S₁ p - outgoingQuotient S₂ p| +
  |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1) -
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1)| +
  |(fderivWithin ℝ (outgoingQuotient S₁)
      (closedCoordTriangle 0 B) p) (0, 1) -
    (fderivWithin ℝ (outgoingQuotient S₂)
      (closedCoordTriangle 0 B) p) (0, 1)|

/-- The incoming expansion difference on an outgoing slice. -/
@[expose] noncomputable def incomingDifferenceSummand
    (S₁ S₂ : Fields) (p : ℝ × ℝ) : ℝ :=
  |S₁.nu p.1 p.2 - S₂.nu p.1 p.2|

/-- The moving outgoing four-field supremum. -/
@[expose] noncomputable def outgoingDifference (B : ℝ) (hB : 0 ≤ B)
    (S₁ S₂ : Fields) (u : ℝ) : ℝ :=
  movingSliceSupReal B hB (outgoingDifferenceSummand B S₁ S₂) u

/-- The moving incoming-expansion supremum. -/
@[expose] noncomputable def incomingDifference (B : ℝ) (hB : 0 ≤ B)
    (S₁ S₂ : Fields) (u : ℝ) : ℝ :=
  movingSliceSupReal B hB (incomingDifferenceSummand S₁ S₂) u

/-- The four-field summand is continuous on every smaller closed triangle. -/
theorem outgoing_difference_summand_continuousOn {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    ContinuousOn (outgoingDifferenceSummand B S₁ S₂)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hl₁ := (five_fields_contDiffOn hB hB₁ H₁).1
  have hl₂ := (five_fields_contDiffOn hB hB₂ H₂).1
  have hh₁ := alpha_div_lam_contDiffOn hB hB₁ H₁
  have hh₂ := alpha_div_lam_contDiffOn hB hB₂ H₂
  have hlj₁ : ContinuousOn (fun p =>
      (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2) K p) (0, 1)) K :=
    (hl₁.continuousOn_fderivWithin hunique
    (by norm_num)).clm_apply continuousOn_const
  have hlj₂ : ContinuousOn (fun p =>
      (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2) K p) (0, 1)) K :=
    (hl₂.continuousOn_fderivWithin hunique
    (by norm_num)).clm_apply continuousOn_const
  have hhj₁ : ContinuousOn (fun p =>
      (fderivWithin ℝ (outgoingQuotient S₁) K p) (0, 1)) K :=
    (hh₁.continuousOn_fderivWithin hunique
    (by norm_num)).clm_apply continuousOn_const
  have hhj₂ : ContinuousOn (fun p =>
      (fderivWithin ℝ (outgoingQuotient S₂) K p) (0, 1)) K :=
    (hh₂.continuousOn_fderivWithin hunique
    (by norm_num)).clm_apply continuousOn_const
  change ContinuousOn (fun p =>
    |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| +
    |outgoingQuotient S₁ p - outgoingQuotient S₂ p| +
    |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2) K p) (0, 1) -
      (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2) K p) (0, 1)| +
    |(fderivWithin ℝ (outgoingQuotient S₁) K p) (0, 1) -
      (fderivWithin ℝ (outgoingQuotient S₂) K p) (0, 1)|) K
  exact (((hl₁.continuousOn.sub hl₂.continuousOn).abs.add
    (hh₁.continuousOn.sub hh₂.continuousOn).abs).add
    (hlj₁.sub hlj₂).abs).add (hhj₁.sub hhj₂).abs

/-- The incoming summand is continuous on the smaller closed triangle. -/
theorem incoming_difference_summand_continuousOn {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    ContinuousOn (incomingDifferenceSummand S₁ S₂)
      (closedCoordTriangle 0 B) :=
  ((five_fields_contDiffOn hB hB₁ H₁).2.1.continuousOn.sub
    (five_fields_contDiffOn hB hB₂ H₂).2.1.continuousOn).abs

/-- Both outgoing-slice suprema are continuous real functions. -/
theorem continuous_outgoing_and_incoming_difference {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    Continuous (outgoingDifference B hB.le S₁ S₂) ∧
    Continuous (incomingDifference B hB.le S₁ S₂) :=
  ⟨continuous_movingSliceSupReal hB.le
      (outgoing_difference_summand_continuousOn hB hB₁ hB₂ H₁ H₂),
    continuous_movingSliceSupReal hB.le
      (incoming_difference_summand_continuousOn hB hB₁ hB₂ H₁ H₂)⟩

/-- The four pointwise value and outgoing-jet differences are bounded by
their moving outgoing supremum. -/
theorem outgoing_components_le_difference {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |S₁.lam u v - S₂.lam u v| ≤
      outgoingDifference B hB.le S₁ S₂ u ∧
    |outgoingQuotient S₁ (u, v) - outgoingQuotient S₂ (u, v)| ≤
      outgoingDifference B hB.le S₁ S₂ u ∧
    |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
      outgoingDifference B hB.le S₁ S₂ u ∧
    |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
      outgoingDifference B hB.le S₁ S₂ u := by
  let D := outgoingDifference B hB.le S₁ S₂ u
  have hsum := le_movingSliceSup hB.le
    (outgoing_difference_summand_continuousOn hB hB₁ hB₂ H₁ H₂)
    hu huv hv
  have huI : u ∈ Icc 0 B := ⟨hu, huv.trans hv⟩
  have hD : D = movingSliceSup B (outgoingDifferenceSummand B S₁ S₂)
      ⟨u, huI⟩ := by
    dsimp [D, outgoingDifference, movingSliceSupReal]
    rw [Set.projIcc_of_mem hB.le huI]
  rw [← hD] at hsum
  change outgoingDifferenceSummand B S₁ S₂ (u, v) ≤ D at hsum
  dsimp only [outgoingDifferenceSummand] at hsum
  have h₀ := abs_nonneg (S₁.lam u v - S₂.lam u v)
  have h₁ := abs_nonneg
    (outgoingQuotient S₁ (u, v) - outgoingQuotient S₂ (u, v))
  have h₂ := abs_nonneg
    ((fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
      (closedCoordTriangle 0 B) (u, v)) (0, 1) -
     (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
      (closedCoordTriangle 0 B) (u, v)) (0, 1))
  have h₃ := abs_nonneg
    ((fderivWithin ℝ (outgoingQuotient S₁)
      (closedCoordTriangle 0 B) (u, v)) (0, 1) -
     (fderivWithin ℝ (outgoingQuotient S₂)
      (closedCoordTriangle 0 B) (u, v)) (0, 1))
  exact ⟨by linarith only [hsum, h₁, h₂, h₃],
    by linarith only [hsum, h₀, h₂, h₃],
    by linarith only [hsum, h₀, h₁, h₃],
    by linarith only [hsum, h₀, h₁, h₂]⟩

/-- The pointwise incoming expansion difference is bounded by its moving
outgoing supremum. -/
theorem incoming_component_le_difference {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |S₁.nu u v - S₂.nu u v| ≤
      incomingDifference B hB.le S₁ S₂ u := by
  have h := le_movingSliceSup hB.le
    (incoming_difference_summand_continuousOn hB hB₁ hB₂ H₁ H₂)
    hu huv hv
  have huI : u ∈ Icc 0 B := ⟨hu, huv.trans hv⟩
  rw [incomingDifference, movingSliceSupReal,
    Set.projIcc_of_mem hB.le huI]
  exact h

/-- The moving outgoing seminorm is nonnegative on its natural interval. -/
theorem outgoing_difference_nonneg {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    0 ≤ outgoingDifference B hB.le S₁ S₂ u := by
  have hf0 : ∀ p ∈ closedCoordTriangle 0 B,
      0 ≤ outgoingDifferenceSummand B S₁ S₂ p := by
    intro p hp
    unfold outgoingDifferenceSummand
    positivity
  have h := movingSliceSup_nonneg hB.le
    (outgoing_difference_summand_continuousOn hB hB₁ hB₂ H₁ H₂)
    hf0 ⟨u, hu⟩
  change 0 ≤ movingSliceSup B (outgoingDifferenceSummand B S₁ S₂)
    (Set.projIcc 0 B hB.le u)
  rw [Set.projIcc_of_mem hB.le hu]
  exact h

/-- At a fixed outgoing coordinate, the canonical source-factor values
obey the coefficient from the vertical source-factor bound in the four-field seminorm. -/
theorem canonical_source_factor_sub_le_difference
    {b₁ b₂ B c C Bv : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hlower₁ : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S₁.lam p.1 p.2)
    (hlowerUpper₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |canonicalSourceFactor S₁ (u, v) - canonicalSourceFactor S₂ (u, v)| ≤
      ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)) *
        (v - u) * outgoingDifference B hB.le S₁ S₂ u := by
  let K := closedCoordTriangle 0 B
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let f₁ := outgoingQuotient S₁
  let f₂ := outgoingQuotient S₂
  let G₁ := fderivWithin ℝ f₁ K
  let G₂ := fderivWithin ℝ f₂ K
  let D := outgoingDifference B hB.le S₁ S₂ u
  have huI : u ∈ Icc 0 B := ⟨hu, huv.trans hv⟩
  have hD : 0 ≤ D := outgoing_difference_nonneg hB hB₁ hB₂ H₁ H₂ huI
  have hw₁ := (five_fields_contDiffOn hB hB₁ H₁).1.continuousOn
  have hw₂ := (five_fields_contDiffOn hB hB₂ H₂).1.continuousOn
  have hf₁ := alpha_div_lam_contDiffOn hB hB₁ H₁
  have hf₂ := alpha_div_lam_contDiffOn hB hB₂ H₂
  have hjet₁ : ∀ p ∈ K, HasFDerivWithinAt f₁ (G₁ p) K p := by
    intro p hp
    exact (hf₁.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hjet₂ : ∀ p ∈ K, HasFDerivWithinAt f₂ (G₂ p) K p := by
    intro p hp
    exact (hf₂.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D := by
    intro t ht
    exact (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂
      hu ht.1 (ht.2.trans hv)).1
  have hverticalDiff : ∀ t ∈ Icc u v,
      |G₁ (u, t) (0, 1) - G₂ (u, t) (0, 1)| ≤ D := by
    intro t ht
    exact (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂
      hu ht.1 (ht.2.trans hv)).2.2.2
  have h := intervalIntegral.abs_weightedDiagonalError_sub_le_on_ray
    hc hD hw₁ hw₂ hf₁.continuousOn hf₂.continuousOn
    hlower₁ hlowerUpper₂ hjet₁ hjet₂
    hhvertical₁ hhvertical₂ hu huv hv hwdiff hverticalDiff
  change |intervalIntegral.weightedDiagonalError w₁ f₁ (u, v) -
    intervalIntegral.weightedDiagonalError w₂ f₂ (u, v)| ≤
      ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)) * (v - u) * D at h
  rw [← canonical_source_factor_eq_weightedDiagonalError hB hB₁ H₁
      ⟨hu, huv, hv⟩,
    ← canonical_source_factor_eq_weightedDiagonalError hB hB₂ H₂
      ⟨hu, huv, hv⟩] at h
  exact h

/-- In the strict triangle interior, the outgoing source-factor jet
difference has the coefficient from the vertical source-factor bound in the moving seminorm. -/
theorem canonical_source_factor_vertical_jet_sub_le_difference_interior
    {b₁ b₂ B c C Bv : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < B) :
    |(fderivWithin ℝ (canonicalSourceFactor S₁)
        (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ (canonicalSourceFactor S₂)
        (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
      (1 + (Bv + C * ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / c +
        C * Bv / c ^ 2) * outgoingDifference B hB.le S₁ S₂ u := by
  let K := closedCoordTriangle 0 B
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let f₁ := outgoingQuotient S₁
  let f₂ := outgoingQuotient S₂
  let G₁ := fderivWithin ℝ f₁ K
  let G₂ := fderivWithin ℝ f₂ K
  let E₁ := intervalIntegral.weightedDiagonalError w₁ f₁
  let E₂ := intervalIntegral.weightedDiagonalError w₂ f₂
  let D := outgoingDifference B hB.le S₁ S₂ u
  have hp : (u, v) ∈ K := ⟨hu.le, huv.le, hv.le⟩
  have huI : u ∈ Icc 0 B := ⟨hu.le, huv.le.trans hv.le⟩
  have hD : 0 ≤ D := outgoing_difference_nonneg hB hB₁ hB₂ H₁ H₂ huI
  have hw₁ := (five_fields_contDiffOn hB hB₁ H₁).1.continuousOn
  have hw₂ := (five_fields_contDiffOn hB hB₂ H₂).1.continuousOn
  have hf₁ := alpha_div_lam_contDiffOn hB hB₁ H₁
  have hf₂ := alpha_div_lam_contDiffOn hB hB₂ H₂
  have hjet₁ : ∀ p ∈ K, HasFDerivWithinAt f₁ (G₁ p) K p := by
    intro p hp
    exact (hf₁.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hjet₂ : ∀ p ∈ K, HasFDerivWithinAt f₂ (G₂ p) K p := by
    intro p hp
    exact (hf₂.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hdf₁ : DifferentiableOn ℝ f₁ (interior K) :=
    (hf₁.differentiableOn (by norm_num)).mono interior_subset
  have hdf₂ : DifferentiableOn ℝ f₂ (interior K) :=
    (hf₂.differentiableOn (by norm_num)).mono interior_subset
  have hderiv₁ : ∀ p ∈ interior K, fderiv ℝ f₁ p = G₁ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hderiv₂ : ∀ p ∈ interior K, fderiv ℝ f₂ p = G₂ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D := by
    intro t ht
    exact (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂
      hu.le ht.1 (ht.2.trans hv.le)).1
  have hverticalDiff : ∀ t ∈ Icc u v,
      |G₁ (u, t) (0, 1) - G₂ (u, t) (0, 1)| ≤ D := by
    intro t ht
    exact (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂
      hu.le ht.1 (ht.2.trans hv.le)).2.2.2
  have hderivBound := intervalIntegral.abs_deriv_weightedDiagonalError_vertical_sub_le_on_ray
    hw₁ hw₂ hf₁.continuousOn hf₂.continuousOn
    hdf₁ hdf₂ hderiv₁ hderiv₂ hjet₁ hjet₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂
    hc hBv hD hu huv hv hwdiff hverticalDiff
  have heq₁ : EqOn (canonicalSourceFactor S₁) E₁ K := by
    intro p hp
    exact canonical_source_factor_eq_weightedDiagonalError hB hB₁ H₁ hp
  have heq₂ : EqOn (canonicalSourceFactor S₂) E₂ K := by
    intro p hp
    exact canonical_source_factor_eq_weightedDiagonalError hB hB₂ H₂ hp
  have hE₁ : ContDiffOn ℝ 1 E₁ K :=
    (canonical_source_factor_box_inputs hB hB₁ H₁).1.congr heq₁.symm
  have hE₂ : ContDiffOn ℝ 1 E₂ K :=
    (canonical_source_factor_box_inputs hB hB₂ H₂).1.congr heq₂.symm
  have hjetEq₁ := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
    (fderivWithin_congr' heq₁ hp)
  have hjetEq₂ := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
    (fderivWithin_congr' heq₂ hp)
  have hderivEq₁ := intervalIntegral.fderivWithin_vertical_eq_deriv_on_ray
    hB hE₁ hu huv hv
  have hderivEq₂ := intervalIntegral.fderivWithin_vertical_eq_deriv_on_ray
    hB hE₂ hu huv hv
  calc
    |(fderivWithin ℝ (canonicalSourceFactor S₁) K (u, v)) (0, 1) -
      (fderivWithin ℝ (canonicalSourceFactor S₂) K (u, v)) (0, 1)| =
      |(fderivWithin ℝ E₁ K (u, v)) (0, 1) -
        (fderivWithin ℝ E₂ K (u, v)) (0, 1)| := by rw [hjetEq₁, hjetEq₂]
    _ = |deriv (fun x => E₁ (u, x)) v -
        deriv (fun x => E₂ (u, x)) v| := by rw [hderivEq₁, hderivEq₂]
    _ ≤ _ := hderivBound

/-- The outgoing source-factor jet estimate extends to the closed
triangle, including both vertices and the regular axis. -/
theorem canonical_source_factor_vertical_jet_sub_le_difference
    {b₁ b₂ B c C Bv : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    |(fderivWithin ℝ (canonicalSourceFactor S₁)
        (closedCoordTriangle 0 B) p) (0, 1) -
      (fderivWithin ℝ (canonicalSourceFactor S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤
      (1 + (Bv + C * ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / c +
        C * Bv / c ^ 2) * outgoingDifference B hB.le S₁ S₂ p.1 := by
  let K := closedCoordTriangle 0 B
  let F₁ := canonicalSourceFactor S₁
  let F₂ := canonicalSourceFactor S₂
  let A := 1 + (Bv + C * ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / c +
    C * Bv / c ^ 2
  let D := outgoingDifference B hB.le S₁ S₂
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hF₁ := (canonical_source_factor_box_inputs hB hB₁ H₁).1
  have hF₂ := (canonical_source_factor_box_inputs hB hB₂ H₂).1
  have hj₁ : ContinuousOn (fun q => (fderivWithin ℝ F₁ K q) (0, 1)) K :=
    (hF₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hj₂ : ContinuousOn (fun q => (fderivWithin ℝ F₂ K q) (0, 1)) K :=
    (hF₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hf : ContinuousOn (fun q =>
      |(fderivWithin ℝ F₁ K q) (0, 1) -
        (fderivWithin ℝ F₂ K q) (0, 1)|) K :=
    (hj₁.sub hj₂).abs
  have hD : Continuous D :=
    (continuous_outgoing_and_incoming_difference hB hB₁ hB₂ H₁ H₂).1
  have hg : ContinuousOn (fun q : ℝ × ℝ => A * D q.1) K :=
    continuousOn_const.mul (hD.comp continuous_fst).continuousOn
  have hinside : ∀ q ∈ interior K,
      |(fderivWithin ℝ F₁ K q) (0, 1) -
        (fderivWithin ℝ F₂ K q) (0, 1)| ≤ A * D q.1 := by
    rintro ⟨u, v⟩ hq
    have hstrict : (u, v) ∈ openCoordTriangle 0 B := by
      rwa [interior_closedCoordTriangle] at hq
    exact canonical_source_factor_vertical_jet_sub_le_difference_interior
      hB hB₁ hB₂ hc hBv H₁ H₂ hweight₁ hweight₂
      hhvertical₁ hhvertical₂ hstrict.1 hstrict.2.1 hstrict.2.2
  exact intervalIntegral.le_on_closedCoordTriangle_of_interior hB
    hf hg hinside p hp

end ChristodoulouBV.C1Solution

end
