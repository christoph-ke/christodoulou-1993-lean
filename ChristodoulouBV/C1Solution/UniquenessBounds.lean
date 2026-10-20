module

public import ChristodoulouBV.C1Solution.ExtractionRemovable
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Compact bounds for outgoing C¹ data

The arbitrary-bound uniqueness ledger requires only values and outgoing
first jets of the two solutions. Compactness supplies these bounds on each
smaller closed triangle.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- A C¹ real field on a compact closed triangle has one common bound for
its value and outgoing relative derivative. -/
theorem exists_value_vertical_jet_bound {B : ℝ} (hB : 0 < B)
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ closedCoordTriangle 0 B,
      |F p| ≤ M ∧
      |(fderivWithin ℝ F (closedCoordTriangle 0 B) p) (0, 1)| ≤ M := by
  let K := closedCoordTriangle 0 B
  let j : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ F K p) (0, 1)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hj : ContinuousOn j K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hsum : ContinuousOn (fun p => |F p| + |j p|) K :=
    hF.continuousOn.abs.add hj.abs
  obtain ⟨M, hM⟩ :=
    (isCompact_closedCoordTriangle 0 B).exists_bound_of_continuousOn hsum
  have hpoint : (0, 0) ∈ K := by
    change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ B
    exact ⟨le_rfl, le_rfl, hB.le⟩
  have hM0 : 0 ≤ M :=
    (norm_nonneg (|F (0, 0)| + |j (0, 0)|)).trans (hM (0, 0) hpoint)
  refine ⟨M, hM0, ?_⟩
  intro p hp
  have hbound : |F p| + |j p| ≤ M := by
    have h := hM p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (abs_nonneg (F p)) (abs_nonneg (j p)))] using h
  exact ⟨(le_add_of_nonneg_right (abs_nonneg (j p))).trans hbound,
    (le_add_of_nonneg_left (abs_nonneg (F p))).trans (by simpa only [add_comm] using hbound)⟩

/-- One compact bound controls `λ`, `ν`, `h=α/λ` and their outgoing
relative jets for two arbitrary frozen C¹ solutions. -/
theorem exists_common_outgoing_bound {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    ∃ M : ℝ, 0 < M ∧ ∀ p ∈ closedCoordTriangle 0 B,
      |S₁.lam p.1 p.2| ≤ M ∧ |S₂.lam p.1 p.2| ≤ M ∧
      |S₁.nu p.1 p.2| ≤ M ∧ |S₂.nu p.1 p.2| ≤ M ∧
      |outgoingQuotient S₁ p| ≤ M ∧ |outgoingQuotient S₂ p| ≤ M ∧
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ M ∧
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ M ∧
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ M ∧
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ M := by
  obtain ⟨M₁, hM₁, hlam1⟩ := exists_value_vertical_jet_bound hB
    (five_fields_contDiffOn hB hB₁ H₁).1
  obtain ⟨M₂, hM₂, hlam2⟩ := exists_value_vertical_jet_bound hB
    (five_fields_contDiffOn hB hB₂ H₂).1
  obtain ⟨M₃, hM₃, hnu1⟩ := exists_value_vertical_jet_bound hB
    (five_fields_contDiffOn hB hB₁ H₁).2.1
  obtain ⟨M₄, hM₄, hnu2⟩ := exists_value_vertical_jet_bound hB
    (five_fields_contDiffOn hB hB₂ H₂).2.1
  obtain ⟨M₅, hM₅, hh₁⟩ := exists_value_vertical_jet_bound hB
    (alpha_div_lam_contDiffOn hB hB₁ H₁)
  obtain ⟨M₆, hM₆, hh₂⟩ := exists_value_vertical_jet_bound hB
    (alpha_div_lam_contDiffOn hB hB₂ H₂)
  refine ⟨M₁ + M₂ + M₃ + M₄ + M₅ + M₆ + 1,
    by linarith only [hM₁, hM₂, hM₃, hM₄, hM₅, hM₆], ?_⟩
  intro p hp
  obtain ⟨hlam1v, hlam1j⟩ := hlam1 p hp
  obtain ⟨hlam2v, hlam2j⟩ := hlam2 p hp
  obtain ⟨hnu1v, _⟩ := hnu1 p hp
  obtain ⟨hnu2v, _⟩ := hnu2 p hp
  obtain ⟨hh₁v, hh₁j⟩ := hh₁ p hp
  obtain ⟨hh₂v, hh₂j⟩ := hh₂ p hp
  exact ⟨by linarith only [hlam1v, hM₂, hM₃, hM₄, hM₅, hM₆],
    by linarith only [hlam2v, hM₁, hM₃, hM₄, hM₅, hM₆],
    by linarith only [hnu1v, hM₁, hM₂, hM₄, hM₅, hM₆],
    by linarith only [hnu2v, hM₁, hM₂, hM₃, hM₅, hM₆],
    by change |S₁.alpha p.1 p.2 / S₁.lam p.1 p.2| ≤ _
       linarith only [hh₁v, hM₁, hM₂, hM₃, hM₄, hM₆],
    by change |S₂.alpha p.1 p.2 / S₂.lam p.1 p.2| ≤ _
       linarith only [hh₂v, hM₁, hM₂, hM₃, hM₄, hM₅],
    by linarith only [hlam1j, hM₂, hM₃, hM₄, hM₅, hM₆],
    by linarith only [hlam2j, hM₁, hM₃, hM₄, hM₅, hM₆],
    by change |(fderivWithin ℝ (fun q : ℝ × ℝ =>
         S₁.alpha q.1 q.2 / S₁.lam q.1 q.2)
         (closedCoordTriangle 0 B) p) (0, 1)| ≤ _
       linarith only [hh₁j, hM₁, hM₂, hM₃, hM₄, hM₆],
    by change |(fderivWithin ℝ (fun q : ℝ × ℝ =>
         S₂.alpha q.1 q.2 / S₂.lam q.1 q.2)
         (closedCoordTriangle 0 B) p) (0, 1)| ≤ _
       linarith only [hh₂j, hM₁, hM₂, hM₃, hM₄, hM₅]⟩

/-- Both solutions have shared positive lower bounds for the outgoing
expansion, canonical radius per coordinate gap, and canonical mass gap. -/
theorem exists_common_regular_lower_bounds {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
      ∀ p ∈ closedCoordTriangle 0 B,
        c ≤ S₁.lam p.1 p.2 ∧ c ≤ S₂.lam p.1 p.2 ∧
        c * (p.2 - p.1) ≤ canonicalRadius S₁ p ∧
        c * (p.2 - p.1) ≤ canonicalRadius S₂ p ∧
        ε ≤ 1 - canonicalMassRatio b₁ S₁ p ∧
        ε ≤ 1 - canonicalMassRatio b₂ S₂ p := by
  obtain ⟨c₁, hc₁, hlam1⟩ := exists_lam_lower_bound hB hB₁ H₁
  obtain ⟨c₂, hc₂, hlam2⟩ := exists_lam_lower_bound hB hB₂ H₂
  obtain ⟨r₁, hr₁, hrad1⟩ := canonicalRadius_lower_bound hB hB₁ H₁
  obtain ⟨r₂, hr₂, hrad2⟩ := canonicalRadius_lower_bound hB hB₂ H₂
  obtain ⟨ε₁, hε₁, hgap1⟩ := exists_canonical_mass_gap_lower_bound hB hB₁ H₁
  obtain ⟨ε₂, hε₂, hgap2⟩ := exists_canonical_mass_gap_lower_bound hB hB₂ H₂
  let c := min (min c₁ c₂) (min r₁ r₂)
  let ε := min ε₁ ε₂
  have hc : 0 < c := lt_min (lt_min hc₁ hc₂) (lt_min hr₁ hr₂)
  have hε : 0 < ε := lt_min hε₁ hε₂
  refine ⟨c, ε, hc, hε, ?_⟩
  intro p hp
  have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have hc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hc₂ : c ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁' : c ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₂' : c ≤ r₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hε₁' : ε ≤ ε₁ := min_le_left _ _
  have hε₂' : ε ≤ ε₂ := min_le_right _ _
  exact ⟨hc₁.trans (hlam1 p hp), hc₂.trans (hlam2 p hp),
    (mul_le_mul_of_nonneg_right hr₁' hd).trans (hrad1 p hp),
    (mul_le_mul_of_nonneg_right hr₂' hd).trans (hrad2 p hp),
    hε₁'.trans (hgap1 p hp), hε₂'.trans (hgap2 p hp)⟩

end ChristodoulouBV.C1Solution

end
