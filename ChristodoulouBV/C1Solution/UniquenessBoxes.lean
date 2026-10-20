module

public import ChristodoulouBV.C1Solution.ExtractionRemovable
public import ChristodoulouBV.C1Solution.ExtractionAxisJets
public import ChristodoulouBV.C1Solution.UniquenessBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanIntegral
import Mathlib.Tactic

/-!
# Canonical inputs for uniqueness boxes

The radius and regular factors of a frozen C¹ solution provide the
single-input hypotheses of the removable-coefficient estimates on every
smaller closed triangle. The source factor is the scalar minus the outgoing
quotient; its diagonal value vanishes.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The regular source factor in the equation for the outgoing quotient. -/
@[expose] noncomputable def canonicalSourceFactor (S : Fields)
    (p : ℝ × ℝ) : ℝ := outgoingQuotient S p - S.phi p.1 p.2

/-- The canonical source factor is the weighted diagonal error of the
outgoing quotient. -/
theorem canonical_source_factor_eq_weightedDiagonalError {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalSourceFactor S p =
      intervalIntegral.weightedDiagonalError
        (fun q => S.lam q.1 q.2) (outgoingQuotient S) p := by
  rw [canonicalSourceFactor, phi_eq_weightedDiagonalMean hB hBb H hp]
  rfl

/-- The canonical radius has a positive normalized factor, the expected
diagonal value, and its two diagonal coordinate jets. -/
theorem canonical_radius_box_inputs {b B c : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2) :
    ContDiffOn ℝ 1 (canonicalRadius S) (closedCoordTriangle 0 B) ∧
    ContinuousOn (canonicalNormalizedRadius S) (closedCoordTriangle 0 B) ∧
    (∀ p ∈ closedCoordTriangle 0 B,
      c ≤ canonicalNormalizedRadius S p ∧
      canonicalRadius S p = (p.2 - p.1) * canonicalNormalizedRadius S p) ∧
    (∀ u ∈ Icc 0 B,
      canonicalNormalizedRadius S (u, u) = S.lam u u ∧
      (fderivWithin ℝ (canonicalRadius S)
        (closedCoordTriangle 0 B) (u, u)) (1, 0) = -S.lam u u ∧
      (fderivWithin ℝ (canonicalRadius S)
        (closedCoordTriangle 0 B) (u, u)) (0, 1) = S.lam u u) := by
  have hlam := (five_fields_contDiffOn hB hBb H).1
  refine ⟨canonicalRadius_contDiffOn hB hBb H,
    intervalIntegral.continuousOn_normalizedDiagonalRadius hlam.continuousOn,
    ?_, ?_⟩
  · intro p hp
    exact ⟨intervalIntegral.le_normalizedDiagonalRadius
      hlam.continuousOn hcl hp,
      canonicalRadius_eq_gap_mul_normalized S p.1 p.2⟩
  · intro u hu
    have hp : (u, u) ∈ closedCoordTriangle 0 B :=
      ⟨hu.1, le_rfl, hu.2⟩
    exact ⟨intervalIntegral.normalizedDiagonalRadius_diag _ _,
      by rw [canonicalRadius_horizontal_jet hB hBb H hp,
        nu_eq_neg_lam_axis hB hBb H hu],
      canonicalRadius_vertical_jet hB hBb H hp⟩

/-- The two nonsingular factors are C¹, have a positive outgoing factor,
and take opposite values on the regular axis. -/
theorem canonical_regular_factor_box_inputs {b B c : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) ∧
    (∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2) ∧
    (∀ u ∈ Icc 0 B, S.nu u u = -S.lam u u) := by
  exact ⟨(five_fields_contDiffOn hB hBb H).1,
    (five_fields_contDiffOn hB hBb H).2.1, hcl,
    fun u hu => nu_eq_neg_lam_axis hB hBb H hu⟩

/-- The canonical source factor is C¹ and vanishes on the axis. -/
theorem canonical_source_factor_box_inputs {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalSourceFactor S)
      (closedCoordTriangle 0 B) ∧
    (∀ u ∈ Icc 0 B, canonicalSourceFactor S (u, u) = 0) := by
  constructor
  · exact (alpha_div_lam_contDiffOn hB hBb H).sub
      (five_fields_contDiffOn hB hBb H).2.2.1
  · intro u hu
    obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
    have hp : (u, u) ∈ closedCoordTriangle 0 B :=
      ⟨hu.1, le_rfl, hu.2⟩
    have hne : S.lam u u ≠ 0 := ne_of_gt (hc.trans_le (hcl (u, u) hp))
    rw [canonicalSourceFactor, outgoingQuotient,
      alpha_eq_lam_mul_phi_axis hB hBb H hu]
    field_simp [hne]
    ring

/-- The source factor has the outgoing linear bound of the weighted
diagonal error, using only the outgoing jet of the quotient. -/
theorem canonical_source_factor_abs_le_gap {b B c Bv : ℝ}
    (hB : 0 < B) (hBb : B < b) (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2)
    (hvertical : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    |canonicalSourceFactor S p| ≤ Bv * (p.2 - p.1) := by
  let K := closedCoordTriangle 0 B
  have hlam := (five_fields_contDiffOn hB hBb H).1
  have hh := alpha_div_lam_contDiffOn hB hBb H
  have hjet : ∀ q ∈ K,
      HasFDerivWithinAt (outgoingQuotient S)
        (fderivWithin ℝ (outgoingQuotient S) K q) K q := by
    intro q hq
    exact (hh.differentiableOn (by norm_num) q hq).hasFDerivWithinAt
  have hbound : ∀ q ∈ K,
      ‖(fderivWithin ℝ (outgoingQuotient S) K q) (0, 1)‖ ≤ Bv := by
    intro q hq
    simpa only [Real.norm_eq_abs] using hvertical q hq
  have herror := intervalIntegral.abs_weightedDiagonalError_le_of_jet
    hlam.continuousOn hh.continuousOn hcl hc hBv hjet hbound
    hp.1 hp.2.1 hp.2.2
  change |intervalIntegral.weightedDiagonalError
    (fun q => S.lam q.1 q.2) (outgoingQuotient S) p| ≤
      Bv * (p.2 - p.1) at herror
  rw [← canonical_source_factor_eq_weightedDiagonalError hB hBb H hp] at herror
  exact herror

/-- On a compact triangle the source factor has a linear axis bound and
a uniform outgoing jet bound, with one finite coefficient. -/
theorem exists_canonical_source_factor_vertical_bounds {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ closedCoordTriangle 0 B,
      |canonicalSourceFactor S p| ≤ M * (p.2 - p.1) ∧
      |(fderivWithin ℝ (canonicalSourceFactor S)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ M := by
  let K := closedCoordTriangle 0 B
  have hF := (canonical_source_factor_box_inputs hB hBb H).1
  have haxis := (canonical_source_factor_box_inputs hB hBb H).2
  obtain ⟨M, hM, hbound⟩ := exists_value_vertical_jet_bound hB hF
  refine ⟨M, hM, ?_⟩
  intro p hp
  have hjet : ∀ q ∈ K,
      HasFDerivWithinAt (canonicalSourceFactor S)
        (fderivWithin ℝ (canonicalSourceFactor S) K q) K q := by
    intro q hq
    exact (hF.differentiableOn (by norm_num) q hq).hasFDerivWithinAt
  have hjetBound : ∀ q ∈ K,
      ‖(fderivWithin ℝ (canonicalSourceFactor S) K q) (0, 1)‖ ≤ M := by
    intro q hq
    simpa only [Real.norm_eq_abs] using (hbound q hq).2
  have hval := intervalIntegral.norm_sub_vertical_le_of_jet hjet hjetBound
    hp.1 le_rfl hp.2.1 hp.2.2
  have hu : p.1 ∈ Icc 0 B := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  rw [haxis p.1 hu] at hval
  simpa only [sub_zero, Real.norm_eq_abs] using And.intro hval (hbound p hp).2

/-- A C¹ scalar field on a compact triangle has a shared bound for its
value and both coordinate first jets. -/
theorem exists_value_coordinate_jet_bound {B : ℝ} (hB : 0 < B)
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ closedCoordTriangle 0 B,
      |F p| ≤ M ∧
      |(fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0)| ≤ M ∧
      |(fderivWithin ℝ F (closedCoordTriangle 0 B) p) (0, 1)| ≤ M := by
  let K := closedCoordTriangle 0 B
  let ju : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ F K p) (1, 0)
  let jv : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ F K p) (0, 1)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hjet := hF.continuousOn_fderivWithin hunique (by norm_num)
  have hu : ContinuousOn ju K := hjet.clm_apply continuousOn_const
  have hv : ContinuousOn jv K := hjet.clm_apply continuousOn_const
  have hsum : ContinuousOn (fun p => |F p| + |ju p| + |jv p|) K :=
    (hF.continuousOn.abs.add hu.abs).add hv.abs
  obtain ⟨M, hM⟩ :=
    (isCompact_closedCoordTriangle 0 B).exists_bound_of_continuousOn hsum
  have hpoint : (0, 0) ∈ K := ⟨le_rfl, le_rfl, hB.le⟩
  have hM0 : 0 ≤ M :=
    (norm_nonneg (|F (0, 0)| + |ju (0, 0)| + |jv (0, 0)|)).trans
      (hM (0, 0) hpoint)
  refine ⟨M, hM0, ?_⟩
  intro p hp
  have hbound : |F p| + |ju p| + |jv p| ≤ M := by
    have h := hM p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (add_nonneg (abs_nonneg (F p)) (abs_nonneg (ju p)))
        (abs_nonneg (jv p)))] using h
  dsimp only [ju, jv] at hbound ⊢
  constructor
  · linarith only [hbound, abs_nonneg (ju p), abs_nonneg (jv p)]
  constructor
  · linarith only [hbound, abs_nonneg (F p), abs_nonneg (jv p)]
  · linarith only [hbound, abs_nonneg (F p), abs_nonneg (ju p)]

/-- Two canonical solutions have common value and coordinate-jet bounds
for the two regular factors on every compact smaller triangle. -/
theorem exists_common_regular_factor_box_bounds {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    ∃ C V L : ℝ, 0 ≤ C ∧ 0 ≤ V ∧ 0 ≤ L ∧
      ∀ p ∈ closedCoordTriangle 0 B,
        |S₁.lam p.1 p.2| ≤ C ∧ |S₂.lam p.1 p.2| ≤ C ∧
        |S₁.nu p.1 p.2| ≤ V ∧ |S₂.nu p.1 p.2| ≤ V ∧
        (∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
          |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
            (closedCoordTriangle 0 B) p) e| ≤ L ∧
          |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
            (closedCoordTriangle 0 B) p) e| ≤ L ∧
          |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.nu q.1 q.2)
            (closedCoordTriangle 0 B) p) e| ≤ L ∧
          |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.nu q.1 q.2)
            (closedCoordTriangle 0 B) p) e| ≤ L) := by
  obtain ⟨C₁, hC₁, hlam₁⟩ := exists_value_coordinate_jet_bound hB
    (five_fields_contDiffOn hB hB₁ H₁).1
  obtain ⟨C₂, hC₂, hlam₂⟩ := exists_value_coordinate_jet_bound hB
    (five_fields_contDiffOn hB hB₂ H₂).1
  obtain ⟨V₁, hV₁, hnu₁⟩ := exists_value_coordinate_jet_bound hB
    (five_fields_contDiffOn hB hB₁ H₁).2.1
  obtain ⟨V₂, hV₂, hnu₂⟩ := exists_value_coordinate_jet_bound hB
    (five_fields_contDiffOn hB hB₂ H₂).2.1
  refine ⟨C₁ + C₂, V₁ + V₂, C₁ + C₂ + V₁ + V₂,
    by positivity, by positivity, by positivity, ?_⟩
  intro p hp
  have hl₁ := hlam₁ p hp
  have hl₂ := hlam₂ p hp
  have hn₁ := hnu₁ p hp
  have hn₂ := hnu₂ p hp
  refine ⟨by linarith only [hl₁.1, hC₂],
    by linarith only [hl₂.1, hC₁],
    by linarith only [hn₁.1, hV₂],
    by linarith only [hn₂.1, hV₁], ?_⟩
  intro e he
  rcases he with he | he
  · subst e
    exact ⟨by linarith only [hl₁.2.1, hC₂, hV₁, hV₂],
      by linarith only [hl₂.2.1, hC₁, hV₁, hV₂],
      by linarith only [hn₁.2.1, hC₁, hC₂, hV₂],
      by linarith only [hn₂.2.1, hC₁, hC₂, hV₁]⟩
  · subst e
    exact ⟨by linarith only [hl₁.2.2, hC₂, hV₁, hV₂],
      by linarith only [hl₂.2.2, hC₁, hV₁, hV₂],
      by linarith only [hn₁.2.2, hC₁, hC₂, hV₂],
      by linarith only [hn₂.2.2, hC₁, hC₂, hV₁]⟩

/-- A source factor for a canonical solution has both coordinate jets
bounded and vanishes at most linearly at the axis. -/
theorem exists_canonical_source_factor_box_bounds {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ H₀ H₁ : ℝ, 0 ≤ H₀ ∧ 0 ≤ H₁ ∧
      ∀ p ∈ closedCoordTriangle 0 B,
        |canonicalSourceFactor S p| ≤ H₀ * (p.2 - p.1) ∧
        |(fderivWithin ℝ (canonicalSourceFactor S)
          (closedCoordTriangle 0 B) p) (1, 0)| ≤ H₁ ∧
        |(fderivWithin ℝ (canonicalSourceFactor S)
          (closedCoordTriangle 0 B) p) (0, 1)| ≤ H₁ := by
  obtain ⟨H₀, hH₀, hvertical⟩ :=
    exists_canonical_source_factor_vertical_bounds hB hBb H
  obtain ⟨H₁, hH₁, hcoordinate⟩ :=
    exists_value_coordinate_jet_bound hB
      (canonical_source_factor_box_inputs hB hBb H).1
  refine ⟨H₀, H₁, hH₀, hH₁, ?_⟩
  intro p hp
  exact ⟨(hvertical p hp).1, (hcoordinate p hp).2.1,
    (hcoordinate p hp).2.2⟩

end ChristodoulouBV.C1Solution

end
