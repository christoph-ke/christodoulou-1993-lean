module

public import ChristodoulouBV.Existence.C1FamilyExitIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Upper continuity of the Section 6 null size

The continuous axis extensions and uniform compact-triangle continuity give
one error bound for all outgoing and incoming null slices at nearby finite
cutoffs. Taking suprema then controls `Z` from above at an interior cutoff.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem scaled_outgoing_lintegral_eq_density
    {b B a u : ℝ} (hB : 0 < B) (hBb : B < b)
    (ha : 0 < a) (haB : a < B) (hu : u ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫⁻ t in Ioo u 1,
      ENNReal.ofReal
        (|(Uniqueness.rescaledFields S 0 a).theta u t| /
          (Uniqueness.rescaledFields S 0 a).r u t)) =
    ∫⁻ t in Ioo u 1,
      ENNReal.ofReal
        (a * s6OutgoingDensity B S (a • (u, t))) := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have heq := (s6_rescaled_null_density_eq hB hBb ha haB H
    hu.1.le ht.1 ht.2).1
  have hpoint : a • (u, t) = (a * u, a * t) := by
    ext <;> simp
  change ENNReal.ofReal
    (|(Uniqueness.rescaledFields S 0 a).theta u t| /
      (Uniqueness.rescaledFields S 0 a).r u t) =
    ENNReal.ofReal (a * s6OutgoingDensity B S (a • (u, t)))
  rw [hpoint]
  exact congrArg ENNReal.ofReal heq

private theorem scaled_incoming_lintegral_eq_density
    {b B a v : ℝ} (hB : 0 < B) (hBb : B < b)
    (ha : 0 < a) (haB : a < B) (hv : v ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫⁻ t in Ioo 0 v,
      ENNReal.ofReal
        (|(Uniqueness.rescaledFields S 0 a).zeta t v| /
          (Uniqueness.rescaledFields S 0 a).r t v)) =
    ∫⁻ t in Ioo 0 v,
      ENNReal.ofReal
        (a * s6IncomingDensity B S (a • (t, v))) := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have heq := (s6_rescaled_null_density_eq hB hBb ha haB H
    ht.1.le ht.2 hv.2).2
  have hpoint : a • (t, v) = (a * t, a * v) := by
    ext <;> simp
  change ENNReal.ofReal
    (|(Uniqueness.rescaledFields S 0 a).zeta t v| /
      (Uniqueness.rescaledFields S 0 a).r t v) =
    ENNReal.ofReal (a * s6IncomingDensity B S (a • (t, v)))
  rw [hpoint]
  exact congrArg ENNReal.ofReal heq

private theorem sourceZ_le_of_density_close {b B a a₀ ε : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha : 0 < a) (haB : a < B)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hθ : ∀ p ∈ closedCoordTriangle 0 1,
      |a * s6OutgoingDensity B S (a • p) -
        a₀ * s6OutgoingDensity B S (a₀ • p)| ≤ ε)
    (hζ : ∀ p ∈ closedCoordTriangle 0 1,
      |a * s6IncomingDensity B S (a • p) -
        a₀ * s6IncomingDensity B S (a₀ • p)| ≤ ε) :
    sourceZ (Uniqueness.rescaledFields S 0 a) ≤
      sourceZ (Uniqueness.rescaledFields S 0 a₀) +
        ENNReal.ofReal ε := by
  let T := Uniqueness.rescaledFields S 0 a
  let T₀ := Uniqueness.rescaledFields S 0 a₀
  have hX : sourceX T ≤ sourceX T₀ + ENNReal.ofReal ε := by
    rw [sourceX]
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    have hclose : ∀ t ∈ Ioo u 1,
        |a * s6OutgoingDensity B S (a • (u, t)) -
          a₀ * s6OutgoingDensity B S (a₀ • (u, t))| ≤ ε := by
      intro t ht
      exact hθ (u, t) ⟨hu.1.le, ht.1.le, ht.2.le⟩
    have hlin := s6_lintegral_nearby hu.1.le (le_refl (1 : ℝ)) hclose
    calc
      (∫⁻ t in Ioo u 1, ENNReal.ofReal (|T.theta u t| / T.r u t)) =
          ∫⁻ t in Ioo u 1,
            ENNReal.ofReal (a * s6OutgoingDensity B S (a • (u, t))) :=
        scaled_outgoing_lintegral_eq_density hB hBb ha haB hu H
      _ ≤ (∫⁻ t in Ioo u 1,
            ENNReal.ofReal (a₀ * s6OutgoingDensity B S (a₀ • (u, t)))) +
            ENNReal.ofReal ε := hlin
      _ = (∫⁻ t in Ioo u 1,
            ENNReal.ofReal (|T₀.theta u t| / T₀.r u t)) +
            ENNReal.ofReal ε := by
        rw [scaled_outgoing_lintegral_eq_density hB hBb ha₀ ha₀B hu H]
      _ ≤ sourceX T₀ + ENNReal.ofReal ε := by
        gcongr
        exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have hY : sourceY T ≤ sourceY T₀ + ENNReal.ofReal ε := by
    rw [sourceY]
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    have hclose : ∀ t ∈ Ioo 0 v,
        |a * s6IncomingDensity B S (a • (t, v)) -
          a₀ * s6IncomingDensity B S (a₀ • (t, v))| ≤ ε := by
      intro t ht
      exact hζ (t, v) ⟨ht.1.le, ht.2.le, hv.2.le⟩
    have hlin := s6_lintegral_nearby (le_refl 0) hv.2.le hclose
    calc
      (∫⁻ t in Ioo 0 v, ENNReal.ofReal (|T.zeta t v| / T.r t v)) =
          ∫⁻ t in Ioo 0 v,
            ENNReal.ofReal (a * s6IncomingDensity B S (a • (t, v))) :=
        scaled_incoming_lintegral_eq_density hB hBb ha haB hv H
      _ ≤ (∫⁻ t in Ioo 0 v,
            ENNReal.ofReal (a₀ * s6IncomingDensity B S (a₀ • (t, v)))) +
            ENNReal.ofReal ε := hlin
      _ = (∫⁻ t in Ioo 0 v,
            ENNReal.ofReal (|T₀.zeta t v| / T₀.r t v)) +
            ENNReal.ofReal ε := by
        rw [scaled_incoming_lintegral_eq_density hB hBb ha₀ ha₀B hv H]
      _ ≤ sourceY T₀ + ENNReal.ofReal ε := by
        gcongr
        exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  calc
    sourceZ T = max (sourceX T) (sourceY T) := rfl
    _ ≤ max (sourceX T₀ + ENNReal.ofReal ε)
          (sourceY T₀ + ENNReal.ofReal ε) := max_le_max hX hY
    _ = sourceZ T₀ + ENNReal.ofReal ε := by
      simp only [sourceZ, max_add_add_right]

/-- At every positive cutoff inside a larger C¹ development, the null size
at all sufficiently nearby cutoffs differs by at most any prescribed
positive error. The estimate is uniform over all null slices. -/
theorem s6_sourceZ_nearby {b B a₀ : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ,
      0 < a → a < B → |a - a₀| < δ →
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤
          sourceZ (Uniqueness.rescaledFields S 0 a₀) +
            ENNReal.ofReal ε ∧
      sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤
          sourceZ (Uniqueness.rescaledFields S 0 a) +
            ENNReal.ofReal ε := by
  have hθcont := (s6_outgoing_density_continuous_and_eq hB hBb H).1
  have hζcont := (s6_incoming_density_continuous_and_eq hB hBb H).1
  obtain ⟨δθ, hδθ, hθclose⟩ :=
    s6_scaled_density_uniformly_close ha₀ ha₀B hθcont ε hε
  obtain ⟨δζ, hδζ, hζclose⟩ :=
    s6_scaled_density_uniformly_close ha₀ ha₀B hζcont ε hε
  let δ := min δθ δζ
  have hδ : 0 < δ := lt_min hδθ hδζ
  refine ⟨δ, hδ, ?_⟩
  intro a ha haB hdist
  have hθ : ∀ p ∈ closedCoordTriangle 0 1,
      |a * s6OutgoingDensity B S (a • p) -
        a₀ * s6OutgoingDensity B S (a₀ • p)| ≤ ε :=
    hθclose a ha haB (hdist.trans_le (min_le_left _ _))
  have hζ : ∀ p ∈ closedCoordTriangle 0 1,
      |a * s6IncomingDensity B S (a • p) -
        a₀ * s6IncomingDensity B S (a₀ • p)| ≤ ε :=
    hζclose a ha haB (hdist.trans_le (min_le_right _ _))
  constructor
  · exact sourceZ_le_of_density_close hB hBb ha haB ha₀ ha₀B H hθ hζ
  · have hθ' : ∀ p ∈ closedCoordTriangle 0 1,
        |a₀ * s6OutgoingDensity B S (a₀ • p) -
          a * s6OutgoingDensity B S (a • p)| ≤ ε := by
      intro p hp
      simpa only [abs_sub_comm] using hθ p hp
    have hζ' : ∀ p ∈ closedCoordTriangle 0 1,
        |a₀ * s6IncomingDensity B S (a₀ • p) -
          a * s6IncomingDensity B S (a • p)| ≤ ε := by
      intro p hp
      simpa only [abs_sub_comm] using hζ p hp
    exact sourceZ_le_of_density_close hB hBb ha₀ ha₀B ha haB H hθ' hζ'

end ChristodoulouBV

end
