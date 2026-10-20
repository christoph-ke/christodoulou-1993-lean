module

public import ChristodoulouBV.Existence.C1FamilyExitDensity
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Uniform continuity at finite C¹ cutoff scales

A continuous density on a compact physical triangle remains uniformly close
after nearby dilations. The estimate is uniform over the unit triangle and
is used for both null integrals in the first-exit argument.
-/

public section

open Set

namespace ChristodoulouBV

/-- Nearby dilations of a continuous compact-triangle density are uniformly
close after including the Jacobian factor from the null-coordinate change. -/
theorem s6_scaled_density_uniformly_close {B a₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : ℝ, 0 < a → a < B → |a - a₀| < δ →
        ∀ p ∈ closedCoordTriangle 0 1,
          |a * f (a • p) - a₀ * f (a₀ • p)| ≤ ε := by
  let J : Set ℝ := Icc (a₀ / 2) B
  let K : Set (ℝ × ℝ) := closedCoordTriangle 0 1
  let P : Set (ℝ × (ℝ × ℝ)) := J ×ˢ K
  have hP : IsCompact P :=
    isCompact_Icc.prod (isCompact_closedCoordTriangle 0 1)
  let G : (ℝ × (ℝ × ℝ)) → ℝ :=
    fun z => z.1 * f (z.1 • z.2)
  have hmap : MapsTo (fun z : ℝ × (ℝ × ℝ) => z.1 • z.2)
      P (closedCoordTriangle 0 B) := by
    intro z hz
    have ha : 0 ≤ z.1 := by
      have h := hz.1.1
      linarith only [h, ha₀]
    have haB : z.1 ≤ B := hz.1.2
    have hp := hz.2
    change 0 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2 ∧ z.2.2 ≤ 1 at hp
    change 0 ≤ (z.1 • z.2).1 ∧
      (z.1 • z.2).1 ≤ (z.1 • z.2).2 ∧
      (z.1 • z.2).2 ≤ B
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨mul_nonneg ha hp.1,
      mul_le_mul_of_nonneg_left hp.2.1 ha,
      (by calc
        z.1 * z.2.2 ≤ z.1 * 1 := mul_le_mul_of_nonneg_left hp.2.2 ha
        _ = z.1 := by ring
        _ ≤ B := haB)⟩
  have hchart : Continuous (fun z : ℝ × (ℝ × ℝ) => z.1 • z.2) := by
    fun_prop
  have hG : ContinuousOn G P := by
    dsimp [G]
    exact continuous_fst.continuousOn.mul
      (hf.comp hchart.continuousOn hmap)
  have hUC : UniformContinuousOn G P :=
    hP.uniformContinuousOn_of_continuous hG
  intro ε hε
  obtain ⟨δ₀, hδ₀, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  let δ := min δ₀ (a₀ / 2)
  have hδ : 0 < δ := lt_min hδ₀ (half_pos ha₀)
  refine ⟨δ, hδ, ?_⟩
  intro a ha haB hdist p hp
  have haJ : a ∈ J := by
    dsimp [J]
    constructor
    · have hbound : |a - a₀| < a₀ / 2 :=
        hdist.trans_le (min_le_right _ _)
      have hlow := (abs_lt.mp hbound).1
      linarith only [hlow]
    · exact haB.le
  have ha₀J : a₀ ∈ J := by
    dsimp [J]
    exact ⟨by linarith only [ha₀], ha₀B.le⟩
  have hpair : (a, p) ∈ P := ⟨haJ, hp⟩
  have hpair₀ : (a₀, p) ∈ P := ⟨ha₀J, hp⟩
  have hpairDist : dist (a, p) (a₀, p) < δ₀ := by
    rw [Prod.dist_eq]
    rw [dist_self, max_eq_left (dist_nonneg : 0 ≤ dist a a₀),
      Real.dist_eq]
    exact hdist.trans_le (min_le_left _ _)
  have hclose' := hclose (a, p) hpair (a₀, p) hpair₀ hpairDist
  dsimp [G] at hclose'
  rw [Real.dist_eq] at hclose'
  exact hclose'.le

end ChristodoulouBV

end
