module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaRhoFinite
public import ChristodoulouBV.AreaEstimates.OutgoingAreaDensity
import all ChristodoulouBV.AreaEstimates.OutgoingAreaDensity
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Measurability of the rho density

The frozen mass and radius are replaced locally by their canonical C¹
representatives on the strict triangle. This supplies the regularity needed
to apply Tonelli to the rho density in (4.23).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The canonical mass ratio and radius represent rho at every strict point. -/
theorem sourceRho_eq_canonical {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    sourceRho S u v = C1Solution.canonicalRadius S (u, v) *
      (((C1Solution.canonicalMassRatio 1 S (u, v) *
          S.nu u v * S.lam u v) /
          (1 - C1Solution.canonicalMassRatio 1 S (u, v))) +
        S.theta u v * S.zeta u v) := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hp.2.2]
  have hvB : v ≤ B := by dsimp [B]; linarith only [hp.2.2]
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    hp.1.le hp.2.1 hvB
  have hmu := C1Solution.canonicalMassRatio_eq_mass_ratio H
    (show (u, v) ∈ developmentWithInitialEdge 1 from
      ⟨hp.1.le, hp.2.1, hp.2.2⟩)
  rw [hr, hmu]
  rfl

/-- The rho density is continuous on the strict unit triangle. -/
theorem sourceRhoDensity_continuousOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContinuousOn (sourceRhoDensity S) (openCoordTriangle 0 1) := by
  intro p hp
  rcases p with ⟨u, v⟩
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let R := C1Solution.canonicalRadius S
  let μ := C1Solution.canonicalMassRatio 1 S
  let Q : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal
      (|R p *
          (μ p * S.nu p.1 p.2 * S.lam p.1 p.2 / (1 - μ p) +
            S.theta p.1 p.2 * S.zeta p.1 p.2)| / R p ^ 3)
  have hB : 0 < B := by dsimp [B]; linarith only [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith only [hp.2.2]
  have hpK : (u, v) ∈ K := ⟨hp.1.le, hp.2.1.le, hvB.le⟩
  have hKn : K ∈ 𝓝 (u, v) := by
    apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
    rw [interior_closedCoordTriangle]
    exact ⟨hp.1, hp.2.1, hvB⟩
  have hR : ContinuousAt R (u, v) :=
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H).continuousOn.continuousAt hKn
  have hμ : ContinuousAt μ (u, v) :=
    (C1Solution.canonicalMassRatio_contDiffOn hB hB1 H).continuousOn.continuousAt hKn
  have hfields := C1Solution.five_fields_contDiffOn hB hB1 H
  have hNu : ContinuousAt (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v) :=
    hfields.2.1.continuousOn.continuousAt hKn
  have hLam : ContinuousAt (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v) :=
    hfields.1.continuousOn.continuousAt hKn
  have hTheta : ContinuousAt (fun p : ℝ × ℝ => S.theta p.1 p.2) (u, v) :=
    hfields.2.2.2.1.continuousOn.continuousAt hKn
  have hZeta : ContinuousAt (fun p : ℝ × ℝ => S.zeta p.1 p.2) (u, v) :=
    hfields.2.2.2.2.continuousOn.continuousAt hKn
  have hgap : 1 - μ (u, v) ≠ 0 := by
    have hlt := C1Solution.canonicalMassRatio_lt_one hB hB1 H
      hp.1.le hp.2.1 hvB.le
    exact ne_of_gt (sub_pos.mpr hlt)
  have hRne : R (u, v) ≠ 0 := by
    change C1Solution.canonicalRadius S (u, v) ≠ 0
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hvB.le]
    exact ne_of_gt (H.solution.radius_pos (u, v)
      ⟨hp.1.le, hp.2.1, hp.2.2⟩)
  have hQ : ContinuousAt Q (u, v) := by
    have hNum : ContinuousAt (fun p => R p *
        (μ p * S.nu p.1 p.2 * S.lam p.1 p.2 / (1 - μ p) +
          S.theta p.1 p.2 * S.zeta p.1 p.2)) (u, v) :=
      hR.mul ((((hμ.mul hNu).mul hLam).div
        (continuousAt_const.sub hμ) hgap).add (hTheta.mul hZeta))
    exact ENNReal.continuous_ofReal.continuousAt.comp
      (hNum.abs.div (hR.pow 3) (pow_ne_zero 3 hRne))
  have hEq : (sourceRhoDensity S) =ᶠ[𝓝 (u, v)] Q := by
    have hOpen : openCoordTriangle 0 B ∈ 𝓝 (u, v) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior.mem_nhds (by
        rw [interior_closedCoordTriangle]
        exact ⟨hp.1, hp.2.1, hvB⟩)
    filter_upwards [hOpen] with p hpB
    have hp1 : p ∈ openCoordTriangle 0 1 :=
      ⟨hpB.1, hpB.2.1, hpB.2.2.trans hB1⟩
    have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
      hpB.1.le hpB.2.1 hpB.2.2.le
    have hρ := sourceRho_eq_canonical H hp1
    unfold sourceRhoDensity
    rw [hρ, ← hr]
  exact (hQ.congr_of_eventuallyEq hEq).continuousWithinAt

/-- The rho density is almost everywhere measurable on the strict
triangle, the hypothesis needed for area Tonelli. -/
theorem sourceRhoDensity_aemeasurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    AEMeasurable (sourceRhoDensity S)
      (volume.restrict (openCoordTriangle 0 1)) := by
  have hT : MeasurableSet (openCoordTriangle 0 1) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  exact (sourceRhoDensity_continuousOn H).aemeasurable hT

end ChristodoulouBV

end
