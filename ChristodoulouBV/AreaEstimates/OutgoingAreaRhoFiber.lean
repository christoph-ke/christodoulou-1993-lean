module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaHardy
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Regularity of rho on incoming fibers

The quotient `ρ/ν` is represented on a compact incoming fiber by a C¹
expression in the canonical radius and mass ratio. This representation
does not assign a value to the frozen mass or radius at the axis.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- `ρ/ν` is C¹ on each compact incoming segment away from the diagonal.
The initial endpoint `u=0` is included. -/
theorem sourceRhoOverNu_contDiffOn_fiber {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v c : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo 0 v) :
    ContDiffOn ℝ 1 (fun u => sourceRho S u v / S.nu u v) (Icc 0 c) := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let μ := C1Solution.canonicalMassRatio 1 S
  let R := C1Solution.canonicalRadius S
  let Q : ℝ × ℝ → ℝ := fun p =>
    R p *
      (μ p * S.lam p.1 p.2 / (1 - μ p) +
        S.theta p.1 p.2 * S.zeta p.1 p.2 / S.nu p.1 p.2)
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hfields := C1Solution.five_fields_contDiffOn hB hB1 H
  have hR := C1Solution.canonicalRadius_contDiffOn hB hB1 H
  have hμ := C1Solution.canonicalMassRatio_contDiffOn hB hB1 H
  obtain ⟨ε, hε, hgap⟩ :=
    C1Solution.exists_canonical_mass_gap_lower_bound hB hB1 H
  have hgapNe : ∀ p ∈ K, 1 - μ p ≠ 0 :=
    fun p hp => ne_of_gt (hε.trans_le (hgap p hp))
  have hnuNe : ∀ p ∈ K, S.nu p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hp)
  have hQ : ContDiffOn ℝ 1 Q K :=
    hR.mul (((hμ.mul hfields.1).div
      (contDiffOn_const.sub hμ) hgapNe).add
        ((hfields.2.2.2.1.mul hfields.2.2.2.2).div
          hfields.2.1 hnuNe))
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 c) K := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hc.2.le, hvB.le⟩
  have hpair : ContDiffOn ℝ 1 (fun u : ℝ => (u, v)) (Icc 0 c) := by
    fun_prop
  have hQslice : ContDiffOn ℝ 1 (fun u => Q (u, v)) (Icc 0 c) :=
    hQ.comp hpair hmap
  apply hQslice.congr
  intro u hu
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.1, hu.2.trans_lt hc.2, hv.2⟩
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    hu.1 (hu.2.trans_lt hc.2) hvB.le
  have hmu := C1Solution.canonicalMassRatio_eq_mass_ratio H hpU
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 := hnuNe (u, v) (hmap hu)
  have hgapne : 1 - μ (u, v) ≠ 0 := hgapNe (u, v) (hmap hu)
  have hgapne' : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    simpa only [μ, hmu] using hgapne
  symm
  change C1Solution.canonicalRadius S (u, v) *
      (C1Solution.canonicalMassRatio 1 S (u, v) * S.lam u v /
          (1 - C1Solution.canonicalMassRatio 1 S (u, v)) +
        S.theta u v * S.zeta u v / S.nu u v) =
      sourceRho S u v / S.nu u v
  rw [hr, hmu]
  unfold sourceRho
  field_simp [hrne, hnune, hgapne']

end ChristodoulouBV

end
