module

public import ChristodoulouBV.AreaEstimates.IncomingAreaHardy
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Regularity of rho on outgoing fibers

The quotient `ρ/λ` is represented on compact outgoing segments away from
the diagonal by the canonical C¹ radius and mass ratio.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- `ρ/λ` is C¹ on a compact outgoing segment separated from the axis. -/
theorem sourceRhoOverLam_contDiffOn_fiber {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u a c : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Ioo u 1) (hc : c ∈ Ioo a 1) :
    ContDiffOn ℝ 1 (fun v => sourceRho S u v / S.lam u v) (Icc a c) := by
  let B : ℝ := (c + 1) / 2
  let K := closedCoordTriangle 0 B
  let μ := C1Solution.canonicalMassRatio 1 S
  let R := C1Solution.canonicalRadius S
  let Q : ℝ × ℝ → ℝ := fun p =>
    R p *
      (μ p * S.nu p.1 p.2 / (1 - μ p) +
        S.theta p.1 p.2 * S.zeta p.1 p.2 / S.lam p.1 p.2)
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, ha.1, hc.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hc.2]
  have hcB : c < B := by dsimp [B]; linarith only [hc.2]
  have hfields := C1Solution.five_fields_contDiffOn hB hB1 H
  have hR := C1Solution.canonicalRadius_contDiffOn hB hB1 H
  have hμ := C1Solution.canonicalMassRatio_contDiffOn hB hB1 H
  obtain ⟨ε, hε, hgap⟩ :=
    C1Solution.exists_canonical_mass_gap_lower_bound hB hB1 H
  obtain ⟨δ, hδ, hlamLower⟩ :=
    C1Solution.exists_lam_lower_bound hB hB1 H
  have hgapNe : ∀ p ∈ K, 1 - μ p ≠ 0 :=
    fun p hp => ne_of_gt (hε.trans_le (hgap p hp))
  have hlamNe : ∀ p ∈ K, S.lam p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hδ.trans_le (hlamLower p hp))
  have hQ : ContDiffOn ℝ 1 Q K :=
    hR.mul (((hμ.mul hfields.2.1).div
      (contDiffOn_const.sub hμ) hgapNe).add
        ((hfields.2.2.2.1.mul hfields.2.2.2.2).div
          hfields.1 hlamNe))
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc a c) K := by
    intro v hv
    exact ⟨hu.1.le, ha.1.le.trans hv.1, hv.2.trans hcB.le⟩
  have hpair : ContDiffOn ℝ 1 (fun v : ℝ => (u, v)) (Icc a c) := by
    fun_prop
  have hQslice : ContDiffOn ℝ 1 (fun v => Q (u, v)) (Icc a c) :=
    hQ.comp hpair hmap
  apply hQslice.congr
  intro v hv
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.1.le, ha.1.trans_le hv.1, hv.2.trans_lt hc.2⟩
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    hu.1.le (ha.1.trans_le hv.1) (hv.2.trans hcB.le)
  have hmu := C1Solution.canonicalMassRatio_eq_mass_ratio H hpU
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := hlamNe (u, v) (hmap hv)
  have hgapne : 1 - μ (u, v) ≠ 0 := hgapNe (u, v) (hmap hv)
  have hgapne' : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    simpa only [μ, hmu] using hgapne
  symm
  change C1Solution.canonicalRadius S (u, v) *
      (C1Solution.canonicalMassRatio 1 S (u, v) * S.nu u v /
          (1 - C1Solution.canonicalMassRatio 1 S (u, v)) +
        S.theta u v * S.zeta u v / S.lam u v) =
      sourceRho S u v / S.lam u v
  rw [hr, hmu]
  unfold sourceRho
  field_simp [hrne, hlamne, hgapne']

end ChristodoulouBV

end
