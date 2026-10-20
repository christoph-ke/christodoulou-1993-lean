module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Incoming-axis cancellation for rho

The C¹ extraction factors make `ρ/r²` vanish when the outgoing coordinate
approaches the fixed incoming coordinate from above.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

private theorem incoming_rho_over_radius_sq_factor {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {B u v : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (hp : (u, v) ∈ openCoordTriangle 0 B) :
    sourceRho S u v / S.r u v ^ 2 = (v - u) *
      (C1Solution.normalizedMassOverRadiusSq 1 B S (u, v) *
          S.nu u v * S.lam u v /
          (1 - C1Solution.canonicalMassRatio 1 S (u, v)) +
        C1Solution.normalizedTheta B S (u, v) *
          C1Solution.normalizedZeta B S (u, v) /
          C1Solution.canonicalNormalizedRadius S (u, v)) := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hr : S.r u v = C1Solution.canonicalRadius S (u, v) :=
    (C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hp.2.2.le).symm
  have hrad := C1Solution.canonicalRadius_eq_gap_mul_normalized S u v
  obtain ⟨_, c, hc, hcl⟩ :=
    C1Solution.canonicalNormalizedRadius_continuousOn_and_lower_bound hB hB1 H
  have hnr : C1Solution.canonicalNormalizedRadius S (u, v) ≠ 0 :=
    ne_of_gt (hc.trans_le (hcl (u, v) hpK))
  have hd : v - u ≠ 0 := sub_ne_zero.mpr hp.2.1.ne'
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hgap : 1 - C1Solution.canonicalMassRatio 1 S (u, v) ≠ 0 :=
    ne_of_gt (sub_pos.mpr
      (C1Solution.canonicalMassRatio_lt_one hB hB1 H
        hp.1.le hp.2.1 hp.2.2.le))
  have hmu := C1Solution.canonicalMassRatio_eq_mass_ratio H hpU
  have hmass := C1Solution.canonicalMassOverRadiusSq_eq_gap_mul_normalized
    hB hB1 H hpK
  have htheta := C1Solution.theta_eq_gap_mul_normalizedTheta hB hB1 H hpK
  have hzeta := C1Solution.zeta_eq_gap_mul_normalizedZeta hB hB1 H hpK
  have hratioOver : C1Solution.canonicalMassRatio 1 S (u, v) / S.r u v =
      (v - u) * C1Solution.normalizedMassOverRadiusSq 1 B S (u, v) := by
    rw [hmu, ← hmass, C1Solution.canonicalMassOverRadiusSq,
      C1Solution.canonicalMass_eq_mass hpU]
    rw [← hr]
    field_simp [hrne]
  have hthetaOver : S.theta u v * S.zeta u v / S.r u v =
      (v - u) * (C1Solution.normalizedTheta B S (u, v) *
        C1Solution.normalizedZeta B S (u, v) /
        C1Solution.canonicalNormalizedRadius S (u, v)) := by
    rw [htheta, hzeta, hr, hrad]
    field_simp [hd, hnr]
  calc
    sourceRho S u v / S.r u v ^ 2 =
        (C1Solution.canonicalMassRatio 1 S (u, v) / S.r u v) *
          (S.nu u v * S.lam u v /
            (1 - C1Solution.canonicalMassRatio 1 S (u, v))) +
          S.theta u v * S.zeta u v / S.r u v := by
      rw [sourceRho, ← hmu]
      field_simp [hrne, hgap]
    _ = (v - u) *
      (C1Solution.normalizedMassOverRadiusSq 1 B S (u, v) *
          S.nu u v * S.lam u v /
          (1 - C1Solution.canonicalMassRatio 1 S (u, v)) +
        C1Solution.normalizedTheta B S (u, v) *
          C1Solution.normalizedZeta B S (u, v) /
          C1Solution.canonicalNormalizedRadius S (u, v)) := by
      rw [hratioOver, hthetaOver]
      ring

/-- The conjugate axis cancellation after (4.27): for each fixed
`u ∈ (0,1)`, `ρ(u,v)/r(u,v)²` tends to zero as `v` approaches `u` from above. -/
theorem rho_axis_out {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun v => sourceRho S u v / S.r u v ^ 2)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  let B : ℝ := (u + 1) / 2
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun p =>
    C1Solution.normalizedMassOverRadiusSq 1 B S p *
        S.nu p.1 p.2 * S.lam p.1 p.2 /
        (1 - C1Solution.canonicalMassRatio 1 S p) +
      C1Solution.normalizedTheta B S p *
        C1Solution.normalizedZeta B S p /
        C1Solution.canonicalNormalizedRadius S p
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hu.2]
  have huB : u < B := by dsimp [B]; linarith only [hu.2]
  have hF : ContinuousOn F K := by
    have hM := C1Solution.normalizedMassOverRadiusSq_continuousOn hB hB1 H
    have hN := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1.continuousOn
    have hL := (C1Solution.five_fields_contDiffOn hB hB1 H).1.continuousOn
    have hμ := C1Solution.canonicalMassRatio_continuousOn hB hB1 H
    obtain ⟨_, hgap, hgapLower⟩ :=
      C1Solution.exists_canonical_mass_gap_lower_bound hB hB1 H
    obtain ⟨hR, c, hc, hRLower⟩ :=
      C1Solution.canonicalNormalizedRadius_continuousOn_and_lower_bound hB hB1 H
    have hgapNe : ∀ p ∈ K,
        1 - C1Solution.canonicalMassRatio 1 S p ≠ 0 :=
      fun p hp => ne_of_gt (hgap.trans_le (hgapLower p hp))
    have hRNe : ∀ p ∈ K, C1Solution.canonicalNormalizedRadius S p ≠ 0 :=
      fun p hp => ne_of_gt (hc.trans_le (hRLower p hp))
    exact (((hM.mul hN).mul hL).div
      (continuousOn_const.sub hμ) hgapNe).add
        (((C1Solution.normalizedTheta_continuousOn hB hB1 H).mul
          (C1Solution.normalizedZeta_continuousOn hB hB1 H)).div hR hRNe)
  have hslice : ContinuousOn (fun v => F (u, v)) (Icc u B) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu.1.le, hv.1, hv.2⟩)
  have hFend : Tendsto (fun v => F (u, v)) (𝓝[>] u) (𝓝 (F (u, u))) := by
    have hright : ContinuousWithinAt (fun v => F (u, v)) (Ici u) u :=
      (continuousWithinAt_Icc_iff_Ici (by dsimp [B]; linarith only [hu.2])).mp
        (hslice.continuousWithinAt ⟨le_rfl, huB.le⟩)
    exact (hright.mono Ioi_subset_Ici_self).tendsto
  have hgapT : Tendsto (fun v : ℝ => v - u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hId : Tendsto (fun v : ℝ => v) (𝓝[>] u) (𝓝 u) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hConst : Tendsto (fun _ : ℝ => u) (𝓝[>] u) (𝓝 u) :=
      tendsto_const_nhds
    simpa only [sub_self] using hId.sub hConst
  have hmain := hgapT.mul hFend
  have heq : (fun v => sourceRho S u v / S.r u v ^ 2) =ᶠ[𝓝[>] u]
      (fun v => (v - u) * F (u, v)) := by
    filter_upwards [Ioo_mem_nhdsGT huB] with v hv
    exact incoming_rho_over_radius_sq_factor H hB hB1
      ⟨hu.1, hv.1, hv.2⟩
  simpa only [zero_mul] using hmain.congr' heq.symm

end ChristodoulouBV

end
