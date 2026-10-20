module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaCore
import all ChristodoulouBV.AreaEstimates.LogTransportMixed
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Transport equation for rho

The differentiated identity (4.22) is stated with the oriented analytic
Jacobian used by the Section 4 area measure.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

private theorem outgoing_area_horizontal_hasDerivAt
    {B : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => f (t, v))
      ((fderivWithin ℝ f (closedCoordTriangle 0 B) (u, v)) (1, 0)) u := by
  have hpi : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hKn : closedCoordTriangle 0 B ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  have hdiff : DifferentiableAt ℝ f (u, v) :=
    (hf.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt hKn
  have hline : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have h := hdiff.hasFDerivAt.comp_hasDerivAt u hline
  change HasDerivAt (fun t => f (t, v)) ((fderiv ℝ f (u, v)) (1, 0)) u at h
  rwa [fderivWithin_of_mem_nhds hKn]

private theorem outgoing_area_vertical_hasDerivAt
    {B : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => f (u, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 B) (u, v)) (0, 1)) v := by
  have hpi : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hKn : closedCoordTriangle 0 B ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  have hdiff : DifferentiableAt ℝ f (u, v) :=
    (hf.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt hKn
  have hline : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have h := hdiff.hasFDerivAt.comp_hasDerivAt v hline
  change HasDerivAt (fun t => f (u, t)) ((fderiv ℝ f (u, v)) (0, 1)) v at h
  rwa [fderivWithin_of_mem_nhds hKn]

private theorem sourceRho_transport_local {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {B u v : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => sourceRho S t v / S.nu t v) u =
      -(S.r u v ^ 2) * (fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det := by
  let K := closedCoordTriangle 0 B
  let μ : ℝ → ℝ := fun t => 2 * S.m t v / S.r t v
  let q : ℝ → ℝ := fun t => S.beta t v / S.nu t v
  let F : ℝ → ℝ := fun t =>
    (2 * S.m t v * S.lam t v) / (1 - μ t) +
      S.r t v * S.theta t v * (q t - S.phi t v)
  have hpK : (u, v) ∈ K := ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - μ u ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    dsimp [μ]
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hrCanon := outgoing_area_horizontal_hasDerivAt
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H) hp
  rw [C1Solution.canonicalRadius_horizontal_jet hB hB1 H hpK] at hrCanon
  have hrEq : (fun t => C1Solution.canonicalRadius S (t, v)) =ᶠ[𝓝 u]
      (fun t => S.r t v) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    exact C1Solution.canonicalRadius_eq_radius hB hB1 H ht.1.le ht.2 hp.2.2.le
  have hr : HasDerivAt (fun t => S.r t v) (S.nu u v) u :=
    hrCanon.congr_of_eventuallyEq hrEq.symm
  have hmCanon := C1Solution.canonicalMass_horizontal_hasDerivAt hB hB1 H hp
  rw [C1Solution.canonicalMassIncomingDensity,
    C1Solution.canonicalMassRatio_eq_mass_ratio H hpU] at hmCanon
  have hmEq : (fun t => C1Solution.canonicalMass 1 S (t, v)) =ᶠ[𝓝 u]
      (fun t => S.m t v) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    exact C1Solution.canonicalMass_eq_mass
      ⟨ht.1.le, ht.2, hp.2.2.trans hB1⟩
  have hm : HasDerivAt (fun t => S.m t v)
      ((1 - μ u) * S.zeta u v ^ 2 / (2 * S.nu u v)) u := by
    simpa only [μ] using hmCanon.congr_of_eventuallyEq hmEq.symm
  have hlam := outgoing_area_horizontal_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp
  have htheta := outgoing_area_horizontal_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.1 hp
  have hphi := outgoing_area_horizontal_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1 hp
  have hbeta := outgoing_area_horizontal_hasDerivAt
    (C1Solution.beta_contDiffOn hB hB1 H) hp
  have hnu := outgoing_area_horizontal_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp
  have hlamJet := (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).1
  rw [hlamJet, C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H
    hp.1.le hp.2.1 hp.2.2.le] at hlam
  have hthetaJet := theta_incoming_pointwise hB hB1 H hpK hp.2.1
  have hphiJet := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    hB hB1 H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
    hp.1.le hp.2.1 hp.2.2.le] at hphiJet
  have hthetaVal : deriv (fun t => S.theta t v) u =
      -(S.lam u v * S.zeta u v / S.r u v) := by
    rw [htheta.deriv]
    calc
      (fderivWithin ℝ (fun p => S.theta p.1 p.2) K (u, v)) (1, 0) =
          -(S.lam u v / S.r u v * S.zeta u v) := by
            linarith only [hthetaJet]
      _ = -(S.lam u v * S.zeta u v / S.r u v) := by ring
  have hphiVal : deriv (fun t => S.phi t v) u =
      S.zeta u v / S.r u v := by
    rw [hphi.deriv]
    apply (eq_div_iff hrne).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using hphiJet.symm
  have hlamVal : deriv (fun t => S.lam t v) u =
      μ u * S.lam u v * S.nu u v / S.r u v /
        (1 - μ u) := by
    rw [hlam.deriv]
    dsimp [μ]
    field_simp [hrne, hgapne]
  have hμ := (hm.const_mul 2).div hr hrne
  have hgap := (hasDerivAt_const u (1 : ℝ)).sub hμ
  have hq := hbeta.div hnu hnune
  have hF := (((hm.const_mul 2).mul hlam).div hgap hgapne).add
    (((hr.mul htheta).mul (hq.sub hphi)))
  have hFVal : deriv F u =
      μ u * S.lam u v * S.zeta u v ^ 2 /
        ((1 - μ u) * S.nu u v) +
          S.r u v * S.theta u v * deriv q u := by
    have hqVal : q u - S.phi u v = S.zeta u v / S.nu u v := by
      dsimp [q]
      unfold Fields.zeta
      field_simp [hnune]
    have hF' := hF.deriv
    change deriv F u = _ at hF'
    rw [hF']
    have hthetaJet' :
        (fderivWithin ℝ (fun p => S.theta p.1 p.2) K (u, v)) (1, 0) =
          -(S.lam u v / S.r u v * S.zeta u v) := by
      linarith only [hthetaJet]
    have hphiJet' :
        (fderivWithin ℝ (fun p => S.phi p.1 p.2) K (u, v)) (1, 0) =
          S.zeta u v / S.r u v := by
      apply (eq_div_iff hrne).2
      simpa only [Prod.fst, Prod.snd, mul_comm] using hphiJet.symm
    have hqDeriv := hq.deriv
    change deriv q u = _ at hqDeriv
    rw [hqDeriv]
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
    rw [hthetaJet', hphiJet', hqVal]
    dsimp [μ]
    field_simp [hrne, hnune, hgapne, hmassgapne, hlamne]
    ring
  have hEq : (fun t => sourceRho S t v / S.nu t v) =ᶠ[𝓝 u] F := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    have hpU' : (t, v) ∈ developmentWithInitialEdge 1 :=
      ⟨ht.1.le, ht.2, hp.2.2.trans hB1⟩
    have hrne' : S.r t v ≠ 0 := ne_of_gt (H.solution.radius_pos (t, v) hpU')
    have hnune' : S.nu t v ≠ 0 := by
      have hpK' : (t, v) ∈ K := ⟨ht.1.le, ht.2.le, hp.2.2.le⟩
      exact ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK')
    have hgapne' : 1 - 2 * S.m t v / S.r t v ≠ 0 := by
      have hratio := (hBV.mass_ratio_bounds hpU').2
      linarith
    dsimp [sourceRho, F, μ, q]
    unfold Fields.zeta
    field_simp [hrne', hnune', hgapne']
  have hRhoVal : deriv (fun t => sourceRho S t v / S.nu t v) u =
      μ u * S.lam u v * S.zeta u v ^ 2 /
        ((1 - μ u) * S.nu u v) +
          S.r u v * S.theta u v * deriv q u :=
    hEq.deriv_eq.trans hFVal
  have hqV := eq4_10b H hrGauge hcenter hboot hpU hp.1
  have hJ := (sourceJacobianPhiBetaNu_eq_det hB hB1 H hp).symm
  rw [hJ]
  unfold sourceJacobianPhiBetaNu
  rw [hRhoVal]
  have hphiV : deriv (S.phi u) v = S.theta u v / S.r u v := by
    have h := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
      hB hB1 H hpK
    have hφ := (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1
    have hderiv := outgoing_area_vertical_hasDerivAt hφ hp
    rw [hderiv.deriv]
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hp.2.2.le] at h
    apply (eq_div_iff hrne).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using h.symm
  rw [hphiVal, hphiV, hqV]
  dsimp [μ, q]
  field_simp [hrne, hnune, hgapne, hmassgapne]
  ring

/-- Equation (4.22): the horizontal derivative of `ρ/ν` is minus `r²`
times the oriented `(φ, β/ν)` Jacobian. -/
theorem eq4_22 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    deriv (fun t => sourceRho S t v / S.nu t v) u =
      -(S.r u v ^ 2) * (fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith only [hp.2.2]
  exact sourceRho_transport_local H hr hcenter hboot hB hB1 ⟨hp.1, hp.2.1, hvB⟩

end ChristodoulouBV

end
