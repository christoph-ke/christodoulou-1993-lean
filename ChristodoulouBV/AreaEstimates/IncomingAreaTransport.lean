module

public import ChristodoulouBV.AreaEstimates.IncomingAreaCore
import all ChristodoulouBV.AreaEstimates.LogTransportMixed
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Conjugate transport equation for rho

The vertical derivative of `ρ/λ` is the oriented `(φ, α/λ)` Jacobian
weighted by the square of the radius.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

private theorem incoming_area_horizontal_hasDerivAt
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

private theorem incoming_area_vertical_hasDerivAt
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

private theorem sourceRho_transport_vertical_local {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {B u v : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => sourceRho S u t / S.lam u t) v =
      S.r u v ^ 2 * (fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det := by
  let K := closedCoordTriangle 0 B
  let μ : ℝ → ℝ := fun t => 2 * S.m u t / S.r u t
  let q : ℝ → ℝ := fun t => S.alpha u t / S.lam u t
  let F : ℝ → ℝ := fun t =>
    (2 * S.m u t * S.nu u t) / (1 - μ t) +
      S.r u t * S.zeta u t * (q t - S.phi u t)
  have hpK : (u, v) ∈ K := ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hlamne : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - μ v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    dsimp [μ]
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hrCanon := incoming_area_vertical_hasDerivAt
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H) hp
  rw [C1Solution.canonicalRadius_vertical_jet hB hB1 H hpK] at hrCanon
  have hrEq : (fun t => C1Solution.canonicalRadius S (u, t)) =ᶠ[𝓝 v]
      (fun t => S.r u t) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    exact C1Solution.canonicalRadius_eq_radius hB hB1 H hp.1.le ht.1 ht.2.le
  have hr : HasDerivAt (fun t => S.r u t) (S.lam u v) v :=
    hrCanon.congr_of_eventuallyEq hrEq.symm
  have hmCanon := C1Solution.canonicalMass_vertical_hasDerivAt hB hB1 H hp
  rw [C1Solution.canonicalMassOutgoingDensity,
    C1Solution.canonicalMassRatio_eq_mass_ratio H hpU] at hmCanon
  have hmEq : (fun t => C1Solution.canonicalMass 1 S (u, t)) =ᶠ[𝓝 v]
      (fun t => S.m u t) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    exact C1Solution.canonicalMass_eq_mass
      ⟨hp.1.le, ht.1, ht.2.trans hB1⟩
  have hm : HasDerivAt (fun t => S.m u t)
      ((1 - μ v) * S.theta u v ^ 2 / (2 * S.lam u v)) v := by
    simpa only [μ] using hmCanon.congr_of_eventuallyEq hmEq.symm
  have hnu := incoming_area_vertical_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp
  have hzeta := incoming_area_vertical_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.2 hp
  have hphi := incoming_area_vertical_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1 hp
  have halpha := incoming_area_vertical_hasDerivAt
    (C1Solution.alpha_contDiffOn hB hB1 H) hp
  have hlam := incoming_area_vertical_hasDerivAt
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp
  have hnuJet := (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).2.1
  rw [hnuJet, C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H
    hp.1.le hp.2.1 hp.2.2.le] at hnu
  have hzetaJet := zeta_outgoing_pointwise hB hB1 H hpK hp.2.1
  have hphiJet := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hB1 H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
    hp.1.le hp.2.1 hp.2.2.le] at hphiJet
  have hzetaVal : deriv (fun t => S.zeta u t) v =
      -(S.nu u v * S.theta u v / S.r u v) := by
    rw [hzeta.deriv]
    calc
      (fderivWithin ℝ (fun p => S.zeta p.1 p.2) K (u, v)) (0, 1) =
          -(S.nu u v / S.r u v * S.theta u v) := by
            linarith only [hzetaJet]
      _ = -(S.nu u v * S.theta u v / S.r u v) := by ring
  have hphiVal : deriv (fun t => S.phi u t) v =
      S.theta u v / S.r u v := by
    rw [hphi.deriv]
    apply (eq_div_iff hrne).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using hphiJet.symm
  have hnuVal : deriv (fun t => S.nu u t) v =
      μ v * S.nu u v * S.lam u v / S.r u v /
        (1 - μ v) := by
    rw [hnu.deriv]
    dsimp [μ]
    field_simp [hrne, hgapne]
  have hμ := (hm.const_mul 2).div hr hrne
  have hgap := (hasDerivAt_const v (1 : ℝ)).sub hμ
  have hq := halpha.div hlam hlamne
  have hF := (((hm.const_mul 2).mul hnu).div hgap hgapne).add
    (((hr.mul hzeta).mul (hq.sub hphi)))
  have hFVal : deriv F v =
      μ v * S.nu u v * S.theta u v ^ 2 /
        ((1 - μ v) * S.lam u v) +
          S.r u v * S.zeta u v * deriv q v := by
    have hqVal : q v - S.phi u v = S.theta u v / S.lam u v := by
      dsimp [q]
      unfold Fields.theta
      field_simp [hlamne]
    have hF' := hF.deriv
    change deriv F v = _ at hF'
    rw [hF']
    have hzetaJet' :
        (fderivWithin ℝ (fun p => S.zeta p.1 p.2) K (u, v)) (0, 1) =
          -(S.nu u v / S.r u v * S.theta u v) := by
      linarith only [hzetaJet]
    have hphiJet' :
        (fderivWithin ℝ (fun p => S.phi p.1 p.2) K (u, v)) (0, 1) =
          S.theta u v / S.r u v := by
      apply (eq_div_iff hrne).2
      simpa only [Prod.fst, Prod.snd, mul_comm] using hphiJet.symm
    have hqDeriv := hq.deriv
    change deriv q v = _ at hqDeriv
    rw [hqDeriv]
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
    rw [hzetaJet', hphiJet', hqVal]
    dsimp [μ]
    field_simp [hrne, hlamne, hgapne, hmassgapne, hnune]
    ring
  have hEq : (fun t => sourceRho S u t / S.lam u t) =ᶠ[𝓝 v] F := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    have hpU' : (u, t) ∈ developmentWithInitialEdge 1 :=
      ⟨hp.1.le, ht.1, ht.2.trans hB1⟩
    have hrne' : S.r u t ≠ 0 := ne_of_gt (H.solution.radius_pos (u, t) hpU')
    have hlamne' : S.lam u t ≠ 0 :=
      ne_of_gt (H.solution.lam_pos (u, t) hpU')
    have hgapne' : 1 - 2 * S.m u t / S.r u t ≠ 0 := by
      have hratio := (hBV.mass_ratio_bounds hpU').2
      linarith
    dsimp [sourceRho, F, μ, q]
    unfold Fields.theta
    field_simp [hrne', hlamne', hgapne']
  have hRhoVal : deriv (fun t => sourceRho S u t / S.lam u t) v =
      μ v * S.nu u v * S.theta u v ^ 2 /
        ((1 - μ v) * S.lam u v) +
          S.r u v * S.zeta u v * deriv q v :=
    hEq.deriv_eq.trans hFVal
  have hqU := eq4_10a H hrGauge hcenter hboot hpU hp.1
  have hJ := (sourceJacobianPhiAlphaLam_eq_det hB hB1 H hp).symm
  rw [hJ]
  unfold sourceJacobianPhiAlphaLam
  rw [hRhoVal]
  have hphiU : deriv (fun t => S.phi t v) u = S.zeta u v / S.r u v := by
    have h := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
      hB hB1 H hpK
    have hφ := (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1
    have hderiv := incoming_area_horizontal_hasDerivAt hφ hp
    rw [hderiv.deriv]
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hp.2.2.le] at h
    apply (eq_div_iff hrne).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using h.symm
  rw [hphiU, hphiVal, hqU]
  dsimp [μ, q]
  field_simp [hrne, hlamne, hgapne, hmassgapne]
  ring

/-- Equation (4.27): the vertical derivative of `ρ/λ` is `r²` times
the oriented `(φ, α/λ)` Jacobian. -/
theorem eq4_27 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    deriv (fun t => sourceRho S u t / S.lam u t) v =
      S.r u v ^ 2 * (fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith only [hp.2.2]
  exact sourceRho_transport_vertical_local H hr hcenter hboot hB hB1
    ⟨hp.1, hp.2.1, hvB⟩

end ChristodoulouBV

end
