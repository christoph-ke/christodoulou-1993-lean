module

public import ChristodoulouBV.AreaEstimates.ScalarAreaIntegral
import ChristodoulouBV.AreaEstimates.ScalarAreaAlgebra
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Scalar quotient Jacobians

The quotient rule gives the two area densities in terms of the field
transport residuals and the `(λ, φ)` and `(ν, φ)` Jacobians.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

private theorem fderiv_div_real_local
    {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (hne : g p ≠ 0) :
    fderiv ℝ (fun q => f q / g q) p =
      (1 / g p) • fderiv ℝ f p -
        (f p / g p ^ 2) • fderiv ℝ g p := by
  have hi := (hasFDerivAt_inv hne).comp p hg.hasFDerivAt
  have hm := hf.hasFDerivAt.mul hi
  change fderiv ℝ (f * ((fun y : ℝ => y⁻¹) ∘ g)) p = _
  rw [hm.fderiv]
  apply ContinuousLinearMap.ext
  intro e
  simp only [add_apply, sub_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  field_simp [hne]
  ring

/-- The map whose analytic area is the left side of (4.16). -/
@[expose] noncomputable def sourcePhiAlphaLamMap (S : Fields) (p : ℝ × ℝ) : ℝ × ℝ :=
  (S.phi p.1 p.2, S.alpha p.1 p.2 / S.lam p.1 p.2)

/-- The map whose analytic area is the left side of (4.18). -/
@[expose] noncomputable def sourcePhiBetaNuMap (S : Fields) (p : ℝ × ℝ) : ℝ × ℝ :=
  (S.phi p.1 p.2, S.beta p.1 p.2 / S.nu p.1 p.2)

private theorem alpha_jacobian_quotient
    {lam alpha phi : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hlam : DifferentiableAt ℝ lam p)
    (halpha : DifferentiableAt ℝ alpha p)
    (hphi : DifferentiableAt ℝ phi p)
    (hlamne : lam p ≠ 0)
    (htransport : (fderiv ℝ alpha p) (1, 0) =
      (fderiv ℝ lam p) (1, 0) * phi p) :
    (fderiv ℝ (fun q => (phi q, alpha q / lam q)) p).det =
      ((fderiv ℝ phi p) (1, 0) / lam p) *
        ((fderiv ℝ alpha p) (0, 1) -
          (fderiv ℝ lam p) (0, 1) * phi p) +
      ((alpha p - lam p * phi p) / lam p ^ 2) *
        (fderiv ℝ (fun q => (lam q, phi q)) p).det := by
  let h : ℝ × ℝ → ℝ := fun q => alpha q / lam q
  have hdiff : DifferentiableAt ℝ h p :=
    halpha.mul (hlam.inv hlamne)
  have hq := fderiv_div_real_local halpha hlam hlamne
  have hprod (e : ℝ × ℝ) :
      (fderiv ℝ alpha p) e =
        (fderiv ℝ lam p) e * h p + lam p * (fderiv ℝ h p) e := by
    rw [hq]
    simp only [sub_apply, smul_apply, smul_eq_mul, h]
    field_simp [hlamne]
    ring
  rw [det_fderiv_prodMk hphi hdiff, det_fderiv_prodMk hlam hphi]
  exact alpha_quotient_jacobian_algebra
    (lam p) (alpha p) (phi p) (alpha p - lam p * phi p)
    ((fderiv ℝ lam p) (1, 0)) ((fderiv ℝ lam p) (0, 1))
    ((fderiv ℝ alpha p) (1, 0)) ((fderiv ℝ alpha p) (0, 1))
    ((fderiv ℝ phi p) (1, 0)) ((fderiv ℝ phi p) (0, 1))
    ((fderiv ℝ h p) (1, 0)) ((fderiv ℝ h p) (0, 1))
    hlamne rfl (hprod _) (hprod _) htransport

private theorem beta_jacobian_quotient
    {nu beta phi : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hnu : DifferentiableAt ℝ nu p)
    (hbeta : DifferentiableAt ℝ beta p)
    (hphi : DifferentiableAt ℝ phi p)
    (hnune : nu p ≠ 0)
    (htransport : (fderiv ℝ beta p) (0, 1) =
      (fderiv ℝ nu p) (0, 1) * phi p) :
    (fderiv ℝ (fun q => (phi q, beta q / nu q)) p).det =
      -((fderiv ℝ phi p) (0, 1) / nu p) *
        ((fderiv ℝ beta p) (1, 0) -
          (fderiv ℝ nu p) (1, 0) * phi p) +
      ((beta p - nu p * phi p) / nu p ^ 2) *
        (fderiv ℝ (fun q => (nu q, phi q)) p).det := by
  let h : ℝ × ℝ → ℝ := fun q => beta q / nu q
  have hdiff : DifferentiableAt ℝ h p :=
    hbeta.mul (hnu.inv hnune)
  have hq := fderiv_div_real_local hbeta hnu hnune
  have hprod (e : ℝ × ℝ) :
      (fderiv ℝ beta p) e =
        (fderiv ℝ nu p) e * h p + nu p * (fderiv ℝ h p) e := by
    rw [hq]
    simp only [sub_apply, smul_apply, smul_eq_mul, h]
    field_simp [hnune]
    ring
  rw [det_fderiv_prodMk hphi hdiff, det_fderiv_prodMk hnu hphi]
  exact beta_quotient_jacobian_algebra
    (nu p) (beta p) (phi p) (beta p - nu p * phi p)
    ((fderiv ℝ nu p) (1, 0)) ((fderiv ℝ nu p) (0, 1))
    ((fderiv ℝ beta p) (1, 0)) ((fderiv ℝ beta p) (0, 1))
    ((fderiv ℝ phi p) (1, 0)) ((fderiv ℝ phi p) (0, 1))
    ((fderiv ℝ h p) (1, 0)) ((fderiv ℝ h p) (0, 1))
    hnune rfl (hprod _) (hprod _) htransport

/-- The pointwise Jacobian identity preceding (4.15a). -/
theorem source_alpha_area_jacobian {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det =
      (S.zeta u v / S.r u v / S.lam u v) *
        ((fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2) (u, v)) (0, 1) -
          (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (0, 1) *
            S.phi u v) +
      (S.theta u v / S.lam u v ^ 2) *
        (fderiv ℝ (sourceLamPhiMap S) (u, v)).det := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let p : ℝ × ℝ := (u, v)
  let lam : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let alpha : ℝ × ℝ → ℝ := fun q => S.alpha q.1 q.2
  let phi : ℝ × ℝ → ℝ := fun q => S.phi q.1 q.2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : p ∈ K := by
    simpa only [K, p, closedCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) ≤ u ∧ u ≤ v ∧ v ≤ B from ⟨hu.le, huv.le, hvB.le⟩)
  have hpInt : p ∈ interior K := by
    rw [interior_closedCoordTriangle]
    simpa only [p, openCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) < u ∧ u < v ∧ v < B from ⟨hu, huv, hvB⟩)
  have hnhds : K ∈ 𝓝 p :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  obtain ⟨hlamK, _, hphiK, halphaK, _⟩ := unit_field_contDiffOn H
  have hKsub : K ⊆ closedCoordTriangle 0 1 := by
    intro q hq
    have hq' : (0 : ℝ) ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ B := by
      simpa only [K, closedCoordTriangle, mem_ofPred_eq] using hq
    simpa only [closedCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ 1 from
        ⟨hq'.1, hq'.2.1, hq'.2.2.trans hBb.le⟩)
  have hlamDiff : DifferentiableAt ℝ lam p :=
    ((hlamK.mono hKsub).differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have halphaDiff : DifferentiableAt ℝ alpha p :=
    ((halphaK.mono hKsub).differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hphiDiff : DifferentiableAt ℝ phi p :=
    ((hphiK.mono hKsub).differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hpU : p ∈ developmentWithInitialEdge 1 := ⟨hu.le, huv, hv⟩
  have hlamne : lam p ≠ 0 := ne_of_gt (H.solution.lam_pos p hpU)
  obtain ⟨hLamJet, _, hAlphaJet, _⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  rw [fderivWithin_of_mem_nhds hnhds] at hLamJet hAlphaJet
  have htransport : (fderiv ℝ alpha p) (1, 0) =
      (fderiv ℝ lam p) (1, 0) * phi p := by
    rw [hAlphaJet, hLamJet]
  have hZeta :=
    C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet hB hBb H hpK
  rw [fderivWithin_of_mem_nhds hnhds,
    C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le] at hZeta
  have hrPos : 0 < S.r u v := H.solution.radius_pos p hpU
  have hphiU : (fderiv ℝ phi p) (1, 0) = S.zeta u v / S.r u v := by
    apply (eq_div_iff hrPos.ne').2
    simpa only [mul_comm] using hZeta.symm
  have hj := alpha_jacobian_quotient hlamDiff halphaDiff hphiDiff
    hlamne htransport
  change (fderiv ℝ (fun q => (phi q, alpha q / lam q)) p).det = _
  rw [hj, hphiU]
  rw [show sourceLamPhiMap S = (fun q => (lam q, phi q)) from rfl]
  simp only [Fields.theta, p, lam, alpha, phi]

/-- The pointwise Jacobian identity preceding (4.17a). -/
theorem source_beta_area_jacobian {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det =
      -(S.theta u v / S.r u v / S.nu u v) *
        ((fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, v)) (1, 0) -
          (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (1, 0) *
            S.phi u v) +
      (S.zeta u v / S.nu u v ^ 2) *
        (fderiv ℝ (sourceNuPhiMap S) (u, v)).det := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let p : ℝ × ℝ := (u, v)
  let nu : ℝ × ℝ → ℝ := fun q => S.nu q.1 q.2
  let beta : ℝ × ℝ → ℝ := fun q => S.beta q.1 q.2
  let phi : ℝ × ℝ → ℝ := fun q => S.phi q.1 q.2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : p ∈ K := by
    simpa only [K, p, closedCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) ≤ u ∧ u ≤ v ∧ v ≤ B from ⟨hu.le, huv.le, hvB.le⟩)
  have hpInt : p ∈ interior K := by
    rw [interior_closedCoordTriangle]
    simpa only [p, openCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) < u ∧ u < v ∧ v < B from ⟨hu, huv, hvB⟩)
  have hnhds : K ∈ 𝓝 p :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  obtain ⟨_, hnuK, hphiK, _, hbetaK⟩ := unit_field_contDiffOn H
  have hKsub : K ⊆ closedCoordTriangle 0 1 := by
    intro q hq
    have hq' : (0 : ℝ) ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ B := by
      simpa only [K, closedCoordTriangle, mem_ofPred_eq] using hq
    simpa only [closedCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ 1 from
        ⟨hq'.1, hq'.2.1, hq'.2.2.trans hBb.le⟩)
  have hnuDiff : DifferentiableAt ℝ nu p :=
    ((hnuK.mono hKsub).differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hbetaDiff : DifferentiableAt ℝ beta p :=
    ((hbetaK.mono hKsub).differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hphiDiff : DifferentiableAt ℝ phi p :=
    ((hphiK.mono hKsub).differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hpU : p ∈ developmentWithInitialEdge 1 := ⟨hu.le, huv, hv⟩
  have hnune : nu p ≠ 0 := ne_of_lt (C1Solution.nu_neg hB hBb H hu.le huv hvB.le)
  obtain ⟨_, hNuJet, _, hBetaJet⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  rw [fderivWithin_of_mem_nhds hnhds] at hNuJet hBetaJet
  have htransport : (fderiv ℝ beta p) (0, 1) =
      (fderiv ℝ nu p) (0, 1) * phi p := by
    rw [hBetaJet, hNuJet]
  have hTheta :=
    C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet hB hBb H hpK
  rw [fderivWithin_of_mem_nhds hnhds,
    C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le] at hTheta
  have hrPos : 0 < S.r u v := H.solution.radius_pos p hpU
  have hphiV : (fderiv ℝ phi p) (0, 1) = S.theta u v / S.r u v := by
    apply (eq_div_iff hrPos.ne').2
    simpa only [mul_comm] using hTheta.symm
  have hj := beta_jacobian_quotient hnuDiff hbetaDiff hphiDiff
    hnune htransport
  change (fderiv ℝ (fun q => (phi q, beta q / nu q)) p).det = _
  rw [hj, hphiV]
  rw [show sourceNuPhiMap S = (fun q => (nu q, phi q)) from rfl]
  simp only [Fields.zeta, p, nu, beta, phi]

end ChristodoulouBV

end
