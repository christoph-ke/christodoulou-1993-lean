module

public import ChristodoulouBV.AreaEstimates.LogTransportCore
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Mixed logarithmic identities

The quotient transports in (4.10) use the extracted C¹ coordinate jets.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

private theorem horizontal_hasDerivAt_of_closed_triangle
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

private theorem vertical_hasDerivAt_of_closed_triangle
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

private theorem radius_vertical_hasDerivAt {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (S.r u) (S.lam u v) v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hcanon := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H) hp
  rw [C1Solution.canonicalRadius_vertical_jet hB hB1 H hpK] at hcanon
  have heq : (fun t => C1Solution.canonicalRadius S (u, t)) =ᶠ[𝓝 v] S.r u := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    exact C1Solution.canonicalRadius_eq_radius hB hB1 H hp.1.le ht.1 ht.2.le
  exact hcanon.congr_of_eventuallyEq heq.symm

private theorem mass_vertical_hasDerivAt {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (S.m u)
      ((1 - 2 * S.m u v / S.r u v) * S.theta u v ^ 2 /
        (2 * S.lam u v)) v := by
  have hcanon := C1Solution.canonicalMass_vertical_hasDerivAt hB hB1 H hp
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  rw [C1Solution.canonicalMassOutgoingDensity,
    C1Solution.canonicalMassRatio_eq_mass_ratio H hpU] at hcanon
  have heq : (fun t => C1Solution.canonicalMass 1 S (u, t)) =ᶠ[𝓝 v] S.m u := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    exact C1Solution.canonicalMass_eq_mass
      ⟨hp.1.le, ht.1, ht.2.trans hB1⟩
  exact hcanon.congr_of_eventuallyEq heq.symm

private theorem radius_horizontal_hasDerivAt {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => S.r t v) (S.nu u v) u := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hcanon := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H) hp
  rw [C1Solution.canonicalRadius_horizontal_jet hB hB1 H hpK] at hcanon
  have heq : (fun t => C1Solution.canonicalRadius S (t, v)) =ᶠ[𝓝 u]
      (fun t => S.r t v) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    exact C1Solution.canonicalRadius_eq_radius hB hB1 H ht.1.le ht.2 hp.2.2.le
  exact hcanon.congr_of_eventuallyEq heq.symm

private theorem mass_horizontal_hasDerivAt {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => S.m t v)
      ((1 - 2 * S.m u v / S.r u v) * S.zeta u v ^ 2 /
        (2 * S.nu u v)) u := by
  have hcanon := C1Solution.canonicalMass_horizontal_hasDerivAt hB hB1 H hp
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  rw [C1Solution.canonicalMassIncomingDensity,
    C1Solution.canonicalMassRatio_eq_mass_ratio H hpU] at hcanon
  have heq : (fun t => C1Solution.canonicalMass 1 S (t, v)) =ᶠ[𝓝 u]
      (fun t => S.m t v) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    exact C1Solution.canonicalMass_eq_mass
      ⟨ht.1.le, ht.2, hp.2.2.trans hB1⟩
  exact hcanon.congr_of_eventuallyEq heq.symm

private theorem phi_horizontal_deriv {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => S.phi t v) u = S.zeta u v / S.r u v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hphi := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1 hp
  have hzeta := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    hB hB1 H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hB1 H hp.1.le hp.2.1 hp.2.2.le]
    at hzeta
  have hrne : S.r u v ≠ 0 := ne_of_gt
    (H.solution.radius_pos (u, v) ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩)
  have hd := hphi.deriv
  rw [hd]  -- the derivative is the extracted scalar jet
  apply (eq_div_iff hrne).2
  simpa only [Prod.fst, Prod.snd, mul_comm] using hzeta.symm

private theorem phi_vertical_deriv {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (S.phi u) v = S.theta u v / S.r u v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hphi := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1 hp
  have htheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hB1 H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hB1 H hp.1.le hp.2.1 hp.2.2.le]
    at htheta
  have hrne : S.r u v ≠ 0 := ne_of_gt
    (H.solution.radius_pos (u, v) ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩)
  have hd := hphi.deriv
  rw [hd]
  apply (eq_div_iff hrne).2
  simpa only [Prod.fst, Prod.snd, mul_comm] using htheta.symm

/-- The derivative expansion in (4.7a), expressed through the first
logarithmic transport coefficient. -/
theorem eq4_7a_coefficient {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t =>
      (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
        (S.nu u t / S.r u t)) v =
      -2 * ((2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v * S.lam u v / S.r u v ^ 2) +
      (1 / (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v / S.r u v ^ 2) *
          (S.theta u v ^ 2 / S.lam u v) := by
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hr := radius_vertical_hasDerivAt hB hB1 H hp
  have hm := mass_vertical_hasDerivAt hB hB1 H hp
  have hnu := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp
  have hnuJet := (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).2.1
  rw [hnuJet,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hp.1.le hp.2.1 hp.2.2.le] at hnu
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hmu := (hm.const_mul 2).div hr hrne
  have hgap := (hasDerivAt_const v (1 : ℝ)).sub hmu
  have hquot := hmu.div hgap hgapne
  have hnuR := hnu.div hr hrne
  have hderiv := (hquot.mul hnuR).deriv
  simp only [Pi.div_apply, Pi.sub_apply] at hderiv
  convert hderiv using 1
  field_simp [hrne, hlamne, hgapne, hmassgapne]
  <;> ring

/-- The derivative expansion in (4.7b), expressed through the second
logarithmic transport coefficient. -/
theorem eq4_7b_coefficient {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t =>
      (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
        (S.lam t v / S.r t v)) u =
      -2 * ((2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v * S.lam u v / S.r u v ^ 2) +
      (1 / (1 - 2 * S.m u v / S.r u v)) *
        (S.lam u v / S.r u v ^ 2) *
          (S.zeta u v ^ 2 / S.nu u v) := by
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hr := radius_horizontal_hasDerivAt hB hB1 H hp
  have hm := mass_horizontal_hasDerivAt hB hB1 H hp
  have hlam := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp
  have hlamJet := (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).1
  rw [hlamJet,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hp.1.le hp.2.1 hp.2.2.le] at hlam
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hmu := (hm.const_mul 2).div hr hrne
  have hgap := (hasDerivAt_const u (1 : ℝ)).sub hmu
  have hquot := hmu.div hgap hgapne
  have hlamR := hlam.div hr hrne
  have hderiv := (hquot.mul hlamR).deriv
  simp only [Pi.div_apply, Pi.sub_apply] at hderiv
  convert hderiv using 1
  field_simp [hrne, hnune, hgapne, hmassgapne]
  <;> ring

private theorem log_lam_horizontal_deriv_at {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => Real.log (S.lam t v)) u =
      (2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v) *
        (S.nu u v / S.r u v) := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hlam := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp
  have hjet := (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).1
  rw [hjet,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hp.1.le hp.2.1 hp.2.2.le] at hlam
  have hlampos := H.solution.lam_pos (u, v) hpU
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hlog := (hlam.log hlampos.ne').deriv
  convert hlog using 1
  field_simp [hrne, hlampos.ne', hgapne, hmassgapne]
  <;> ring

/-- Equation (4.7a) as an interior mixed partial, with the `v` derivative
outside the incoming logarithmic derivative. -/
theorem eq4_7a_interior {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => deriv (fun s => Real.log (S.lam s t)) u) v =
      -2 * ((2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v * S.lam u v / S.r u v ^ 2) +
      (1 / (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v / S.r u v ^ 2) *
          (S.theta u v ^ 2 / S.lam u v) := by
  have heq : (fun t => deriv (fun s => Real.log (S.lam s t)) u) =ᶠ[𝓝 v]
      (fun t => (2 * S.m u t / S.r u t) /
        (1 - 2 * S.m u t / S.r u t) * (S.nu u t / S.r u t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    exact log_lam_horizontal_deriv_at hB hB1 H ⟨hp.1, ht.1, ht.2⟩
  rw [heq.deriv_eq]
  exact eq4_7a_coefficient hB hB1 H hp

private theorem log_nu_vertical_deriv_at {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => Real.log (-S.nu u t)) v =
      (2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v) *
        (S.lam u v / S.r u v) := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hnu := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp
  have hjet := (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).2.1
  rw [hjet,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hp.1.le hp.2.1 hp.2.2.le] at hnu
  have hnupos : 0 < -S.nu u v :=
    neg_pos.mpr (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hnune : S.nu u v ≠ 0 := ne_of_lt (neg_pos.mp hnupos)
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hlog := (hnu.neg.log hnupos.ne').deriv
  change deriv (fun t => Real.log (-S.nu u t)) v =
    -((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
      ((1 - 2 * S.m u v / S.r u v) * S.r u v)) / (-S.nu u v) at hlog
  convert hlog using 1
  field_simp [hrne, hnune, hnupos.ne', hgapne, hmassgapne]
  <;> ring

/-- Equation (4.7b) as an interior mixed partial, with the `u` derivative
outside the outgoing logarithmic derivative. -/
theorem eq4_7b_interior {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => deriv (fun s => Real.log (-S.nu t s)) v) u =
      -2 * ((2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v * S.lam u v / S.r u v ^ 2) +
      (1 / (1 - 2 * S.m u v / S.r u v)) *
        (S.lam u v / S.r u v ^ 2) *
          (S.zeta u v ^ 2 / S.nu u v) := by
  have heq : (fun t => deriv (fun s => Real.log (-S.nu t s)) v) =ᶠ[𝓝 u]
      (fun t => (2 * S.m t v / S.r t v) /
        (1 - 2 * S.m t v / S.r t v) * (S.lam t v / S.r t v)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    exact log_nu_vertical_deriv_at hB hB1 H ⟨ht.1, ht.2, hp.2.2⟩
  rw [heq.deriv_eq]
  exact eq4_7b_coefficient hB hB1 H hp

/-- Equation (4.8a) on a strict subtriangle. -/
theorem eq4_8a_interior {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => deriv (fun s => Real.log (S.lam s t)) u) v =
      deriv (fun t =>
        (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
          (S.lam t v / S.r t v)) u +
      (1 / (1 - 2 * S.m u v / S.r u v)) /
        S.r u v ^ 2 *
          (S.nu u v * S.theta u v ^ 2 / S.lam u v -
            S.lam u v * S.zeta u v ^ 2 / S.nu u v) := by
  rw [eq4_7a_interior hB hB1 H hp, eq4_7b_coefficient hB hB1 H hp]
  ring

/-- Equation (4.8b) on a strict subtriangle. -/
theorem eq4_8b_interior {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => deriv (fun s => Real.log (-S.nu t s)) v) u =
      deriv (fun t =>
        (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
          (S.nu u t / S.r u t)) v -
      (1 / (1 - 2 * S.m u v / S.r u v)) /
        S.r u v ^ 2 *
          (S.nu u v * S.theta u v ^ 2 / S.lam u v -
            S.lam u v * S.zeta u v ^ 2 / S.nu u v) := by
  rw [eq4_7b_interior hB hB1 H hp, eq4_7a_coefficient hB hB1 H hp]
  ring

/-- The oriented Jacobian of `(φ, β/ν)` in the mixed outgoing transport. -/
noncomputable def sourceJacobianPhiBetaNu (S : Fields) (u v : ℝ) : ℝ :=
  deriv (fun t => S.phi t v) u *
      deriv (fun t => S.beta u t / S.nu u t) v -
    deriv (S.phi u) v *
      deriv (fun t => S.beta t v / S.nu t v) u

/-- The oriented Jacobian of `(φ, α/λ)` in the mixed incoming transport. -/
noncomputable def sourceJacobianPhiAlphaLam (S : Fields) (u v : ℝ) : ℝ :=
  deriv (fun t => S.phi t v) u *
      deriv (fun t => S.alpha u t / S.lam u t) v -
    deriv (S.phi u) v *
      deriv (fun t => S.alpha t v / S.lam t v) u

/-- Equation (4.10a): the incoming derivative of the outgoing scalar quotient. -/
theorem eq4_10a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) (hu : 0 < u) :
    deriv (fun t => S.alpha t v / S.lam t v) u =
      -((2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v / S.r u v) * (S.theta u v / S.lam u v) := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith [hp.2.2]
  have hpT : (u, v) ∈ openCoordTriangle 0 B :=
    ⟨hu, hp.2.1, hvB⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hu.le, hp.2.1.le, hvB.le⟩
  have hAlpha := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.alpha_contDiffOn hB hB1 H) hpT
  have hLam := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hpT
  obtain ⟨hLamJet, _, hAlphaJet, _⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hB1 H hpK
  have hLamNe : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hp)
  have hRNe : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hGapNe : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
      IsC1Solution.isBVSolution_development (by norm_num) H
    have hratio := (hBV.mass_ratio_bounds hp).2
    linarith
  have hquot := (hAlpha.div hLam hLamNe).deriv
  rw [hAlphaJet, hLamJet,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hp.1 hp.2.1 hvB.le] at hquot
  convert hquot using 1
  unfold Fields.theta
  field_simp [hLamNe, hRNe, hGapNe]
  <;> ring

/-- Equation (4.10b): the outgoing derivative of the incoming scalar quotient. -/
theorem eq4_10b {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) (hu : 0 < u) :
    deriv (fun t => S.beta u t / S.nu u t) v =
      -((2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v)) *
        (S.lam u v / S.r u v) * (S.zeta u v / S.nu u v) := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith [hp.2.2]
  have hpT : (u, v) ∈ openCoordTriangle 0 B :=
    ⟨hu, hp.2.1, hvB⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hu.le, hp.2.1.le, hvB.le⟩
  have hBeta := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.beta_contDiffOn hB hB1 H) hpT
  have hNu := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hpT
  obtain ⟨_, hNuJet, _, hBetaJet⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hB1 H hpK
  have hNuNe : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hRNe : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hGapNe : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
      IsC1Solution.isBVSolution_development (by norm_num) H
    have hratio := (hBV.mass_ratio_bounds hp).2
    linarith
  have hquot := (hBeta.div hNu hNuNe).deriv
  rw [hBetaJet, hNuJet,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hp.1 hp.2.1 hvB.le] at hquot
  convert hquot using 1
  unfold Fields.zeta
  field_simp [hNuNe, hRNe, hGapNe]
  <;> ring

/-- The derivative of the outgoing quadratic correction: the remaining
derivative of `β/ν` is exactly the Jacobian contribution. -/
theorem sourceLogCorrection_horizontal_deriv {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => sourceLogCorrection S t v) u =
      (1 / (1 - 2 * S.m u v / S.r u v)) / S.r u v ^ 2 *
        (S.lam u v / S.nu u v * S.zeta u v ^ 2 -
          S.nu u v / S.lam u v * S.theta u v ^ 2) +
      sourceJacobianPhiBetaNu S u v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hr := radius_horizontal_hasDerivAt hB hB1 H hp
  have htheta := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.1 hp
  have halpha := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.alpha_contDiffOn hB hB1 H) hp
  have hlam := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp
  have hbeta := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.beta_contDiffOn hB hB1 H) hp
  have hnu := horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp
  have hthetaJet := theta_incoming_pointwise hB hB1 H hpK hp.2.1
  have hthetaVal : deriv (fun t => S.theta t v) u =
      -(S.lam u v / S.r u v * S.zeta u v) := by
    rw [htheta.deriv]
    linarith only [hthetaJet]
  have hAlt := ((htheta.div hr hrne).mul
    ((halpha.div hlam hlamne).sub (hbeta.div hnu hnune))).deriv
  have hEq : (fun t => sourceLogCorrection S t v) =ᶠ[𝓝 u]
      (fun t => S.theta t v / S.r t v *
        (S.alpha t v / S.lam t v - S.beta t v / S.nu t v)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.1, hp.2.1⟩] with t ht
    have hpT : (t, v) ∈ openCoordTriangle 0 B :=
      ⟨ht.1, ht.2, hp.2.2⟩
    have hpK' : (t, v) ∈ closedCoordTriangle 0 B :=
      ⟨ht.1.le, ht.2.le, hp.2.2.le⟩
    have hpU' : (t, v) ∈ developmentWithInitialEdge 1 :=
      ⟨ht.1.le, ht.2, hp.2.2.trans hB1⟩
    exact eq4_9a S t v
      (ne_of_gt (H.solution.lam_pos (t, v) hpU'))
      (ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK'))
  have hAltEq : deriv (fun t => sourceLogCorrection S t v) u =
      deriv (fun t => S.theta t v / S.r t v *
        (S.alpha t v / S.lam t v - S.beta t v / S.nu t v)) u :=
    hEq.deriv_eq
  have hAlt' := hAlt
  simp only [Pi.div_apply, Pi.sub_apply] at hAlt'
  change deriv (fun t => S.theta t v / S.r t v *
    (S.alpha t v / S.lam t v - S.beta t v / S.nu t v)) u = _ at hAlt'
  rw [hAltEq, hAlt']
  have hPhiU := phi_horizontal_deriv hB hB1 H hp
  have hPhiV := phi_vertical_deriv hB hB1 H hp
  have hAlphaQuot := eq4_10a H hrGauge hcenter hboot hpU hp.1
  have hBetaQuot := eq4_10b H hrGauge hcenter hboot hpU hp.1
  have hAlphaDeriv := (halpha.div hlam hlamne).deriv
  have hBetaDeriv := (hbeta.div hnu hnune).deriv
  simp only [Pi.div_apply, Prod.fst, Prod.snd] at hAlphaDeriv hBetaDeriv
  change deriv (fun t => S.alpha t v / S.lam t v) u = _ at hAlphaDeriv
  change deriv (fun t => S.beta t v / S.nu t v) u = _ at hBetaDeriv
  rw [← hAlphaDeriv, ← hBetaDeriv, hAlphaQuot] 
  have hThetaJetValue :
      (fderivWithin ℝ (fun p : ℝ × ℝ => S.theta p.1 p.2)
        (closedCoordTriangle 0 B) (u, v)) (1, 0) =
        -(S.lam u v / S.r u v * S.zeta u v) := by
    linarith only [hthetaJet]
  rw [hThetaJetValue]
  have hbracket : S.alpha u v / S.lam u v - S.beta u v / S.nu u v =
      S.theta u v / S.lam u v - S.zeta u v / S.nu u v := by
    unfold Fields.theta Fields.zeta
    field_simp [hlamne, hnune]
    <;> ring
  rw [hbracket]
  unfold sourceJacobianPhiBetaNu
  rw [hPhiU, hPhiV, hBetaQuot]
  field_simp [hrne, hlamne, hnune, hgapne, hmassgapne]
  <;> ring

/-- The outgoing derivative of `f*`. The sign in the paper's display before
(4.11b) is erroneous: both the quadratic term and Jacobian have positive
signs here. -/
theorem sourceLogCorrectionStar_vertical_deriv {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => sourceLogCorrectionStar S u t) v =
      (1 / (1 - 2 * S.m u v / S.r u v)) / S.r u v ^ 2 *
        (S.lam u v / S.nu u v * S.zeta u v ^ 2 -
          S.nu u v / S.lam u v * S.theta u v ^ 2) +
      sourceJacobianPhiAlphaLam S u v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hmassgapne : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hBV.two_mass_lt_radius hpU))
  have hr := radius_vertical_hasDerivAt hB hB1 H hp
  have hzeta := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.2 hp
  have halpha := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.alpha_contDiffOn hB hB1 H) hp
  have hlam := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp
  have hbeta := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.beta_contDiffOn hB hB1 H) hp
  have hnu := vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp
  have hzetaJet := zeta_outgoing_pointwise hB hB1 H hpK hp.2.1
  have hAlt := ((hzeta.div hr hrne).mul
    ((halpha.div hlam hlamne).sub (hbeta.div hnu hnune))).deriv
  have hEq : (fun t => sourceLogCorrectionStar S u t) =ᶠ[𝓝 v]
      (fun t => S.zeta u t / S.r u t *
        (S.alpha u t / S.lam u t - S.beta u t / S.nu u t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hp.2.1, hp.2.2⟩] with t ht
    have hpK' : (u, t) ∈ closedCoordTriangle 0 B :=
      ⟨hp.1.le, ht.1.le, ht.2.le⟩
    have hpU' : (u, t) ∈ developmentWithInitialEdge 1 :=
      ⟨hp.1.le, ht.1, ht.2.trans hB1⟩
    exact eq4_9b S u t
      (ne_of_gt (H.solution.lam_pos (u, t) hpU'))
      (ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK'))
  have hAltEq : deriv (fun t => sourceLogCorrectionStar S u t) v =
      deriv (fun t => S.zeta u t / S.r u t *
        (S.alpha u t / S.lam u t - S.beta u t / S.nu u t)) v :=
    hEq.deriv_eq
  have hAlt' := hAlt
  simp only [Pi.div_apply, Pi.sub_apply] at hAlt'
  change deriv (fun t => S.zeta u t / S.r u t *
    (S.alpha u t / S.lam u t - S.beta u t / S.nu u t)) v = _ at hAlt'
  rw [hAltEq, hAlt']
  have hPhiU := phi_horizontal_deriv hB hB1 H hp
  have hPhiV := phi_vertical_deriv hB hB1 H hp
  have hAlphaQuot := eq4_10a H hrGauge hcenter hboot hpU hp.1
  have hBetaQuot := eq4_10b H hrGauge hcenter hboot hpU hp.1
  have hAlphaDeriv := (halpha.div hlam hlamne).deriv
  have hBetaDeriv := (hbeta.div hnu hnune).deriv
  change deriv (fun t => S.alpha u t / S.lam u t) v = _ at hAlphaDeriv
  change deriv (fun t => S.beta u t / S.nu u t) v = _ at hBetaDeriv
  rw [← hAlphaDeriv, ← hBetaDeriv, hBetaQuot]
  have hZetaJetValue :
      (fderivWithin ℝ (fun p : ℝ × ℝ => S.zeta p.1 p.2)
        (closedCoordTriangle 0 B) (u, v)) (0, 1) =
        -(S.nu u v / S.r u v * S.theta u v) := by
    linarith only [hzetaJet]
  rw [hZetaJetValue]
  have hbracket : S.alpha u v / S.lam u v - S.beta u v / S.nu u v =
      S.theta u v / S.lam u v - S.zeta u v / S.nu u v := by
    unfold Fields.theta Fields.zeta
    field_simp [hlamne, hnune]
    ring
  rw [hbracket]
  unfold sourceJacobianPhiAlphaLam
  rw [hPhiU, hPhiV, hAlphaQuot]
  field_simp [hrne, hlamne, hnune, hgapne, hmassgapne]
  ring

/-- The uncommuted interior form used to prove equation (4.11a). -/
theorem eq4_11a_uncommuted {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => deriv (fun s => Real.log (S.lam s t)) u) v =
      deriv (fun t =>
        (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
          (S.lam t v / S.r t v) - sourceLogCorrection S t v) u +
      sourceJacobianPhiBetaNu S u v := by
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hr := (radius_horizontal_hasDerivAt hB hB1 H hp).differentiableAt
  have hm := (mass_horizontal_hasDerivAt hB hB1 H hp).differentiableAt
  have hlam := (horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp).differentiableAt
  have htheta := (horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.1 hp).differentiableAt
  have hzeta := (horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.2 hp).differentiableAt
  have hnu := (horizontal_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp).differentiableAt
  have hmu := (hm.const_mul 2).div hr hrne
  have hmass : DifferentiableAt ℝ (fun t =>
      (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
        (S.lam t v / S.r t v)) u :=
    (hmu.div ((differentiableAt_const (1 : ℝ)).sub hmu) hgapne).mul
      (hlam.div hr hrne)
  have hf : DifferentiableAt ℝ (fun t => sourceLogCorrection S t v) u := by
    change DifferentiableAt ℝ (fun t => S.theta t v / S.r t v *
      (S.theta t v / S.lam t v - S.zeta t v / S.nu t v)) u
    exact (htheta.div hr hrne).mul
      ((htheta.div hlam hlamne).sub (hzeta.div hnu hnune))
  have hdiff : deriv (fun t =>
      (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
        (S.lam t v / S.r t v) - sourceLogCorrection S t v) u =
      deriv (fun t =>
        (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
          (S.lam t v / S.r t v)) u -
      deriv (fun t => sourceLogCorrection S t v) u := by
    convert (deriv_sub hmass hf) using 1
  rw [eq4_8a_interior hB hB1 H hp, hdiff,
    sourceLogCorrection_horizontal_deriv hB hB1 H hrGauge hcenter hboot hp]
  ring

/-- The uncommuted interior form used to prove sign-corrected (4.11b). -/
theorem eq4_11b_corrected_uncommuted {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun t => deriv (fun s => Real.log (-S.nu t s)) v) u =
      deriv (fun t =>
        (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
          (S.nu u t / S.r u t) + sourceLogCorrectionStar S u t) v -
      sourceJacobianPhiAlphaLam S u v := by
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hr := (radius_vertical_hasDerivAt hB hB1 H hp).differentiableAt
  have hm := (mass_vertical_hasDerivAt hB hB1 H hp).differentiableAt
  have hnu := (vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1 hp).differentiableAt
  have hzeta := (vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.2 hp).differentiableAt
  have htheta := (vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.2.1 hp).differentiableAt
  have hlam := (vertical_hasDerivAt_of_closed_triangle
    (C1Solution.five_fields_contDiffOn hB hB1 H).1 hp).differentiableAt
  have hmu := (hm.const_mul 2).div hr hrne
  have hmass : DifferentiableAt ℝ (fun t =>
      (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
        (S.nu u t / S.r u t)) v :=
    (hmu.div ((differentiableAt_const (1 : ℝ)).sub hmu) hgapne).mul
      (hnu.div hr hrne)
  have hf : DifferentiableAt ℝ (fun t => sourceLogCorrectionStar S u t) v := by
    change DifferentiableAt ℝ (fun t => S.zeta u t / S.r u t *
      (S.theta u t / S.lam u t - S.zeta u t / S.nu u t)) v
    exact (hzeta.div hr hrne).mul
      ((htheta.div hlam hlamne).sub (hzeta.div hnu hnune))
  have hdiff : deriv (fun t =>
      (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
        (S.nu u t / S.r u t) + sourceLogCorrectionStar S u t) v =
      deriv (fun t =>
        (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
          (S.nu u t / S.r u t)) v +
      deriv (fun t => sourceLogCorrectionStar S u t) v := by
    convert (deriv_add hmass hf) using 1
  rw [eq4_8b_interior hB hB1 H hp, hdiff,
    sourceLogCorrectionStar_vertical_deriv hB hB1 H hrGauge hcenter hboot hp]
  ring


end ChristodoulouBV

end
