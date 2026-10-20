module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceSystem
public import ChristodoulouBV.C1Solution.AxisLocalExistenceGeneralEdgeBounds
import ChristodoulouBV.C1Solution.AxisMassDefect
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Ordinary equations for the normalized translated axis triangle

Relative first jets of the Picard reconstruction give ordinary derivatives
in the interior and on its incoming edge.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

open ChristodoulouBV.C1Solution

/-- A translated axis development point belongs to its closed triangle. -/
theorem axis_development_subset_closed {a b u v : ℝ}
    (hp : (u, v) ∈ axisTriangleDevelopment a b) :
    (u, v) ∈ closedCoordTriangle a b := by
  change a ≤ u ∧ u ≤ v ∧ v ≤ b
  exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩

/-- A point away from the incoming edge is in the open triangle. -/
theorem axis_development_interior {a b u v : ℝ}
    (hu : a < u) (hp : (u, v) ∈ axisTriangleDevelopment a b) :
    (u, v) ∈ openCoordTriangle a b := by
  change a < u ∧ u < v ∧ v < b
  exact ⟨hu, hp.2.1, hp.2.2⟩

/-- The normalized Picard fixed point satisfies every classical reduced
equation on its translated axis triangle. -/
theorem Box.is_classical_axis_triangle {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint) :
    AxisClassicalSolution a b x.1.toTriple.toFields := by
  let S := x.1.toTriple.toFields
  let K := closedCoordTriangle a b
  have hbasic := x.reconstructed_fields_basic hab hM hsmall hg
  dsimp only at hbasic
  rcases hbasic with
    ⟨hrC1, hphiC1, hmC1, hlamC1, hnuC1, halphaC1, hbetaC1,
      hsign, haxis⟩
  have hrv : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (S.r u) (S.lam u v) v := by
    intro u v hp
    have h := vertical_hasDerivAt_axis_development hrC1 hp
    change HasDerivAt (fun t => x.1.toTriple.radius (u, t))
      ((fderivWithin ℝ x.1.toTriple.radius K (u, v)) (0, 1)) v at h
    rw [x.radius_v hab (axis_development_subset_closed hp)] at h
    exact h
  have hru : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.r w v) (S.nu u v) u := by
    intro u v hu hp
    have h := horizontal_hasDerivAt_of_triangle_c1 hrC1
      (axis_development_interior hu hp)
    change HasDerivAt (fun t => x.1.toTriple.radius (t, v))
      ((fderivWithin ℝ x.1.toTriple.radius K (u, v)) (1, 0)) u at h
    rw [x.radius_u hab hM hsmall hfixed
      (axis_development_subset_closed hp)] at h
    exact h
  have hpsiC1 : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => x.1.toTriple.radius p * x.1.toTriple.phi p) K :=
    hrC1.mul hphiC1
  have hpsiEq : EqOn x.1.toTriple.scalarRadius
      (fun p : ℝ × ℝ => x.1.toTriple.radius p * x.1.toTriple.phi p) K :=
    fun _ hp => x.scalarRadius_eq_radius_mul_phi_on hp
  have hpsiv : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.r u w * S.phi u w) (S.alpha u v) v := by
    intro u v hp
    have hpK := axis_development_subset_closed hp
    have h := vertical_hasDerivAt_axis_development hpsiC1 hp
    have hj := fderivWithin_congr' (𝕜 := ℝ) hpsiEq hpK
    change HasDerivAt (fun t => x.1.toTriple.radius (u, t) *
      x.1.toTriple.phi (u, t))
      ((fderivWithin ℝ (fun p : ℝ × ℝ =>
        x.1.toTriple.radius p * x.1.toTriple.phi p) K (u, v)) (0, 1)) v at h
    rw [← hj, x.scalarRadius_v hab hpK] at h
    exact h
  have hpsiu : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.r w v * S.phi w v) (S.beta u v) u := by
    intro u v hu hp
    have hpK := axis_development_subset_closed hp
    have h := horizontal_hasDerivAt_of_triangle_c1 hpsiC1
      (axis_development_interior hu hp)
    have hj := fderivWithin_congr' (𝕜 := ℝ) hpsiEq hpK
    change HasDerivAt (fun t => x.1.toTriple.radius (t, v) *
      x.1.toTriple.phi (t, v))
      ((fderivWithin ℝ (fun p : ℝ × ℝ =>
        x.1.toTriple.radius p * x.1.toTriple.phi p) K (u, v)) (1, 0)) u at h
    rw [← hj, x.scalarRadius_u hab hM hsmall hfixed hpK] at h
    exact h
  have hmv : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (S.m u)
        ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
          (2 * S.lam u v)) v := by
    intro u v hp
    have hpK := axis_development_subset_closed hp
    have h := vertical_hasDerivAt_axis_development hmC1 hp
    change HasDerivAt (fun t => x.1.toTriple.mass (u, t))
      ((fderivWithin ℝ x.1.toTriple.mass K (u, v)) (0, 1)) v at h
    have hj := x.outgoing_mass_equation hab hpK hp.2.1
    have heq := x.massRatio_off_axis hp.2.1
    have hlamLower := (hsign (u, v) hpK).1
    change (1 / 4 : ℝ) ≤ x.1.toTriple.lam (u, v) at hlamLower
    have hlam : x.1.toTriple.lam (u, v) ≠ 0 :=
      ne_of_gt (by linarith only [hlamLower])
    have hderiv : (fderivWithin ℝ x.1.toTriple.mass K (u, v)) (0, 1) =
        (1 - 2 * x.1.toTriple.mass (u, v) /
            x.1.toTriple.radius (u, v)) *
          x.1.toTriple.theta (u, v) ^ 2 /
            (2 * x.1.toTriple.lam (u, v)) := by
      rw [heq] at hj
      apply (eq_div_iff (mul_ne_zero (by norm_num) hlam)).2
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hj
    rw [hderiv] at h
    exact h
  have hmu : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.m w v)
        ((1 - 2 * S.m u v / S.r u v) * (S.zeta u v)^2 /
          (2 * S.nu u v)) u := by
    intro u v hu hp
    have hpK := axis_development_subset_closed hp
    have h := horizontal_hasDerivAt_of_triangle_c1 hmC1
      (axis_development_interior hu hp)
    change HasDerivAt (fun t => x.1.toTriple.mass (t, v))
      ((fderivWithin ℝ x.1.toTriple.mass K (u, v)) (1, 0)) u at h
    have hj := x.incoming_mass_equation hab hM hsmall hg hfixed hpK hp.2.1
    have heq := x.massRatio_off_axis hp.2.1
    have hnuUpper := (hsign (u, v) hpK).2.2.1
    change x.1.toTriple.nu (u, v) ≤ -(1 / 4 : ℝ) at hnuUpper
    have hnu : x.1.toTriple.nu (u, v) ≠ 0 :=
      ne_of_lt (by linarith only [hnuUpper])
    have hderiv : (fderivWithin ℝ x.1.toTriple.mass K (u, v)) (1, 0) =
        (1 - 2 * x.1.toTriple.mass (u, v) /
            x.1.toTriple.radius (u, v)) *
          x.1.toTriple.zeta (u, v) ^ 2 /
            (2 * x.1.toTriple.nu (u, v)) := by
      rw [heq] at hj
      apply (eq_div_iff (mul_ne_zero (by norm_num) hnu)).2
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hj
    rw [hderiv] at h
    exact h
  have hlamu : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.lam w v)
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u := by
    intro u v hu hp
    have hpK := axis_development_subset_closed hp
    have h := horizontal_hasDerivAt_of_triangle_c1 hlamC1
      (axis_development_interior hu hp)
    change HasDerivAt (fun t => x.1.toTriple.lam (t, v))
      ((fderivWithin ℝ x.1.toTriple.lam K (u, v)) (1, 0)) u at h
    rw [x.radius_uv_equation hab hM hsmall hfixed hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hnuv : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (S.nu u)
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v := by
    intro u v hp
    have hpK := axis_development_subset_closed hp
    have h := vertical_hasDerivAt_axis_development hnuC1 hp
    change HasDerivAt (fun t => x.1.toTriple.nu (u, t))
      ((fderivWithin ℝ x.1.toTriple.nu K (u, v)) (0, 1)) v at h
    rw [x.nu_v_equation hab hM hsmall hfixed hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hthetau : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.theta w v)
        (-(S.lam u v / S.r u v * S.zeta u v)) u := by
    intro u v hu hp
    have hpK := axis_development_subset_closed hp
    have hthetaC1 : ContDiffOn ℝ 1 x.1.toTriple.theta K :=
      halphaC1.sub (hlamC1.mul hphiC1)
    have h := horizontal_hasDerivAt_of_triangle_c1 hthetaC1
      (axis_development_interior hu hp)
    change HasDerivAt (fun t => x.1.toTriple.theta (t, v))
      ((fderivWithin ℝ x.1.toTriple.theta K (u, v)) (1, 0)) u at h
    rw [x.theta_transport hab hM hsmall hfixed hpK hp.2.1] at h
    change HasDerivAt (fun w => x.1.toTriple.theta (w, v))
      (-(x.1.toTriple.lam (u, v) / x.1.toTriple.radius (u, v) *
        x.1.toTriple.zeta (u, v))) u
    simpa only [neg_mul] using h
  have hzetav : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (S.zeta u)
        (-(S.nu u v / S.r u v * S.theta u v)) v := by
    intro u v hp
    have hpK := axis_development_subset_closed hp
    have hzetaC1 : ContDiffOn ℝ 1 x.1.toTriple.zeta K :=
      hbetaC1.sub (hnuC1.mul hphiC1)
    have h := vertical_hasDerivAt_axis_development hzetaC1 hp
    change HasDerivAt (fun t => x.1.toTriple.zeta (u, t))
      ((fderivWithin ℝ x.1.toTriple.zeta K (u, v)) (0, 1)) v at h
    rw [x.zeta_transport hab hM hsmall hfixed hpK hp.2.1] at h
    change HasDerivAt (fun w => x.1.toTriple.zeta (u, w))
      (-(x.1.toTriple.nu (u, v) / x.1.toTriple.radius (u, v) *
        x.1.toTriple.theta (u, v))) v
    simpa only [neg_mul] using h
  have halphau : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (fun w => S.alpha w v)
        (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) u := by
    intro u v hu hp
    have hpK := axis_development_subset_closed hp
    have h := horizontal_hasDerivAt_of_triangle_c1 halphaC1
      (axis_development_interior hu hp)
    change HasDerivAt (fun t => x.1.toTriple.alpha (t, v))
      ((fderivWithin ℝ x.1.toTriple.alpha K (u, v)) (1, 0)) u at h
    rw [x.alpha_u hab hM hsmall hfixed hpK,
      x.gravitational_off_axis hab hM hsmall hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hbetav : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
      HasDerivAt (S.beta u)
        (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) v := by
    intro u v hp
    have hpK := axis_development_subset_closed hp
    have h := vertical_hasDerivAt_axis_development hbetaC1 hp
    change HasDerivAt (fun t => x.1.toTriple.beta (u, t))
      ((fderivWithin ℝ x.1.toTriple.beta K (u, v)) (0, 1)) v at h
    rw [x.beta_v hab hM hsmall hpK,
      x.gravitational_off_axis hab hM hsmall hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have haxisr : ∀ u ∈ Icc a b, S.r u u = 0 :=
    fun u hu => (haxis u hu).1
  have haxism : ∀ u ∈ Icc a b, S.m u u = 0 :=
    fun u hu => (haxis u hu).2
  have hrpos : ∀ p ∈ axisTriangleDevelopment a b, 0 < S.r p.1 p.2 := by
    intro p hp
    exact x.radius_pos (axis_development_subset_closed hp) hp.2.1
  have hlampos : ∀ p ∈ K, 0 < S.lam p.1 p.2 := by
    intro p hp
    linarith only [(hsign p hp).1]
  have hnuneg : ∀ p ∈ axisTriangleDevelopment a b,
      S.nu p.1 p.2 < 0 := by
    intro p hp
    linarith only [(hsign p (axis_development_subset_closed hp)).2.2.1]
  have hApos : ∀ p ∈ axisTriangleDevelopment a b,
      0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 := by
    intro p hp
    linarith only [(hsign p (axis_development_subset_closed hp)).2.2.2.2]
  exact {
    r_c1 := hrC1
    phi_c1 := hphiC1
    m_c1 := hmC1
    lam_c1 := hlamC1
    nu_c1 := hnuC1
    alpha_c1 := halphaC1
    beta_c1 := hbetaC1
    r_v := hrv
    r_u := hru
    psi_v := hpsiv
    psi_u := hpsiu
    m_v := hmv
    m_u := hmu
    lam_u := hlamu
    nu_v := hnuv
    theta_u := hthetau
    zeta_v := hzetav
    alpha_u := halphau
    beta_v := hbetav
    r_axis := haxisr
    m_axis := haxism
    r_pos := hrpos
    lam_pos := hlampos
    nu_neg := hnuneg
    gap_pos := hApos }

end ChristodoulouBV.AxisPicard

end
