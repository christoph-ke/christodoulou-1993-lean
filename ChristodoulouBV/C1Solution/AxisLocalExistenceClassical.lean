module

public import ChristodoulouBV.C1Solution.AxisLocalExistence
public import ChristodoulouBV.C1Solution.AxisMassDefectGauge
public import ChristodoulouBV.C1Solution.FrozenBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Classical derivatives of the reconstructed initial axis triangle

The Picard construction produces relative first jets on a closed triangle.
These lemmas turn them into ordinary derivatives on the open development,
including the outgoing initial edge.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- An open-development point belongs to the closed triangle. -/
theorem initial_development_subset_closed {b u v : ℝ}
    (hp : (u, v) ∈ developmentWithInitialEdge b) :
    (u, v) ∈ closedCoordTriangle 0 b := by
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ b
  exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩

/-- At a strictly positive incoming coordinate, a development point lies in
the ordinary interior of the closed triangle. -/
theorem initial_development_interior {b u v : ℝ}
    (hu : 0 < u) (hp : (u, v) ∈ developmentWithInitialEdge b) :
    (u, v) ∈ openCoordTriangle 0 b := by
  change 0 < u ∧ u < v ∧ v < b
  exact ⟨hu, hp.2.1, hp.2.2⟩

/-- A relative vertical first jet becomes an ordinary derivative at every
point of the initial-edge development. -/
theorem vertical_hasDerivAt_initial_development {b u v : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 b))
    (hp : (u, v) ∈ developmentWithInitialEdge b) :
    HasDerivAt (fun t => f (u, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (u, v)) (0, 1)) v := by
  rcases lt_or_eq_of_le hp.1 with hu | hu
  · exact vertical_hasDerivAt_of_triangle_c1 hf
      (initial_development_interior hu hp)
  · change 0 = u at hu
    subst u
    exact vertical_hasDerivAt_initial_edge hf ⟨hp.2.1, hp.2.2⟩

/-- A relative horizontal first jet becomes an ordinary derivative at every
development point with strictly positive incoming coordinate. -/
theorem horizontal_hasDerivAt_initial_development {b u v : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 b))
    (hu : 0 < u) (hp : (u, v) ∈ developmentWithInitialEdge b) :
    HasDerivAt (fun t => f (t, v))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (u, v)) (1, 0)) u :=
  horizontal_hasDerivAt_of_triangle_c1 hf
    (initial_development_interior hu hp)

/-- The reconstructed fields satisfy the frozen C¹ solution predicate on
an initial axis development whenever their Picard edge data satisfy the normalized Picard box bounds. -/
theorem Box.isSolution_and_isC1Solution_initial {b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box 0 b M g hEdge)
    (hb : 0 < b) (hM : 1 ≤ M)
    (hsmall : b ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc 0 b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint) :
    let S := x.1.toTriple.toFields
    IsSolution (developmentWithInitialEdge b) S ∧
      IsC1Solution (developmentWithInitialEdge b) S := by
  let S := x.1.toTriple.toFields
  let K := closedCoordTriangle 0 b
  have hsmall' : b - 0 ≤ (numericalLedger M).lifetime M := by
    simpa using hsmall
  have hbasic := x.reconstructed_fields_basic hb hM hsmall' hg
  dsimp only at hbasic
  rcases hbasic with
    ⟨hrC1, hphiC1, hmC1, hlamC1, hnuC1, halphaC1, hbetaC1,
      hsign, haxis⟩
  have hrv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.r u) (S.lam u v) v := by
    intro u v hp
    have h := vertical_hasDerivAt_initial_development hrC1 hp
    change HasDerivAt (fun t => x.1.toTriple.radius (u, t))
      ((fderivWithin ℝ x.1.toTriple.radius K (u, v)) (0, 1)) v at h
    rw [x.radius_v hb (initial_development_subset_closed hp)] at h
    exact h
  have hru : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.r w v) (S.nu u v) u := by
    intro u v hu hp
    have h := horizontal_hasDerivAt_initial_development hrC1 hu hp
    change HasDerivAt (fun t => x.1.toTriple.radius (t, v))
      ((fderivWithin ℝ x.1.toTriple.radius K (u, v)) (1, 0)) u at h
    rw [x.radius_u hb hM hsmall' hfixed
      (initial_development_subset_closed hp)] at h
    exact h
  have hpsiC1 : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => x.1.toTriple.radius p * x.1.toTriple.phi p) K :=
    hrC1.mul hphiC1
  have hpsiEq : EqOn x.1.toTriple.scalarRadius
      (fun p : ℝ × ℝ => x.1.toTriple.radius p * x.1.toTriple.phi p) K :=
    fun _ hp => x.scalarRadius_eq_radius_mul_phi_on hp
  have hpsiv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.r u w * S.phi u w) (S.alpha u v) v := by
    intro u v hp
    have hpK := initial_development_subset_closed hp
    have h := vertical_hasDerivAt_initial_development hpsiC1 hp
    have hj := fderivWithin_congr' (𝕜 := ℝ) hpsiEq hpK
    change HasDerivAt (fun t => x.1.toTriple.radius (u, t) *
      x.1.toTriple.phi (u, t))
      ((fderivWithin ℝ (fun p : ℝ × ℝ =>
        x.1.toTriple.radius p * x.1.toTriple.phi p) K (u, v)) (0, 1)) v at h
    rw [← hj, x.scalarRadius_v hb hpK] at h
    exact h
  have hpsiu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.r w v * S.phi w v) (S.beta u v) u := by
    intro u v hu hp
    have hpK := initial_development_subset_closed hp
    have h := horizontal_hasDerivAt_initial_development hpsiC1 hu hp
    have hj := fderivWithin_congr' (𝕜 := ℝ) hpsiEq hpK
    change HasDerivAt (fun t => x.1.toTriple.radius (t, v) *
      x.1.toTriple.phi (t, v))
      ((fderivWithin ℝ (fun p : ℝ × ℝ =>
        x.1.toTriple.radius p * x.1.toTriple.phi p) K (u, v)) (1, 0)) u at h
    rw [← hj, x.scalarRadius_u hb hM hsmall' hfixed hpK] at h
    exact h
  have hmv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.m u)
        ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
          (2 * S.lam u v)) v := by
    intro u v hp
    have hpK := initial_development_subset_closed hp
    have h := vertical_hasDerivAt_initial_development hmC1 hp
    change HasDerivAt (fun t => x.1.toTriple.mass (u, t))
      ((fderivWithin ℝ x.1.toTriple.mass K (u, v)) (0, 1)) v at h
    have hj := x.outgoing_mass_equation hb hpK hp.2.1
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
  have hmu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.m w v)
        ((1 - 2 * S.m u v / S.r u v) * (S.zeta u v)^2 /
          (2 * S.nu u v)) u := by
    intro u v hu hp
    have hpK := initial_development_subset_closed hp
    have h := horizontal_hasDerivAt_initial_development hmC1 hu hp
    change HasDerivAt (fun t => x.1.toTriple.mass (t, v))
      ((fderivWithin ℝ x.1.toTriple.mass K (u, v)) (1, 0)) u at h
    have hj := x.incoming_mass_equation hb hM hsmall' hg hfixed hpK hp.2.1
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
  have hlamu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.lam w v)
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u := by
    intro u v hu hp
    have hpK := initial_development_subset_closed hp
    have h := horizontal_hasDerivAt_initial_development hlamC1 hu hp
    change HasDerivAt (fun t => x.1.toTriple.lam (t, v))
      ((fderivWithin ℝ x.1.toTriple.lam K (u, v)) (1, 0)) u at h
    rw [x.radius_uv_equation hb hM hsmall' hfixed hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hnuv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.nu u)
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v := by
    intro u v hp
    have hpK := initial_development_subset_closed hp
    have h := vertical_hasDerivAt_initial_development hnuC1 hp
    change HasDerivAt (fun t => x.1.toTriple.nu (u, t))
      ((fderivWithin ℝ x.1.toTriple.nu K (u, v)) (0, 1)) v at h
    rw [x.nu_v_equation hb hM hsmall' hfixed hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hthetau : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.theta w v)
        (-(S.lam u v / S.r u v * S.zeta u v)) u := by
    intro u v hu hp
    have hpK := initial_development_subset_closed hp
    have hthetaC1 : ContDiffOn ℝ 1 x.1.toTriple.theta K :=
      halphaC1.sub (hlamC1.mul hphiC1)
    have h := horizontal_hasDerivAt_initial_development hthetaC1 hu hp
    change HasDerivAt (fun t => x.1.toTriple.theta (t, v))
      ((fderivWithin ℝ x.1.toTriple.theta K (u, v)) (1, 0)) u at h
    rw [x.theta_transport hb hM hsmall' hfixed hpK hp.2.1] at h
    change HasDerivAt (fun w => x.1.toTriple.theta (w, v))
      (-(x.1.toTriple.lam (u, v) / x.1.toTriple.radius (u, v) *
        x.1.toTriple.zeta (u, v))) u
    simpa only [neg_mul] using h
  have hzetav : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.zeta u)
        (-(S.nu u v / S.r u v * S.theta u v)) v := by
    intro u v hp
    have hpK := initial_development_subset_closed hp
    have hzetaC1 : ContDiffOn ℝ 1 x.1.toTriple.zeta K :=
      hbetaC1.sub (hnuC1.mul hphiC1)
    have h := vertical_hasDerivAt_initial_development hzetaC1 hp
    change HasDerivAt (fun t => x.1.toTriple.zeta (u, t))
      ((fderivWithin ℝ x.1.toTriple.zeta K (u, v)) (0, 1)) v at h
    rw [x.zeta_transport hb hM hsmall' hfixed hpK hp.2.1] at h
    change HasDerivAt (fun w => x.1.toTriple.zeta (u, w))
      (-(x.1.toTriple.nu (u, v) / x.1.toTriple.radius (u, v) *
        x.1.toTriple.theta (u, v))) v
    simpa only [neg_mul] using h
  have halphau : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.alpha w v)
        (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) u := by
    intro u v hu hp
    have hpK := initial_development_subset_closed hp
    have h := horizontal_hasDerivAt_initial_development halphaC1 hu hp
    change HasDerivAt (fun t => x.1.toTriple.alpha (t, v))
      ((fderivWithin ℝ x.1.toTriple.alpha K (u, v)) (1, 0)) u at h
    rw [x.alpha_u hb hM hsmall' hfixed hpK,
      x.gravitational_off_axis hb hM hsmall' hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hbetav : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.beta u)
        (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) v := by
    intro u v hp
    have hpK := initial_development_subset_closed hp
    have h := vertical_hasDerivAt_initial_development hbetaC1 hp
    change HasDerivAt (fun t => x.1.toTriple.beta (u, t))
      ((fderivWithin ℝ x.1.toTriple.beta K (u, v)) (0, 1)) v at h
    rw [x.beta_v hb hM hsmall' hpK,
      x.gravitational_off_axis hb hM hsmall' hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have haxisr : ∀ a, 0 ≤ a → a ≤ b → S.r a a = 0 := by
    intro a ha hb'
    exact (haxis a ⟨ha, hb'⟩).1
  have haxism : ∀ a, 0 ≤ a → a ≤ b → S.m a a = 0 := by
    intro a ha hb'
    exact (haxis a ⟨ha, hb'⟩).2
  have hrpos : ∀ p ∈ developmentWithInitialEdge b, 0 < S.r p.1 p.2 := by
    intro p hp
    exact x.radius_pos (initial_development_subset_closed hp) hp.2.1
  have hlampos : ∀ p ∈ K, 0 < S.lam p.1 p.2 := by
    intro p hp
    linarith only [(hsign p hp).1]
  have hnuneg : ∀ p ∈ developmentWithInitialEdge b,
      S.nu p.1 p.2 < 0 := by
    intro p hp
    linarith only [(hsign p (initial_development_subset_closed hp)).2.2.1]
  have hApos : ∀ p ∈ developmentWithInitialEdge b,
      0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 := by
    intro p hp
    linarith only [(hsign p (initial_development_subset_closed hp)).2.2.2.2]
  exact ChristodoulouBV.C1Solution.isSolution_and_isC1Solution_of_classical hb S
    hrC1 hphiC1 hmC1 hlamC1 hnuC1 halphaC1 hbetaC1
    hrv hru hpsiv hpsiu hmv hmu hlamu hnuv hthetau hzetav halphau hbetav
    haxisr haxism hrpos hlampos hnuneg hApos

end ChristodoulouBV.AxisPicard

end
