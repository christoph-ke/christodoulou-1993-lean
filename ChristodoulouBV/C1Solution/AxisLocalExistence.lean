module

public import ChristodoulouBV.Frozen.Fields
public import ChristodoulouBV.C1Solution.AxisPicardFixedPointBanach
public import ChristodoulouBV.C1Solution.AxisReconstructionFixedPoint
public import ChristodoulouBV.C1Solution.AxisReconstructionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Local reconstruction on a closed axis triangle

The Picard fixed point gives a total seven-field representative. Its equations
are stated as relative first-jet identities on the closed triangle.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The seven physical fields reconstructed from a Picard triple. -/
@[expose] def Triple.toFields (x : Triple) : Fields where
  r u v := x.radius (u, v)
  phi u v := x.phi (u, v)
  m u v := x.mass (u, v)
  lam u v := x.lam (u, v)
  nu u v := x.nu (u, v)
  alpha u v := x.alpha (u, v)
  beta u v := x.beta (u, v)

/-- The fixed-point reconstruction has the seven relative `C¹` fields,
regular-axis traces, and uniform sign bounds on its closed triangle. -/
theorem Box.reconstructed_fields_basic {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v) :
    let T := x.1.toTriple.toFields
    let K := closedCoordTriangle a b
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.r p.1 p.2) K ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.phi p.1 p.2) K ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.m p.1 p.2) K ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.lam p.1 p.2) K ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.nu p.1 p.2) K ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.alpha p.1 p.2) K ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.beta p.1 p.2) K ∧
    (∀ p ∈ K, (1 / 4 : ℝ) ≤ T.lam p.1 p.2 ∧
      -(3 / 4 : ℝ) ≤ T.nu p.1 p.2 ∧ T.nu p.1 p.2 ≤ -(1 / 4 : ℝ) ∧
      0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
      2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ (1 / 4 : ℝ)) ∧
    (∀ u ∈ Icc a b, T.r u u = 0 ∧ T.m u u = 0) := by
  dsimp only
  refine ⟨x.radius_c1 hab, x.phi_c1 hab, x.mass_c1 hab,
    x.lam_c1, x.nu_c1, x.alpha_c1, x.beta_c1 hab hM hsmall,
    ?_, ?_⟩
  · intro p hp
    have hmu := x.massRatio_bounds hab hM hsmall hp
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have hratio : 2 * x.1.toTriple.mass p / x.1.toTriple.radius p =
        x.1.toTriple.massRatio p := by
      by_cases hstrict : p.1 < p.2
      · exact (x.massRatio_off_axis hstrict).symm
      · have heq : p.1 = p.2 := le_antisymm hcoord.2.1 (le_of_not_gt hstrict)
        rcases p with ⟨u, v⟩
        dsimp only at heq
        subst v
        simp [Triple.outgoing_primitives_diag, Triple.mass_diag]
    change (1 / 4 : ℝ) ≤ x.1.toTriple.lam p ∧
      -(3 / 4 : ℝ) ≤ x.1.toTriple.nu p ∧
      x.1.toTriple.nu p ≤ -(1 / 4 : ℝ) ∧
      0 ≤ 2 * x.1.toTriple.mass p / x.1.toTriple.radius p ∧
      2 * x.1.toTriple.mass p / x.1.toTriple.radius p ≤ (1 / 4 : ℝ)
    rw [hratio]
    exact ⟨x.lam_ge_quarter hp, (x.nu_signs hab hM hsmall hg hp).1,
      (x.nu_signs hab hM hsmall hg hp).2, hmu.1, hmu.2⟩
  · intro u _
    exact ⟨(x.1.toTriple.outgoing_primitives_diag u).1,
      (x.1.toTriple.mass_diag u).1⟩

/-- The prescribed expansion and normalized scalar datum determine the
outgoing physical edge trace. -/
theorem Box.reconstructed_edge_trace {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {v : ℝ} (hv : v ∈ Icc a b) :
    let T := x.1.toTriple.toFields
    T.r a v = ∫ s in a..v, g s ∧
    T.lam a v = g v ∧ T.alpha a v = g v * hEdge v := by
  have hlam : x.1.toTriple.lam (a, v) = g v := x.lam_edge ⟨v, hv⟩
  have hh : x.1.toTriple.h (a, v) = hEdge v := by
    have hbox := x.2.1
    change IsInBox a b M g hEdge x.1 at hbox
    have h := hbox.2.2.1 ⟨v, hv⟩
    change x.1.2.2.extendValue (a, v) = hEdge v
    calc
      _ = x.1.2.2.extendValue (edgePoint ⟨v, hv⟩).1 := rfl
      _ = x.1.2.2.1.1 (edgePoint ⟨v, hv⟩) :=
        x.1.2.2.extendValue_eq (edgePoint ⟨v, hv⟩).2
      _ = hEdge v := h
  have hr : x.1.toTriple.radius (a, v) = ∫ s in a..v, g s := by
    change (∫ s in a..v, x.1.toTriple.lam (a, s)) = _
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc a v := by simpa only [uIcc_of_le hv.1] using hs
    exact x.lam_edge ⟨s, ⟨hs'.1, hs'.2.trans hv.2⟩⟩
  refine ⟨hr, hlam, ?_⟩
  simpa only [Triple.toFields, Triple.alpha] using congrArg₂ (· * ·) hlam hh

/-- Picard existence yields a reconstructed seven-field representative on
every triangle within the numerical lifetime. -/
theorem exists_reconstructed_fields {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ∃ x : Box a b M g hEdge,
      x.IsTriangleFixedPoint ∧
      let T := x.1.toTriple.toFields
      let K := closedCoordTriangle a b
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.r p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.phi p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.m p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.lam p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.nu p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.alpha p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.beta p.1 p.2) K ∧
      (∀ p ∈ K, (1 / 4 : ℝ) ≤ T.lam p.1 p.2 ∧
        -(3 / 4 : ℝ) ≤ T.nu p.1 p.2 ∧ T.nu p.1 p.2 ≤ -(1 / 4 : ℝ) ∧
        0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ (1 / 4 : ℝ)) ∧
      (∀ u ∈ Icc a b, T.r u u = 0 ∧ T.m u u = 0) := by
  let x := Box.picardFixedPoint D hab hM hsmall
  refine ⟨x, ?_, ?_⟩
  · have hcomp : ∀ p ∈ closedCoordTriangle a b,
        (x.1.toTriple.picard a g hEdge).lam p = x.1.toTriple.lam p ∧
        (x.1.toTriple.picard a g hEdge).nu p = x.1.toTriple.nu p ∧
        (x.1.toTriple.picard a g hEdge).h p = x.1.toTriple.h p := by
      intro p hp
      let q : closedCoordTriangle a b := ⟨p, hp⟩
      have h := x.picardMap_values D hab hM hsmall q
      have hfix : Box.picardMap D hab hM hsmall x = x :=
        Box.picardFixedPoint_eq D hab hM hsmall
      rw [hfix] at h
      constructor
      · change (x.1.toTriple.picard a g hEdge).lam p = x.1.1.extendValue p
        rw [x.1.1.extendValue_eq hp]
        exact h.1.symm
      constructor
      · change (x.1.toTriple.picard a g hEdge).nu p = x.1.2.1.extendValue p
        rw [x.1.2.1.extendValue_eq hp]
        exact h.2.1.symm
      · change (x.1.toTriple.picard a g hEdge).h p = x.1.2.2.extendValue p
        rw [x.1.2.2.extendValue_eq hp]
        exact h.2.2.symm
    exact ⟨fun p hp => (hcomp p hp).1,
      fun p hp => (hcomp p hp).2.1,
      fun p hp => (hcomp p hp).2.2⟩
  · exact x.reconstructed_fields_basic hab hM hsmall D.g_lower

/-- Bounded incoming edge data give a triangle-local Picard reconstruction
on a positive subinterval of the prescribed edge. -/
theorem exists_reconstructed_edge_of_bounded_data {a L M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a (a + L) M g hEdge)
    (hL : 0 < L) (hM : 1 ≤ M) :
    ∃ b : ℝ, a < b ∧ b ≤ a + L ∧
      ∃ x : Box a b M g hEdge, x.IsTriangleFixedPoint ∧
        ∀ v ∈ Icc a b,
          let T := x.1.toTriple.toFields
          T.r a v = ∫ s in a..v, g s ∧
          T.lam a v = g v ∧ T.alpha a v = g v * hEdge v := by
  let w := min L ((numericalLedger M).lifetime M)
  let b := a + w
  have hw : 0 < w := lt_min hL (numerical_lifetime_pos hM)
  have hab : a < b := by dsimp [b]; linarith only [hw]
  have hbL : b ≤ a + L := by
    dsimp [b, w]
    linarith only [min_le_left L ((numericalLedger M).lifetime M)]
  have hsmall : b - a ≤ (numericalLedger M).lifetime M := by
    dsimp [b, w]
    linarith only [min_le_right L ((numericalLedger M).lifetime M)]
  have D' : EdgeData a b M g hEdge := {
    g_c1 := D.g_c1
    h_c1 := D.h_c1
    g_lower := fun v hv => D.g_lower v ⟨hv.1, hv.2.trans hbL⟩
    g_upper := fun v hv => D.g_upper v ⟨hv.1, hv.2.trans hbL⟩
    g_deriv_bound := fun v hv => D.g_deriv_bound v ⟨hv.1, hv.2.trans hbL⟩
    h_bound := fun v hv => D.h_bound v ⟨hv.1, hv.2.trans hbL⟩
    h_deriv_bound := fun v hv => D.h_deriv_bound v ⟨hv.1, hv.2.trans hbL⟩ }
  obtain ⟨x, hx, _⟩ := exists_reconstructed_fields D' hab hM hsmall
  refine ⟨b, hab, hbL, x, hx, ?_⟩
  intro v hv
  exact x.reconstructed_edge_trace hv

/-- With the constant initial gauge, the zero-extended jet representative
cannot satisfy the Picard equation as an equality of total functions. -/
theorem Box.not_global_picard_fixed_initial {b M : ℝ} {hEdge : ℝ → ℝ}
    (x : Box 0 b M (fun _ => 1 / 2) hEdge) :
    x.1.toTriple.picard 0 (fun _ => 1 / 2) hEdge ≠ x.1.toTriple := by
  intro hfixed
  have hout : ((0 : ℝ), b + 1) ∉ closedCoordTriangle 0 b := by
    change ¬((0 : ℝ) ≤ 0 ∧ 0 ≤ b + 1 ∧ b + 1 ≤ b)
    intro h
    linarith only [h.2.2]
  have hzero : x.1.toTriple.lam (0, b + 1) = 0 := by
    change x.1.1.extendValue (0, b + 1) = 0
    simp [ScalarJet.extendValue, hout]
  have hhalf : (x.1.toTriple.picard 0 (fun _ => 1 / 2) hEdge).lam
      (0, b + 1) = 1 / 2 := by
    exact x.1.toTriple.picard_lam_edge 0 (b + 1) (fun _ => 1 / 2) hEdge
  have heq := congrArg (fun y : Triple => y.lam (0, b + 1)) hfixed
  rw [hhalf, hzero] at heq
  norm_num at heq

end ChristodoulouBV.AxisPicard

end
