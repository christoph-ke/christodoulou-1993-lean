module

public import ChristodoulouBV.C1Solution.AxisTranslationClassical
public import ChristodoulouBV.C1Solution.FrozenBridge
public import ChristodoulouBV.C1Solution.Rescaling
import Mathlib.Tactic

/-!
# Frozen C¹ solutions in translated axis charts

Classical axis triangles and restrictions of old initial-edge developments
become frozen C¹ solutions after the unit-scale affine chart.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.Uniqueness

/-- A classical solution on a translated axis triangle becomes a frozen C¹
solution after shifting both null coordinates by the incoming-edge parameter. -/
theorem AxisClassicalSolution.shift_isC1Solution {a b : ℝ} {S : Fields}
    (H : AxisClassicalSolution a b S) (hab : a < b) :
    IsC1Solution (developmentWithInitialEdge (b - a))
      (rescaledFields S a 1) := by
  let R := rescaledFields S a 1
  have HR : AxisClassicalSolution 0 (b - a) R := H.shift
  have hb : 0 < b - a := sub_pos.mpr hab
  exact (isSolution_and_isC1Solution_of_classical hb R
    HR.r_c1 HR.phi_c1 HR.m_c1 HR.lam_c1 HR.nu_c1
    HR.alpha_c1 HR.beta_c1 HR.r_v HR.r_u HR.psi_v HR.psi_u
    HR.m_v HR.m_u HR.lam_u HR.nu_v HR.theta_u HR.zeta_v
    HR.alpha_u HR.beta_v
    (fun u hu hub => HR.r_axis u ⟨hu, hub⟩)
    (fun u hu hub => HR.m_axis u ⟨hu, hub⟩)
    HR.r_pos HR.lam_pos HR.nu_neg HR.gap_pos).2

/-- The unit-scale chart of an initial-edge development cut at `c` is the
initial-edge development of width `c - a`. -/
theorem rescaledDomain_initialEdge_shift {a c : ℝ} (ha : 0 ≤ a) :
    rescaledDomain (developmentWithInitialEdge c) a 1 =
      developmentWithInitialEdge (c - a) := by
  ext p
  rcases p with ⟨u, v⟩
  change (0 ≤ u ∧ 0 ≤ a + 1 * u ∧ a + 1 * u < a + 1 * v ∧
      a + 1 * v < c) ↔ (0 ≤ u ∧ u < v ∧ v < c - a)
  constructor
  · rintro ⟨hu, _, huv, hvc⟩
    exact ⟨hu, by linarith, by linarith⟩
  · rintro ⟨hu, huv, hvc⟩
    exact ⟨hu, by linarith, by linarith, by linarith⟩

/-- Restrict a frozen C¹ solution to a shorter initial-edge development. -/
theorem isC1Solution_restrict_initialEdge {b c : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcb : c ≤ b) :
    IsC1Solution (developmentWithInitialEdge c) S := by
  let U := developmentWithInitialEdge c
  let V := developmentWithInitialEdge b
  have hsub : U ⊆ V := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le hcb⟩
  have haxis : adjacentAxis U ⊆ adjacentAxis V := by
    intro u hu
    exact closure_mono hsub hu
  have hsol : IsSolution U S := {
    development := developmentWithInitialEdge_isDomainOfDevelopment c
    radius_out := fun u x y hxy hseg => H.solution.radius_out u x y hxy (hseg.trans hsub)
    radius_in := fun v x y hxy hseg => H.solution.radius_in v x y hxy (hseg.trans hsub)
    scalar_radius_out := fun u x y hxy hseg =>
      H.solution.scalar_radius_out u x y hxy (hseg.trans hsub)
    scalar_radius_in := fun v x y hxy hseg =>
      H.solution.scalar_radius_in v x y hxy (hseg.trans hsub)
    mass_out := fun u x y hxy hseg => H.solution.mass_out u x y hxy (hseg.trans hsub)
    mass_in := fun v x y hxy hseg => H.solution.mass_in v x y hxy (hseg.trans hsub)
    lam_in := fun v x y hxy hseg => H.solution.lam_in v x y hxy (hseg.trans hsub)
    nu_out := fun u x y hxy hseg => H.solution.nu_out u x y hxy (hseg.trans hsub)
    alpha_in := fun v x y hxy hseg => H.solution.alpha_in v x y hxy (hseg.trans hsub)
    beta_out := fun u x y hxy hseg => H.solution.beta_out u x y hxy (hseg.trans hsub)
    radius_axis := by
      intro u hu
      apply (H.solution.radius_axis u (haxis hu)).mono_left
      apply inf_le_inf le_rfl
      apply Filter.principal_mono.mpr
      intro v hv
      exact hsub hv
    mass_axis := by
      intro u hu
      apply (H.solution.mass_axis u (haxis hu)).mono_left
      apply inf_le_inf le_rfl
      apply Filter.principal_mono.mpr
      intro v hv
      exact hsub hv
    radius_pos := fun p hp => H.solution.radius_pos p (hsub hp)
    lam_pos := fun p hp => H.solution.lam_pos p (hsub hp)
    conformal := fun p hp => H.solution.conformal p (hsub hp) }
  refine {
    solution := hsol
    nu_bounded_below := by
      obtain ⟨N, hN⟩ := H.nu_bounded_below
      exact ⟨N, fun p hp => hN p (hsub hp)⟩
    lam_bounded_below := by
      obtain ⟨d, hd, hD⟩ := H.lam_bounded_below
      exact ⟨d, hd, fun p hp => hD p (hsub hp)⟩
    lam_c1 := H.lam_c1.mono (closure_mono hsub)
    nu_c1 := H.nu_c1.mono (closure_mono hsub)
    phi_c1 := H.phi_c1.mono (closure_mono hsub)
    theta_c1 := H.theta_c1.mono (closure_mono hsub)
    zeta_c1 := H.zeta_c1.mono (closure_mono hsub) }

/-- A frozen solution on the original initial-edge development remains a
frozen C¹ solution after cutting at `c` and shifting its incoming edge to zero. -/
theorem isC1Solution_restrict_and_shift {a b c : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (ha : 0 ≤ a) (hcb : c ≤ b) :
    IsC1Solution (developmentWithInitialEdge (c - a))
      (rescaledFields S a 1) := by
  have Hc := isC1Solution_restrict_initialEdge H hcb
  rw [← rescaledDomain_initialEdge_shift ha]
  exact rescaled_isC1Solution Hc ha (by norm_num)

end ChristodoulouBV.C1Solution

end
