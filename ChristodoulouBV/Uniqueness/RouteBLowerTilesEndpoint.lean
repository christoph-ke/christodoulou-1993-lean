module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTopPhysical

/-!
# Restricting the classical endpoint

The twelve classical equations are required only inside a development.
They remain valid when its upper endpoint is decreased.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- Classical relative jet equations persist under shortening the upper
development endpoint. -/
theorem RouteBClassicalJetOn.mono_endpoint
    {b b' : ℝ} {K : Set (ℝ × ℝ)} {S : Fields}
    (h : RouteBClassicalJetOn b K S) (hbb : b' ≤ b) :
    RouteBClassicalJetOn b' K S := by
  have hdev (p : ℝ × ℝ)
      (hp : p ∈ developmentWithInitialEdge b') :
      p ∈ developmentWithInitialEdge b :=
    ⟨hp.1, hp.2.1, hp.2.2.trans_le hbb⟩
  exact {
    radius_out := fun p hp hpb => h.radius_out p hp (hdev p hpb)
    radius_in := fun p hp hpb => h.radius_in p hp (hdev p hpb)
    scalar_radius_out := fun p hp hpb =>
      h.scalar_radius_out p hp (hdev p hpb)
    scalar_radius_in := fun p hp hpb =>
      h.scalar_radius_in p hp (hdev p hpb)
    mass_out := fun p hp hpb => h.mass_out p hp (hdev p hpb)
    mass_in := fun p hp hpb => h.mass_in p hp (hdev p hpb)
    expansion_in := fun p hp hpb => h.expansion_in p hp (hdev p hpb)
    contraction_out := fun p hp hpb =>
      h.contraction_out p hp (hdev p hpb)
    theta_in := fun p hp hpb => h.theta_in p hp (hdev p hpb)
    zeta_out := fun p hp hpb => h.zeta_out p hp (hdev p hpb)
    outgoing_in := fun p hp hpb => h.outgoing_in p hp (hdev p hpb)
    incoming_out := fun p hp hpb => h.incoming_out p hp (hdev p hpb)
  }

end ChristodoulouBV.Uniqueness

end
