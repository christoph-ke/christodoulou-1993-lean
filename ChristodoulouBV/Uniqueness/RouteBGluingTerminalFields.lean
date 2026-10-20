module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisPacket
public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFields

/-!
# The seven terminal values on the old upper rectangle

The off-axis terminal trace data give jointly continuous values of the physical
fields. The incoming scalar derivative is reconstructed from `ζ = β - νφ`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The seven physical fields represented by the terminal trace data on
`[0,a] × [vBar,vStar]`. -/
@[expose] def OffAxisTerminalC1Packet.terminalFields
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S) : Fields where
  r u v := P.state.r (u, v)
  phi u v := P.state.phi (u, v)
  m u v := P.state.m (u, v)
  lam u v := P.state.lam (u, v)
  nu u v := P.state.nu (u, v)
  alpha u v := P.state.alpha (u, v)
  beta u v := P.state.zeta (u, v) +
    P.state.nu (u, v) * P.state.phi (u, v)

/-- All seven terminal values are jointly continuous on the closed upper
rectangle. -/
theorem OffAxisTerminalC1Packet.terminalFields_continuousOn
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S) :
    ∀ c : RouteBField,
      ContinuousOn (routeBField P.terminalFields c)
        (Icc 0 a ×ˢ Icc vBar vStar) := by
  intro c
  cases c
  · exact P.state.r_cont
  · exact P.state.phi_cont
  · exact P.state.m_cont
  · exact P.state.lam_cont
  · exact P.state.nu_cont
  · exact P.state.alpha_cont
  · exact P.state.zeta_cont.add
      (P.state.nu_cont.mul P.state.phi_cont)

/-- Below `vStar`, the terminal values equal every old family member that
is defined at the point, including the reconstructed incoming field. -/
theorem OffAxisTerminalC1Packet.terminalFields_eq_old
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    {d u v : ℝ} (hd : d ∈ Ioo (0 : ℝ) vStar)
    (hu : u ∈ Icc 0 a) (hv : v ∈ Ico vBar d) :
    ∀ c : RouteBField,
      routeBField P.terminalFields c (u, v) =
        routeBField (S d) c (u, v) := by
  obtain ⟨hr, hm, hl, hn, hphi, hz, hα, _, _⟩ :=
    P.state.match_old d hd u hu v hv
  intro c
  cases c
  · exact hr
  · exact hphi
  · exact hm
  · exact hl
  · exact hn
  · exact hα
  · change P.state.zeta (u, v) +
        P.state.nu (u, v) * P.state.phi (u, v) = (S d).beta u v
    rw [hz, hn, hphi]
    simp only [Fields.zeta]
    ring

end ChristodoulouBV.Uniqueness

end
