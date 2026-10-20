module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseODE

/-!
# Closed coefficients for the incoming jet transport

The outgoing `βᵤ` equation is inhomogeneous once the continuous trace of
`νᵤ` is fixed. Its source uses only closed-rectangle lower-order traces.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

variable {a vBar vStar : ℝ} {S : ℝ → Fields}

/-- The closed source in `Bᵥ = (A P + Aᵤν)φ + Aνζ/r`, where `P=νᵤ`.
The coefficient of `B` itself is zero. -/
@[expose] noncomputable def OffAxisTerminalTraces.betaTransportSource
    (T : OffAxisTerminalTraces a vBar vStar S)
    (P : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (T.nuTransportCoefficient p * P p + T.nuTransportSource p) * T.phi p +
    T.nuTransportCoefficient p * T.nu p * T.zeta p / T.r p

/-- A jointly continuous incoming `ν` jet gives a jointly continuous
inhomogeneous source for the outgoing `β` jet. -/
theorem OffAxisTerminalTraces.beta_transport_source_continuousOn
    (T : OffAxisTerminalTraces a vBar vStar S)
    {P : ℝ × ℝ → ℝ}
    (hP : ContinuousOn P (Icc 0 a ×ˢ Icc vBar vStar)) :
    ContinuousOn (T.betaTransportSource P)
      (Icc 0 a ×ˢ Icc vBar vStar) := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  have hA := T.nu_transport_coefficients_continuousOn.1
  have hF := T.nu_transport_coefficients_continuousOn.2
  have hr : ∀ p ∈ K, T.r p ≠ 0 := by
    intro p hp
    exact ne_of_gt (T.radius_pos.trans_le
      (T.floors p.1 hp.1 p.2 hp.2).1)
  change ContinuousOn (fun p =>
    (T.nuTransportCoefficient p * P p + T.nuTransportSource p) * T.phi p +
      T.nuTransportCoefficient p * T.nu p * T.zeta p / T.r p) K
  exact (((hA.mul hP).add hF).mul T.phi_cont).add
    (((hA.mul T.nu_cont).mul T.zeta_cont).div T.r_cont hr)

end ChristodoulouBV.Uniqueness

end
