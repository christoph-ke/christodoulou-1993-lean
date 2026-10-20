module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseIncomingOutgoing

/-!
# Closed outgoing slices of the terminal incoming fields

The finite-development mixed equations and continuity of the canonical
terminal values close the outgoing derivatives at `vStar`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The canonical incoming expansion and scalar amplitude have their
outgoing derivatives at both endpoints of every closed terminal slice. -/
theorem OffAxisTerminalC1Packet.nu_beta_hasDerivWithinAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    HasDerivWithinAt (fun w => P.state.nu (u, w))
      (P.state.lam (u, v) * P.state.lambdaVCoefficient (u, v))
      (Icc vBar vStar) v ∧
    HasDerivWithinAt (fun w => P.state.zeta (u, w) +
        P.state.nu (u, w) * P.state.phi (u, w))
      (P.state.lam (u, v) * P.state.lambdaVCoefficient (u, v) *
        P.state.phi (u, v)) (Icc vBar vStar) v := by
  have hn : ContinuousOn (fun w => P.state.nu (u, w)) (Icc vBar vStar) :=
    P.state.nu_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hb : ContinuousOn (fun w => P.state.zeta (u, w) +
      P.state.nu (u, w) * P.state.phi (u, w)) (Icc vBar vStar) :=
    (P.state.zeta_cont.add (P.state.nu_cont.mul P.state.phi_cont)).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hK : ContinuousOn (fun w => P.state.lam (u, w) *
      P.state.lambdaVCoefficient (u, w)) (Icc vBar vStar) :=
    (P.state.lam_cont.mul P.state.coefficients_continuousOn.2.2.1).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hφ : ContinuousOn (fun w => P.state.phi (u, w))
      (Icc vBar vStar) :=
    P.state.phi_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  exact ⟨hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hn hK
      (fun w hw => (P.nu_beta_hasDerivAt_v ha haBar hfamily hu hw).1) hv,
    hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hb (hK.mul hφ)
      (fun w hw => (P.nu_beta_hasDerivAt_v ha haBar hfamily hu hw).2) hv⟩

/-- Each outgoing slice of the canonical incoming state is relatively
`C¹` through the terminal edge. -/
theorem OffAxisTerminalC1Packet.nu_beta_contDiffOn_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    ContDiffOn ℝ 1 (fun v => P.state.nu (u, v)) (Icc vBar vStar) ∧
    ContDiffOn ℝ 1 (fun v => P.state.zeta (u, v) +
      P.state.nu (u, v) * P.state.phi (u, v)) (Icc vBar vStar) := by
  have hn : ContinuousOn (fun w => P.state.nu (u, w)) (Icc vBar vStar) :=
    P.state.nu_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hb : ContinuousOn (fun w => P.state.zeta (u, w) +
      P.state.nu (u, w) * P.state.phi (u, w)) (Icc vBar vStar) :=
    (P.state.zeta_cont.add (P.state.nu_cont.mul P.state.phi_cont)).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hK : ContinuousOn (fun w => P.state.lam (u, w) *
      P.state.lambdaVCoefficient (u, w)) (Icc vBar vStar) :=
    (P.state.lam_cont.mul P.state.coefficients_continuousOn.2.2.1).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hφ : ContinuousOn (fun w => P.state.phi (u, w))
      (Icc vBar vStar) :=
    P.state.phi_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  exact ⟨contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hn hK
      (fun w hw => (P.nu_beta_hasDerivAt_v ha haBar hfamily hu hw).1),
    contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hb (hK.mul hφ)
      (fun w hw => (P.nu_beta_hasDerivAt_v ha haBar hfamily hu hw).2)⟩

end ChristodoulouBV.Uniqueness

end
