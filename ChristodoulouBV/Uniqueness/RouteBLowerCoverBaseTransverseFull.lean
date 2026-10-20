module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseTrace
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverJetClosure
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseIncomingOutgoingC1
import Mathlib.Tactic.Linarith

/-!
# Full first jets of the incoming fields on the terminal rectangle

The continuous transverse traces and the already known outgoing equations
close the full relative first jets of `ν` and `β`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A field which is C¹ on every compact lower rectangle has a full first
jet on the terminal rectangle when its proposed incoming jet is the old
relative slice derivative and its outgoing derivative is prescribed. -/
theorem rectangle_full_jet_of_lower_c1_and_coordinate_traces
    {a vBar vStar : ℝ} (ha : 0 < a) (hBarStar : vBar < vStar)
    {f du dv : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 a ×ˢ Icc vBar vStar))
    (hdu : ContinuousOn du (Icc 0 a ×ˢ Icc vBar vStar))
    (hdv : ContinuousOn dv (Icc 0 a ×ˢ Icc vBar vStar))
    (hlower : ∀ t ∈ Ioo vBar vStar,
      ContDiffOn ℝ 1 f (Icc 0 a ×ˢ Icc vBar t))
    (hduMatch : ∀ u ∈ Ioo 0 a, ∀ v ∈ Ioo vBar vStar,
      du (u, v) = derivWithin (fun s => f (s, v)) (Icc 0 a) u)
    (hdvDeriv : ∀ u ∈ Ioo 0 a, ∀ v ∈ Ioo vBar vStar,
      HasDerivAt (fun s => f (u, s)) (dv (u, v)) v) :
    ContDiffOn ℝ 1 f (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt f (rectangleScalarJet (du p) (dv p))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  apply rectangle_scalar_full_jet_of_interior ha hBarStar hf hdu hdv
  · intro p hp
    let t : ℝ := (p.2 + vStar) / 2
    have hvt : p.2 < t := by dsimp [t]; linarith only [hp.2.2]
    have ht : t ∈ Ioo vBar vStar := by
      dsimp [t]
      constructor <;> linarith only [hp.2.1, hp.2.2]
    have hi : p ∈ interior (Icc 0 a ×ˢ Icc vBar t) := by
      rw [interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨hp.1, ⟨hp.2.1, hvt⟩⟩
    exact (((hlower t ht).differentiableOn (by norm_num)).mono
      interior_subset p hi).differentiableAt (isOpen_interior.mem_nhds hi)
  · intro p hp
    have hdiff : DifferentiableAt ℝ f p := by
      let t : ℝ := (p.2 + vStar) / 2
      have hvt : p.2 < t := by dsimp [t]; linarith only [hp.2.2]
      have ht : t ∈ Ioo vBar vStar := by
        dsimp [t]
        constructor <;> linarith only [hp.2.1, hp.2.2]
      have hi : p ∈ interior (Icc 0 a ×ˢ Icc vBar t) := by
        rw [interior_prod_eq, interior_Icc, interior_Icc]
        exact ⟨hp.1, ⟨hp.2.1, hvt⟩⟩
      exact (((hlower t ht).differentiableOn (by norm_num)).mono
        interior_subset p hi).differentiableAt (isOpen_interior.mem_nhds hi)
    have hpair : HasDerivAt (fun s : ℝ => (s, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2)
    have hslice : HasDerivAt (fun s => f (s, p.2))
        ((fderiv ℝ f p) (1, 0)) p.1 := by
      simpa only [Function.comp_def] using
        hdiff.hasFDerivAt.comp_hasDerivAt p.1 hpair
    calc
      (fderiv ℝ f p) (1, 0) = deriv (fun s => f (s, p.2)) p.1 :=
        hslice.deriv.symm
      _ = derivWithin (fun s => f (s, p.2)) (Icc 0 a) p.1 :=
        (derivWithin_of_mem_nhds (Icc_mem_nhds hp.1.1 hp.1.2)).symm
      _ = du p := (hduMatch p.1 hp.1 p.2 hp.2).symm
  · intro p hp
    have hdiff : DifferentiableAt ℝ f p := by
      let t : ℝ := (p.2 + vStar) / 2
      have hvt : p.2 < t := by dsimp [t]; linarith only [hp.2.2]
      have ht : t ∈ Ioo vBar vStar := by
        dsimp [t]
        constructor <;> linarith only [hp.2.1, hp.2.2]
      have hi : p ∈ interior (Icc 0 a ×ˢ Icc vBar t) := by
        rw [interior_prod_eq, interior_Icc, interior_Icc]
        exact ⟨hp.1, ⟨hp.2.1, hvt⟩⟩
      exact (((hlower t ht).differentiableOn (by norm_num)).mono
        interior_subset p hi).differentiableAt (isOpen_interior.mem_nhds hi)
    exact fderiv_apply_second_of_hasDerivAt hdiff
      (hdvDeriv p.1 hp.1 p.2 hp.2)

/-- The canonical incoming expansion and scalar-radius incoming amplitude
have full relative first jets on the closed terminal rectangle. Their
incoming coordinates are the jointly continuous transported traces. -/
theorem OffAxisTerminalC1Packet.exists_nu_beta_full_jets
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ N B : ℝ × ℝ → ℝ,
      ContinuousOn N (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn B (Icc 0 a ×ˢ Icc vBar vStar) ∧
      (ContDiffOn ℝ 1 P.state.nu (Icc 0 a ×ˢ Icc vBar vStar) ∧
        ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
          HasFDerivWithinAt P.state.nu
            (rectangleScalarJet (N p) (P.state.lam p *
              P.state.lambdaVCoefficient p))
            (Icc 0 a ×ˢ Icc vBar vStar) p) ∧
      (ContDiffOn ℝ 1 (fun p => P.state.zeta p +
          P.state.nu p * P.state.phi p)
          (Icc 0 a ×ˢ Icc vBar vStar) ∧
        ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
          HasFDerivWithinAt (fun q => P.state.zeta q +
            P.state.nu q * P.state.phi q)
            (rectangleScalarJet (B p)
              (P.state.lam p * P.state.lambdaVCoefficient p *
                P.state.phi p))
            (Icc 0 a ×ˢ Icc vBar vStar) p) := by
  obtain ⟨N, B, hNcont, hBcont, hNmatch, hBmatch⟩ :=
    P.exists_nu_beta_incoming_jet_terminal_traces
      ha haBar hBarStar hfamily
  have hK : ContinuousOn
      (fun p => P.state.lam p * P.state.lambdaVCoefficient p)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    P.state.lam_cont.mul P.state.coefficients_continuousOn.2.2.1
  have hbeta : ContinuousOn
      (fun p => P.state.zeta p + P.state.nu p * P.state.phi p)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    P.state.zeta_cont.add (P.state.nu_cont.mul P.state.phi_cont)
  have hnuFull := rectangle_full_jet_of_lower_c1_and_coordinate_traces
    ha hBarStar P.state.nu_cont hNcont hK
    (fun t ht => (P.nu_beta_contDiffOn_lower_rectangle ha haBar
      hfamily ⟨ht.1.le, ht.2⟩).1)
    (by
      intro u hu v hv
      exact hNmatch u ⟨hu.1.le, hu.2.le⟩ v ⟨hv.1.le, hv.2⟩)
    (by
      intro u hu v hv
      exact (P.nu_beta_hasDerivAt_v ha haBar hfamily
        ⟨hu.1.le, hu.2.le⟩ hv).1)
  have hbetaFull := rectangle_full_jet_of_lower_c1_and_coordinate_traces
    ha hBarStar hbeta hBcont (hK.mul P.state.phi_cont)
    (fun t ht => (P.nu_beta_contDiffOn_lower_rectangle ha haBar
      hfamily ⟨ht.1.le, ht.2⟩).2)
    (by
      intro u hu v hv
      exact hBmatch u ⟨hu.1.le, hu.2.le⟩ v ⟨hv.1.le, hv.2⟩)
    (by
      intro u hu v hv
      exact (P.nu_beta_hasDerivAt_v ha haBar hfamily
        ⟨hu.1.le, hu.2.le⟩ hv).2)
  exact ⟨N, B, hNcont, hBcont, hnuFull, hbetaFull⟩

end ChristodoulouBV.Uniqueness

end
