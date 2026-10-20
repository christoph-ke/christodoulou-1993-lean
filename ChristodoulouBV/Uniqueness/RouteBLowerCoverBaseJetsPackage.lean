module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBasePhysicalJets
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseMass
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverSafety

/-!
# The complete canonical terminal base jets

The seven rectangle variables `(λ, α, ν, β, m, r, rφ)` and the physical
fields `φ, θ, ζ` have jointly continuous values and full relative first jets
on the closed off-axis base. The package also supplies the C¹ seven-state
field, ready for the separate finite-tile construction.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Full closed-base jets of the seven canonical rectangle variables and
the physical fields. The edge value field is the old family's canonical
terminal seven-state tuple. Every coordinate jet formula holds on the
whole rectangle, including the terminal edge. -/
structure RouteBTerminalBaseJets
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S) where
  nuU : ℝ × ℝ → ℝ
  betaU : ℝ × ℝ → ℝ
  nuU_cont : ContinuousOn nuU (Icc 0 a ×ˢ Icc vBar vStar)
  betaU_cont : ContinuousOn betaU (Icc 0 a ×ˢ Icc vBar vStar)
  lam_full :
    ContDiffOn ℝ 1 P.state.lam (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.lam
          (rectangleScalarJet
            (P.state.lam p * P.state.lambdaVCoefficient p)
            (P.lambdaVTrace p))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  alpha_full :
    ContDiffOn ℝ 1 P.state.alpha (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.alpha
          (rectangleScalarJet
            (P.state.lam p * P.state.lambdaVCoefficient p * P.state.phi p)
            (P.lambdaVTrace p * P.state.quotient p +
              P.state.lam p *
                (P.state.lam p * P.alphaPrimeTrace p)))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  nu_full :
    ContDiffOn ℝ 1 P.state.nu (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.nu
          (rectangleScalarJet (nuU p)
            (P.state.lam p * P.state.lambdaVCoefficient p))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  beta_full :
    ContDiffOn ℝ 1 (fun p => P.state.zeta p +
        P.state.nu p * P.state.phi p)
        (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt (fun q => P.state.zeta q +
          P.state.nu q * P.state.phi q)
          (rectangleScalarJet (betaU p)
            (P.state.lam p * P.state.lambdaVCoefficient p *
              P.state.phi p))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  mass_full :
    ContDiffOn ℝ 1 P.state.m (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.m
          (rectangleScalarJet
            (P.state.massGap p * P.state.zeta p ^ 2 /
              (2 * P.state.nu p))
            (P.state.massGap p * P.state.theta p ^ 2 /
              (2 * P.state.lam p)))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  radius_full :
    ContDiffOn ℝ 1 P.state.r (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.r
          (rectangleScalarJet (P.state.nu p) (P.state.lam p))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  scalarRadius_full :
    ContDiffOn ℝ 1 (fun p => P.state.r p * P.state.phi p)
      (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt (fun q => P.state.r q * P.state.phi q)
          (rectangleScalarJet
            (P.state.zeta p + P.state.nu p * P.state.phi p)
            (P.state.alpha p))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  phi_full :
    ContDiffOn ℝ 1 P.state.phi (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.phi
          (rectangleScalarJet
            (P.state.zeta p / P.state.r p)
            (P.state.theta p / P.state.r p))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  theta_full :
    ContDiffOn ℝ 1 P.state.theta (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.theta
          (rectangleScalarJet
            (P.state.lam p * P.state.lambdaVCoefficient p * P.state.phi p -
              (P.state.lam p * P.state.lambdaVCoefficient p * P.state.phi p +
                P.state.lam p * (P.state.zeta p / P.state.r p)))
            ((P.lambdaVTrace p * P.state.quotient p +
                P.state.lam p * (P.state.lam p * P.alphaPrimeTrace p)) -
              (P.lambdaVTrace p * P.state.phi p +
                P.state.lam p * (P.state.theta p / P.state.r p))))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  zeta_full :
    ContDiffOn ℝ 1 P.state.zeta (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.zeta
          (rectangleScalarJet
            (betaU p - (nuU p * P.state.phi p +
              P.state.nu p * (P.state.zeta p / P.state.r p)))
            (P.state.lam p * P.state.lambdaVCoefficient p *
                P.state.phi p -
              (P.state.lam p * P.state.lambdaVCoefficient p *
                  P.state.phi p +
                P.state.nu p * (P.state.theta p / P.state.r p))))
          (Icc 0 a ×ˢ Icc vBar vStar) p
  state_c1 :
    ContDiffOn ℝ 1 P.state.rectangleState
      (Icc 0 a ×ˢ Icc vBar vStar)

/-- The canonical old family supplies every rectangle-state and physical
base jet. The mass component uses the established expansion floor derived from
the frozen tail premise. -/
theorem OffAxisTerminalC1Packet.exists_routeBTerminalBaseJets
    {alpha₀ : ℝ → ℝ} {a vBar vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    Nonempty (RouteBTerminalBaseJets P) := by
  obtain ⟨N, B, hNcont, hBcont, hNu, hBeta⟩ :=
    P.exists_nu_beta_full_jets ha haBar hBarStar hfamily
  have hLam := P.lam_full_jet ha haBar hBarStar hfamily
  have hAlpha := P.alpha_full_jet ha haBar hBarStar hfamily
  have hMass := P.mass_full_jet ha haBar hBarStar hu₀ hα
    hfamily hε1 htail
  have hRadius := P.radius_full_jet ha haBar hBarStar hfamily
  have hScalarRadius := P.scalarRadius_full_jet ha haBar hBarStar hfamily
  have hPhi := P.phi_full_jet ha haBar hBarStar hfamily
  have hTheta := P.theta_full_jet ha haBar hBarStar hfamily
  have hZeta := P.zeta_full_jet hNu hBeta hPhi
  have hState : ContDiffOn ℝ 1 P.state.rectangleState
      (Icc 0 a ×ˢ Icc vBar vStar) := by
    change ContDiffOn ℝ 1 (fun p =>
      ((P.state.lam p, P.state.alpha p),
        (P.state.nu p,
          (P.state.zeta p + P.state.nu p * P.state.phi p,
            (P.state.m p,
              (P.state.r p, P.state.r p * P.state.phi p)))))) _
    exact (hLam.1.prodMk hAlpha.1).prodMk
      (hNu.1.prodMk (hBeta.1.prodMk
        (hMass.1.prodMk (hRadius.1.prodMk hScalarRadius.1))))
  exact ⟨{
    nuU := N, betaU := B,
    nuU_cont := hNcont, betaU_cont := hBcont,
    lam_full := hLam, alpha_full := hAlpha,
    nu_full := hNu, beta_full := hBeta,
    mass_full := hMass, radius_full := hRadius,
    scalarRadius_full := hScalarRadius,
    phi_full := hPhi, theta_full := hTheta, zeta_full := hZeta,
    state_c1 := hState
  }⟩

end ChristodoulouBV.Uniqueness

end
