module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseFull
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseAlpha
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseRadius
import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalarIncoming
import ChristodoulouBV.Uniqueness.ExtensionLocalRadius
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Physical scalar jets on the Route B terminal base

The canonical scalar has incoming jet `ζ/r` and outgoing jet `θ/r` on the
closed off-axis rectangle. The remaining derived amplitudes are algebraic
combinations of the seven-state variables.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Product rule in the coordinate-jet notation used on the terminal base. -/
theorem rectangleScalarJet_mul
    {f g : ℝ × ℝ → ℝ} {fu fv gu gv : ℝ}
    {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hf : HasFDerivWithinAt f (rectangleScalarJet fu fv) K p)
    (hg : HasFDerivWithinAt g (rectangleScalarJet gu gv) K p) :
    HasFDerivWithinAt (fun q => f q * g q)
      (rectangleScalarJet (fu * g p + f p * gu)
        (fv * g p + f p * gv)) K p := by
  convert hf.mul hg using 1
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨x, y⟩
  simp [rectangleScalarJet, smul_eq_mul]
  ring

/-- Subtraction rule in coordinate-jet notation. -/
theorem rectangleScalarJet_sub
    {f g : ℝ × ℝ → ℝ} {fu fv gu gv : ℝ}
    {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hf : HasFDerivWithinAt f (rectangleScalarJet fu fv) K p)
    (hg : HasFDerivWithinAt g (rectangleScalarJet gu gv) K p) :
    HasFDerivWithinAt (fun q => f q - g q)
      (rectangleScalarJet (fu - gu) (fv - gv)) K p := by
  convert hf.sub hg using 1
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨x, y⟩
  simp [rectangleScalarJet, smul_eq_mul]
  ring

/-- The physical scalar has its two regular coordinate jets throughout the
closed terminal rectangle. -/
theorem OffAxisTerminalC1Packet.phi_full_jet
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ContDiffOn ℝ 1 P.state.phi (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.phi
          (rectangleScalarJet
            (P.state.zeta p / P.state.r p)
            (P.state.theta p / P.state.r p))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  have hr : ∀ p ∈ K, P.state.r p ≠ 0 := by
    intro p hp
    exact ne_of_gt (P.state.radius_pos.trans_le
      (P.state.floors p.1 hp.1 p.2 hp.2).1)
  have hdu : ContinuousOn (fun p => P.state.zeta p / P.state.r p) K :=
    P.state.zeta_cont.div P.state.r_cont hr
  have hdv : ContinuousOn (fun p => P.state.theta p / P.state.r p) K :=
    P.state.theta_cont.div P.state.r_cont hr
  apply rectangle_scalar_full_jet_of_compatible_family
    (F := fun b p => (S b).phi p.1 p.2)
    (f := P.state.phi)
    (du := fun p => P.state.zeta p / P.state.r p)
    (dv := fun p => P.state.theta p / P.state.r p)
    ha haBar hBarStar P.state.phi_cont hdu hdv
  · intro b hb u hu v hv
    exact (P.state.match_old b hb u hu v hv).2.2.2.2.1
  · intro b hb u hu v hv
    let H := (hfamily b hb).1
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    have huv : u < v := hu.2.trans (haBar.trans hv.1)
    have hpK : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu.1, huv, hvB⟩
    have hdiff : DifferentiableAt ℝ
        (fun p : ℝ × ℝ => (S b).phi p.1 p.2) (u, v) :=
      (((C1Solution.five_fields_contDiffOn hB hBb H).2.2.1.differentiableOn
        (by norm_num)).mono interior_subset (u, v) hpK).differentiableAt
        (isOpen_interior.mem_nhds hpK)
    have hpDev : (u, v) ∈ interior (developmentWithInitialEdge b) := by
      have hopen : IsOpen (openCoordTriangle 0 b) := by
        rw [← interior_closedCoordTriangle]
        exact isOpen_interior
      have hsub : openCoordTriangle 0 b ⊆ developmentWithInitialEdge b := by
        intro q hq
        exact ⟨hq.1.le, hq.2.1, hq.2.2⟩
      exact (hopen.subset_interior_iff.mpr hsub) ⟨hu.1, huv, hv.2⟩
    obtain ⟨hrOld, _, _, _, _, hz, _, htheta, _⟩ :=
      P.state.match_old b hb u ⟨hu.1.le, hu.2.le⟩ v
        ⟨hv.1.le, hv.2⟩
    have hU := phi_hasDerivAt_u_of_c1 H
      (show (u, v) ∈ openDevelopment 0 b from
        ⟨⟨hu.1, huv.trans hv.2⟩, ⟨huv, hv.2⟩⟩)
    have hV := phi_hasDerivAt_v_of_c1_interior H hpDev
    refine ⟨hdiff, ?_, ?_⟩
    · rw [hz, hrOld]
      exact fderiv_apply_first_of_hasDerivAt hdiff hU
    · rw [htheta, hrOld]
      exact fderiv_apply_second_of_hasDerivAt hdiff hV

/-- The outgoing scalar amplitude agrees with its algebraic definition at
the terminal edge as well as below it. -/
theorem OffAxisTerminalC1Packet.theta_eq_alpha_sub_lam_phi
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    {p : ℝ × ℝ} (hp : p ∈ Icc 0 a ×ˢ Icc vBar vStar) :
    P.state.theta p = P.state.alpha p -
      P.state.lam p * P.state.phi p := by
  let f : ℝ → ℝ := fun w =>
    P.state.theta (p.1, w) -
      (P.state.alpha (p.1, w) -
        P.state.lam (p.1, w) * P.state.phi (p.1, w))
  have hpair : ContinuousOn (fun w : ℝ => (p.1, w)) (Icc vBar vStar) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmapK : MapsTo (fun w : ℝ => (p.1, w))
      (Icc vBar vStar) (Icc 0 a ×ˢ Icc vBar vStar) :=
    fun _ hw => ⟨hp.1, hw⟩
  have hf : ContinuousOn f (Icc vBar vStar) := by
    exact (P.state.theta_cont.comp hpair hmapK).sub
      ((P.state.alpha_cont.comp hpair hmapK).sub
        ((P.state.lam_cont.comp hpair hmapK).mul
          (P.state.phi_cont.comp hpair hmapK)))
  have hmap : MapsTo f (Ico vBar vStar) {0} := by
    intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    obtain ⟨_, _, hlam, _, hphi, _, halpha, htheta, _⟩ :=
      P.state.match_old b hb p.1 hp.1 w ⟨hw.1, hwb⟩
    change f w = 0
    dsimp [f]
    rw [htheta, halpha, hlam, hphi]
    simp only [Fields.theta, sub_self]
  have hclosed : closure (Ico vBar vStar) = Icc vBar vStar :=
    closure_Ico hBarStar.ne
  have hvcl : p.2 ∈ closure (Ico vBar vStar) := by
    rw [hclosed]
    exact hp.2
  rw [← hclosed] at hf
  have hzero := hmap.closure_of_continuousOn hf hvcl
  have hfzero : f p.2 = 0 := by
    simpa only [closure_singleton, mem_singleton_iff] using hzero
  exact sub_eq_zero.mp hfzero

/-- The outgoing amplitude has a full relative first jet on the closed
terminal rectangle, obtained from `θ = α - λφ`. -/
theorem OffAxisTerminalC1Packet.theta_full_jet
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
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
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  have hLam := P.lam_full_jet ha haBar hBarStar hfamily
  have hAlpha := P.alpha_full_jet ha haBar hBarStar hfamily
  have hPhi := P.phi_full_jet ha haBar hBarStar hfamily
  have hEq : EqOn P.state.theta
      (fun p => P.state.alpha p - P.state.lam p * P.state.phi p) K :=
    fun p hp => P.theta_eq_alpha_sub_lam_phi ha haBar hBarStar hp
  constructor
  · exact (hAlpha.1.sub (hLam.1.mul hPhi.1)).congr hEq
  · intro p hp
    have hProd := rectangleScalarJet_mul (hLam.2 p hp) (hPhi.2 p hp)
    have hSub := rectangleScalarJet_sub (hAlpha.2 p hp) hProd
    exact hSub.congr' hEq hp

/-- The incoming scalar amplitude has a full relative first jet on the
closed terminal rectangle, using `ζ = β - νφ`. -/
theorem OffAxisTerminalC1Packet.zeta_full_jet
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    {N B : ℝ × ℝ → ℝ}
    (hNu : ContDiffOn ℝ 1 P.state.nu (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.nu
          (rectangleScalarJet (N p)
            (P.state.lam p * P.state.lambdaVCoefficient p))
          (Icc 0 a ×ˢ Icc vBar vStar) p)
    (hBeta : ContDiffOn ℝ 1 (fun p => P.state.zeta p +
        P.state.nu p * P.state.phi p)
        (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt (fun q => P.state.zeta q +
          P.state.nu q * P.state.phi q)
          (rectangleScalarJet (B p)
            (P.state.lam p * P.state.lambdaVCoefficient p *
              P.state.phi p))
          (Icc 0 a ×ˢ Icc vBar vStar) p)
    (hPhi : ContDiffOn ℝ 1 P.state.phi (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.phi
          (rectangleScalarJet
            (P.state.zeta p / P.state.r p)
            (P.state.theta p / P.state.r p))
          (Icc 0 a ×ˢ Icc vBar vStar) p) :
    ContDiffOn ℝ 1 P.state.zeta (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.zeta
          (rectangleScalarJet
            (B p - (N p * P.state.phi p +
              P.state.nu p * (P.state.zeta p / P.state.r p)))
            (P.state.lam p * P.state.lambdaVCoefficient p *
                P.state.phi p -
              (P.state.lam p * P.state.lambdaVCoefficient p *
                  P.state.phi p +
                P.state.nu p * (P.state.theta p / P.state.r p))))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  have hEq : EqOn P.state.zeta
      (fun p => (P.state.zeta p + P.state.nu p * P.state.phi p) -
        P.state.nu p * P.state.phi p) K := by
    intro p _
    ring
  constructor
  · exact (hBeta.1.sub (hNu.1.mul hPhi.1)).congr hEq
  · intro p hp
    have hProd := rectangleScalarJet_mul (hNu.2 p hp) (hPhi.2 p hp)
    have hSub := rectangleScalarJet_sub (hBeta.2 p hp) hProd
    exact hSub.congr' hEq hp

end ChristodoulouBV.Uniqueness

end
