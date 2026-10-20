module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseOutgoing
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverJetClosure
import ChristodoulouBV.C1Solution.ExtractionCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full first jet of the canonical terminal radius

The canonical finite radii have incoming jet `ν` and outgoing jet `λ`.
Their compatible terminal trace therefore has these full first jets on the
closed off-axis rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The canonical terminal radius has its complete first jet through the
terminal base, including at the initial incoming coordinate. -/
theorem OffAxisTerminalC1Packet.radius_full_jet
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ContDiffOn ℝ 1 P.state.r (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.r
          (rectangleScalarJet (P.state.nu p) (P.state.lam p))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  apply rectangle_scalar_full_jet_of_compatible_family
    (F := fun b p => C1Solution.canonicalRadius (S b) p)
    (f := P.state.r) (du := P.state.nu) (dv := P.state.lam)
    ha haBar hBarStar P.state.r_cont P.state.nu_cont P.state.lam_cont
  · intro b hb u hu v hv
    have hr := (P.state.match_old b hb u hu v hv).1
    rw [hr]
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by
      dsimp [B]
      linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v ≤ B := by dsimp [B]; linarith only [hv.2]
    exact (C1Solution.canonicalRadius_eq_radius hB hBb
      (hfamily b hb).1 hu.1
      (hu.2.trans_lt (haBar.trans_le hv.1)) hvB).symm
  · intro b hb u hu v hv
    let H := (hfamily b hb).1
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    have huv : u < v := hu.2.trans (haBar.trans hv.1)
    have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
      ⟨hu.1.le, huv.le, hvB.le⟩
    have hpi : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu.1, huv, hvB⟩
    have hc1 := C1Solution.canonicalRadius_contDiffOn hB hBb H
    have hdiff : DifferentiableAt ℝ
        (C1Solution.canonicalRadius (S b)) (u, v) :=
      ((hc1.differentiableOn (by norm_num)).mono interior_subset
        (u, v) hpi).differentiableAt (isOpen_interior.mem_nhds hpi)
    have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
      uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
    have hwithin : fderivWithin ℝ
        (C1Solution.canonicalRadius (S b)) (closedCoordTriangle 0 B) (u, v) =
        fderiv ℝ (C1Solution.canonicalRadius (S b)) (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) hpK) hdiff
    have hm := P.state.match_old b hb u ⟨hu.1.le, hu.2.le⟩ v
      ⟨hv.1.le, hv.2⟩
    obtain ⟨_, _, hlam, hnu, _, _, _, _, _⟩ := hm
    have hjetU := C1Solution.canonicalRadius_horizontal_jet hB hBb H hpK
    have hjetV := C1Solution.canonicalRadius_vertical_jet hB hBb H hpK
    rw [hwithin] at hjetU hjetV
    exact ⟨hdiff, hjetU.trans hnu.symm, hjetV.trans hlam.symm⟩

/-- The canonical scalar-radius trace has incoming jet `β = ζ + νφ`
and outgoing jet `α` on the full closed terminal rectangle. -/
theorem OffAxisTerminalC1Packet.scalarRadius_full_jet
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ContDiffOn ℝ 1 (fun p => P.state.r p * P.state.phi p)
      (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt (fun q => P.state.r q * P.state.phi q)
          (rectangleScalarJet
            (P.state.zeta p + P.state.nu p * P.state.phi p)
            (P.state.alpha p))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  have hvalue : ContinuousOn
      (fun p => P.state.r p * P.state.phi p)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    P.state.r_cont.mul P.state.phi_cont
  have hdu : ContinuousOn
      (fun p => P.state.zeta p + P.state.nu p * P.state.phi p)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    P.state.zeta_cont.add (P.state.nu_cont.mul P.state.phi_cont)
  apply rectangle_scalar_full_jet_of_compatible_family
    (F := fun b p => C1Solution.canonicalScalarRadius (S b) p)
    (f := fun p => P.state.r p * P.state.phi p)
    (du := fun p => P.state.zeta p + P.state.nu p * P.state.phi p)
    (dv := P.state.alpha)
    ha haBar hBarStar hvalue hdu P.state.alpha_cont
  · intro b hb u hu v hv
    obtain ⟨hr, _, _, _, hphi, _, _, _, _⟩ :=
      P.state.match_old b hb u hu v hv
    rw [hr, hphi]
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by
      dsimp [B]
      linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v ≤ B := by dsimp [B]; linarith only [hv.2]
    exact (C1Solution.canonicalScalarRadius_eq_radius_mul_phi hB hBb
      (hfamily b hb).1 hu.1
      (hu.2.trans_lt (haBar.trans_le hv.1)) hvB).symm
  · intro b hb u hu v hv
    let H := (hfamily b hb).1
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    have huv : u < v := hu.2.trans (haBar.trans hv.1)
    have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
      ⟨hu.1.le, huv.le, hvB.le⟩
    have hpi : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu.1, huv, hvB⟩
    have hc1 := C1Solution.canonicalScalarRadius_contDiffOn hB hBb H
    have hdiff : DifferentiableAt ℝ
        (C1Solution.canonicalScalarRadius (S b)) (u, v) :=
      ((hc1.differentiableOn (by norm_num)).mono interior_subset
        (u, v) hpi).differentiableAt (isOpen_interior.mem_nhds hpi)
    have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
      uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
    have hwithin : fderivWithin ℝ
        (C1Solution.canonicalScalarRadius (S b)) (closedCoordTriangle 0 B) (u, v) =
        fderiv ℝ (C1Solution.canonicalScalarRadius (S b)) (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) hpK) hdiff
    have hm := P.state.match_old b hb u ⟨hu.1.le, hu.2.le⟩ v
      ⟨hv.1.le, hv.2⟩
    obtain ⟨_, _, _, hnu, hphi, hzeta, halpha, _, _⟩ := hm
    have hjetU := C1Solution.canonicalScalarRadius_horizontal_jet hB hBb H hpK
    have hjetV := C1Solution.canonicalScalarRadius_vertical_jet hB hBb H hpK
    rw [hwithin] at hjetU hjetV
    refine ⟨hdiff, ?_, hjetV.trans halpha.symm⟩
    calc
      (fderiv ℝ (C1Solution.canonicalScalarRadius (S b)) (u, v)) (1, 0) =
          (S b).beta u v := hjetU
      _ = P.state.zeta (u, v) +
          P.state.nu (u, v) * P.state.phi (u, v) := by
        rw [hzeta, hnu, hphi]
        simp only [Fields.zeta]
        ring

end ChristodoulouBV.Uniqueness

end
