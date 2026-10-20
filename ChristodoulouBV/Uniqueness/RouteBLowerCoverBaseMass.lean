module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseRadius
import ChristodoulouBV.Uniqueness.RouteBLowerCoverSafety
import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import ChristodoulouBV.BVSolution.Signs
import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Full first jet of the terminal Hawking mass

The two mass equations are algebraic in the continuous terminal value traces.
They close the relative first jet of mass on the compact off-axis rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The terminal mass has its incoming and outgoing algebraic jets on the
whole closed off-axis rectangle. -/
theorem OffAxisTerminalC1Packet.mass_full_jet
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
    ContDiffOn ℝ 1 P.state.m (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.m
          (rectangleScalarJet
            (P.state.massGap p * P.state.zeta p ^ 2 /
              (2 * P.state.nu p))
            (P.state.massGap p * P.state.theta p ^ 2 /
              (2 * P.state.lam p)))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  let du : ℝ × ℝ → ℝ := fun p =>
    P.state.massGap p * P.state.zeta p ^ 2 / (2 * P.state.nu p)
  let dv : ℝ × ℝ → ℝ := fun p =>
    P.state.massGap p * P.state.theta p ^ 2 / (2 * P.state.lam p)
  have hgap : ContinuousOn P.state.massGap K :=
    continuousOn_const.sub
      ((continuousOn_const.mul P.state.m_cont).div P.state.r_cont
        (fun p hp => ne_of_gt (P.state.radius_pos.trans_le
          (P.state.floors p.1 hp.1 p.2 hp.2).1)))
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε1 htail
  have hnu : ∀ p ∈ K, P.state.nu p ≠ 0 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    rcases lt_or_eq_of_le hv.2 with hvStar | rfl
    · let b : ℝ := (v + vStar) / 2
      have hvb : v < b := by dsimp [b]; linarith only [hvStar]
      have hb : b ∈ Ioo (0 : ℝ) vStar := by
        dsimp [b]
        constructor <;> linarith only [ha, haBar, hv.1, hvStar]
      have huv : u < v := hu.2.trans_lt (haBar.trans_le hv.1)
      have hBV := (hfamily b hb).1.isBVSolution_development
        (hu.1.trans_lt (huv.trans hvb))
      have hn : (S b).nu u v ≤ -c :=
        hBV.nu_le_neg_lower hc
          (fun q hq => hfloor b hb q.1 q.2 hq.1 hq.2.1 hq.2.2)
          ⟨hu.1, huv, hvb⟩
      rw [(P.state.match_old b hb u hu v ⟨hv.1, hvb⟩).2.2.2.1]
      exact ne_of_lt (hn.trans_lt (by linarith only [hc]))
    · exact ne_of_lt ((P.state.nu_le_neg_floor ha haBar hBarStar
        hc hfamily hfloor hu).trans_lt (by linarith only [hc]))
  have hlam : ∀ p ∈ K, P.state.lam p ≠ 0 := by
    intro p hp
    exact ne_of_gt (P.state.expansion_pos.trans_le
      (P.state.floors p.1 hp.1 p.2 hp.2).2.1)
  have hdu : ContinuousOn du K :=
    (hgap.mul (P.state.zeta_cont.pow 2)).div
      (continuousOn_const.mul P.state.nu_cont)
      (fun p hp => mul_ne_zero (by norm_num) (hnu p hp))
  have hdv : ContinuousOn dv K :=
    (hgap.mul (P.state.theta_cont.pow 2)).div
      (continuousOn_const.mul P.state.lam_cont)
      (fun p hp => mul_ne_zero (by norm_num) (hlam p hp))
  apply rectangle_scalar_full_jet_of_compatible_family
    (F := fun b p => C1Solution.canonicalMass b (S b) p)
    (f := P.state.m) (du := du) (dv := dv)
    ha haBar hBarStar P.state.m_cont hdu hdv
  · intro b hb u hu v hv
    rw [(P.state.match_old b hb u hu v hv).2.1]
    have hp : (u, v) ∈ developmentWithInitialEdge b :=
      ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv.2⟩
    exact (C1Solution.canonicalMass_eq_mass (b := b)
      (S := S b) (p := (u, v)) hp).symm
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
    have hc1 := C1Solution.canonicalMass_contDiffOn hB hBb H
    have hdiff : DifferentiableAt ℝ
        (C1Solution.canonicalMass b (S b)) (u, v) :=
      ((hc1.differentiableOn (by norm_num)).mono interior_subset
        (u, v) hpi).differentiableAt (isOpen_interior.mem_nhds hpi)
    have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
      uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
    have hwithin : fderivWithin ℝ
        (C1Solution.canonicalMass b (S b)) (closedCoordTriangle 0 B) (u, v) =
        fderiv ℝ (C1Solution.canonicalMass b (S b)) (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) hpK) hdiff
    obtain ⟨hr, hm, hl, hn, _, hz, _, ht, _⟩ :=
      P.state.match_old b hb u ⟨hu.1.le, hu.2.le⟩ v
        ⟨hv.1.le, hv.2⟩
    have hmass := C1Solution.canonicalMass_coordinate_jets hB hBb H hpK
    rw [hwithin] at hmass
    have hratio : C1Solution.canonicalMassRatio b (S b) (u, v) =
        2 * (S b).m u v / (S b).r u v :=
      C1Solution.canonicalMassRatio_eq_mass_ratio H
        ⟨hu.1.le, huv, hv.2⟩
    refine ⟨hdiff, ?_, ?_⟩
    · rw [hmass.1]
      simp only [du, C1Solution.canonicalMassIncomingDensity,
        OffAxisTerminalTraces.massGap, OffAxisTerminalTraces.massRatio,
        hratio, hr, hm, hn, hz]
    · rw [hmass.2]
      simp only [dv, C1Solution.canonicalMassOutgoingDensity,
        OffAxisTerminalTraces.massGap, OffAxisTerminalTraces.massRatio,
        hratio, hr, hm, hl, ht]

end ChristodoulouBV.Uniqueness

end
