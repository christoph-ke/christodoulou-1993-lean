module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseJets
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import ChristodoulouBV.C1Solution.ExtractionCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Outgoing radius jets on the terminal base

The canonical radius and scalar-radius primitives of each finite old solution
give outgoing derivatives of the corresponding terminal traces, also at the
initial incoming coordinate `u = 0`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The terminal radius trace has outgoing derivative equal to the terminal
expansion at every interior point of the compact base. -/
theorem OffAxisTerminalC1Packet.radius_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.state.r (u, w))
      (P.state.lam (u, v)) v := by
  apply hasDerivAt_terminal_value_of_deriv_match
    (F := fun b w => C1Solution.canonicalRadius (S b) (u, w))
    (G := fun w => P.state.r (u, w))
    (D := fun w => P.state.lam (u, w)) (ha.trans haBar)
  · intro b hb w hw
    rw [(P.state.match_old b hb u hu w hw).1]
    let B : ℝ := (w + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hw.1, hw.2]
    have hBb : B < b := by dsimp [B]; linarith only [hw.2]
    have hwB : w ≤ B := by dsimp [B]; linarith only [hw.2]
    exact (C1Solution.canonicalRadius_eq_radius hB hBb (hfamily b hb).1
      hu.1 (hu.2.trans_lt (haBar.trans_le hw.1)) hwB).symm
  · intro b hb w hw
    let B : ℝ := (w + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hw.1, hw.2]
    have hBb : B < b := by dsimp [B]; linarith only [hw.2]
    have hwB : w < B := by dsimp [B]; linarith only [hw.2]
    exact (vertical_hasDerivAt_of_closed_jet
      (C1Solution.canonicalRadius_contDiffOn hB hBb (hfamily b hb).1)
      hu.1 (hu.2.trans_lt (haBar.trans hw.1)) hwB
      (C1Solution.canonicalRadius_vertical_jet hB hBb (hfamily b hb).1
        ⟨hu.1, (hu.2.trans_lt (haBar.trans hw.1)).le, hwB.le⟩)).differentiableAt
  · intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    have hder := vertical_hasDerivAt_of_closed_jet
      (C1Solution.canonicalRadius_contDiffOn
        (show 0 < (w + b) / 2 by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2])
        (show (w + b) / 2 < b by linarith only [hwb])
        (hfamily b hb).1)
      hu.1 (hu.2.trans_lt (haBar.trans hw.1))
      (show w < (w + b) / 2 by linarith only [hwb])
      (C1Solution.canonicalRadius_vertical_jet
        (show 0 < (w + b) / 2 by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2])
        (show (w + b) / 2 < b by linarith only [hwb])
        (hfamily b hb).1
        ⟨hu.1, (hu.2.trans_lt (haBar.trans hw.1)).le,
          (show w ≤ (w + b) / 2 by linarith only [hwb])⟩)
    rw [hder.deriv]
    exact (P.state.match_old b hb u hu w ⟨hw.1.le, hwb⟩).2.2.1
  · exact hv

/-- The terminal scalar-radius trace has outgoing derivative equal to the
terminal scalar transport variable, including at `u = 0`. -/
theorem OffAxisTerminalC1Packet.scalarRadius_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.state.r (u, w) * P.state.phi (u, w))
      (P.state.alpha (u, v)) v := by
  apply hasDerivAt_terminal_value_of_deriv_match
    (F := fun b w => C1Solution.canonicalScalarRadius (S b) (u, w))
    (G := fun w => P.state.r (u, w) * P.state.phi (u, w))
    (D := fun w => P.state.alpha (u, w)) (ha.trans haBar)
  · intro b hb w hw
    rw [(P.state.match_old b hb u hu w hw).1,
      (P.state.match_old b hb u hu w hw).2.2.2.2.1]
    let B : ℝ := (w + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hw.1, hw.2]
    have hBb : B < b := by dsimp [B]; linarith only [hw.2]
    have hwB : w ≤ B := by dsimp [B]; linarith only [hw.2]
    exact (C1Solution.canonicalScalarRadius_eq_radius_mul_phi hB hBb
      (hfamily b hb).1 hu.1
      (hu.2.trans_lt (haBar.trans_le hw.1)) hwB).symm
  · intro b hb w hw
    let B : ℝ := (w + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hw.1, hw.2]
    have hBb : B < b := by dsimp [B]; linarith only [hw.2]
    have hwB : w < B := by dsimp [B]; linarith only [hw.2]
    exact (vertical_hasDerivAt_of_closed_jet
      (C1Solution.canonicalScalarRadius_contDiffOn hB hBb (hfamily b hb).1)
      hu.1 (hu.2.trans_lt (haBar.trans hw.1)) hwB
      (C1Solution.canonicalScalarRadius_vertical_jet hB hBb (hfamily b hb).1
        ⟨hu.1, (hu.2.trans_lt (haBar.trans hw.1)).le, hwB.le⟩)).differentiableAt
  · intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    have hder := vertical_hasDerivAt_of_closed_jet
      (C1Solution.canonicalScalarRadius_contDiffOn
        (show 0 < (w + b) / 2 by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2])
        (show (w + b) / 2 < b by linarith only [hwb])
        (hfamily b hb).1)
      hu.1 (hu.2.trans_lt (haBar.trans hw.1))
      (show w < (w + b) / 2 by linarith only [hwb])
      (C1Solution.canonicalScalarRadius_vertical_jet
        (show 0 < (w + b) / 2 by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2])
        (show (w + b) / 2 < b by linarith only [hwb])
        (hfamily b hb).1
        ⟨hu.1, (hu.2.trans_lt (haBar.trans hw.1)).le,
          (show w ≤ (w + b) / 2 by linarith only [hwb])⟩)
    rw [hder.deriv]
    exact (P.state.match_old b hb u hu w ⟨hw.1.le, hwb⟩).2.2.2.2.2.2.1
  · exact hv

/-- The canonical radius and scalar-radius derivatives extend to the closed
terminal edge as relative derivatives. -/
theorem OffAxisTerminalC1Packet.radius_scalarRadius_hasDerivWithinAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    HasDerivWithinAt (fun w => P.state.r (u, w))
      (P.state.lam (u, v)) (Icc vBar vStar) v ∧
    HasDerivWithinAt
      (fun w => P.state.r (u, w) * P.state.phi (u, w))
      (P.state.alpha (u, v)) (Icc vBar vStar) v := by
  have hr : ContinuousOn (fun w => P.state.r (u, w))
      (Icc vBar vStar) :=
    P.state.r_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hphi : ContinuousOn (fun w => P.state.phi (u, w))
      (Icc vBar vStar) :=
    P.state.phi_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hlam : ContinuousOn (fun w => P.state.lam (u, w))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have halpha : ContinuousOn (fun w => P.state.alpha (u, w))
      (Icc vBar vStar) :=
    P.state.alpha_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  exact ⟨hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hr hlam
      (fun w hw => P.radius_hasDerivAt_v ha haBar hfamily hu hw) hv,
    hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar (hr.mul hphi) halpha
      (fun w hw => P.scalarRadius_hasDerivAt_v ha haBar hfamily hu hw) hv⟩

/-- Both primitive coordinates of the terminal seven-state tuple are `C¹`
on each compact outgoing slice ending at `vStar`. -/
theorem OffAxisTerminalC1Packet.radius_scalarRadius_contDiffOn_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    ContDiffOn ℝ 1 (fun v => P.state.r (u, v)) (Icc vBar vStar) ∧
    ContDiffOn ℝ 1 (fun v => P.state.r (u, v) * P.state.phi (u, v))
      (Icc vBar vStar) := by
  have hr : ContinuousOn (fun w => P.state.r (u, w))
      (Icc vBar vStar) :=
    P.state.r_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hphi : ContinuousOn (fun w => P.state.phi (u, w))
      (Icc vBar vStar) :=
    P.state.phi_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hlam : ContinuousOn (fun w => P.state.lam (u, w))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have halpha : ContinuousOn (fun w => P.state.alpha (u, w))
      (Icc vBar vStar) :=
    P.state.alpha_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  exact ⟨contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hr hlam
      (fun w hw => P.radius_hasDerivAt_v ha haBar hfamily hu hw),
    contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar (hr.mul hphi) halpha
      (fun w hw => P.scalarRadius_hasDerivAt_v ha haBar hfamily hu hw)⟩

/-- The terminal radius retains the initial gauge on the complete compact
vertical edge, including its terminal endpoint. -/
theorem OffAxisTerminalC1Packet.initial_radius_gauge
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {v : ℝ} (hv : v ∈ Icc vBar vStar) :
    P.state.r (0, v) = v / 2 := by
  have hzero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have hr : ContinuousOn (fun w => P.state.r (0, w))
      (Icc vBar vStar) :=
    P.state.r_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hzero, hw⟩)
  have hmatch : EqOn (fun w => P.state.r (0, w)) (fun w => w / 2)
      (Ico vBar vStar) := by
    intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    exact (P.state.match_old b hb 0 hzero w ⟨hw.1, hwb⟩).1.trans
      ((hfamily b hb).2 w ⟨ha.trans (haBar.trans_le hw.1), hwb⟩).1
  have hclosure : Icc vBar vStar ⊆ closure (Ico vBar vStar) := by
    rw [closure_Ico hBarStar.ne]
  exact hmatch.of_subset_closure hr
    (continuous_id.div_const 2).continuousOn Ico_subset_Icc_self hclosure hv

end ChristodoulouBV.Uniqueness

end
