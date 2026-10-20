module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisDerivativeCompatibility
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.CompactIntervalC1Criterion
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Compact C¹ terminal edge below the corner

The joint Volterra traces supply the outgoing derivatives of the expansion
and quotient on a fixed off-axis edge. The radius derivative is the expansion.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A canonical continuous value trace has the prescribed derivative in the
interior when each finite member is differentiable and the derivative trace
agrees with the chosen member. -/
theorem hasDerivAt_terminal_value_of_deriv_match
    {vBar vStar v : ℝ} {F : ℝ → ℝ → ℝ} {G D : ℝ → ℝ}
    (hBar : 0 < vBar)
    (hmatch : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ w ∈ Ico vBar b, G w = F b w)
    (hdiff : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ w ∈ Ioo vBar b, DifferentiableAt ℝ (F b) w)
    (hD : ∀ w ∈ Ioo vBar vStar,
      D w = deriv (F ((w + vStar) / 2)) w)
    (hv : v ∈ Ioo vBar vStar) : HasDerivAt G (D v) v := by
  let b : ℝ := (v + vStar) / 2
  have hvb : v < b := by dsimp [b]; linarith only [hv.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b]
    constructor <;> linarith only [hBar, hv.1, hv.2]
  have heq : G =ᶠ[𝓝 v] F b := by
    filter_upwards [Ioo_mem_nhds hv.1 hvb] with w hw
    exact hmatch b hb w ⟨hw.1.le, hw.2⟩
  have hold : HasDerivAt (F b) (deriv (F b) v) v :=
    (hdiff b hb v ⟨hv.1, hvb⟩).hasDerivAt
  simpa only [show D v = deriv (F b) v from hD v hv] using
    hold.congr_of_eventuallyEq heq

/-- The expansion, scalar quotient, and radius are `C¹` on a compact
terminal edge below the corner. Their derivative traces are respectively
`λᵥ`, `λα′`, and `λ`. -/
theorem OffAxisTerminalTraces.compact_edge_c1
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {P L : ℝ × ℝ → ℝ}
    (hPcont : ContinuousOn P (Icc 0 a ×ˢ Icc vBar vStar))
    (hLcont : ContinuousOn L (Icc 0 a ×ˢ Icc vBar vStar))
    (hPmatch : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
      P (u, v) =
        deriv (fun t =>
          (S ((v + vStar) / 2)).alpha u t /
            (S ((v + vStar) / 2)).lam u t) v /
          (S ((v + vStar) / 2)).lam u v)
    (hLmatch : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
      L (u, v) = deriv ((S ((v + vStar) / 2)).lam u) v) :
    ContDiffOn ℝ 1 (fun v => T.lam (a, v)) (Icc vBar vStar) ∧
    ContDiffOn ℝ 1 (fun v => T.quotient (a, v)) (Icc vBar vStar) ∧
    ContDiffOn ℝ 1 (fun v => T.r (a, v)) (Icc vBar vStar) := by
  have haI : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hlamCont : ContinuousOn (fun v => T.lam (a, v))
      (Icc vBar vStar) :=
    T.lam_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨haI, hv⟩)
  have hquotCont : ContinuousOn (fun v => T.quotient (a, v))
      (Icc vBar vStar) :=
    T.quotient_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨haI, hv⟩)
  have hrCont : ContinuousOn (fun v => T.r (a, v))
      (Icc vBar vStar) :=
    T.r_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨haI, hv⟩)
  have hLedge : ContinuousOn (fun v => L (a, v)) (Icc vBar vStar) :=
    hLcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨haI, hv⟩)
  have hPedge : ContinuousOn (fun v => T.lam (a, v) * P (a, v))
      (Icc vBar vStar) := hlamCont.mul
        (hPcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun v hv => ⟨haI, hv⟩))
  have hLamDiff (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) vStar)
      (v : ℝ) (hv : v ∈ Ioo vBar b) :
      DifferentiableAt ℝ ((S b).lam a) v := by
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    exact (vertical_hasDerivAt_of_closed_jet
      (C1Solution.five_fields_contDiffOn hB hBb (hfamily b hb).1).1
      ha.le (haBar.trans hv.1) hvB
      (g := (fderivWithin ℝ
        (fun p : ℝ × ℝ => (S b).lam p.1 p.2)
        (closedCoordTriangle 0 B) (a, v)) (0, 1)) rfl).differentiableAt
  have hQuotDiff (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) vStar)
      (v : ℝ) (hv : v ∈ Ioo vBar b) :
      DifferentiableAt ℝ
        (fun w => (S b).alpha a w / (S b).lam a w) v := by
    let B : ℝ := (v + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hv.2]
    have hBb : B < b := by dsimp [B]; linarith only [hv.2]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    exact (vertical_hasDerivAt_of_closed_jet
      (C1Solution.alpha_div_lam_contDiffOn hB hBb (hfamily b hb).1)
      ha.le (haBar.trans hv.1) hvB
      (g := (fderivWithin ℝ
        (fun p : ℝ × ℝ => (S b).alpha p.1 p.2 / (S b).lam p.1 p.2)
        (closedCoordTriangle 0 B) (a, v)) (0, 1)) rfl).differentiableAt
  have hcutoff (v : ℝ) (hv : v ∈ Ioo vBar vStar) :
      (v + vStar) / 2 ∈ Ioo (0 : ℝ) vStar ∧
      v < (v + vStar) / 2 := by
    constructor
    · constructor <;> linarith only [ha, haBar, hv.1, hv.2]
    · linarith only [hv.2]
  have hLamDeriv : ∀ v ∈ Ioo vBar vStar,
      HasDerivAt (fun w => T.lam (a, w)) (L (a, v)) v := by
    intro v hv
    apply hasDerivAt_terminal_value_of_deriv_match
      (F := fun b w => (S b).lam a w)
      (G := fun w => T.lam (a, w))
      (D := fun w => L (a, w))
      (ha.trans haBar)
    · intro b hb w hw
      exact (T.match_old b hb a haI w hw).2.2.1
    · exact hLamDiff
    · intro w hw
      exact hLmatch a haI w ⟨hw.1.le, hw.2⟩
    · exact hv
  have hQuotDeriv : ∀ v ∈ Ioo vBar vStar,
      HasDerivAt (fun w => T.quotient (a, w))
        (T.lam (a, v) * P (a, v)) v := by
    intro v hv
    apply hasDerivAt_terminal_value_of_deriv_match
      (F := fun b w => (S b).alpha a w / (S b).lam a w)
      (G := fun w => T.quotient (a, w))
      (D := fun w => T.lam (a, w) * P (a, w))
      (ha.trans haBar)
    · intro b hb w hw
      exact (T.match_old b hb a haI w hw).2.2.2.2.2.2.2.2
    · exact hQuotDiff
    · intro w hw
      obtain ⟨hb, hwb⟩ := hcutoff w hw
      have hlam := (T.match_old ((w + vStar) / 2) hb a haI w
        ⟨hw.1.le, hwb⟩).2.2.1
      have hlpos := (hfamily ((w + vStar) / 2) hb).1.solution.lam_pos
        (a, w) (show (a, w) ∈ developmentWithInitialEdge ((w + vStar) / 2) from
          ⟨ha.le, haBar.trans hw.1, hwb⟩)
      rw [hPmatch a haI w ⟨hw.1.le, hw.2⟩, hlam]
      exact mul_div_cancel₀ _ (ne_of_gt hlpos)
    · exact hv
  have hrDeriv : ∀ v ∈ Ioo vBar vStar,
      HasDerivAt (fun w => T.r (a, w)) (T.lam (a, v)) v := by
    intro v hv
    apply hasDerivAt_terminal_value_of_deriv_match
      (F := fun b w => (S b).r a w)
      (G := fun w => T.r (a, w))
      (D := fun w => T.lam (a, w))
      (ha.trans haBar)
    · intro b hb w hw
      exact (T.match_old b hb a haI w hw).1
    · intro b hb w hw
      have hp : (a, w) ∈ openDevelopment 0 b :=
        ⟨⟨ha, (haBar.trans hw.1).trans hw.2⟩,
          ⟨haBar.trans hw.1, hw.2⟩⟩
      exact (radius_hasDerivAt_v_of_c1 (hfamily b hb).1 hp).differentiableAt
    · intro w hw
      obtain ⟨hb, hwb⟩ := hcutoff w hw
      have hp : (a, w) ∈ openDevelopment 0 ((w + vStar) / 2) :=
        ⟨⟨ha, (haBar.trans hw.1).trans hwb⟩,
          ⟨haBar.trans hw.1, hwb⟩⟩
      rw [(radius_hasDerivAt_v_of_c1 (hfamily _ hb).1 hp).deriv]
      exact (T.match_old _ hb a haI w ⟨hw.1.le, hwb⟩).2.2.1
    · exact hv
  exact ⟨contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hlamCont hLedge hLamDeriv,
    contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hquotCont hPedge hQuotDeriv,
    contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hrCont hlamCont hrDeriv⟩

/-- The outgoing derivative of the terminal radius trace is the terminal
expansion at every interior point of the off-axis edge. -/
theorem OffAxisTerminalTraces.radius_terminal_edge_hasDerivAt
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {v : ℝ} (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => T.r (a, w)) (T.lam (a, v)) v := by
  have haI : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  apply hasDerivAt_terminal_value_of_deriv_match
    (F := fun b w => (S b).r a w)
    (G := fun w => T.r (a, w))
    (D := fun w => T.lam (a, w))
    (ha.trans haBar)
  · intro b hb w hw
    exact (T.match_old b hb a haI w hw).1
  · intro b hb w hw
    have hp : (a, w) ∈ openDevelopment 0 b :=
      ⟨⟨ha, (haBar.trans hw.1).trans hw.2⟩,
        ⟨haBar.trans hw.1, hw.2⟩⟩
    exact (radius_hasDerivAt_v_of_c1 (hfamily b hb).1 hp).differentiableAt
  · intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    have hp : (a, w) ∈ openDevelopment 0 b :=
      ⟨⟨ha, (haBar.trans hw.1).trans hwb⟩,
        ⟨haBar.trans hw.1, hwb⟩⟩
    rw [(radius_hasDerivAt_v_of_c1 (hfamily b hb).1 hp).deriv]
    exact (T.match_old b hb a haI w ⟨hw.1.le, hwb⟩).2.2.1
  · exact hv

end ChristodoulouBV.Uniqueness

end
