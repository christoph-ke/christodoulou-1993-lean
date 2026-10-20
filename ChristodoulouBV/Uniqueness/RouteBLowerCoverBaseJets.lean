module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisPacket
import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisEdgeC1
import ChristodoulouBV.ForMathlib.Analysis.Calculus.CompactIntervalC1Criterion
import ChristodoulouBV.BVSolution.C1InitialCompatibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Outgoing jets on the Route B terminal base

The parametric Volterra trace of the outgoing derivative of `λ` is the
derivative of every fixed incoming slice. This includes `u = 0`, where a
two-dimensional interior derivative argument would not apply.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A continuous interior derivative supplies the one-sided derivative at
both endpoints of a compact interval. -/
theorem hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
    {a b : ℝ} (hab : a < b) {f d : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hd : ContinuousOn d (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (d x) (Icc a b) x := by
  have hc1 := contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
    hab hf hd hderiv
  have hjet : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hc1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hinterior : EqOn (derivWithin f (Icc a b)) d (Ioo a b) := by
    intro y hy
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    exact (hderiv y hy).deriv
  have hall : EqOn (derivWithin f (Icc a b)) d (Icc a b) :=
    hinterior.of_subset_closure hjet hd Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have h := (hc1.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  rw [hall hx] at h
  exact h

/-- On every incoming coordinate of the compact lower base, the canonical
terminal expansion has the outgoing derivative supplied by the construction. -/
theorem OffAxisTerminalC1Packet.lam_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.state.lam (u, w))
      (P.lambdaVTrace (u, v)) v := by
  apply hasDerivAt_terminal_value_of_deriv_match
    (F := fun b w => (S b).lam u w)
    (G := fun w => P.state.lam (u, w))
    (D := fun w => P.lambdaVTrace (u, w))
    (ha.trans haBar)
  · intro b hb w hw
    exact (P.state.match_old b hb u hu w hw).2.2.1
  · intro b hb w hw
    let B : ℝ := (w + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hw.1, hw.2]
    have hBb : B < b := by dsimp [B]; linarith only [hw.2]
    have hwB : w < B := by dsimp [B]; linarith only [hw.2]
    exact (vertical_hasDerivAt_of_closed_jet
      (C1Solution.five_fields_contDiffOn hB hBb (hfamily b hb).1).1
      hu.1 (hu.2.trans_lt (haBar.trans hw.1)) hwB
      (g := (fderivWithin ℝ
        (fun p : ℝ × ℝ => (S b).lam p.1 p.2)
        (closedCoordTriangle 0 B) (u, w)) (0, 1)) rfl).differentiableAt
  · intro w hw
    exact P.lambdaV_match u hu w ⟨hw.1.le, hw.2⟩
  · exact hv

/-- Every outgoing expansion slice of the canonical terminal state is
relatively `C¹` on the closed interval ending at `vStar`. -/
theorem OffAxisTerminalC1Packet.lam_contDiffOn_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    ContDiffOn ℝ 1 (fun v => P.state.lam (u, v)) (Icc vBar vStar) := by
  have hvalue : ContinuousOn (fun v => P.state.lam (u, v))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hderiv : ContinuousOn (fun v => P.lambdaVTrace (u, v))
      (Icc vBar vStar) :=
    P.lambdaV_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  exact contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
    hBarStar hvalue hderiv
    (fun v hv => P.lam_hasDerivAt_v ha haBar hfamily hu hv)

/-- The canonical quotient `α/λ` has derivative `λ α′` on every outgoing
slice of the compact terminal base. -/
theorem OffAxisTerminalC1Packet.quotient_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.state.quotient (u, w))
      (P.state.lam (u, v) * P.alphaPrimeTrace (u, v)) v := by
  apply hasDerivAt_terminal_value_of_deriv_match
    (F := fun b w => (S b).alpha u w / (S b).lam u w)
    (G := fun w => P.state.quotient (u, w))
    (D := fun w => P.state.lam (u, w) * P.alphaPrimeTrace (u, w))
    (ha.trans haBar)
  · intro b hb w hw
    exact (P.state.match_old b hb u hu w hw).2.2.2.2.2.2.2.2
  · intro b hb w hw
    let B : ℝ := (w + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hw.1, hw.2]
    have hBb : B < b := by dsimp [B]; linarith only [hw.2]
    have hwB : w < B := by dsimp [B]; linarith only [hw.2]
    exact (vertical_hasDerivAt_of_closed_jet
      (C1Solution.alpha_div_lam_contDiffOn hB hBb (hfamily b hb).1)
      hu.1 (hu.2.trans_lt (haBar.trans hw.1)) hwB
      (g := (fderivWithin ℝ
        (fun p : ℝ × ℝ => (S b).alpha p.1 p.2 / (S b).lam p.1 p.2)
        (closedCoordTriangle 0 B) (u, w)) (0, 1)) rfl).differentiableAt
  · intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    have hlam := (P.state.match_old b hb u hu w ⟨hw.1.le, hwb⟩).2.2.1
    have hlpos := (hfamily b hb).1.solution.lam_pos
      (u, w) (show (u, w) ∈ developmentWithInitialEdge b from
        ⟨hu.1, hu.2.trans_lt (haBar.trans hw.1), hwb⟩)
    rw [P.alphaPrime_match u hu w ⟨hw.1.le, hw.2⟩, hlam]
    exact mul_div_cancel₀ _ (ne_of_gt hlpos)
  · exact hv

/-- The canonical quotient is relatively `C¹` on each complete outgoing
interval ending at `vStar`. -/
theorem OffAxisTerminalC1Packet.quotient_contDiffOn_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    ContDiffOn ℝ 1 (fun v => P.state.quotient (u, v)) (Icc vBar vStar) := by
  have hvalue : ContinuousOn (fun v => P.state.quotient (u, v))
      (Icc vBar vStar) :=
    P.state.quotient_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hlam : ContinuousOn (fun v => P.state.lam (u, v))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hprime : ContinuousOn (fun v => P.alphaPrimeTrace (u, v))
      (Icc vBar vStar) :=
    P.alphaPrime_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  exact contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
    hBarStar hvalue (hlam.mul hprime)
    (fun v hv => P.quotient_hasDerivAt_v ha haBar hfamily hu hv)

/-- The canonical quotient and expansion reconstruct `α` throughout the
closed terminal rectangle, including its terminal edge. -/
theorem OffAxisTerminalC1Packet.alpha_eq_lam_mul_quotient
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    P.state.alpha (u, v) =
      P.state.lam (u, v) * P.state.quotient (u, v) := by
  let f : ℝ → ℝ := fun w =>
    P.state.alpha (u, w) -
      P.state.lam (u, w) * P.state.quotient (u, w)
  have hf : ContinuousOn f (Icc vBar vStar) := by
    exact (P.state.alpha_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)).sub
      ((P.state.lam_cont.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hw => ⟨hu, hw⟩)).mul
       (P.state.quotient_cont.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hw => ⟨hu, hw⟩)))
  have hmap : MapsTo f (Ico vBar vStar) {0} := by
    intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    obtain ⟨_, _, hlam, _, _, _, halpha, _, hquot⟩ :=
      P.state.match_old b hb u hu w ⟨hw.1, hwb⟩
    have hlpos := (hfamily b hb).1.solution.lam_pos
      (u, w) (show (u, w) ∈ developmentWithInitialEdge b from
        ⟨hu.1, hu.2.trans_lt (haBar.trans_le hw.1), hwb⟩)
    change f w = 0
    dsimp [f]
    rw [halpha, hlam, hquot]
    field_simp [ne_of_gt hlpos]
    ring
  have hclosed : closure (Ico vBar vStar) = Icc vBar vStar :=
    closure_Ico hBarStar.ne
  have hvcl : v ∈ closure (Ico vBar vStar) := by rw [hclosed]; exact hv
  rw [← hclosed] at hf
  have hzero := hmap.closure_of_continuousOn hf hvcl
  have hfzero : f v = 0 := by
    simpa only [closure_singleton, mem_singleton_iff] using hzero
  exact sub_eq_zero.mp hfzero

/-- The outgoing derivative of the canonical `α` slice is determined by
the two Volterra derivative traces and the canonical quotient. -/
theorem OffAxisTerminalC1Packet.alpha_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.state.alpha (u, w))
      (P.lambdaVTrace (u, v) * P.state.quotient (u, v) +
        P.state.lam (u, v) *
          (P.state.lam (u, v) * P.alphaPrimeTrace (u, v))) v := by
  have hprod := (P.lam_hasDerivAt_v ha haBar hfamily hu hv).mul
    (P.quotient_hasDerivAt_v ha haBar hfamily hu hv)
  have heq : (fun w => P.state.alpha (u, w)) =ᶠ[𝓝 v]
      (fun w => P.state.lam (u, w) * P.state.quotient (u, w)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
    exact P.alpha_eq_lam_mul_quotient ha haBar hBarStar hfamily hu
      ⟨hw.1.le, hw.2.le⟩
  exact hprod.congr_of_eventuallyEq heq

/-- Every canonical `α` slice is relatively `C¹` up to the terminal edge. -/
theorem OffAxisTerminalC1Packet.alpha_contDiffOn_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    ContDiffOn ℝ 1 (fun v => P.state.alpha (u, v)) (Icc vBar vStar) := by
  have hvalue : ContinuousOn (fun v => P.state.alpha (u, v))
      (Icc vBar vStar) :=
    P.state.alpha_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hlam : ContinuousOn (fun v => P.state.lam (u, v))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hquot : ContinuousOn (fun v => P.state.quotient (u, v))
      (Icc vBar vStar) :=
    P.state.quotient_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hL : ContinuousOn (fun v => P.lambdaVTrace (u, v))
      (Icc vBar vStar) :=
    P.lambdaV_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  have hP : ContinuousOn (fun v => P.alphaPrimeTrace (u, v))
      (Icc vBar vStar) :=
    P.alphaPrime_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨hu, hv⟩)
  exact contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
    hBarStar hvalue ((hL.mul hquot).add (hlam.mul (hlam.mul hP)))
    (fun v hv => P.alpha_hasDerivAt_v ha haBar hBarStar hfamily hu hv)

/-- Both incoming rectangle variables have their canonical outgoing
derivatives on the entire closed terminal base, including its endpoints. -/
theorem OffAxisTerminalC1Packet.incoming_hasDerivWithinAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    HasDerivWithinAt
      (fun w => (P.state.lam (u, w), P.state.alpha (u, w)))
      (P.lambdaVTrace (u, v),
        P.lambdaVTrace (u, v) * P.state.quotient (u, v) +
          P.state.lam (u, v) *
            (P.state.lam (u, v) * P.alphaPrimeTrace (u, v)))
      (Icc vBar vStar) v := by
  have hlam : ContinuousOn (fun w => P.state.lam (u, w))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have halpha : ContinuousOn (fun w => P.state.alpha (u, w))
      (Icc vBar vStar) :=
    P.state.alpha_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hquot : ContinuousOn (fun w => P.state.quotient (u, w))
      (Icc vBar vStar) :=
    P.state.quotient_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hL : ContinuousOn (fun w => P.lambdaVTrace (u, w))
      (Icc vBar vStar) :=
    P.lambdaV_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  have hP : ContinuousOn (fun w => P.alphaPrimeTrace (u, w))
      (Icc vBar vStar) :=
    P.alphaPrime_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hu, hw⟩)
  exact (hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
    hBarStar hlam hL
    (fun w hw => P.lam_hasDerivAt_v ha haBar hfamily hu hw) hv).prodMk
    (hasDerivWithinAt_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar halpha ((hL.mul hquot).add (hlam.mul (hlam.mul hP)))
      (fun w hw => P.alpha_hasDerivAt_v ha haBar hBarStar hfamily hu hw) hv)

/-- The canonical terminal incoming state retains the prescribed initial
gauge through the endpoint `vStar`. -/
theorem OffAxisTerminalC1Packet.initial_terminal_gauge
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {v : ℝ} (hv : v ∈ Icc vBar vStar) :
    P.state.lam (0, v) = 1 / 2 ∧ P.state.alpha (0, v) = alpha₀ v := by
  have hzero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have hclosed : Icc vBar vStar ⊆ closure (Ico vBar vStar) := by
    rw [closure_Ico hBarStar.ne]
  have hmatch (w : ℝ) (hw : w ∈ Ico vBar vStar) :
      P.state.lam (0, w) = 1 / 2 ∧
      P.state.alpha (0, w) = alpha₀ w := by
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hw.1, hw.2]
    have hm := P.state.match_old b hb 0 hzero w ⟨hw.1, hwb⟩
    have hw0b : w ∈ Ioo (0 : ℝ) b :=
      ⟨ha.trans (haBar.trans_le hw.1), hwb⟩
    exact ⟨hm.2.2.1.trans
        (initial_lam_eq_of_gauge (hfamily b hb).1
          (fun t ht => ((hfamily b hb).2 t ht).1) hw0b),
      hm.2.2.2.2.2.2.1.trans ((hfamily b hb).2 w hw0b).2⟩
  have hlamCont : ContinuousOn (fun w => P.state.lam (0, w))
      (Icc vBar vStar) :=
    P.state.lam_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hzero, hw⟩)
  have halphaCont : ContinuousOn (fun w => P.state.alpha (0, w))
      (Icc vBar vStar) :=
    P.state.alpha_cont.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hzero, hw⟩)
  have hαCont : ContinuousOn alpha₀ (Icc vBar vStar) :=
    hα.continuousOn.mono
      (fun _ hw => le_trans (by linarith only [ha, haBar]) hw.1)
  constructor
  · exact (show EqOn (fun w => P.state.lam (0, w)) (fun _ => 1 / 2)
        (Ico vBar vStar) from fun w hw => (hmatch w hw).1).of_subset_closure
        hlamCont continuousOn_const Ico_subset_Icc_self hclosed hv
  · exact (show EqOn (fun w => P.state.alpha (0, w)) alpha₀
        (Ico vBar vStar) from fun w hw => (hmatch w hw).2).of_subset_closure
        halphaCont hαCont Ico_subset_Icc_self hclosed hv

end ChristodoulouBV.Uniqueness

end
