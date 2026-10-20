module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointMass
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointAlphaTheta
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyGap
import Mathlib.Tactic.Linarith

/-!
# Joint lower-order state on a terminal off-axis rectangle

The compatible family gives one continuous tuple on each fixed compact
rectangle. Radius, outgoing expansion, and mass gap keep positive floors.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Continuous values needed in the off-axis incoming transport equations. -/
structure OffAxisTerminalTraces (a vBar vStar : ℝ) (S : ℝ → Fields) where
  r : ℝ × ℝ → ℝ
  m : ℝ × ℝ → ℝ
  lam : ℝ × ℝ → ℝ
  nu : ℝ × ℝ → ℝ
  phi : ℝ × ℝ → ℝ
  zeta : ℝ × ℝ → ℝ
  alpha : ℝ × ℝ → ℝ
  theta : ℝ × ℝ → ℝ
  quotient : ℝ × ℝ → ℝ
  ρ : ℝ
  c : ℝ
  q : ℝ
  radius_pos : 0 < ρ
  expansion_pos : 0 < c
  gap_pos : 0 < q
  r_cont : ContinuousOn r (Icc 0 a ×ˢ Icc vBar vStar)
  m_cont : ContinuousOn m (Icc 0 a ×ˢ Icc vBar vStar)
  lam_cont : ContinuousOn lam (Icc 0 a ×ˢ Icc vBar vStar)
  nu_cont : ContinuousOn nu (Icc 0 a ×ˢ Icc vBar vStar)
  phi_cont : ContinuousOn phi (Icc 0 a ×ˢ Icc vBar vStar)
  zeta_cont : ContinuousOn zeta (Icc 0 a ×ˢ Icc vBar vStar)
  alpha_cont : ContinuousOn alpha (Icc 0 a ×ˢ Icc vBar vStar)
  theta_cont : ContinuousOn theta (Icc 0 a ×ˢ Icc vBar vStar)
  quotient_cont : ContinuousOn quotient (Icc 0 a ×ˢ Icc vBar vStar)
  floors : ∀ u ∈ Icc 0 a, ∀ v ∈ Icc vBar vStar,
    ρ ≤ r (u, v) ∧ c ≤ lam (u, v) ∧
      q ≤ 1 - 2 * m (u, v) / r (u, v)
  match_old : ∀ b ∈ Ioo (0 : ℝ) vStar,
    ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
      r (u, v) = (S b).r u v ∧
      m (u, v) = (S b).m u v ∧
      lam (u, v) = (S b).lam u v ∧
      nu (u, v) = (S b).nu u v ∧
      phi (u, v) = (S b).phi u v ∧
      zeta (u, v) = (S b).zeta u v ∧
      alpha (u, v) = (S b).alpha u v ∧
      theta (u, v) = (S b).theta u v ∧
      quotient (u, v) = (S b).alpha u v / (S b).lam u v

/-- The entire lower-order state, with positive denominators, extends
jointly to every compact rectangle below the terminal corner. -/
theorem exists_offAxisTerminalTraces
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    Nonempty (OffAxisTerminalTraces a vBar vStar S) := by
  obtain ⟨ρ, hρ, R, hR, hRfloor, hRmatch⟩ :=
    exists_radius_terminal_trace_with_floor_on_rectangle
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨M, hM, hMmatch⟩ :=
    exists_mass_terminal_trace_on_rectangle
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨c, hc, L, H, A, T, hL, hH, hA, hT, hLfloor, hscalar⟩ :=
    exists_alpha_theta_terminal_traces_on_rectangle
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨N, P, Z, hN, hP, hZ, hNPZ⟩ :=
    exists_nu_phi_zeta_terminal_traces_on_rectangle
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  obtain ⟨q, hq, hgap⟩ :=
    exists_mass_gap_floor_before_star hu₀ hα hfamily hεlt htail
  have hRne : ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar, R p ≠ 0 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ne_of_gt (hρ.trans_le (hRfloor u hu v hv))
  have hQcont : ContinuousOn
      (fun p => 1 - 2 * M p / R p) (Icc 0 a ×ˢ Icc vBar vStar) :=
    continuousOn_const.sub ((continuousOn_const.mul hM).div hR hRne)
  have hQfloor : ∀ u ∈ Icc 0 a, ∀ v ∈ Icc vBar vStar,
      q ≤ 1 - 2 * M (u, v) / R (u, v) := by
    intro u hu v hv
    have hslice : ContinuousOn (fun w => 1 - 2 * M (u, w) / R (u, w))
        (Icc vBar vStar) :=
      hQcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun w hw => ⟨hu, hw⟩)
    have hmap : MapsTo (fun w => 1 - 2 * M (u, w) / R (u, w))
        (Ico vBar vStar) (Ici q) := by
      intro w hw
      let b : ℝ := (w + vStar) / 2
      have hwb : w < b := by dsimp [b]; linarith only [hw.2]
      have hbStar : b < vStar := by dsimp [b]; linarith only [hw.2]
      have hb0 : 0 < b := by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2]
      have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hb0, hbStar⟩
      change q ≤ 1 - 2 * M (u, w) / R (u, w)
      rw [hMmatch b hb u hu w ⟨hw.1, hwb⟩,
        hRmatch b hb u hu w ⟨hw.1, hwb⟩]
      exact hgap b hb u w hu.1
        (hu.2.trans_lt (haBar.trans_le hw.1)) hwb
    have hclosed : closure (Ico vBar vStar) = Icc vBar vStar :=
      closure_Ico hBarStar.ne
    rw [← hclosed] at hslice hv
    have h := hmap.closure_of_continuousOn hslice hv
    simpa only [isClosed_Ici.closure_eq, Set.mem_Ici] using h
  refine ⟨{
    r := R, m := M, lam := L, nu := N, phi := P, zeta := Z,
    alpha := A, theta := T, quotient := H,
    ρ := ρ, c := c, q := q,
    radius_pos := hρ, expansion_pos := hc, gap_pos := hq,
    r_cont := hR, m_cont := hM, lam_cont := hL,
    nu_cont := hN, phi_cont := hP, zeta_cont := hZ,
    alpha_cont := hA, theta_cont := hT, quotient_cont := hH,
    floors := by
      intro u hu v hv
      exact ⟨hRfloor u hu v hv, hLfloor u hu v hv, hQfloor u hu v hv⟩,
    match_old := by
      intro b hb u hu v hv
      have hs := hscalar b hb u hu v hv
      have hn := hNPZ b hb u hu v hv
      exact ⟨hRmatch b hb u hu v hv, hMmatch b hb u hu v hv,
        hs.1, hn.1, hn.2.1, hn.2.2,
        hs.2.2.1, hs.2.2.2, hs.2.1⟩
  }⟩

end ChristodoulouBV.Uniqueness

end
