module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisPacket
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import Mathlib.Tactic.Linarith

/-!
# A cutoff-independent floor for Route B edge data

The compact construction records a positive floor chosen after the incoming cutoff.
The old-family expansion estimate gives one floor for every cutoff instead.
It passes through the compact edge and both of its endpoints by continuity.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A lower bound on the whole strict old family passes to the compact
characteristic edge, including its terminal endpoint and its axis endpoint. -/
theorem OffAxisTerminalC1Packet.g_ge_of_old_expansion_floor
    {a vBar vStar c : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfloor : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
        c ≤ (S b).lam u v) :
    ∀ v ∈ Icc a vStar, c ≤ P.g v := by
  have haStar : a < vStar := haBar.trans hBarStar
  have hopen : ∀ v ∈ Ioo a vStar, c ≤ P.g v := by
    intro v hv
    by_cases hvt : v ≤ P.t
    · have hvOld : v ∈ Icc a P.t := ⟨hv.1.le, hvt⟩
      rw [(P.old_match v hvOld).1]
      exact hfloor P.b₀ P.b₀_mem a v ha.le hv.1
        (hvt.trans_lt P.t_lt_b₀)
    · have hvBar : vBar ≤ v :=
        (P.vBar_lt_t.trans (lt_of_not_ge hvt)).le
      have hvTop : v ∈ Icc vBar vStar := ⟨hvBar, hv.2.le⟩
      let b : ℝ := (v + vStar) / 2
      have hvb : v < b := by dsimp [b]; linarith only [hv.2]
      have hbStar : b < vStar := by dsimp [b]; linarith only [hv.2]
      have hb : b ∈ Ioo (0 : ℝ) vStar :=
        ⟨ha.trans (hv.1.trans hvb), hbStar⟩
      have haI : a ∈ Icc (0 : ℝ) a := ⟨ha.le, le_rfl⟩
      calc
        c ≤ (S b).lam a v := hfloor b hb a v ha.le hv.1 hvb
        _ = P.state.lam (a, v) :=
          ((P.state.match_old b hb a haI v ⟨hvBar, hvb⟩).2.2.1).symm
        _ = P.g v := ((P.top_match v hvTop).1).symm
  have hclosure : closure (Ioo a vStar) = Icc a vStar :=
    closure_Ioo haStar.ne
  intro v hv
  have hcont : ContinuousOn P.g (Icc a vStar) :=
    P.g_c1.continuousOn
  have h := le_on_closure hopen
    (by rw [hclosure]; exact continuousOn_const)
    (by rw [hclosure]; exact hcont)
    (by rw [hclosure]; exact hv)
  exact h

/-- The expansion floor from the frozen premises works for every compact
Route B edge, irrespective of the chosen incoming cutoff. -/
theorem exists_uniform_routeB_edge_floor
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {a vBar : ℝ} (_ha : 0 < a) (_haBar : a < vBar)
        (_hBarStar : vBar < vStar)
        (P : OffAxisTerminalC1Packet a vBar vStar S),
        ∀ v ∈ Icc a vStar, c ≤ P.g v := by
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε htail
  exact ⟨c, hc, fun ha haBar hBarStar P =>
    P.g_ge_of_old_expansion_floor ha haBar hBarStar hfloor⟩

end ChristodoulouBV.Uniqueness

end
