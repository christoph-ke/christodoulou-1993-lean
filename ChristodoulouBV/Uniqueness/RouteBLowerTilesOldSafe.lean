module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesOldCharacteristic
import ChristodoulouBV.BVSolution.Signs
import Mathlib.Tactic

/-!
# Safety of the old closed off-axis base

The old family is strictly safe below the terminal edge. Its uniform
expansion bound keeps the limiting incoming expansion strictly negative at
the terminal edge as well.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Every canonical old state in the complete closed off-axis rectangle is
inside the open domain of the characteristic system. -/
theorem OffAxisTerminalC1Packet.safe_on_closed_base
    {a vBar vStar c : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hfloor : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < b → c ≤ (S b).lam u v)
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    C1Solution.IsSafeRectangleState (P.state.rectangleState (u, v)) := by
  have hr := (P.state.floors u hu v hv).1
  have hlam := (P.state.floors u hu v hv).2.1
  have hgap := (P.state.floors u hu v hv).2.2
  have hrpos : 0 < P.state.r (u, v) :=
    P.state.radius_pos.trans_le hr
  have hlampos : 0 < P.state.lam (u, v) :=
    P.state.expansion_pos.trans_le hlam
  have hgapRatio : 0 < 1 - 2 * P.state.m (u, v) /
      P.state.r (u, v) := P.state.gap_pos.trans_le hgap
  have hgapMass : 0 < P.state.r (u, v) - 2 * P.state.m (u, v) := by
    have hmul := mul_pos hgapRatio hrpos
    have heq :
        (1 - 2 * P.state.m (u, v) / P.state.r (u, v)) *
          P.state.r (u, v) =
          P.state.r (u, v) - 2 * P.state.m (u, v) := by
      field_simp [ne_of_gt hrpos]
    simpa only [heq] using hmul
  have hnupos : P.state.nu (u, v) < 0 := by
    by_cases htop : v = vStar
    · subst v
      exact (P.state.nu_le_neg_floor ha haBar hBarStar hc hfamily
        hfloor hu).trans_lt (by linarith only [hc])
    · have hvStar : v < vStar := lt_of_le_of_ne hv.2 htop
      let b : ℝ := (v + vStar) / 2
      have hvb : v < b := by dsimp [b]; linarith only [hvStar]
      have hbStar : b < vStar := by dsimp [b]; linarith only [hvStar]
      have hb0 : 0 < b := by
        dsimp [b]
        linarith only [ha, haBar, hv.1, hvStar]
      have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hb0, hbStar⟩
      have huv : u < v := hu.2.trans_lt (haBar.trans_le hv.1)
      have hBV := (hfamily b hb).1.isBVSolution_development
        (hu.1.trans_lt (huv.trans hvb))
      have hlamB : ∀ p ∈ developmentWithInitialEdge b,
          c ≤ (S b).lam p.1 p.2 := by
        intro p hp
        exact hfloor b hb p.1 p.2 hp.1 hp.2.1 hp.2.2
      have hν : (S b).nu u v ≤ -c :=
        hBV.nu_le_neg_lower hc hlamB ⟨hu.1, huv, hvb⟩
      have hmatch := P.state.match_old b hb u hu v ⟨hv.1, hvb⟩
      have hνold : P.state.nu (u, v) = (S b).nu u v :=
        hmatch.2.2.2.1
      rw [hνold]
      exact hν.trans_lt (by linarith only [hc])
  exact ⟨hrpos, hlampos, hnupos, hgapMass⟩

end ChristodoulouBV.Uniqueness

end
