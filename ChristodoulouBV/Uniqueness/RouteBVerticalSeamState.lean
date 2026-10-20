module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamScalar
public import ChristodoulouBV.C1Solution.RectangleSolution
import Mathlib.Tactic

/-!
# Off-axis seven-state form of a Route B field

The seven-state characteristic rectangle system uses the rescaled scalar `ψ = r φ` as its seventh
coordinate. Physical signs on a Route B piece make this state safe.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- A physical seven-field value in the coordinates used by the off-axis
rectangle ODE. -/
def routeBRectangleState (S : Fields) (p : ℝ × ℝ) :
    C1Solution.RectangleState :=
  ((S.lam p.1 p.2, S.alpha p.1 p.2),
    (S.nu p.1 p.2, (S.beta p.1 p.2,
      (S.m p.1 p.2, (S.r p.1 p.2,
        S.r p.1 p.2 * S.phi p.1 p.2)))))

/-- Positive radius, expansion and mass gap, together with negative
contraction, put the converted state in the open safe set for the rectangle system. -/
theorem routeBRectangleState_safe_of_physical_signs
    (S : Fields) (p : ℝ × ℝ)
    (hr : 0 < S.r p.1 p.2)
    (hl : 0 < S.lam p.1 p.2)
    (hn : S.nu p.1 p.2 < 0)
    (hgap : 0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) :
    C1Solution.IsSafeRectangleState (routeBRectangleState S p) := by
  change 0 < S.r p.1 p.2 ∧ 0 < S.lam p.1 p.2 ∧
    S.nu p.1 p.2 < 0 ∧
      0 < S.r p.1 p.2 - 2 * S.m p.1 p.2
  refine ⟨hr, hl, hn, ?_⟩
  have hproduct := mul_pos hgap hr
  have hidentity :
      (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2 =
        S.r p.1 p.2 - 2 * S.m p.1 p.2 := by
    field_simp [ne_of_gt hr]
  exact hidentity ▸ hproduct

/-- Every physically signed edge value admits a safe cube for the rectangle system centered at
that value. -/
theorem exists_routeB_safeRectangleBox_centered
    (S : Fields) (p : ℝ × ℝ)
    (hr : 0 < S.r p.1 p.2)
    (hl : 0 < S.lam p.1 p.2)
    (hn : S.nu p.1 p.2 < 0)
    (hgap : 0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) :
    ∃ B : C1Solution.SafeRectangleBox,
      B.center = routeBRectangleState S p := by
  let z := routeBRectangleState S p
  have hz : C1Solution.IsSafeRectangleState z :=
    routeBRectangleState_safe_of_physical_signs S p hr hl hn hgap
  rcases hz with ⟨hr', hl', hn', hgap'⟩
  let δ := min (C1Solution.stateRadius z / 2)
    (min (C1Solution.stateLam z / 2)
      (min (-C1Solution.stateNu z / 2)
        (C1Solution.stateMassGap z / 6)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith only [hr'])
      (lt_min (by linarith only [hl'])
        (lt_min (by linarith only [hn'])
          (by linarith only [hgap'])))
  have hrδ : δ ≤ C1Solution.stateRadius z / 2 := min_le_left _ _
  have hlδ : δ ≤ C1Solution.stateLam z / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hnδ : δ ≤ -C1Solution.stateNu z / 2 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hgapδ : δ ≤ C1Solution.stateMassGap z / 6 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨{
    center := z
    radius := δ
    radius_pos := hδ
    radius_margin := by linarith only [hrδ, hr']
    lam_margin := by linarith only [hlδ, hl']
    nu_margin := by linarith only [hnδ, hn']
    gap_margin := by linarith only [hgapδ, hgap']
  }, rfl⟩

end ChristodoulouBV.Uniqueness

end
