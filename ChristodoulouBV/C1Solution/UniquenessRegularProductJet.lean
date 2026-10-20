module

public import ChristodoulouBV.C1Solution.UniquenessCoefficientValue
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing jet of the regular product

The equation `ν_v = K_g` fixes the product jet needed after the value
estimate for `K_g` has been established.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The outgoing relative jet of `λν` is
`λ_v ν + λ K_g` on the whole closed triangle. -/
theorem canonical_lam_nu_vertical_jet_eq
    {b T : ℝ} (hT : 0 < T) (hTb : T < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    (fderivWithin ℝ
      (fun q : ℝ × ℝ => S.lam q.1 q.2 * S.nu q.1 q.2)
      (closedCoordTriangle 0 T) p) (0, 1) =
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1) * S.nu p.1 p.2 +
      S.lam p.1 p.2 * canonicalMixedCoefficient b S p := by
  let K := closedCoordTriangle 0 T
  let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let z : ℝ × ℝ → ℝ := fun q => S.nu q.1 q.2
  have hfields := five_fields_contDiffOn hT hTb H
  have hunique : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hT)) p hp
  change (fderivWithin ℝ (fun q => w q * z q) K p) (0, 1) = _
  rw [fderivWithin_fun_mul hunique
    ((hfields.1.differentiableOn (by norm_num)) p hp)
    ((hfields.2.1.differentiableOn (by norm_num)) p hp)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [(four_mixed_coordinate_jets hT hTb H hp).2.1]
  ring

end ChristodoulouBV.C1Solution

end
