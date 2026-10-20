module

public import ChristodoulouBV.C1Solution.AxisPicardBox
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Triangle-local Picard fixed points

The Picard operator is evaluated only on the closed triangle represented by a box.
-/

@[expose] public section

namespace ChristodoulouBV.AxisPicard

/-- The three Picard components agree with a boxed triple on its closed triangle. -/
def Box.IsTriangleFixedPoint {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) : Prop :=
  Set.EqOn (x.1.toTriple.picard a g hEdge).lam x.1.toTriple.lam
      (closedCoordTriangle a b) ∧
  Set.EqOn (x.1.toTriple.picard a g hEdge).nu x.1.toTriple.nu
      (closedCoordTriangle a b) ∧
  Set.EqOn (x.1.toTriple.picard a g hEdge).h x.1.toTriple.h
      (closedCoordTriangle a b)

end ChristodoulouBV.AxisPicard

end
