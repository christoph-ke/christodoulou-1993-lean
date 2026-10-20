module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJetComplete
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Complete continuous segment jets on an axis triangle

The value and full derivative fields are bounded continuous functions on the
closed coordinate triangle. The segment identity is a closed condition in
their product norm.
-/

public section

namespace ChristodoulouBV.AxisPicard

/-- A continuous scalar value and full first jet on the closed axis triangle,
with the segment fundamental-theorem identity. -/
abbrev ScalarJet (a b : ℝ) :=
  {p : BoundedContinuousFunction (closedCoordTriangle a b) ℝ ×
    BoundedContinuousFunction (closedCoordTriangle a b) ((ℝ × ℝ) →L[ℝ] ℝ) //
    (convex_closedCoordTriangle a b).IsContinuousSegmentJet p}

/-- The segment jets form a complete metric space. -/
instance scalarJetComplete (a b : ℝ) : CompleteSpace (ScalarJet a b) :=
  ((convex_closedCoordTriangle a b).isClosed_isContinuousSegmentJet.isComplete).completeSpace_coe

/-- The three continuous first jets iterated by the axis Picard map. -/
abbrev TripleJet (a b : ℝ) := ScalarJet a b × ScalarJet a b × ScalarJet a b

/-- The triple jet space is complete in its product norm. -/
instance tripleJetComplete (a b : ℝ) : CompleteSpace (TripleJet a b) :=
  inferInstance

end ChristodoulouBV.AxisPicard

end
