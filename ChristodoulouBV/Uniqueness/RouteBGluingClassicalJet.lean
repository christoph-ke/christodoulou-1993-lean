module

public import ChristodoulouBV.Uniqueness.RouteBGluingExpression

/-!
# Classical reduced equations as relative jets on a closed piece

These equations are the classical derivative identities passed to
`C1Solution.isSolution_and_isC1Solution_of_classical`. Relative jets are
used so they retain a precise value on the closed seams.
-/

@[expose] public section

noncomputable section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Select one primary field from a seven-value state. -/
def routeBSelector (c : RouteBField) (x : RouteBField → ℝ) : ℝ := x c

/-- The derived outgoing amplitude as a pointwise seven-field expression. -/
def routeBThetaExpr (x : RouteBField → ℝ) : ℝ :=
  x .outgoing - x .expansion * x .scalar

/-- The derived incoming amplitude as a pointwise seven-field expression. -/
def routeBZetaExpr (x : RouteBField → ℝ) : ℝ :=
  x .incoming - x .contraction * x .scalar

/-- The common mixed coefficient in the classical reduced system. -/
def routeBMixedExpr (x : RouteBField → ℝ) : ℝ :=
  ((2 * x .mass / x .radius) * x .expansion * x .contraction) /
    ((1 - 2 * x .mass / x .radius) * x .radius)

/-- The outgoing mass derivative in the classical system. -/
def routeBMassOutgoingExpr (x : RouteBField → ℝ) : ℝ :=
  (1 - 2 * x .mass / x .radius) * (routeBThetaExpr x) ^ 2 /
    (2 * x .expansion)

/-- The incoming mass derivative in the classical system. -/
def routeBMassIncomingExpr (x : RouteBField → ℝ) : ℝ :=
  (1 - 2 * x .mass / x .radius) * (routeBZetaExpr x) ^ 2 /
    (2 * x .contraction)

/-- The incoming derivative of the outgoing scalar amplitude. -/
def routeBThetaIncomingExpr (x : RouteBField → ℝ) : ℝ :=
  -(x .expansion / x .radius * routeBZetaExpr x)

/-- The outgoing derivative of the incoming scalar amplitude. -/
def routeBZetaOutgoingExpr (x : RouteBField → ℝ) : ℝ :=
  -(x .contraction / x .radius * routeBThetaExpr x)

/-- The common mixed coefficient multiplied by the scalar field. -/
def routeBMixedScalarExpr (x : RouteBField → ℝ) : ℝ :=
  routeBMixedExpr x * x .scalar

/-- One ordinary classical equation expressed by its unique relative first
jet on a closed region. The equation is required only in the enlarged open
development, where denominators and ordinary slice derivatives are used. -/
def RouteBLocalJetEquation (b : ℝ) (K : Set (ℝ × ℝ)) (S : Fields)
    (E rhs : (RouteBField → ℝ) → ℝ) (direction : ℝ × ℝ) : Prop :=
  ∀ p ∈ K, p ∈ developmentWithInitialEdge b →
    (fderivWithin ℝ (routeBScalarExpression E S) K p) direction =
      rhs (fun c => routeBField S c p)

/-- The twelve classical reduced equations on one closed piece, with full
relative first jets specified at all points meeting the open development.
This is a property of a given piece, not a new existence assumption. -/
structure RouteBClassicalJetOn (b : ℝ) (K : Set (ℝ × ℝ))
    (S : Fields) : Prop where
  radius_out : RouteBLocalJetEquation b K S
    (routeBSelector .radius) (routeBSelector .expansion) (0, 1)
  radius_in : RouteBLocalJetEquation b K S
    (routeBSelector .radius) (routeBSelector .contraction) (1, 0)
  scalar_radius_out : RouteBLocalJetEquation b K S
    routeBScalarRadiusExpr (routeBSelector .outgoing) (0, 1)
  scalar_radius_in : RouteBLocalJetEquation b K S
    routeBScalarRadiusExpr (routeBSelector .incoming) (1, 0)
  mass_out : RouteBLocalJetEquation b K S
    (routeBSelector .mass) routeBMassOutgoingExpr (0, 1)
  mass_in : RouteBLocalJetEquation b K S
    (routeBSelector .mass) routeBMassIncomingExpr (1, 0)
  expansion_in : RouteBLocalJetEquation b K S
    (routeBSelector .expansion) routeBMixedExpr (1, 0)
  contraction_out : RouteBLocalJetEquation b K S
    (routeBSelector .contraction) routeBMixedExpr (0, 1)
  theta_in : RouteBLocalJetEquation b K S
    routeBThetaExpr routeBThetaIncomingExpr (1, 0)
  zeta_out : RouteBLocalJetEquation b K S
    routeBZetaExpr routeBZetaOutgoingExpr (0, 1)
  outgoing_in : RouteBLocalJetEquation b K S
    (routeBSelector .outgoing) routeBMixedScalarExpr (1, 0)
  incoming_out : RouteBLocalJetEquation b K S
    (routeBSelector .incoming) routeBMixedScalarExpr (0, 1)

end ChristodoulouBV.Uniqueness

end
