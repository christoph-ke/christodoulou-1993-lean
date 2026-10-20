module

public import ChristodoulouBV.Uniqueness.RouteBGluing
public import ChristodoulouBV.Frozen.Fields
public import ChristodoulouBV.Frozen.FieldsTheta
public import ChristodoulouBV.Frozen.FieldsZeta

/-!
# Seven-field C¹ gluing for the Route B cover

The seven scalar closed-jet glues are assembled into one `Fields` value. The
input old fields are the canonical closed-region extension, rather than an
individual old family member on a strict terminal cutoff.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The seven primary scalar coordinates of a reduced field. -/
inductive RouteBField where
  | radius | scalar | mass | expansion | contraction | outgoing | incoming
  deriving DecidableEq

/-- Select a scalar coordinate, as a function of the double-null point. -/
@[expose] def routeBField (S : Fields) : RouteBField → ℝ × ℝ → ℝ
  | .radius => fun p => S.r p.1 p.2
  | .scalar => fun p => S.phi p.1 p.2
  | .mass => fun p => S.m p.1 p.2
  | .expansion => fun p => S.lam p.1 p.2
  | .contraction => fun p => S.nu p.1 p.2
  | .outgoing => fun p => S.alpha p.1 p.2
  | .incoming => fun p => S.beta p.1 p.2

/-- Relative C¹ regularity of all seven primary fields on one closed region. -/
@[expose] def RouteBFieldsC1On (S : Fields) (K : Set (ℝ × ℝ)) : Prop :=
  ∀ c : RouteBField, ContDiffOn ℝ 1 (routeBField S c) K

/-- Agreement of all seven primary field values on a set. -/
@[expose] def RouteBFieldsEqOn (S T : Fields) (K : Set (ℝ × ℝ)) : Prop :=
  ∀ c : RouteBField, EqOn (routeBField S c) (routeBField T c) K

/-- Agreement of all seven relative full first jets on an intersection. -/
@[expose] def RouteBFieldsJetEqOn (S T : Fields)
    (KS KT : Set (ℝ × ℝ)) : Prop :=
  ∀ c : RouteBField,
    EqOn (fderivWithin ℝ (routeBField S c) KS)
      (fderivWithin ℝ (routeBField T c) KT) (KS ∩ KT)

/-- Build a reduced state from seven scalar coordinate functions. -/
@[expose] def routeBFieldsOfComponents
    (f : RouteBField → ℝ × ℝ → ℝ) : Fields where
  r u v := f .radius (u, v)
  phi u v := f .scalar (u, v)
  m u v := f .mass (u, v)
  lam u v := f .expansion (u, v)
  nu u v := f .contraction (u, v)
  alpha u v := f .outgoing (u, v)
  beta u v := f .incoming (u, v)

/-- Component selection in a state assembled from scalar functions. -/
theorem routeBField_ofComponents
    (f : RouteBField → ℝ × ℝ → ℝ) (c : RouteBField) :
    routeBField (routeBFieldsOfComponents f) c = f c := by
  cases c <;> rfl

/-- The two derived scalar amplitudes inherit C¹ regularity from the seven
primary fields. These are precisely the remaining regularity fields in the
frozen `IsC1Solution` predicate. -/
theorem RouteBFieldsC1On.theta_zeta
    {S : Fields} {K : Set (ℝ × ℝ)} (hS : RouteBFieldsC1On S K) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.zeta p.1 p.2) K := by
  constructor
  · simpa only [routeBField, Fields.theta] using
      (hS .outgoing).sub ((hS .expansion).mul (hS .scalar))
  · simpa only [routeBField, Fields.zeta] using
      (hS .incoming).sub ((hS .contraction).mul (hS .scalar))

/-- If all seven values and full relative jets match at each of the three
pairwise overlaps, there is one seven-field state C¹ on `K_{0,b}` which
agrees with each given state on its closed piece. -/
theorem exists_routeB_fields_c1_glue
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx : Fields)
    (hOld : RouteBFieldsC1On SOld (closedCoordTriangle 0 vStar))
    (hLow : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hOldLow : RouteBFieldsEqOn SOld SLow
      (closedCoordTriangle 0 vStar ∩ routeBLowerRegion a vStar b))
    (hOldAx : RouteBFieldsEqOn SOld SAx
      (closedCoordTriangle 0 vStar ∩ closedCoordTriangle a b))
    (hLowAx : RouteBFieldsEqOn SLow SAx
      (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b))
    (hJetOldLow : RouteBFieldsJetEqOn SOld SLow
      (closedCoordTriangle 0 vStar) (routeBLowerRegion a vStar b))
    (hJetOldAx : RouteBFieldsJetEqOn SOld SAx
      (closedCoordTriangle 0 vStar) (closedCoordTriangle a b))
    (hJetLowAx : RouteBFieldsJetEqOn SLow SAx
      (routeBLowerRegion a vStar b) (closedCoordTriangle a b)) :
    ∃ T : Fields,
      RouteBFieldsC1On T (closedCoordTriangle 0 b) ∧
      RouteBFieldsEqOn T SOld (closedCoordTriangle 0 vStar) ∧
      RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b) ∧
      RouteBFieldsEqOn T SAx (closedCoordTriangle a b) := by
  have hglue (c : RouteBField) :
      ∃ f : ℝ × ℝ → ℝ,
        ContDiffOn ℝ 1 f (closedCoordTriangle 0 b) ∧
        EqOn f (routeBField SOld c) (closedCoordTriangle 0 vStar) ∧
        EqOn f (routeBField SLow c) (routeBLowerRegion a vStar b) ∧
        EqOn f (routeBField SAx c) (closedCoordTriangle a b) :=
    exists_routeB_scalar_glue ha haStar hStarb
      (routeBField SOld c) (routeBField SLow c) (routeBField SAx c)
      (hOld c) (hLow c) (hAx c)
      (hOldLow c) (hOldAx c) (hLowAx c)
      (hJetOldLow c) (hJetOldAx c) (hJetLowAx c)
  let f : RouteBField → ℝ × ℝ → ℝ := fun c => Classical.choose (hglue c)
  let T := routeBFieldsOfComponents f
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).1
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).2.1
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).2.2.1
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).2.2.2

end ChristodoulouBV.Uniqueness

end
