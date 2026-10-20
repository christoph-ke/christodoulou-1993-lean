module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedScalar
public import ChristodoulouBV.Uniqueness.RouteBGluingFields
public import ChristodoulouBV.Frozen.Fields
public import ChristodoulouBV.Frozen.FieldsTheta
public import ChristodoulouBV.Frozen.FieldsZeta

/-!
# Seven-field C¹ gluing for the corrected Route B cover

The seven scalar closed-jet glues are assembled into one `Fields` value. The
input old fields are the canonical closed-region extension, rather than an
individual old family member on a strict terminal cutoff.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.Uniqueness

/-- If all seven values and full relative jets match at each of the three
pairwise overlaps, there is one seven-field state C¹ on `K_{0,b}` which
agrees with each given state on its closed piece. -/
theorem exists_routeB_clipped_fields_c1_glue
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx : Fields)
    (hOld : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hLow : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hOldLow : RouteBFieldsEqOn SOld SLow
      (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b))
    (hOldAx : RouteBFieldsEqOn SOld SAx
      (routeBOldRegion a vStar ∩ closedCoordTriangle a b))
    (hLowAx : RouteBFieldsEqOn SLow SAx
      (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b))
    (hJetOldLow : RouteBFieldsJetEqOn SOld SLow
      (routeBOldRegion a vStar) (routeBLowerRegion a vStar b))
    (hJetOldAx : RouteBFieldsJetEqOn SOld SAx
      (routeBOldRegion a vStar) (closedCoordTriangle a b))
    (hJetLowAx : RouteBFieldsJetEqOn SLow SAx
      (routeBLowerRegion a vStar b) (closedCoordTriangle a b)) :
    ∃ T : Fields,
      RouteBFieldsC1On T (closedCoordTriangle 0 b) ∧
      RouteBFieldsEqOn T SOld (routeBOldRegion a vStar) ∧
      RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b) ∧
      RouteBFieldsEqOn T SAx (closedCoordTriangle a b) := by
  have hglue (c : RouteBField) :
      ∃ f : ℝ × ℝ → ℝ,
        ContDiffOn ℝ 1 f (closedCoordTriangle 0 b) ∧
        EqOn f (routeBField SOld c) (routeBOldRegion a vStar) ∧
        EqOn f (routeBField SLow c) (routeBLowerRegion a vStar b) ∧
        EqOn f (routeBField SAx c) (closedCoordTriangle a b) :=
    exists_routeB_clipped_scalar_glue ha haStar hStarb
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
