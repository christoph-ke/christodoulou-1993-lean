module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFields
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Initial-edge data after Route B gluing

The old closed piece supplies the initial data through `vStar`, and the
lower band supplies them from `vStar` to the enlarged endpoint.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Matching the old and lower states preserves the radius and scalar
amplitude data on the entire enlarged initial edge. -/
theorem routeB_clipped_initial_data_of_fields_eqOn
    {a vStar b : ℝ} (ha : 0 < a) (_haStar : a < vStar) (_hStarb : vStar < b)
    (alpha₀ : ℝ → ℝ) (SOld SLow T : Fields)
    (hOld : RouteBFieldsEqOn T SOld (routeBOldRegion a vStar))
    (hLow : RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b))
    (hOldData : ∀ v ∈ Icc (0 : ℝ) vStar,
      SOld.r 0 v = v / 2 ∧ SOld.alpha 0 v = alpha₀ v)
    (hLowData : ∀ v ∈ Icc vStar b,
      SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) :
    ∀ v ∈ Ioo (0 : ℝ) b,
      T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v := by
  intro v hv
  by_cases hbelow : v ≤ vStar
  · have hp : (0, v) ∈ routeBOldRegion a vStar :=
      mem_routeBOldRegion.mpr ⟨le_rfl, ha.le, hv.1.le, hbelow⟩
    have hr := hOld .radius hp
    have hα := hOld .outgoing hp
    change T.r 0 v = SOld.r 0 v at hr
    change T.alpha 0 v = SOld.alpha 0 v at hα
    obtain ⟨hrOld, hαOld⟩ := hOldData v ⟨hv.1.le, hbelow⟩
    exact ⟨hr.trans hrOld, hα.trans hαOld⟩
  · have htop : vStar ≤ v := le_of_not_ge hbelow
    have hp : (0, v) ∈ routeBLowerRegion a vStar b :=
      ⟨⟨le_rfl, ha.le⟩, ⟨htop, hv.2.le⟩⟩
    have hr := hLow .radius hp
    have hα := hLow .outgoing hp
    change T.r 0 v = SLow.r 0 v at hr
    change T.alpha 0 v = SLow.alpha 0 v at hα
    obtain ⟨hrLow, hαLow⟩ := hLowData v ⟨htop, hv.2.le⟩
    exact ⟨hr.trans hrLow, hα.trans hαLow⟩

/-- The seven-field gluing theorem also preserves prescribed initial data
when the old and lower input pieces carry them on their closed edge parts. -/
theorem exists_routeB_clipped_fields_c1_glue_with_initial_data
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (alpha₀ : ℝ → ℝ) (SOld SLow SAx : Fields)
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
      (routeBLowerRegion a vStar b) (closedCoordTriangle a b))
    (hOldData : ∀ v ∈ Icc (0 : ℝ) vStar,
      SOld.r 0 v = v / 2 ∧ SOld.alpha 0 v = alpha₀ v)
    (hLowData : ∀ v ∈ Icc vStar b,
      SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) :
    ∃ T : Fields,
      RouteBFieldsC1On T (closedCoordTriangle 0 b) ∧
      RouteBFieldsEqOn T SOld (routeBOldRegion a vStar) ∧
      RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b) ∧
      RouteBFieldsEqOn T SAx (closedCoordTriangle a b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) := by
  obtain ⟨T, hC1, hMatchOld, hMatchLow, hMatchAx⟩ :=
    exists_routeB_clipped_fields_c1_glue ha haStar hStarb SOld SLow SAx
      hOld hLow hAx hOldLow hOldAx hLowAx
      hJetOldLow hJetOldAx hJetLowAx
  exact ⟨T, hC1, hMatchOld, hMatchLow, hMatchAx,
    routeB_clipped_initial_data_of_fields_eqOn ha haStar hStarb
      alpha₀ SOld SLow T hMatchOld hMatchLow hOldData hLowData⟩

end ChristodoulouBV.Uniqueness

end
