module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamCoefficientJet
public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamLocalSlices
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Matching the gravitational coefficient on the vertical seam

A fixed thin rectangle inside the axis triangle stays away from the axis.
The coefficient and its incoming jet can therefore be compared there with
the coefficient on the full lower band.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The fixed thin axis-side rectangle is contained in the off-axis part of
the axis triangle. -/
theorem routeB_axis_seam_strip_subset
    {a vStar b : ℝ} (haStar : a < vStar) :
    Icc a ((a + vStar) / 2) ×ˢ Icc vStar b ⊆
      closedCoordTriangle a b := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  change a ≤ u ∧ u ≤ v ∧ v ≤ b
  refine ⟨hu.1, ?_, hv.2⟩
  have hc : (a + vStar) / 2 < vStar := by linarith only [haStar]
  exact (hu.2.trans_lt hc).le.trans hv.1

/-- The coefficient `A = 2mλ/(r(r-2m))` and its incoming relative jet
agree on the closed seam when the radius, mass, and expansion values and
full jets agree. The axis coefficient jet is read on a safe thin strip. -/
theorem routeB_vertical_gravCoefficient_values_and_jets_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hRLow : ∀ p ∈ routeBLowerRegion a vStar b, 0 < SLow.r p.1 p.2)
    (hGapLow : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2)
    (hRAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      0 < SAx.r p.1 p.2)
    (hGapAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2)
    (hValues : ∀ c ∈ ({RouteBField.radius, RouteBField.mass,
        RouteBField.expansion} : Set RouteBField),
      ∀ v ∈ Icc vStar b,
        routeBField SLow c (a, v) = routeBField SAx c (a, v))
    (hJets : ∀ c ∈ ({RouteBField.radius, RouteBField.mass,
        RouteBField.expansion} : Set RouteBField),
      ∀ v ∈ Icc vStar b,
        fderivWithin ℝ (routeBField SLow c)
          (routeBLowerRegion a vStar b) (a, v) =
        fderivWithin ℝ (routeBField SAx c)
          (closedCoordTriangle a b) (a, v)) :
    (∀ v ∈ Icc vStar b,
      routeBGravCoefficient SLow (a, v) =
        routeBGravCoefficient SAx (a, v)) ∧
    (∀ v ∈ Icc vStar b,
      fderivWithin ℝ (routeBGravCoefficient SLow)
        (routeBLowerRegion a vStar b) (a, v) =
      fderivWithin ℝ (routeBGravCoefficient SAx)
        (Icc a ((a + vStar) / 2) ×ˢ Icc vStar b) (a, v)) := by
  let KL := routeBLowerRegion a vStar b
  let KA := closedCoordTriangle a b
  let R := Icc a ((a + vStar) / 2) ×ˢ Icc vStar b
  have hRsub : R ⊆ KA := routeB_axis_seam_strip_subset haStar
  have hRUnique : UniqueDiffOn ℝ R :=
    routeB_uniqueDiffOn_closed_rectangle (by linarith only [haStar]) hStarb
  have hLUnique : UniqueDiffOn ℝ KL :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vStar b).2
      (routeBLowerRegion_interior_nonempty ha hStarb)
  have hAUnique : UniqueDiffOn ℝ KA :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  have hRC1 : RouteBFieldsC1On SAx R :=
    fun c => (hAxC1 c).mono hRsub
  have hLradiusNe : ∀ p ∈ KL, SLow.r p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hRLow p hp)
  have hLgapNe : ∀ p ∈ KL,
      SLow.r p.1 p.2 - 2 * SLow.m p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (routeB_mass_gap_pos_of_radius_and_ratio
      (hRLow p hp) (hGapLow p hp))
  have hRradiusNe : ∀ p ∈ R, SAx.r p.1 p.2 ≠ 0 := by
    intro p hp
    have hOff : p.1 < p.2 := by
      have hc : (a + vStar) / 2 < vStar := by linarith only [haStar]
      exact hp.1.2.trans_lt (hc.trans_le hp.2.1)
    exact ne_of_gt (hRAx p (hRsub hp) hOff)
  have hRgapNe : ∀ p ∈ R,
      SAx.r p.1 p.2 - 2 * SAx.m p.1 p.2 ≠ 0 := by
    intro p hp
    have hOff : p.1 < p.2 := by
      have hc : (a + vStar) / 2 < vStar := by linarith only [haStar]
      exact hp.1.2.trans_lt (hc.trans_le hp.2.1)
    exact ne_of_gt (routeB_mass_gap_pos_of_radius_and_ratio
      (hRAx p (hRsub hp) hOff) (hGapAx p (hRsub hp) hOff))
  have hLCoeffC1 : ContDiffOn ℝ 1 (routeBGravCoefficient SLow) KL :=
    routeB_gravCoefficient_contDiffOn hLowC1 hLradiusNe hLgapNe
  have hRCoeffC1 : ContDiffOn ℝ 1 (routeBGravCoefficient SAx) R :=
    routeB_gravCoefficient_contDiffOn hRC1 hRradiusNe hRgapNe
  constructor
  · intro v hv
    have hr := hValues .radius (by simp) v hv
    have hm := hValues .mass (by simp) v hv
    have hl := hValues .expansion (by simp) v hv
    change SLow.r a v = SAx.r a v at hr
    change SLow.m a v = SAx.m a v at hm
    change SLow.lam a v = SAx.lam a v at hl
    change 2 * SLow.m a v * SLow.lam a v /
        (SLow.r a v * (SLow.r a v - 2 * SLow.m a v)) =
      2 * SAx.m a v * SAx.lam a v /
        (SAx.r a v * (SAx.r a v - 2 * SAx.m a v))
    rw [hr, hm, hl]
  · intro v hv
    have hpL : (a, v) ∈ KL := ⟨⟨ha.le, le_rfl⟩, hv⟩
    have hpR : (a, v) ∈ R :=
      ⟨⟨le_rfl, by linarith only [haStar]⟩, hv⟩
    have hpA : (a, v) ∈ KA := hRsub hpR
    have hRestr (c : RouteBField) :
        fderivWithin ℝ (routeBField SAx c) R (a, v) =
        fderivWithin ℝ (routeBField SAx c) KA (a, v) :=
      fderivWithin_subset hRsub (hRUnique (a, v) hpR)
        ((hAxC1 c).differentiableOn (by norm_num) (a, v) hpA)
    have hFull (c : RouteBField)
        (hc : c ∈ ({RouteBField.radius, RouteBField.mass,
            RouteBField.expansion} : Set RouteBField)) :
        fderivWithin ℝ (routeBField SLow c) KL (a, v) =
        fderivWithin ℝ (routeBField SAx c) R (a, v) :=
      (hJets c hc v hv).trans (hRestr c).symm
    exact routeB_gravCoefficient_jet_eq_of_primary_jets
      (hLUnique (a, v) hpL) (hRUnique (a, v) hpR)
      hLowC1 hRC1 hpL hpR
      (hValues .radius (by simp) v hv)
      (hValues .mass (by simp) v hv)
      (hValues .expansion (by simp) v hv)
      (hFull .radius (by simp))
      (hFull .mass (by simp))
      (hFull .expansion (by simp))
      (hLradiusNe (a, v) hpL) (hLgapNe (a, v) hpL)

end ChristodoulouBV.Uniqueness

end
