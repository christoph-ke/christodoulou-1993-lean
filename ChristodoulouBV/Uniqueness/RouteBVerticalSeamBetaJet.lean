module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamNuJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The incoming transport transverse jet on the vertical seam

The outgoing equation for `βᵤ` has a source determined by the matched
`νᵤ`, scalar value, scalar incoming jet, and gravitational coefficient jet.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Once the `νᵤ` and scalar incoming jets match, the transverse `β` jets
also agree on the full closed seam. -/
theorem routeB_vertical_beta_horizontal_jet_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRLow : ∀ p ∈ routeBLowerRegion a vStar b, 0 < SLow.r p.1 p.2)
    (hGapLow : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2)
    (hRAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      0 < SAx.r p.1 p.2)
    (hGapAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2)
    (hValues : ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      routeBField SLow c (a, v) = routeBField SAx c (a, v))
    (hPrimaryJets : ∀ c ∈ ({RouteBField.radius, RouteBField.mass,
        RouteBField.expansion} : Set RouteBField),
      ∀ v ∈ Icc vStar b,
        fderivWithin ℝ (routeBField SLow c)
          (routeBLowerRegion a vStar b) (a, v) =
        fderivWithin ℝ (routeBField SAx c)
          (closedCoordTriangle a b) (a, v))
    (hNuJet : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .contraction)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .contraction)
        (closedCoordTriangle a b) (a, v)) (1, 0))
    (hPhiJet : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .scalar)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .scalar)
        (closedCoordTriangle a b) (a, v)) (1, 0))
    (hCorner :
      (fderivWithin ℝ (routeBField SLow .incoming)
        (routeBLowerRegion a vStar b) (a, vStar)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .incoming)
        (closedCoordTriangle a b) (a, vStar)) (1, 0)) :
    ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .incoming)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .incoming)
        (closedCoordTriangle a b) (a, v)) (1, 0) := by
  let KL := routeBLowerRegion a vStar b
  let KA := closedCoordTriangle a b
  let QL : ℝ → ℝ := fun t =>
    (fderivWithin ℝ (routeBField SLow .incoming) KL (a, t)) (1, 0)
  let QA : ℝ → ℝ := fun t =>
    (fderivWithin ℝ (routeBField SAx .incoming) KA (a, t)) (1, 0)
  let F : ℝ → ℝ := fun t =>
    (((fderivWithin ℝ (routeBGravCoefficient SLow) KL (a, t)) (1, 0) *
        SLow.nu a t + routeBGravCoefficient SLow (a, t) *
          (fderivWithin ℝ (routeBField SLow .contraction) KL (a, t)) (1, 0)) *
        SLow.phi a t +
      routeBGravCoefficient SLow (a, t) * SLow.nu a t *
        (fderivWithin ℝ (routeBField SLow .scalar) KL (a, t)) (1, 0))
  have hLU : UniqueDiffOn ℝ KL :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vStar b).2
      (routeBLowerRegion_interior_nonempty ha hStarb)
  have hAU : UniqueDiffOn ℝ KA :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  have hLrne : ∀ p ∈ KL, SLow.r p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hRLow p hp)
  have hLgne : ∀ p ∈ KL,
      SLow.r p.1 p.2 - 2 * SLow.m p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (routeB_mass_gap_pos_of_radius_and_ratio
      (hRLow p hp) (hGapLow p hp))
  have hLCoeffC1 : ContDiffOn ℝ 1 (routeBGravCoefficient SLow) KL :=
    routeB_gravCoefficient_contDiffOn hLowC1 hLrne hLgne
  have hCoeff := routeB_vertical_gravCoefficient_values_and_jets_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1
    hRLow hGapLow hRAx hGapAx
    (fun c hc v hv => hValues c v hv) hPrimaryJets
  have hMapL : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b) KL :=
    fun t ht => ⟨⟨ha.le, le_rfl⟩, ht⟩
  have hMapA : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b) KA :=
    fun t ht => ⟨le_rfl, haStar.le.trans ht.1, ht.2⟩
  have hQLcont : ContinuousOn QL (Icc vStar b) :=
    (((hLowC1 .incoming).continuousOn_fderivWithin hLU (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hQAcont : ContinuousOn QA (Icc vStar b) :=
    (((hAxC1 .incoming).continuousOn_fderivWithin hAU (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn hMapA
  have hAucont : ContinuousOn
      (fun t => (fderivWithin ℝ (routeBGravCoefficient SLow) KL (a, t)) (1, 0))
      (Icc vStar b) :=
    ((hLCoeffC1.continuousOn_fderivWithin hLU (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hAcont : ContinuousOn (fun t => routeBGravCoefficient SLow (a, t))
      (Icc vStar b) :=
    hLCoeffC1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hNucont : ContinuousOn (fun t => SLow.nu a t) (Icc vStar b) :=
    (hLowC1 .contraction).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hPhicont : ContinuousOn (fun t => SLow.phi a t) (Icc vStar b) :=
    (hLowC1 .scalar).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hNuUcont : ContinuousOn
      (fun t => (fderivWithin ℝ (routeBField SLow .contraction) KL (a, t)) (1, 0))
      (Icc vStar b) :=
    (((hLowC1 .contraction).continuousOn_fderivWithin hLU (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hPhiUcont : ContinuousOn
      (fun t => (fderivWithin ℝ (routeBField SLow .scalar) KL (a, t)) (1, 0))
      (Icc vStar b) :=
    (((hLowC1 .scalar).continuousOn_fderivWithin hLU (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn hMapL
  have hFcont : ContinuousOn F (Icc vStar b) :=
    (((hAucont.mul hNucont).add (hAcont.mul hNuUcont)).mul hPhicont).add
      ((hAcont.mul hNucont).mul hPhiUcont)
  have hODE : ∀ v ∈ Ioo vStar b,
      HasDerivAt QL (F v) v ∧ HasDerivAt QA (F v) v := by
    intro v hv
    let RL := Icc (a / 2) a ×ˢ Icc ((vStar + v) / 2) ((v + b) / 2)
    let RA := Icc a ((a + vStar) / 2) ×ˢ
      Icc ((vStar + v) / 2) ((v + b) / 2)
    obtain ⟨huL, hv₀, hv₁, haL, hRLsub, hRLdev⟩ :=
      routeB_lower_local_rectangle_at_vertical_seam ha haStar hv
    obtain ⟨huA, _, _, haA, hRAsub, hRAdev⟩ :=
      routeB_axis_local_rectangle_at_vertical_seam ha haStar hv
    have hRLU : UniqueDiffOn ℝ RL :=
      routeB_uniqueDiffOn_closed_rectangle huL (hv₀.trans hv₁)
    have hRAU : UniqueDiffOn ℝ RA :=
      routeB_uniqueDiffOn_closed_rectangle huA (hv₀.trans hv₁)
    have hpRL : (a, v) ∈ RL := ⟨haL, ⟨hv₀.le, hv₁.le⟩⟩
    have hpRA : (a, v) ∈ RA := ⟨haA, ⟨hv₀.le, hv₁.le⟩⟩
    have hpL : (a, v) ∈ KL := hRLsub hpRL
    have hpA : (a, v) ∈ KA := hRAsub hpRA
    have hOffRA (p : ℝ × ℝ) (hp : p ∈ RA) : p.1 < p.2 := by
      have hc : (a + vStar) / 2 < vStar := by linarith only [haStar]
      have hvStar₀ : vStar < (vStar + v) / 2 := by linarith only [hv.1]
      exact hp.1.2.trans_lt (hc.trans (hvStar₀.trans_le hp.2.1))
    have hRLr : ∀ p ∈ RL, SLow.r p.1 p.2 ≠ 0 :=
      fun p hp => hLrne p (hRLsub hp)
    have hRLg : ∀ p ∈ RL,
        SLow.r p.1 p.2 - 2 * SLow.m p.1 p.2 ≠ 0 :=
      fun p hp => hLgne p (hRLsub hp)
    have hRAr : ∀ p ∈ RA, SAx.r p.1 p.2 ≠ 0 :=
      fun p hp => ne_of_gt (hRAx p (hRAsub hp) (hOffRA p hp))
    have hRAg : ∀ p ∈ RA,
        SAx.r p.1 p.2 - 2 * SAx.m p.1 p.2 ≠ 0 := by
      intro p hp
      exact ne_of_gt (routeB_mass_gap_pos_of_radius_and_ratio
        (hRAx p (hRAsub hp) (hOffRA p hp))
        (hGapAx p (hRAsub hp) (hOffRA p hp)))
    have hALocalL := fderivWithin_subset hRLsub (hRLU (a, v) hpRL)
      (hLCoeffC1.differentiableOn (by norm_num) (a, v) hpL)
    have hLocalField (c : RouteBField)
        (hc : c ∈ ({RouteBField.radius, RouteBField.mass,
            RouteBField.expansion} : Set RouteBField)) :
        fderivWithin ℝ (routeBField SLow c) RL (a, v) =
        fderivWithin ℝ (routeBField SAx c) RA (a, v) := by
      have hRestrL := fderivWithin_subset hRLsub (hRLU (a, v) hpRL)
        ((hLowC1 c).differentiableOn (by norm_num) (a, v) hpL)
      have hRestrA := fderivWithin_subset hRAsub (hRAU (a, v) hpRA)
        ((hAxC1 c).differentiableOn (by norm_num) (a, v) hpA)
      exact hRestrL.trans ((hPrimaryJets c hc v ⟨hv.1.le, hv.2.le⟩).trans
        hRestrA.symm)
    have hALocal : fderivWithin ℝ (routeBGravCoefficient SLow) RL (a, v) =
        fderivWithin ℝ (routeBGravCoefficient SAx) RA (a, v) :=
      routeB_gravCoefficient_jet_eq_of_primary_jets
        (hRLU (a, v) hpRL) (hRAU (a, v) hpRA)
        (fun c => (hLowC1 c).mono hRLsub)
        (fun c => (hAxC1 c).mono hRAsub)
        hpRL hpRA
        (by simpa only [routeBField] using hValues .radius v ⟨hv.1.le, hv.2.le⟩)
        (by simpa only [routeBField] using hValues .mass v ⟨hv.1.le, hv.2.le⟩)
        (by simpa only [routeBField] using hValues .expansion v ⟨hv.1.le, hv.2.le⟩)
        (hLocalField .radius (by simp))
        (hLocalField .mass (by simp))
        (hLocalField .expansion (by simp))
        (hRLr (a, v) hpRL) (hRLg (a, v) hpRL)
    have hLocalCoeffL := congrArg
      (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0)) hALocalL
    have hLocalCoeff := congrArg
      (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0)) hALocal
    have hODEL := routeB_beta_horizontal_jet_hasDerivAt_linear_local
      huL hv₀ hv₁ haL hRLsub hRLdev hLU hLowC1 hLowJet hRLr hRLg
    have hODEA := routeB_beta_horizontal_jet_hasDerivAt_linear_local
      huA hv₀ hv₁ haA hRAsub hRAdev hAU hAxC1 hAxJet hRAr hRAg
    constructor
    · change HasDerivAt QL
        (((fderivWithin ℝ (routeBGravCoefficient SLow) RL (a, v)) (1, 0) *
            SLow.nu a v + routeBGravCoefficient SLow (a, v) *
              (fderivWithin ℝ (routeBField SLow .contraction) KL (a, v)) (1, 0)) *
            SLow.phi a v + routeBGravCoefficient SLow (a, v) * SLow.nu a v *
              (fderivWithin ℝ (routeBField SLow .scalar) KL (a, v)) (1, 0)) v
          at hODEL
      rw [hLocalCoeffL] at hODEL
      exact hODEL
    · change HasDerivAt QA
        (((fderivWithin ℝ (routeBGravCoefficient SAx) RA (a, v)) (1, 0) *
            SAx.nu a v + routeBGravCoefficient SAx (a, v) *
              (fderivWithin ℝ (routeBField SAx .contraction) KA (a, v)) (1, 0)) *
            SAx.phi a v + routeBGravCoefficient SAx (a, v) * SAx.nu a v *
              (fderivWithin ℝ (routeBField SAx .scalar) KA (a, v)) (1, 0)) v
          at hODEA
      rw [← hLocalCoeff, hLocalCoeffL,
        ← hCoeff.1 v ⟨hv.1.le, hv.2.le⟩] at hODEA
      have hNu : SLow.nu a v = SAx.nu a v := by
        simpa only [routeBField] using hValues .contraction v ⟨hv.1.le, hv.2.le⟩
      have hPhi : SLow.phi a v = SAx.phi a v := by
        simpa only [routeBField] using hValues .scalar v ⟨hv.1.le, hv.2.le⟩
      rw [← hNu, ← hPhi, ← hNuJet v ⟨hv.1.le, hv.2.le⟩,
        ← hPhiJet v ⟨hv.1.le, hv.2.le⟩] at hODEA
      exact hODEA
  have hEq := C1Solution.edge_jets_eq_of_linear_ode_on_open hStarb
    hQLcont hQAcont (A := fun _ => 0) (B := F)
    continuousOn_const hFcont
    (fun v hv => by simpa using (hODE v hv).1)
    (fun v hv => by simpa using (hODE v hv).2) hCorner
  exact hEq

end ChristodoulouBV.Uniqueness

end
