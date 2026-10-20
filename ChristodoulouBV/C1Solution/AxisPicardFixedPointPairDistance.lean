module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairNu
import all ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedCoordTriangleJetDistance
import Mathlib.Tactic

/-! # Coordinate distance bound for two Picard outputs -/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Pointwise value and coordinate derivative estimates bound the uniform
sum distance of two first jets. -/
theorem coordinateJetDistanceOn_le_of_bounds {K : Set (ℝ × ℝ)}
    (hne : K.Nonempty) {f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    {A₀ A₁ A₂ : ℝ}
    (h₀ : ∀ p ∈ K, |f₁ p - f₂ p| ≤ A₀)
    (h₁ : ∀ p ∈ K, |G₁ p (1, 0) - G₂ p (1, 0)| ≤ A₁)
    (h₂ : ∀ p ∈ K, |G₁ p (0, 1) - G₂ p (0, 1)| ≤ A₂) :
    coordinateJetDistanceOn K f₁ f₂ G₁ G₂ ≤ A₀ + A₁ + A₂ := by
  have hs₀ : uniformAbsOn K (f₁ - f₂) ≤ A₀ := by
    apply csSup_le (hne.image (fun p => |(f₁ - f₂) p|))
    rintro z ⟨p, hp, rfl⟩
    simpa only [Pi.sub_apply] using h₀ p hp
  have hs₁ : uniformAbsOn K (fun p => G₁ p (1, 0) - G₂ p (1, 0)) ≤ A₁ := by
    apply csSup_le (hne.image
      (fun p => |G₁ p (1, 0) - G₂ p (1, 0)|))
    rintro z ⟨p, hp, rfl⟩
    exact h₁ p hp
  have hs₂ : uniformAbsOn K (fun p => G₁ p (0, 1) - G₂ p (0, 1)) ≤ A₂ := by
    apply csSup_le (hne.image
      (fun p => |G₁ p (0, 1) - G₂ p (0, 1)|))
    rintro z ⟨p, hp, rfl⟩
    exact h₂ p hp
  dsimp only [coordinateJetDistanceOn]
  linarith

/-- The outgoing component of two Picard outputs has a uniform coordinate
distance bound. -/
theorem Box.picard_lam_coordinateDistance_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.picardJets D hab hM hsmall).1.coordinateDistance
      (y.picardJets D hab hM hsmall).1 ≤
      (numericalLedger M).KΔ₀ * (b - a) ^ 2 *
        x.1.coordinateDistance y.1 +
      2 * ((numericalLedger M).KΔ₀ + (numericalLedger M).KΔ₁) *
        (b - a) * x.1.coordinateDistance y.1 := by
  let K := closedCoordTriangle a b
  let F := (x.picardJets D hab hM hsmall).1
  let G := (y.picardJets D hab hM hsmall).1
  have hne : K.Nonempty := by
    let aa : Icc a b := ⟨a, le_refl _, hab.le⟩
    exact ⟨(edgePoint aa).1, (edgePoint aa).2⟩
  have h := coordinateJetDistanceOn_le_of_bounds hne
    (f₁ := F.extendValue) (f₂ := G.extendValue)
    (G₁ := F.extendDerivative) (G₂ := G.extendDerivative)
    (A₀ := (numericalLedger M).KΔ₀ * (b - a) ^ 2 * x.1.coordinateDistance y.1)
    (A₁ := ((numericalLedger M).KΔ₀ + (numericalLedger M).KΔ₁) *
      (b - a) * x.1.coordinateDistance y.1)
    (A₂ := ((numericalLedger M).KΔ₀ + (numericalLedger M).KΔ₁) *
      (b - a) * x.1.coordinateDistance y.1) ?_ ?_ ?_
  · change coordinateJetDistanceOn K F.extendValue G.extendValue
      F.extendDerivative G.extendDerivative ≤ _
    nlinarith only [h]
  · intro p hp
    rw [F.extendValue_eq hp, G.extendValue_eq hp]
    change |(x.1.toTriple.picard a g hEdge).lam p -
      (y.1.toTriple.picard a g hEdge).lam p| ≤ _
    exact x.picard_lam_value_sub_bound y hab hM hsmall hp
  · intro p hp
    rw [F.extendDerivative_eq hp, G.extendDerivative_eq hp]
    change |(x.picardJets D hab hM hsmall).1.1.2 ⟨p, hp⟩ (1, 0) -
      (y.picardJets D hab hM hsmall).1.1.2 ⟨p, hp⟩ (1, 0)| ≤ _
    exact x.picard_lam_coordinate_sub_bound D y hab hM hsmall ⟨p, hp⟩ 0
  · intro p hp
    rw [F.extendDerivative_eq hp, G.extendDerivative_eq hp]
    change |(x.picardJets D hab hM hsmall).1.1.2 ⟨p, hp⟩ (0, 1) -
      (y.picardJets D hab hM hsmall).1.1.2 ⟨p, hp⟩ (0, 1)| ≤ _
    exact x.picard_lam_coordinate_sub_bound D y hab hM hsmall ⟨p, hp⟩ 1

/-- The incoming component of two Picard outputs has a uniform coordinate
distance bound. -/
theorem Box.picard_nu_coordinateDistance_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.picardJets D hab hM hsmall).2.1.coordinateDistance
      (y.picardJets D hab hM hsmall).2.1 ≤
      2 * (numericalLedger M).KΔ₀ * (b - a) ^ 2 *
        x.1.coordinateDistance y.1 +
      (2 * (numericalLedger M).KΔ₀ + 3 * (numericalLedger M).KΔ₁) *
        (b - a) * x.1.coordinateDistance y.1 +
      (numericalLedger M).KΔ₀ * (b - a) *
        x.1.coordinateDistance y.1 := by
  let K := closedCoordTriangle a b
  let F := (x.picardJets D hab hM hsmall).2.1
  let G := (y.picardJets D hab hM hsmall).2.1
  have hne : K.Nonempty := by
    let aa : Icc a b := ⟨a, le_refl _, hab.le⟩
    exact ⟨(edgePoint aa).1, (edgePoint aa).2⟩
  have h := coordinateJetDistanceOn_le_of_bounds hne
    (f₁ := F.extendValue) (f₂ := G.extendValue)
    (G₁ := F.extendDerivative) (G₂ := G.extendDerivative)
    (A₀ := 2 * (numericalLedger M).KΔ₀ * (b - a) ^ 2 *
      x.1.coordinateDistance y.1)
    (A₁ := (2 * (numericalLedger M).KΔ₀ +
      3 * (numericalLedger M).KΔ₁) * (b - a) * x.1.coordinateDistance y.1)
    (A₂ := (numericalLedger M).KΔ₀ * (b - a) *
      x.1.coordinateDistance y.1) ?_ ?_ ?_
  · change coordinateJetDistanceOn K F.extendValue G.extendValue
      F.extendDerivative G.extendDerivative ≤ _
    exact h
  · intro p hp
    rw [F.extendValue_eq hp, G.extendValue_eq hp]
    change |(x.1.toTriple.picard a g hEdge).nu p -
      (y.1.toTriple.picard a g hEdge).nu p| ≤ _
    exact x.picard_nu_value_sub_bound y hab hM hsmall hp
  · intro p hp
    rw [F.extendDerivative_eq hp, G.extendDerivative_eq hp]
    change |(x.picardJets D hab hM hsmall).2.1.1.2 ⟨p, hp⟩ (1, 0) -
      (y.picardJets D hab hM hsmall).2.1.1.2 ⟨p, hp⟩ (1, 0)| ≤ _
    exact x.picard_nu_horizontal_sub_bound D y hab hM hsmall ⟨p, hp⟩
  · intro p hp
    rw [F.extendDerivative_eq hp, G.extendDerivative_eq hp]
    change |(x.picardJets D hab hM hsmall).2.1.1.2 ⟨p, hp⟩ (0, 1) -
      (y.picardJets D hab hM hsmall).2.1.1.2 ⟨p, hp⟩ (0, 1)| ≤ _
    exact x.picard_nu_vertical_sub_bound D y hab hM hsmall ⟨p, hp⟩

/-- The scalar component of two Picard outputs has a uniform coordinate
distance bound. -/
theorem Box.picard_h_coordinateDistance_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.picardJets D hab hM hsmall).2.2.coordinateDistance
      (y.picardJets D hab hM hsmall).2.2 ≤
      (numericalLedger M).QΔ₀ * (b - a) ^ 3 *
        x.1.coordinateDistance y.1 +
      2 * ((numericalLedger M).QΔ₀ + (numericalLedger M).QΔ₁) *
        (b - a) ^ 2 * x.1.coordinateDistance y.1 := by
  let K := closedCoordTriangle a b
  let F := (x.picardJets D hab hM hsmall).2.2
  let G := (y.picardJets D hab hM hsmall).2.2
  have hne : K.Nonempty := by
    let aa : Icc a b := ⟨a, le_refl _, hab.le⟩
    exact ⟨(edgePoint aa).1, (edgePoint aa).2⟩
  have h := coordinateJetDistanceOn_le_of_bounds hne
    (f₁ := F.extendValue) (f₂ := G.extendValue)
    (G₁ := F.extendDerivative) (G₂ := G.extendDerivative)
    (A₀ := (numericalLedger M).QΔ₀ * (b - a) ^ 3 *
      x.1.coordinateDistance y.1)
    (A₁ := ((numericalLedger M).QΔ₀ + (numericalLedger M).QΔ₁) *
      (b - a) ^ 2 * x.1.coordinateDistance y.1)
    (A₂ := ((numericalLedger M).QΔ₀ + (numericalLedger M).QΔ₁) *
      (b - a) ^ 2 * x.1.coordinateDistance y.1) ?_ ?_ ?_
  · change coordinateJetDistanceOn K F.extendValue G.extendValue
      F.extendDerivative G.extendDerivative ≤ _
    nlinarith only [h]
  · intro p hp
    rw [F.extendValue_eq hp, G.extendValue_eq hp]
    change |(x.1.toTriple.picard a g hEdge).h p -
      (y.1.toTriple.picard a g hEdge).h p| ≤ _
    exact x.picard_h_value_sub_bound y hab hM hsmall hp
  · intro p hp
    rw [F.extendDerivative_eq hp, G.extendDerivative_eq hp]
    change |(x.picardJets D hab hM hsmall).2.2.1.2 ⟨p, hp⟩ (1, 0) -
      (y.picardJets D hab hM hsmall).2.2.1.2 ⟨p, hp⟩ (1, 0)| ≤ _
    exact x.picard_h_coordinate_sub_bound D y hab hM hsmall ⟨p, hp⟩ 0
  · intro p hp
    rw [F.extendDerivative_eq hp, G.extendDerivative_eq hp]
    change |(x.picardJets D hab hM hsmall).2.2.1.2 ⟨p, hp⟩ (0, 1) -
      (y.picardJets D hab hM hsmall).2.2.1.2 ⟨p, hp⟩ (0, 1)| ≤ _
    exact x.picard_h_coordinate_sub_bound D y hab hM hsmall ⟨p, hp⟩ 1

end ChristodoulouBV.AxisPicard

end
