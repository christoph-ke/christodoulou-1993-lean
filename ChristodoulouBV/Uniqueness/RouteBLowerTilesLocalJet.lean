module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassicalTransfer
import ChristodoulouBV.C1Solution.RectangleMassConstraintState
import Mathlib.Tactic

/-!
# Coordinate equations on one safe lower tile

Relative C¹ on a nondegenerate closed rectangle makes each coordinate
slice derivative equal the corresponding evaluation of the full first jet.
These helpers retain the equations at edges and corners.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A horizontal slice equation determines the full relative jet in the
incoming direction on a closed rectangle. -/
theorem horizontal_jet_eq_of_slice_derivative
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    {f : ℝ × ℝ → ℝ} {u v d : ℝ}
    (hf : ContDiffOn ℝ 1 f (Goursat.rectangle u₀ u₁ v₀ v₁))
    (hu' : u ∈ Icc u₀ u₁) (hv' : v ∈ Icc v₀ v₁)
    (hderiv : HasDerivWithinAt (fun s => f (s, v)) d
      (Icc u₀ u₁) u) :
    (fderivWithin ℝ f (Goursat.rectangle u₀ u₁ v₀ v₁)
      (u, v)) (1, 0) = d := by
  have hslice :=
    (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
      hu hv hf hu' hv').1
  have hunique := (uniqueDiffOn_Icc hu) u hu'
  exact (hslice.derivWithin hunique).symm.trans
    (hderiv.derivWithin hunique)

/-- A vertical slice equation determines the full relative jet in the
outgoing direction on a closed rectangle. -/
theorem vertical_jet_eq_of_slice_derivative
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    {f : ℝ × ℝ → ℝ} {u v d : ℝ}
    (hf : ContDiffOn ℝ 1 f (Goursat.rectangle u₀ u₁ v₀ v₁))
    (hu' : u ∈ Icc u₀ u₁) (hv' : v ∈ Icc v₀ v₁)
    (hderiv : HasDerivWithinAt (fun t => f (u, t)) d
      (Icc v₀ v₁) v) :
    (fderivWithin ℝ f (Goursat.rectangle u₀ u₁ v₀ v₁)
      (u, v)) (0, 1) = d := by
  have hslice :=
    (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
      hu hv hf hu' hv').2
  have hunique := (uniqueDiffOn_Icc hv) v hv'
  exact (hslice.derivWithin hunique).symm.trans
    (hderiv.derivWithin hunique)

/-- The classical mixed coefficient is the rational coefficient used by
the safe rectangle solver. -/
theorem mixed_coefficient_eq_rectangle_grav
    {r m lam nu : ℝ} (hr : r ≠ 0) (hgap : r - 2 * m ≠ 0) :
    ((2 * m / r) * lam * nu) / ((1 - 2 * m / r) * r) =
      2 * m * lam * nu / (r * (r - 2 * m)) := by
  have hratio : (1 - 2 * m / r) * r = r - 2 * m := by
    field_simp [hr]
  rw [hratio]
  field_simp [hr, hgap]

/-- The classical mass density equals the radius-gap form stored by the
rectangle equations. -/
theorem mass_out_density_eq_rectangle_density
    {r m lam theta : ℝ} (hr : r ≠ 0) :
    (1 - 2 * m / r) * theta ^ 2 / (2 * lam) =
      ((r - 2 * m) / r) * theta ^ 2 / (2 * lam) := by
  field_simp [hr]

end ChristodoulouBV.Uniqueness

end
