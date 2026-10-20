module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Planar Jacobians for the Section 4 field transports

The analytic area measure uses the determinant of a Fréchet derivative.
These formulas identify that determinant with the two coordinate jets used
in the characteristic transport equations.
-/

public section

open Module
open MeasureTheory Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The determinant of a planar map assembled from two scalar linear maps. -/
theorem det_prod_of_scalar_maps (A B : (ℝ × ℝ) →L[ℝ] ℝ) :
    (A.prod B).det = A (1, 0) * B (0, 1) - A (0, 1) * B (1, 0) := by
  change LinearMap.det (A.prod B).toLinearMap = _
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  simp only [Matrix.det_fin_two, LinearMap.toMatrix_apply,
    Basis.finTwoProd_zero, Basis.finTwoProd_one,
    Basis.coe_finTwoProd_repr]
  rfl

/-- Coordinate formula for the analytic Jacobian of a pair of differentiable
scalar fields. -/
theorem det_fderiv_prodMk {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    (fderiv ℝ (fun q => (f q, g q)) p).det =
      (fderiv ℝ f p) (1, 0) * (fderiv ℝ g p) (0, 1) -
        (fderiv ℝ f p) (0, 1) * (fderiv ℝ g p) (1, 0) := by
  rw [hf.fderiv_prodMk hg]
  exact det_prod_of_scalar_maps _ _

/-- A C¹ planar map has a measurable absolute Jacobian density on its open
carrier, even when the total map is arbitrary outside that carrier. -/
theorem jacobianDensity_aemeasurable_of_contDiffOn
    {F : ℝ × ℝ → ℝ × ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) :
    AEMeasurable (fun p => ENNReal.ofReal |(fderiv ℝ F p).det|)
      (volume.restrict U) := by
  have hFderiv := hF.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hDet : ContinuousOn (fun p => (fderiv ℝ F p).det) U :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hFderiv
  exact (hDet.abs.aemeasurable hU.measurableSet).ennreal_ofReal

/-- Tonelli on a measurable rectangle, with the characteristic incoming
variable integrated last. This form matches the outgoing residual estimate. -/
theorem lintegral_rectangle_swap (A B : Set ℝ)
    (F : ℝ × ℝ → ℝ≥0∞)
    (hF : AEMeasurable F ((volume.restrict A).prod (volume.restrict B))) :
    (∫⁻ p in A ×ˢ B, F p) = ∫⁻ y in B, ∫⁻ x in A, F (x, y) := by
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict A B]
  exact lintegral_prod_symm F hF

/-- Integrate a pointwise residual bound on an outgoing segment. The double
integral is exactly the analytic density on the preceding rectangle. -/
theorem lintegral_residual_le_initial_add_rectangle
    (A B : Set ℝ) (R I : ℝ → ℝ≥0∞) (J : ℝ × ℝ → ℝ≥0∞)
    (hB : MeasurableSet B) (hI : AEMeasurable I (volume.restrict B))
    (hJ : AEMeasurable J ((volume.restrict A).prod (volume.restrict B)))
    (hpoint : ∀ y ∈ B, R y ≤ I y + ∫⁻ x in A, J (x, y)) :
    (∫⁻ y in B, R y) ≤ (∫⁻ y in B, I y) +
      ∫⁻ p in A ×ˢ B, J p := by
  calc
    (∫⁻ y in B, R y) ≤
        ∫⁻ y in B, I y + ∫⁻ x in A, J (x, y) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with y hy
      exact hpoint y hy
    _ = (∫⁻ y in B, I y) + ∫⁻ y in B, ∫⁻ x in A, J (x, y) := by
      rw [lintegral_add_left' hI]
    _ = (∫⁻ y in B, I y) + ∫⁻ p in A ×ˢ B, J p := by
      rw [lintegral_rectangle_swap A B J hJ]

end ChristodoulouBV

end
