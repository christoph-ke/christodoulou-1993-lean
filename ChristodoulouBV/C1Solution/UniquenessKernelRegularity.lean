module

public import ChristodoulouBV.C1Solution.UniquenessMassODE
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Regularity of the canonical quadratic and quotient kernels

The quotient kernel has a removable axis singularity. Its closed-triangle
first jet is supplied by the diagonal Volterra regularity theorem.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- Both kernels in the canonical mass equation are C¹ on every compact
smaller closed triangle. -/
theorem canonical_mass_kernels_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1
      (intervalIntegral.weightedDiagonalQuadraticKernel
        (fun p => S.lam p.1 p.2) (outgoingQuotient S))
      (closedCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1
      (intervalIntegral.weightedDiagonalQuotientKernel
        (fun p => S.lam p.1 p.2) (outgoingQuotient S))
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  let w : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let f := outgoingQuotient S
  let Gw := fderivWithin ℝ w K
  let Gf := fderivWithin ℝ f K
  have hwC1 : ContDiffOn ℝ 1 w K := (five_fields_contDiffOn hB hBb H).1
  have hfC1 : ContDiffOn ℝ 1 f K := alpha_div_lam_contDiffOn hB hBb H
  have hHC1 : ContDiffOn ℝ 1
      (intervalIntegral.weightedDiagonalError w f) K :=
    (canonical_source_factor_box_inputs hB hBb H).1.congr
      (fun p hp => (canonical_source_factor_eq_weightedDiagonalError
        hB hBb H hp).symm)
  have hjC1 : ContDiffOn ℝ 1
      (intervalIntegral.weightedDiagonalQuadraticKernel w f) K := by
    change ContDiffOn ℝ 1 (fun p => w p *
      (intervalIntegral.weightedDiagonalError w f p) ^ 2) K
    exact hwC1.mul (hHC1.pow 2)
  refine ⟨hjC1, ?_⟩
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hGw : ContinuousOn Gw K :=
    hwC1.continuousOn_fderivWithin hunique (by norm_num)
  have hGf : ContinuousOn Gf K :=
    hfC1.continuousOn_fderivWithin hunique (by norm_num)
  have hdw : DifferentiableOn ℝ w (interior K) :=
    (hwC1.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ f (interior K) :=
    (hfC1.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ p ∈ interior K, fderiv ℝ w p = Gw p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdw p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hderivf : ∀ p ∈ interior K, fderiv ℝ f p = Gf p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdf p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  exact intervalIntegral.contDiffOn_weightedDiagonalQuotientKernel hB
    hwC1.continuousOn hfC1.continuousOn hGw hGf
    hdw hdf hderivw hderivf hcl hc

end ChristodoulouBV.C1Solution

end
