module

public import ChristodoulouBV.Existence.C1EndpointMeasure
public import ChristodoulouBV.AreaEstimates.GaugeAxisShift
public import ChristodoulouBV.AreaEstimates.FieldTransportDerivatives
public import ChristodoulouBV.AreaEstimates.ScalarAreaJacobian
import Mathlib.Tactic

/-!
# Scalar shifts preserve the four analytic areas

The four Section 4 maps change only by constant translations in their
two-dimensional targets wherever the two null expansions are nonzero.
-/

public section

open Set

namespace ChristodoulouBV

/-- Centering the scalar field leaves all four analytic Jacobian areas on an
open domain unchanged when `λ` and `ν` do not vanish there. -/
theorem s6_scalar_shift_four_areas (S : Fields) (c : ℝ)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hlam : ∀ p ∈ U, S.lam p.1 p.2 ≠ 0)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≠ 0) :
    smoothAnalyticArea (sourcePhiAlphaLamMap (scalarShift S c)) U =
        smoothAnalyticArea (sourcePhiAlphaLamMap S) U ∧
    smoothAnalyticArea (sourcePhiBetaNuMap (scalarShift S c)) U =
        smoothAnalyticArea (sourcePhiBetaNuMap S) U ∧
    smoothAnalyticArea (sourceLamPhiMap (scalarShift S c)) U =
        smoothAnalyticArea (sourceLamPhiMap S) U ∧
    smoothAnalyticArea (sourceNuPhiMap (scalarShift S c)) U =
        smoothAnalyticArea (sourceNuPhiMap S) U := by
  have hA (p : ℝ × ℝ) (hp : p ∈ U) :
      sourcePhiAlphaLamMap (scalarShift S c) p =
        sourcePhiAlphaLamMap S p + (c, c) := by
    simp only [sourcePhiAlphaLamMap, scalarShift, Prod.mk_add_mk]
    congr 1
    field_simp [hlam p hp]
  have hB (p : ℝ × ℝ) (hp : p ∈ U) :
      sourcePhiBetaNuMap (scalarShift S c) p =
        sourcePhiBetaNuMap S p + (c, c) := by
    simp only [sourcePhiBetaNuMap, scalarShift, Prod.mk_add_mk]
    congr 1
    field_simp [hnu p hp]
  have hL (p : ℝ × ℝ) (_hp : p ∈ U) :
      sourceLamPhiMap (scalarShift S c) p =
        sourceLamPhiMap S p + (0, c) := by
    simp only [sourceLamPhiMap, scalarShift, Prod.mk_add_mk, add_zero]
  have hN (p : ℝ × ℝ) (_hp : p ∈ U) :
      sourceNuPhiMap (scalarShift S c) p =
        sourceNuPhiMap S p + (0, c) := by
    simp only [sourceNuPhiMap, scalarShift, Prod.mk_add_mk, add_zero]
  exact ⟨smoothAnalyticArea_eq_of_eq_add_const_on_open _ _ _ hU hA,
    smoothAnalyticArea_eq_of_eq_add_const_on_open _ _ _ hU hB,
    smoothAnalyticArea_eq_of_eq_add_const_on_open _ _ _ hU hL,
    smoothAnalyticArea_eq_of_eq_add_const_on_open _ _ _ hU hN⟩

end ChristodoulouBV

end
