module

public import ChristodoulouBV.AreaEstimates.FieldTransport
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# The scalar residual majorants in Section 4

These are the one-variable functions `F` and `F*` in (4.15) and (4.17).
Extended nonnegative integrals retain their meaning without an advance
finiteness assumption on the areas.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- The outgoing residual majorant `F(v)` in (4.15b). -/
noncomputable def sourceAlphaMajorant (S : Fields) (v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    |deriv (S.alpha 0) v - deriv (S.lam 0) v * S.phi 0 v| +
  ∫⁻ u in Ioo 0 v,
    ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (u, v)).det|

/-- The incoming residual majorant `F*(u)` in (4.17b). -/
noncomputable def sourceBetaMajorant (S : Fields) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    |deriv (fun t => S.beta t t) u -
      deriv (fun t => S.nu t t) u * S.phi u u| +
  ∫⁻ v in Ioo u 1,
    ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, v)).det|

/-- Equation (4.15b), as the defining expression for `F`. -/
theorem eq4_15b (S : Fields) (v : ℝ) :
    sourceAlphaMajorant S v =
      ENNReal.ofReal
        |deriv (S.alpha 0) v - deriv (S.lam 0) v * S.phi 0 v| +
      ∫⁻ u in Ioo 0 v,
        ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (u, v)).det| :=
  rfl

/-- Equation (4.17b), as the defining expression for `F*`. -/
theorem eq4_17b (S : Fields) (u : ℝ) :
    sourceBetaMajorant S u =
      ENNReal.ofReal
        |deriv (fun t => S.beta t t) u -
          deriv (fun t => S.nu t t) u * S.phi u u| +
      ∫⁻ v in Ioo u 1,
        ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, v)).det| :=
  rfl

/-- Equation (4.15a): the outgoing residual is bounded by `F(v)`. -/
theorem eq4_15a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ENNReal.ofReal
      |deriv (S.alpha u) v - deriv (S.lam u) v * S.phi u v| ≤
        sourceAlphaMajorant S v := by
  exact eq4_4a H hr hcenter hboot hu huv hv |>.trans (by
    simp only [sourceAlphaMajorant]
    gcongr)

/-- Equation (4.17a): the incoming residual is bounded by `F*(u)`. -/
theorem eq4_17a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ENNReal.ofReal
      |deriv (fun t => S.beta t v) u -
        deriv (fun t => S.nu t v) u * S.phi u v| ≤
        sourceBetaMajorant S u := by
  exact eq4_5a H hr hcenter hboot hu huv hv |>.trans (by
    simp only [sourceBetaMajorant]
    gcongr)

end ChristodoulouBV

end
