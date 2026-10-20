module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxSourceQuotient
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraWeighted
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Weighted Volterra data for the removable coefficient box

The abstract cubic axis data are supplied here by the weighted attenuated
Volterra construction and its uniform axis theorem. The radius is the
vertical integral of the same positive weight.
-/

public section

open Set

namespace intervalIntegral

/-- Weighted diagonal Volterra data with a regular opposite-axis factor
construct the common single-input removable coefficient box. -/
@[expose] noncomputable def weightedDiagonalCubicRationalTriangleBox
    {a b c J₀ J₁ K₀ K₁ : ℝ}
    (hab : a < b) (hc : 0 < c)
    {w f z : ℝ × ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hz : ContDiffOn ℝ 1 z (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hzdiag : ∀ u ∈ Icc a b, z (u, u) = -w (u, u))
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hjbound : ∀ p ∈ closedCoordTriangle a b,
      weightedDiagonalQuadraticKernel w f p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hjubound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
        (closedCoordTriangle a b) p) (1, 0)| ≤ J₁ * (p.2 - p.1))
    (hkbound : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ weightedDiagonalQuotientKernel w f p ∧
        weightedDiagonalQuotientKernel w f p ≤ K₀ * (p.2 - p.1))
    (hkubound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
        (closedCoordTriangle a b) p) (1, 0)| ≤ K₁) :
    CubicRationalTriangleBox a b c := by
  let K := closedCoordTriangle a b
  let Gw := fderivWithin ℝ w K
  let Gf := fderivWithin ℝ f K
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hGw : ContinuousOn Gw K :=
    hw.continuousOn_fderivWithin hunique (by norm_num)
  have hGf : ContinuousOn Gf K :=
    hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdw : DifferentiableOn ℝ w (interior K) :=
    (hw.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ f (interior K) :=
    (hf.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ p ∈ interior K, fderiv ℝ w p = Gw p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hderivf : ∀ p ∈ interior K, fderiv ℝ f p = Gf p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hJc1 := contDiffOn_weightedDiagonalAttenuatedVolterra
    hab hw.continuousOn hf.continuousOn hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hrc1 := contDiffOn_weightedDiagonalRadius hab
    hw.continuousOn hGw hdw hderivw
  have hHc1 := contDiffOn_weightedDiagonalError hab
    hw.continuousOn hf.continuousOn hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have haxis := weightedDiagonalAttenuatedVolterra_uniform_axis hab
    hw.continuousOn hf.continuousOn hGw hGf
    hdw hdf hderivw hderivf hweight hc
    hJ₀ hJ₁ hK₀ hK₁ hjbound hjubound hkbound hkubound
  refine {
    J := weightedDiagonalAttenuatedVolterra w f
    r := weightedDiagonalRadius w
    ρ := normalizedDiagonalRadius w
    w := w
    z := z
    H := weightedDiagonalError w f
    h := fun p => Gf p (0, 1)
    J_c1 := hJc1
    r_c1 := hrc1
    ρ_cont := continuousOn_normalizedDiagonalRadius hw.continuousOn
    w_c1 := hw
    z_c1 := hz
    H_c1 := hHc1
    h_cont := hGf.clm_apply continuousOn_const
    ρ_lower := fun p hp => le_normalizedDiagonalRadius hw.continuousOn hweight hp
    w_lower := hweight
    r_factor := fun p _ => weightedDiagonalRadius_eq_gap_mul_normalized w p.1 p.2
    J_diag := by
      intro u hu
      exact weightedDiagonalAttenuatedVolterra_diag w f u
    H_diag := by
      intro u hu
      exact weightedDiagonalError_diag
        (ne_of_gt (hc.trans_le (hweight (u, u) ⟨hu.1, le_rfl, hu.2⟩)))
    ρ_diag := fun u _ => normalizedDiagonalRadius_diag w u
    z_diag := hzdiag
    r_u_diag := by
      intro u hu
      simpa using fderivWithin_weightedDiagonalRadius_diag_apply
        hab hw.continuousOn hGw hdw hderivw hu.1 hu.2 (1, 0)
    r_v_diag := by
      intro u hu
      simpa using fderivWithin_weightedDiagonalRadius_diag_apply
        hab hw.continuousOn hGw hdw hderivw hu.1 hu.2 (0, 1)
    J_axis := by
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := haxis ε hε
      refine ⟨δ, hδ, ?_⟩
      intro u v hu huv hv hgap
      have h := (hbound u v hu huv hv hgap).1
      convert h using 1; ring
    J_u_axis := by
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := haxis ε hε
      refine ⟨δ, hδ, ?_⟩
      intro u v hu huv hv hgap
      have h := (hbound u v hu huv hv hgap).2.2
      convert h using 1; ring
    J_v_axis := by
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := haxis ε hε
      refine ⟨δ, hδ, ?_⟩
      intro u v hu huv hv hgap
      have h := (hbound u v hu huv hv hgap).2.1
      convert h using 1; ring
  }

end intervalIntegral

end
