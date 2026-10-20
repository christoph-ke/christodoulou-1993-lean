module

public import ChristodoulouBV.C1Solution.UniquenessKernelValueJets
import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraQuotientBox
import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Vertical quotient-kernel difference

The five-term quotient ledger applies on each outgoing ray with the moving
four-field seminorm.  The interior estimate is subsequently extended to the
closed triangle by continuity.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- On the open triangle, the vertical jet of the quotient kernel satisfies
the five-term quadratic-kernel difference coefficient in the fixed-ray seminorm. -/
theorem canonical_quotient_kernel_vertical_jet_sub_le_difference_interior
    {b₁ b₂ T c C Bv L : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv) (hL : 0 ≤ L)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hlamVertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < T) :
    let Hc := Bv + C * Bv / c
    let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
    let Hdv := 1 + (Bv + C * Hd) / c + C * Bv / c ^ 2
    let j₀ := C * Bv ^ 2
    let j₁ := L * Bv ^ 2 + 2 * C * Bv * Hc
    let jΔ₀ := Bv ^ 2 + 2 * C * Bv * Hd
    let jΔ₁ := Bv ^ 2 + 2 * L * Bv * Hd +
      2 * (Bv * Hc + C * Hd * Hc + C * Bv * Hdv)
    |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuotientKernel
        (fun q => S₁.lam q.1 q.2) (outgoingQuotient S₁))
      (closedCoordTriangle 0 T) (u, v)) (0, 1) -
      (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuotientKernel
        (fun q => S₂.lam q.1 q.2) (outgoingQuotient S₂))
      (closedCoordTriangle 0 T) (u, v)) (0, 1)| ≤
      (jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * C / c ^ 2 +
        j₀ / c ^ 2 + 2 * j₀ * C / c ^ 3) *
      outgoingDifference T hT.le S₁ S₂ u := by
  dsimp only
  let K := closedCoordTriangle 0 T
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let f₁ := outgoingQuotient S₁
  let f₂ := outgoingQuotient S₂
  let Gw₁ := fderivWithin ℝ w₁ K
  let Gw₂ := fderivWithin ℝ w₂ K
  let Gf₁ := fderivWithin ℝ f₁ K
  let Gf₂ := fderivWithin ℝ f₂ K
  let D := outgoingDifference T hT.le S₁ S₂ u
  let Hc := Bv + C * Bv / c
  let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
  let Hdv := 1 + (Bv + C * Hd) / c + C * Bv / c ^ 2
  let j₀ := C * Bv ^ 2
  let j₁ := L * Bv ^ 2 + 2 * C * Bv * Hc
  let jΔ₀ := Bv ^ 2 + 2 * C * Bv * Hd
  let jΔ₁ := Bv ^ 2 + 2 * L * Bv * Hd +
    2 * (Bv * Hc + C * Hd * Hc + C * Bv * Hdv)
  have hp : (u, v) ∈ K := ⟨hu.le, huv.le, hv.le⟩
  have hwC1₁ : ContDiffOn ℝ 1 w₁ K := (five_fields_contDiffOn hT hT₁ H₁).1
  have hwC1₂ : ContDiffOn ℝ 1 w₂ K := (five_fields_contDiffOn hT hT₂ H₂).1
  have hfC1₁ : ContDiffOn ℝ 1 f₁ K := alpha_div_lam_contDiffOn hT hT₁ H₁
  have hfC1₂ : ContDiffOn ℝ 1 f₂ K := alpha_div_lam_contDiffOn hT hT₂ H₂
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hT)
  have hGw₁ : ContinuousOn Gw₁ K :=
    hwC1₁.continuousOn_fderivWithin hunique (by norm_num)
  have hGw₂ : ContinuousOn Gw₂ K :=
    hwC1₂.continuousOn_fderivWithin hunique (by norm_num)
  have hGf₁ : ContinuousOn Gf₁ K :=
    hfC1₁.continuousOn_fderivWithin hunique (by norm_num)
  have hGf₂ : ContinuousOn Gf₂ K :=
    hfC1₂.continuousOn_fderivWithin hunique (by norm_num)
  have hdw₁ : DifferentiableOn ℝ w₁ (interior K) :=
    (hwC1₁.differentiableOn (by norm_num)).mono interior_subset
  have hdw₂ : DifferentiableOn ℝ w₂ (interior K) :=
    (hwC1₂.differentiableOn (by norm_num)).mono interior_subset
  have hdf₁ : DifferentiableOn ℝ f₁ (interior K) :=
    (hfC1₁.differentiableOn (by norm_num)).mono interior_subset
  have hdf₂ : DifferentiableOn ℝ f₂ (interior K) :=
    (hfC1₂.differentiableOn (by norm_num)).mono interior_subset
  have hderivw₁ : ∀ p ∈ interior K, fderiv ℝ w₁ p = Gw₁ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hderivw₂ : ∀ p ∈ interior K, fderiv ℝ w₂ p = Gw₂ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hderivf₁ : ∀ p ∈ interior K, fderiv ℝ f₁ p = Gf₁ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hderivf₂ : ∀ p ∈ interior K, fderiv ℝ f₂ p = Gf₂ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂
    ⟨hu.le, huv.le.trans hv.le⟩
  have hj₀ : 0 ≤ j₀ := by dsimp [j₀]; positivity
  have hj₁ : 0 ≤ j₁ := by dsimp [j₁, Hc]; positivity
  have hjΔ₀ : 0 ≤ jΔ₀ := by dsimp [jΔ₀, Hd]; positivity
  have hjΔ₁ : 0 ≤ jΔ₁ := by dsimp [jΔ₁, Hc, Hd, Hdv]; positivity
  have hr : 0 ≤ C := hC
  have hrΔ : 0 ≤ (1 : ℝ) := by norm_num
  have hj₂ : |intervalIntegral.weightedDiagonalQuadraticKernel w₂ f₂ (u, v)| ≤
      j₀ * (v - u) ^ 2 := by
    have h := (canonical_mass_kernel_value_bounds hT hT₂ hc hBv H₂
      hweight₂ hhvertical₂ hp).1
    rw [abs_of_nonneg h.1]
    exact h.2
  have hjdiff : |intervalIntegral.weightedDiagonalQuadraticKernel w₁ f₁ (u, v) -
      intervalIntegral.weightedDiagonalQuadraticKernel w₂ f₂ (u, v)| ≤
      jΔ₀ * (v - u) ^ 2 * D :=
    canonical_quadratic_kernel_sub_le_difference hT hT₁ hT₂ hc hC hBv
      H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂ hu.le huv.le hv.le
  have hji₂ : |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuadraticKernel w₂ f₂) K (u, v)) (0, 1)| ≤
      j₁ * (v - u) :=
    canonical_quadratic_kernel_vertical_jet_abs_le hT hTwidth hT₂
      hc hC hBv hL H₂ hweight₂ hhvertical₂ hlamVertical₂ hp
  have hHc₁ : ∀ p ∈ K,
      |(fderivWithin ℝ (canonicalSourceFactor S₁) K p) (0, 1)| ≤ Hc := by
    intro p hp
    exact canonical_source_factor_vertical_jet_abs_le hT hT₁ hc hBv
      H₁ hweight₁ hhvertical₁ hp
  have hjidiff : |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuadraticKernel w₁ f₁) K (u, v)) (0, 1) -
      (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuadraticKernel w₂ f₂) K (u, v)) (0, 1)| ≤
      jΔ₁ * (v - u) * D :=
    canonical_quadratic_kernel_vertical_jet_sub_le_difference
      hT hTwidth hT₁ hT₂ hc hBv hL H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂
      hlamVertical₂ hHc₁ hu.le huv.le hv.le
  have hw₁ : ContinuousOn w₁ K := hwC1₁.continuousOn
  have hw₂ : ContinuousOn w₂ K := hwC1₂.continuousOn
  have hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D := by
    intro t ht
    exact (outgoing_components_le_difference hT hT₁ hT₂ H₁ H₂
      hu.le ht.1 (ht.2.trans hv.le)).1
  have hrdiff : |intervalIntegral.weightedDiagonalRadius w₁ (u, v) -
      intervalIntegral.weightedDiagonalRadius w₂ (u, v)| ≤ (v - u) * D := by
    rw [mul_comm]
    exact intervalIntegral.abs_weightedDiagonalRadius_sub_le_on_ray
      hw₁ hw₂ hu.le huv.le hv.le hwdiff
  have hradjet₁ : (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalRadius w₁) K (u, v)) (0, 1) =
      w₁ (u, v) := weightedDiagonalRadius_vertical_jet hT hwC1₁ hp
  have hradjet₂ : (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalRadius w₂) K (u, v)) (0, 1) =
      w₂ (u, v) := weightedDiagonalRadius_vertical_jet hT hwC1₂ hp
  have hri₁ : |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalRadius w₁) K (u, v)) (0, 1)| ≤ C := by
    rw [hradjet₁, abs_of_nonneg (hc.le.trans (hweight₁ (u, v) hp).1)]
    exact (hweight₁ (u, v) hp).2
  have hri₂ : |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalRadius w₂) K (u, v)) (0, 1)| ≤ C := by
    rw [hradjet₂, abs_of_nonneg (hc.le.trans (hweight₂ (u, v) hp).1)]
    exact (hweight₂ (u, v) hp).2
  have hridiff : |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalRadius w₁) K (u, v)) (0, 1) -
      (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalRadius w₂) K (u, v)) (0, 1)| ≤
      (1 : ℝ) * D := by
    rw [hradjet₁, hradjet₂, one_mul]
    exact (outgoing_components_le_difference hT hT₁ hT₂ H₁ H₂
      hu.le huv.le hv.le).1
  have h := intervalIntegral.abs_fderivWithin_weightedDiagonalQuotientKernel_sub_le_of_bounds
    hT hw₁ hw₂ hfC1₁.continuousOn hfC1₂.continuousOn
    hGw₁ hGw₂ hGf₁ hGf₂ hdw₁ hdw₂ hdf₁ hdf₂
    hderivw₁ hderivw₂ hderivf₁ hderivf₂
    (fun p hp => (hweight₁ p hp).1)
    (fun p hp => (hweight₂ p hp).1)
    hc hj₀ hj₁ hjΔ₀ hjΔ₁ hr hrΔ hD hp huv
    hj₂ hjdiff hji₂ hjidiff hrdiff hri₁ hri₂ hridiff
  simpa only [mul_one, w₁, w₂, f₁, f₂, j₀, j₁, jΔ₀, jΔ₁,
    Hc, Hd, Hdv, D] using h

/-- The fixed-ray vertical quotient-kernel difference extends to both
vertices and the axis of the closed triangle. -/
theorem canonical_quotient_kernel_vertical_jet_sub_le_difference
    {b₁ b₂ T c C Bv L : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv) (hL : 0 ≤ L)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hlamVertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    let Hc := Bv + C * Bv / c
    let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
    let Hdv := 1 + (Bv + C * Hd) / c + C * Bv / c ^ 2
    let j₀ := C * Bv ^ 2
    let j₁ := L * Bv ^ 2 + 2 * C * Bv * Hc
    let jΔ₀ := Bv ^ 2 + 2 * C * Bv * Hd
    let jΔ₁ := Bv ^ 2 + 2 * L * Bv * Hd +
      2 * (Bv * Hc + C * Hd * Hc + C * Bv * Hdv)
    |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuotientKernel
        (fun q => S₁.lam q.1 q.2) (outgoingQuotient S₁))
      (closedCoordTriangle 0 T) (u, v)) (0, 1) -
      (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuotientKernel
        (fun q => S₂.lam q.1 q.2) (outgoingQuotient S₂))
      (closedCoordTriangle 0 T) (u, v)) (0, 1)| ≤
      (jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * C / c ^ 2 +
        j₀ / c ^ 2 + 2 * j₀ * C / c ^ 3) *
      outgoingDifference T hT.le S₁ S₂ u := by
  dsimp only
  let K := closedCoordTriangle 0 T
  let k₁ := intervalIntegral.weightedDiagonalQuotientKernel
    (fun q => S₁.lam q.1 q.2) (outgoingQuotient S₁)
  let k₂ := intervalIntegral.weightedDiagonalQuotientKernel
    (fun q => S₂.lam q.1 q.2) (outgoingQuotient S₂)
  let A :=
    let Hc := Bv + C * Bv / c
    let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
    let Hdv := 1 + (Bv + C * Hd) / c + C * Bv / c ^ 2
    let j₀ := C * Bv ^ 2
    let j₁ := L * Bv ^ 2 + 2 * C * Bv * Hc
    let jΔ₀ := Bv ^ 2 + 2 * C * Bv * Hd
    let jΔ₁ := Bv ^ 2 + 2 * L * Bv * Hd +
      2 * (Bv * Hc + C * Hd * Hc + C * Bv * Hdv)
    jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * C / c ^ 2 +
      j₀ / c ^ 2 + 2 * j₀ * C / c ^ 3
  let F : ℝ × ℝ → ℝ := fun p =>
    |(fderivWithin ℝ k₁ K p) (0, 1) -
      (fderivWithin ℝ k₂ K p) (0, 1)|
  let G : ℝ × ℝ → ℝ := fun p =>
    A * outgoingDifference T hT.le S₁ S₂ p.1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hT)
  have hk₁ : ContDiffOn ℝ 1 k₁ K :=
    (canonical_mass_kernels_contDiffOn hT hT₁ H₁).2
  have hk₂ : ContDiffOn ℝ 1 k₂ K :=
    (canonical_mass_kernels_contDiffOn hT hT₂ H₂).2
  have hjet₁ : ContinuousOn (fun p => (fderivWithin ℝ k₁ K p) (0, 1)) K :=
    (hk₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hjet₂ : ContinuousOn (fun p => (fderivWithin ℝ k₂ K p) (0, 1)) K :=
    (hk₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hF : ContinuousOn F K := (hjet₁.sub hjet₂).abs
  have hD : Continuous (outgoingDifference T hT.le S₁ S₂) :=
    (continuous_outgoing_and_incoming_difference hT hT₁ hT₂ H₁ H₂).1
  have hG : ContinuousOn G K :=
    continuousOn_const.mul (hD.comp continuous_fst).continuousOn
  have hinterior : ∀ p ∈ interior K, F p ≤ G p := by
    rintro ⟨x, y⟩ hp
    have hxy : 0 < x ∧ x < y ∧ y < T := by
      simpa only [K, interior_closedCoordTriangle, openCoordTriangle,
        Set.mem_ofPred_eq] using hp
    exact canonical_quotient_kernel_vertical_jet_sub_le_difference_interior
      hT hTwidth hT₁ hT₂ hc hC hBv hL H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hlamVertical₂
      hxy.1 hxy.2.1 hxy.2.2
  have h := intervalIntegral.le_on_closedCoordTriangle_of_interior
    hT hF hG hinterior (u, v) ⟨hu, huv, hv⟩
  exact h

end ChristodoulouBV.C1Solution

end
