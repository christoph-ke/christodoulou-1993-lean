module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernel
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Divided differences and jets of quadratic kernels

A continuous first jet gives a continuous vertical divided difference on a
closed coordinate triangle. This is the regular factor behind a quadratic
kernel divided by a radius that vanishes on the diagonal.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The normalized vertical divided difference of a first jet, defined also
on the diagonal by integrating its vertical derivative. -/
@[expose] noncomputable def verticalJetMean
    (F : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, F (diagonalSegment p t) (0, 1)

/-- A continuous first jet has a continuous normalized vertical derivative
mean on a closed coordinate triangle. -/
theorem continuousOn_verticalJetMean {a b : ℝ}
    {F : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hF : ContinuousOn F (closedCoordTriangle a b)) :
    ContinuousOn (verticalJetMean F) (closedCoordTriangle a b) := by
  exact continuousOn_integral_diagonalSegment
    (hF.clm_apply continuousOn_const)

/-- The divided difference agrees with the vertical increment of the
function, including when the increment is zero. -/
theorem sub_diag_eq_gap_mul_verticalJetMean {a b : ℝ} (hab : a < b)
    {f : ℝ × ℝ → ℝ} {F : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hF : ContinuousOn F (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = F p)
    {u v : ℝ} (hp : (u, v) ∈ closedCoordTriangle a b) :
    f (u, v) - f (u, u) = (v - u) * verticalJetMean F (u, v) := by
  have hpdiag : (u, u) ∈ closedCoordTriangle a b := by
    rcases hp with ⟨hu, huv, hv⟩
    exact ⟨hu, le_rfl, huv.trans hv⟩
  have hseg := (convex_closedCoordTriangle a b).sub_eq_integral_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hf hF hdiff hderiv hpdiag hp
  have hvector : ((u, v) : ℝ × ℝ) - (u, u) = (v - u) • (0, 1) := by
    ext <;> simp [smul_eq_mul]
  simp only [hvector, map_smul, smul_eq_mul] at hseg
  rw [verticalJetMean, ← intervalIntegral.integral_const_mul]
  simpa [diagonalSegment, smul_eq_mul] using hseg

/-- On the diagonal the vertical derivative mean is the vertical derivative
itself. -/
theorem verticalJetMean_diag (F : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (u : ℝ) :
    verticalJetMean F (u, u) = F (u, u) (0, 1) := by
  simp [verticalJetMean, diagonalSegment]

/-- The mean weight along a normalized vertical segment. -/
@[expose] noncomputable def normalizedDiagonalRadius
    (w : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w (diagonalSegment p t)

/-- The vertical radius factors as the coordinate gap times its normalized
mean, including on the diagonal. -/
theorem weightedDiagonalRadius_eq_gap_mul_normalized
    (w : ℝ × ℝ → ℝ) (u v : ℝ) :
    weightedDiagonalRadius w (u, v) =
      (v - u) * normalizedDiagonalRadius w (u, v) :=
  weightedDiagonalRadius_eq_mul_integral w u v

/-- The normalized radius is continuous on the whole closed triangle. -/
theorem continuousOn_normalizedDiagonalRadius {a b : ℝ}
    {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b)) :
    ContinuousOn (normalizedDiagonalRadius w) (closedCoordTriangle a b) :=
  continuousOn_integral_diagonalSegment hw

/-- The normalized radius inherits a continuous first jet from its weight. -/
theorem contDiffOn_normalizedDiagonalRadius {a b : ℝ} (hab : a < b)
    {w : ℝ × ℝ → ℝ} {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p) :
    ContDiffOn ℝ 1 (normalizedDiagonalRadius w) (closedCoordTriangle a b) :=
  contDiffOn_integral_diagonalSegment hab hw hGw hdw hderivw

/-- On the diagonal the normalized radius is the weight. -/
theorem normalizedDiagonalRadius_diag (w : ℝ × ℝ → ℝ) (u : ℝ) :
    normalizedDiagonalRadius w (u, u) = w (u, u) := by
  simp [normalizedDiagonalRadius, diagonalSegment]

/-- A positive weight bounds the normalized radius away from zero. -/
theorem le_normalizedDiagonalRadius {a b c : ℝ}
    {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    c ≤ normalizedDiagonalRadius w p :=
  integral_diagonalSegment_weight_ge hw hweight hp

/-- The vertical radius has a continuous first jet on a closed triangle. -/
theorem contDiffOn_weightedDiagonalRadius {a b : ℝ} (hab : a < b)
    {w : ℝ × ℝ → ℝ} {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p) :
    ContDiffOn ℝ 1 (weightedDiagonalRadius w) (closedCoordTriangle a b) := by
  have hgap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.2 - p.1)
      (closedCoordTriangle a b) := by fun_prop
  have hρ := contDiffOn_normalizedDiagonalRadius hab hw hGw hdw hderivw
  apply (hgap.mul hρ).congr
  intro p hp
  exact weightedDiagonalRadius_eq_gap_mul_normalized w p.1 p.2

/-- The first jet of the radius on the diagonal depends only on the weight
there; horizontal and vertical derivatives have opposite signs. -/
theorem fderivWithin_weightedDiagonalRadius_diag_apply {a b : ℝ} (hab : a < b)
    {w : ℝ × ℝ → ℝ} {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    {u : ℝ} (hu : a ≤ u) (hub : u ≤ b) (q : ℝ × ℝ) :
    (fderivWithin ℝ (weightedDiagonalRadius w) (closedCoordTriangle a b)
      (u, u)) q = w (u, u) * (q.2 - q.1) := by
  let K := closedCoordTriangle a b
  let ρ := normalizedDiagonalRadius w
  let d : ℝ × ℝ → ℝ := fun p => p.2 - p.1
  let D : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ) - (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hp : (u, u) ∈ K := ⟨hu, le_rfl, hub⟩
  have hD : HasFDerivWithinAt d D K (u, u) := by
    have heq : d = D := by
      funext p
      simp [d, D]
    rw [heq]
    exact D.hasFDerivAt.hasFDerivWithinAt
  have hρ : DifferentiableWithinAt ℝ ρ K (u, u) :=
    ((contDiffOn_normalizedDiagonalRadius hab hw hGw hdw hderivw).differentiableOn
      (by norm_num)) (u, u) hp
  have hmul := hD.mul hρ.hasFDerivWithinAt
  have heq : EqOn (weightedDiagonalRadius w) (d * ρ) K := by
    intro p hp
    exact weightedDiagonalRadius_eq_gap_mul_normalized w p.1 p.2
  have hjet := hmul.congr' heq hp
  have hunique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      (u, u) hp
  rw [hjet.fderivWithin hunique]
  simp [d, D, ρ, normalizedDiagonalRadius_diag, smul_eq_mul]

/-- The weighted-mean error factors through the coordinate gap and the
continuous mean of its vertical first jet. -/
theorem weightedDiagonalError_eq_gap_mul_verticalJetMean
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u v : ℝ}
    (hp : (u, v) ∈ closedCoordTriangle a b) :
    weightedDiagonalError w f (u, v) = (v - u) *
      verticalJetMean
        (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b))
        (u, v) := by
  let K := closedCoordTriangle a b
  let H := weightedDiagonalError w f
  let F := fderivWithin ℝ H K
  have hC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hF : ContinuousOn F K := hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hH : ContinuousOn H K := hC1.continuousOn
  have hdiff : DifferentiableOn ℝ H (interior K) :=
    (hC1.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K, fderiv ℝ H p = F p := by
    intro p hp'
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp'))
      (hdiff.differentiableAt (isOpen_interior.mem_nhds hp'))).symm
  have hsub := sub_diag_eq_gap_mul_verticalJetMean hab hH hF hdiff hderiv hp
  have hpdiag : (u, u) ∈ K := by
    rcases hp with ⟨hu, huv, hv⟩
    exact ⟨hu, le_rfl, huv.trans hv⟩
  have hwpos : w (u, u) ≠ 0 :=
    ne_of_gt (hc.trans_le (hweight (u, u) hpdiag))
  simpa [H, weightedDiagonalError_diag hwpos] using hsub

/-- The continuous coefficient of the linearly vanishing quotient kernel. -/
@[expose] noncomputable def normalizedWeightedDiagonalQuotientKernel
    (a b : ℝ) (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  w p * (verticalJetMean
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b)) p) ^ 2 /
    normalizedDiagonalRadius w p

/-- The quotient kernel factors through the coordinate gap on the entire
closed triangle. -/
theorem weightedDiagonalQuotientKernel_eq_gap_mul_normalized
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    weightedDiagonalQuotientKernel w f p =
      (p.2 - p.1) * normalizedWeightedDiagonalQuotientKernel a b w f p := by
  rcases p with ⟨u, v⟩
  by_cases huv : u < v
  · have hρ : normalizedDiagonalRadius w (u, v) ≠ 0 :=
      ne_of_gt (hc.trans_le (le_normalizedDiagonalRadius hw hweight hp))
    have hd : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    simp only [weightedDiagonalQuotientKernel, huv, ↓reduceIte]
    rw [
      weightedDiagonalQuadraticKernel,
      weightedDiagonalError_eq_gap_mul_verticalJetMean hab hw hf hGw hGf
        hdw hdf hderivw hderivf hweight hc hp,
      weightedDiagonalRadius_eq_gap_mul_normalized]
    dsimp [normalizedWeightedDiagonalQuotientKernel]
    field_simp [hd, hρ]
  · have heq : u = v := le_antisymm hp.2.1 (le_of_not_gt huv)
    subst v
    simp [weightedDiagonalQuotientKernel_diag]

/-- The linearly vanishing quotient kernel is continuous on the closed
triangle, including the diagonal. -/
theorem continuousOn_weightedDiagonalQuotientKernel
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContinuousOn (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hH := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hF := hH.continuousOn_fderivWithin hunique (by norm_num)
  have hΦ := continuousOn_verticalJetMean hF
  have hρ := continuousOn_normalizedDiagonalRadius hw
  have hρne : ∀ p ∈ K, normalizedDiagonalRadius w p ≠ 0 := by
    intro p hp
    exact ne_of_gt (hc.trans_le (le_normalizedDiagonalRadius hw hweight hp))
  have hA : ContinuousOn (normalizedWeightedDiagonalQuotientKernel a b w f) K := by
    exact (hw.mul (hΦ.pow 2)).div hρ hρne
  have hgap : ContinuousOn (fun p : ℝ × ℝ => p.2 - p.1) K := by fun_prop
  apply (hgap.mul hA).congr
  intro p hp
  exact weightedDiagonalQuotientKernel_eq_gap_mul_normalized hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hp

/-- The continuous candidate first jet for the quotient kernel. Its factors
use normalized divided differences, so the definition has no singularity on
the diagonal. -/
@[expose] noncomputable def weightedDiagonalQuotientKernelJet
    (a b : ℝ) (w f : ℝ × ℝ → ℝ)
    (Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  let K := closedCoordTriangle a b
  let Φ := verticalJetMean (fderivWithin ℝ (weightedDiagonalError w f) K) p
  let ρ := normalizedDiagonalRadius w p
  ((p.2 - p.1) * Φ ^ 2 / ρ) • Gw p +
    (2 * w p * Φ / ρ) •
      fderivWithin ℝ (weightedDiagonalError w f) K p -
    (w p * Φ ^ 2 / ρ ^ 2) • fderivWithin ℝ (weightedDiagonalRadius w) K p

/-- The quotient-kernel candidate jet is continuous across the diagonal. -/
theorem continuousOn_weightedDiagonalQuotientKernelJet
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContinuousOn (weightedDiagonalQuotientKernelJet a b w f Gw)
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let H := weightedDiagonalError w f
  let F := fderivWithin ℝ H K
  let R := fderivWithin ℝ (weightedDiagonalRadius w) K
  let Φ := verticalJetMean F
  let ρ := normalizedDiagonalRadius w
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hF : ContinuousOn F K :=
    (contDiffOn_weightedDiagonalError hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc).continuousOn_fderivWithin
      hunique (by norm_num)
  have hR : ContinuousOn R K :=
    (contDiffOn_weightedDiagonalRadius hab hw hGw hdw hderivw).continuousOn_fderivWithin
      hunique (by norm_num)
  have hΦ : ContinuousOn Φ K := continuousOn_verticalJetMean hF
  have hρ : ContinuousOn ρ K := continuousOn_normalizedDiagonalRadius hw
  have hρne : ∀ p ∈ K, ρ p ≠ 0 := by
    intro p hp
    exact ne_of_gt (hc.trans_le (le_normalizedDiagonalRadius hw hweight hp))
  have hgap : ContinuousOn (fun p : ℝ × ℝ => p.2 - p.1) K := by fun_prop
  have hfirst : ContinuousOn
      (fun p => ((p.2 - p.1) * Φ p ^ 2 / ρ p) • Gw p) K :=
    ((hgap.mul (hΦ.pow 2)).div hρ hρne).smul hGw
  have hsecond : ContinuousOn
      (fun p => (2 * w p * Φ p / ρ p) • F p) K := by
    exact (((continuousOn_const.mul hw).mul hΦ).div hρ hρne).smul hF
  have hthird : ContinuousOn
      (fun p => (w p * Φ p ^ 2 / ρ p ^ 2) • R p) K := by
    exact ((hw.mul (hΦ.pow 2)).div (hρ.pow 2)
      (fun p hp => pow_ne_zero 2 (hρne p hp))).smul hR
  exact (hfirst.add hsecond).sub hthird

/-- Away from the diagonal the continuous candidate is the ordinary first
derivative of the quotient kernel. -/
theorem fderiv_weightedDiagonalQuotientKernel_interior
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ interior (closedCoordTriangle a b)) :
    fderiv ℝ (weightedDiagonalQuotientKernel w f) p =
      weightedDiagonalQuotientKernelJet a b w f Gw p := by
  let K := closedCoordTriangle a b
  let H := weightedDiagonalError w f
  let j := weightedDiagonalQuadraticKernel w f
  let r := weightedDiagonalRadius w
  let k := weightedDiagonalQuotientKernel w f
  let Φ := verticalJetMean (fderivWithin ℝ H K)
  let ρ := normalizedDiagonalRadius w
  have hpK : p ∈ K := interior_subset hp
  have hpopen : p ∈ openCoordTriangle a b :=
    (interior_closedCoordTriangle a b) ▸ hp
  have hgap : 0 < p.2 - p.1 := sub_pos.mpr hpopen.2.1
  have hrpos : 0 < r p := weightedDiagonalRadius_pos hw hweight hc
    hpK.1 hpopen.2.1 hpK.2.2
  have hρpos : 0 < ρ p := hc.trans_le (le_normalizedDiagonalRadius hw hweight hpK)
  have hHval : H p = (p.2 - p.1) * Φ p :=
    weightedDiagonalError_eq_gap_mul_verticalJetMean hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc hpK
  have hrval : r p = (p.2 - p.1) * ρ p :=
    weightedDiagonalRadius_eq_gap_mul_normalized w p.1 p.2
  have hjC1 := contDiffOn_weightedDiagonalQuadraticKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hrC1 := contDiffOn_weightedDiagonalRadius hab hw hGw hdw hderivw
  have hHC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      p hpK
  have hjAt : DifferentiableAt ℝ j p :=
    ((hjC1.differentiableOn (by norm_num)).mono interior_subset).differentiableAt
      (isOpen_interior.mem_nhds hp)
  have hrAt : DifferentiableAt ℝ r p :=
    ((hrC1.differentiableOn (by norm_num)).mono interior_subset).differentiableAt
      (isOpen_interior.mem_nhds hp)
  have hJderiv : HasFDerivAt j (fderivWithin ℝ j K p) p := by
    rw [fderivWithin_eq_fderiv hunique hjAt]
    exact hjAt.hasFDerivAt
  have hRderiv : HasFDerivAt r (fderivWithin ℝ r K p) p := by
    rw [fderivWithin_eq_fderiv hunique hrAt]
    exact hrAt.hasFDerivAt
  have hinv : HasFDerivAt (fun z => (r z)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(r p ^ 2)⁻¹)).comp
        (fderivWithin ℝ r K p)) p := by
    exact (hasFDerivAt_inv hrpos.ne').comp p hRderiv
  have hquot := hJderiv.mul hinv
  have hevent : k =ᶠ[𝓝 p] j * (fun z => (r z)⁻¹) := by
    have hopen : IsOpen (openCoordTriangle a b) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior
    filter_upwards [hopen.mem_nhds hpopen] with z hz
    change weightedDiagonalQuotientKernel w f z =
      weightedDiagonalQuadraticKernel w f z * (weightedDiagonalRadius w z)⁻¹
    simp [weightedDiagonalQuotientKernel, hz.2.1, div_eq_mul_inv]
  have hkAt := hquot.congr_of_eventuallyEq hevent
  have hform := hkAt.fderiv
  apply ContinuousLinearMap.ext
  intro q
  have hjform := fderivWithin_weightedDiagonalQuadraticKernel_apply hab
    (fun z hz => (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hw hGw hdw hderivw hz)
    hHC1 (e := q) hpK
  have hq := congrArg (fun G : (ℝ × ℝ) →L[ℝ] ℝ => G q) hform
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hq
  rw [hjform] at hq
  dsimp [weightedDiagonalQuotientKernelJet]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  change weightedDiagonalError w f p =
    (p.2 - p.1) * verticalJetMean
      (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b)) p at hHval
  change weightedDiagonalRadius w p =
    (p.2 - p.1) * normalizedDiagonalRadius w p at hrval
  rw [hq]
  dsimp [j, r]
  rw [hHval, hrval]
  dsimp [weightedDiagonalQuadraticKernel]
  rw [hHval]
  have halg (d ρ W P A X R : ℝ) (hd : d ≠ 0) (hρ : ρ ≠ 0) :
      (W * (d * P) ^ 2) * (R * -((d * ρ) ^ 2)⁻¹) +
          (d * ρ)⁻¹ * (A * (d * P) ^ 2 + 2 * W * (d * P) * X) =
        (d * P ^ 2 / ρ) * A + (2 * W * P / ρ) * X -
          (W * P ^ 2 / ρ ^ 2) * R := by
    field_simp [hd, hρ]
    ring
  exact halg (p.2 - p.1) (normalizedDiagonalRadius w p) (w p)
    (verticalJetMean (fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b)) p) (Gw p q)
    ((fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) p) q)
    ((fderivWithin ℝ (weightedDiagonalRadius w) (closedCoordTriangle a b) p) q)
    hgap.ne' hρpos.ne'

/-- The quotient kernel is differentiable at every interior point of the triangle. -/
theorem differentiableOn_weightedDiagonalQuotientKernel_interior
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    DifferentiableOn ℝ (weightedDiagonalQuotientKernel w f)
      (interior (closedCoordTriangle a b)) := by
  intro p hp
  have hpK : p ∈ closedCoordTriangle a b := interior_subset hp
  have hpopen : p ∈ openCoordTriangle a b :=
    (interior_closedCoordTriangle a b) ▸ hp
  have hrpos := weightedDiagonalRadius_pos hw hweight hc
    hpK.1 hpopen.2.1 hpK.2.2
  have hjAt : DifferentiableAt ℝ (weightedDiagonalQuadraticKernel w f) p :=
    (((contDiffOn_weightedDiagonalQuadraticKernel hab hw hf hGw hGf hdw hdf
      hderivw hderivf hweight hc).differentiableOn (by norm_num)).mono
        interior_subset).differentiableAt (isOpen_interior.mem_nhds hp)
  have hrAt : DifferentiableAt ℝ (weightedDiagonalRadius w) p :=
    (((contDiffOn_weightedDiagonalRadius hab hw hGw hdw hderivw).differentiableOn
      (by norm_num)).mono interior_subset).differentiableAt
        (isOpen_interior.mem_nhds hp)
  have hevent : weightedDiagonalQuotientKernel w f =ᶠ[𝓝 p]
      weightedDiagonalQuadraticKernel w f *
        (fun z => (weightedDiagonalRadius w z)⁻¹) := by
    have hopen : IsOpen (openCoordTriangle a b) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior
    filter_upwards [hopen.mem_nhds hpopen] with z hz
    simp [weightedDiagonalQuotientKernel, hz.2.1, div_eq_mul_inv]
  exact ((hjAt.mul (hrAt.inv hrpos.ne')).congr_of_eventuallyEq
    hevent).differentiableWithinAt

/-- The quotient kernel has a continuous first jet on a closed coordinate triangle. -/
theorem contDiffOn_weightedDiagonalQuotientKernel
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContDiffOn ℝ 1 (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) := by
  apply (convex_closedCoordTriangle a b).contDiffOn_one_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  · exact continuousOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc
  · exact continuousOn_weightedDiagonalQuotientKernelJet hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc
  · exact differentiableOn_weightedDiagonalQuotientKernel_interior hab hw hf
      hGw hGf hdw hdf hderivw hderivf hweight hc
  · intro p hp
    exact fderiv_weightedDiagonalQuotientKernel_interior hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc hp

/-- The continuous candidate jet is the relative derivative at every point
of the closed triangle. -/
theorem fderivWithin_weightedDiagonalQuotientKernel_eq_jet
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p =
        weightedDiagonalQuotientKernelJet a b w f Gw p := by
  exact (convex_closedCoordTriangle a b).fderivWithin_eq_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    (continuousOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc)
    (continuousOn_weightedDiagonalQuotientKernelJet hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc)
    (differentiableOn_weightedDiagonalQuotientKernel_interior hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc)
    (fun p hp => fderiv_weightedDiagonalQuotientKernel_interior hab hw hf
      hGw hGf hdw hdf hderivw hderivf hweight hc hp) hp

/-- On the diagonal, the quotient jet is the square of half the vertical
derivative of the input, times the normal coordinate difference. -/
theorem weightedDiagonalQuotientKernelJet_diag_apply
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u : ℝ} (hu : a ≤ u) (hub : u ≤ b) (q : ℝ × ℝ) :
    (weightedDiagonalQuotientKernelJet a b w f Gw (u, u)) q =
      (Gf (u, u) (0, 1)) ^ 2 / 4 * (q.2 - q.1) := by
  let K := closedCoordTriangle a b
  have hp : (u, u) ∈ K := ⟨hu, le_rfl, hub⟩
  have hwu : w (u, u) ≠ 0 := ne_of_gt (hc.trans_le (hweight (u, u) hp))
  have hF (e : ℝ × ℝ) :
      (fderivWithin ℝ (weightedDiagonalError w f) K (u, u)) e =
        (e.2 - e.1) / 2 * Gf (u, u) (0, 1) := by
    rw [fderivWithin_weightedDiagonalError_diag_apply hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc hu hub e]
    have he : (e.1, e.1 + (e.2 - e.1) / 2) =
        e - ((e.2 - e.1) / 2) • (0, 1) := by
      ext <;> simp [smul_eq_mul]; ring
    rw [he, map_sub, map_smul]
    simp only [smul_eq_mul]
    ring
  have hΦ : verticalJetMean
      (fderivWithin ℝ (weightedDiagonalError w f) K) (u, u) =
        Gf (u, u) (0, 1) / 2 := by
    rw [verticalJetMean_diag, hF (0, 1)]
    norm_num
    ring
  have hR := fderivWithin_weightedDiagonalRadius_diag_apply hab hw hGw
    hdw hderivw hu hub q
  dsimp [weightedDiagonalQuotientKernelJet]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [hΦ, normalizedDiagonalRadius_diag, hF q, hR]
  simp only [sub_self, zero_mul, zero_div, zero_add]
  field_simp [hwu]
  ring

/-- The relative derivative of the quotient kernel on the diagonal has
opposite horizontal and vertical components of magnitude `f_v² / 4`. -/
theorem fderivWithin_weightedDiagonalQuotientKernel_diag_apply
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u : ℝ} (hu : a ≤ u) (hub : u ≤ b) (q : ℝ × ℝ) :
    (fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) (u, u)) q =
      (Gf (u, u) (0, 1)) ^ 2 / 4 * (q.2 - q.1) := by
  have hp : (u, u) ∈ closedCoordTriangle a b := ⟨hu, le_rfl, hub⟩
  have hjet := fderivWithin_weightedDiagonalQuotientKernel_eq_jet hab
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hc hp
  rw [hjet]
  exact weightedDiagonalQuotientKernelJet_diag_apply hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hu hub q

end intervalIntegral

end
