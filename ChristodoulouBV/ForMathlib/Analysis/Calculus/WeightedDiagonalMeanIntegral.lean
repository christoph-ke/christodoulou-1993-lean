module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet

/-!
# Weighted means on coordinate triangles

The interval mean of a weight and a function is regular at the diagonal when the
weight stays positive.  The normalized interval representation makes its first
jet at the diagonal visible without differentiating a quotient by a vanishing
radius.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The integral of a weight along a vertical interval in the real plane. -/
@[expose] noncomputable def weightedDiagonalRadius (w : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in p.1..p.2, w (p.1, s)

/-- The integral of a weighted function along a vertical interval. -/
@[expose] noncomputable def weightedDiagonalNumerator (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in p.1..p.2, w (p.1, s) * f (p.1, s)

/-- The affine parametrization of the vertical interval from `(u,u)` to `(u,v)`. -/
@[expose] def diagonalSegment (p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  (p.1, p.1 + t * (p.2 - p.1))

/-- The linear map giving the derivative of the normalized vertical segment
with respect to its endpoint pair. -/
@[expose] noncomputable def diagonalSegmentFDeriv (t : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ) +
      t • ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ)))

/-- Evaluation of the derivative of the normalized vertical segment. -/
theorem diagonalSegmentFDeriv_apply (t : ℝ) (q : ℝ × ℝ) :
    diagonalSegmentFDeriv t q = (q.1, q.1 + t * (q.2 - q.1)) := by
  simp [diagonalSegmentFDeriv, smul_eq_mul]

/-- The normalized vertical segment is linear in its endpoint pair. -/
theorem hasFDerivAt_diagonalSegment (p : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt (fun q => diagonalSegment q t) (diagonalSegmentFDeriv t) p := by
  have heq : (fun q => diagonalSegment q t) = diagonalSegmentFDeriv t := by
    funext q
    exact (diagonalSegmentFDeriv_apply t q).symm
  rw [heq]
  exact (diagonalSegmentFDeriv t).hasFDerivAt

/-- The segment derivative depends continuously on the normalized parameter. -/
theorem continuous_diagonalSegmentFDeriv : Continuous diagonalSegmentFDeriv := by
  have h : Continuous (fun t : ℝ =>
      ((ContinuousLinearMap.fst ℝ ℝ ℝ),
        (ContinuousLinearMap.fst ℝ ℝ ℝ) +
          t • ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
            (ContinuousLinearMap.fst ℝ ℝ ℝ)))) := by
    fun_prop
  have h' := (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := ℝ × ℝ)
    (F := ℝ) (G := ℝ) ℝ).continuous.comp h
  have heq : ((ContinuousLinearMap.prodL (𝕜 := ℝ) (E := ℝ × ℝ)
      (F := ℝ) (G := ℝ) ℝ) ∘ fun t : ℝ =>
      ((ContinuousLinearMap.fst ℝ ℝ ℝ),
        (ContinuousLinearMap.fst ℝ ℝ ℝ) +
          t • ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
            (ContinuousLinearMap.fst ℝ ℝ ℝ)))) = diagonalSegmentFDeriv := by
    funext t
    simp [diagonalSegmentFDeriv]
  rw [heq] at h'
  exact h'

/-- The normalized weighted mean, defined on the whole plane.  On a triangle where
the weight is positive, this agrees with the quotient of the two interval integrals. -/
@[expose] noncomputable def weightedDiagonalMean (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, w (diagonalSegment p t) * f (diagonalSegment p t)) /
    (∫ t in (0 : ℝ)..1, w (diagonalSegment p t))

/-- The difference between a function and its weighted diagonal mean. -/
@[expose] noncomputable def weightedDiagonalError (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f p - weightedDiagonalMean w f p

private theorem intervalIntegrable_vertical {a b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b)) {u v : ℝ}
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    IntervalIntegrable (fun s => f (u, s)) volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le huv]
  apply hf.comp (continuous_const.prodMk continuous_id).continuousOn
  intro s hs
  simpa only [closedCoordTriangle, Set.mem_ofPred_eq, id_eq] using
    (show a ≤ u ∧ u ≤ s ∧ s ≤ b from ⟨hu, hs.1, hs.2.trans hv⟩)

/-- A positive weight bounds its vertical integral below by the interval length. -/
theorem mul_sub_le_weightedDiagonalRadius {a b c : ℝ} {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    c * (v - u) ≤ weightedDiagonalRadius w (u, v) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => c) volume u v := by simp
  have hle := intervalIntegral.integral_mono_on huv hconst
    (intervalIntegrable_vertical hw hu huv hv)
    (fun s hs => hweight (u, s) (by
      simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
        (show a ≤ u ∧ u ≤ s ∧ s ≤ b from ⟨hu, hs.1, hs.2.trans hv⟩)))
  simpa [weightedDiagonalRadius, mul_comm] using hle

/-- The weighted diagonal radius is strictly positive above the diagonal. -/
theorem weightedDiagonalRadius_pos {a b c : ℝ} {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u v : ℝ} (hu : a ≤ u) (huv : u < v) (hv : v ≤ b) :
    0 < weightedDiagonalRadius w (u, v) := by
  exact (mul_pos hc (sub_pos.mpr huv)).trans_le
    (mul_sub_le_weightedDiagonalRadius hw hweight hu huv.le hv)

/-- Rescaling the interval integral gives a fixed integration interval, including when
the two endpoints coincide. -/
theorem weightedDiagonalRadius_eq_mul_integral (w : ℝ × ℝ → ℝ) (u v : ℝ) :
    weightedDiagonalRadius w (u, v) =
      (v - u) * ∫ t in (0 : ℝ)..1, w (diagonalSegment (u, v) t) := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (f := fun s : ℝ => w (u, s)) (a := (0 : ℝ)) (b := 1) (v - u) u
  simpa [weightedDiagonalRadius, diagonalSegment, smul_eq_mul, mul_comm,
    mul_left_comm, mul_assoc] using h.symm

/-- The same rescaling for a weighted numerator. -/
theorem weightedDiagonalNumerator_eq_mul_integral (w f : ℝ × ℝ → ℝ) (u v : ℝ) :
    weightedDiagonalNumerator w f (u, v) =
      (v - u) * ∫ t in (0 : ℝ)..1,
        w (diagonalSegment (u, v) t) * f (diagonalSegment (u, v) t) := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (f := fun s : ℝ => w (u, s) * f (u, s)) (a := (0 : ℝ)) (b := 1) (v - u) u
  simpa [weightedDiagonalNumerator, diagonalSegment, smul_eq_mul, mul_comm,
    mul_left_comm, mul_assoc] using h.symm

/-- The normalized vertical segment stays in the closed coordinate triangle. -/
theorem diagonalSegment_mem_closedCoordTriangle {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    diagonalSegment p t ∈ closedCoordTriangle a b := by
  rcases p with ⟨u, v⟩
  have hp' : a ≤ u ∧ u ≤ v ∧ v ≤ b := by
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using hp
  have h₁ : 0 ≤ t * (v - u) := mul_nonneg ht.1 (sub_nonneg.mpr hp'.2.1)
  have h₂ : t * (v - u) ≤ v - u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hp'.2.1)]
  simpa only [diagonalSegment, closedCoordTriangle, Set.mem_ofPred_eq] using
    (show a ≤ u ∧ u ≤ u + t * (v - u) ∧ u + t * (v - u) ≤ b from
      ⟨hp'.1, by linarith, by linarith⟩)

/-- A positive normalized parameter sends an interior pair to an interior
point of the coordinate triangle. -/
theorem diagonalSegment_mem_openCoordTriangle {a b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ openCoordTriangle a b) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    diagonalSegment p t ∈ openCoordTriangle a b := by
  rcases p with ⟨u, v⟩
  have hp' : a < u ∧ u < v ∧ v < b := by
    simpa only [openCoordTriangle, Set.mem_ofPred_eq] using hp
  have h₁ : 0 < t * (v - u) := mul_pos ht.1 (sub_pos.mpr hp'.2.1)
  have h₂ : t * (v - u) ≤ v - u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hp'.2.1.le)]
  simpa only [diagonalSegment, openCoordTriangle, Set.mem_ofPred_eq] using
    (show a < u ∧ u < u + t * (v - u) ∧ u + t * (v - u) < b from
      ⟨hp'.1, by linarith, by linarith⟩)

private theorem continuous_diagonalSegment_uncurry :
    Continuous (fun pt : (ℝ × ℝ) × ℝ => diagonalSegment pt.1 pt.2) := by
  unfold diagonalSegment
  fun_prop

/-- The integral over the normalized vertical segment is continuous on the
closed triangle for every continuous integrand there. -/
theorem continuousOn_integral_diagonalSegment {a b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b)) :
    ContinuousOn (fun p => ∫ t in (0 : ℝ)..1, f (diagonalSegment p t))
      (closedCoordTriangle a b) := by
  let fK : C(closedCoordTriangle a b, ℝ) := ⟨_, hf.domRestrict⟩
  obtain ⟨F, hF⟩ :=
    fK.exists_restrict_eq (isClosed_closedCoordTriangle a b)
  have hF_eq : ∀ p ∈ closedCoordTriangle a b, F p = f p := by
    intro p hp
    have h := congrArg (fun H : C(closedCoordTriangle a b, ℝ) => H ⟨p, hp⟩) hF
    simpa [fK] using h
  have hcont : Continuous
      (fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, F (diagonalSegment p t)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact F.continuous.comp continuous_diagonalSegment_uncurry
  apply hcont.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact (hF_eq (diagonalSegment p t)
    (diagonalSegment_mem_closedCoordTriangle hp ht')).symm

private theorem intervalIntegrable_diagonalSegment {a b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b)) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    IntervalIntegrable (fun t => f (diagonalSegment p t)) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hseg : Continuous (fun t : ℝ => diagonalSegment p t) := by
    unfold diagonalSegment
    fun_prop
  exact hf.comp hseg.continuousOn
    (fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht)

/-- A positive weight has positive normalized vertical integral. -/
theorem integral_diagonalSegment_weight_ge {a b c : ℝ} {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    c ≤ ∫ t in (0 : ℝ)..1, w (diagonalSegment p t) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => c) volume (0 : ℝ) 1 := by simp
  have h := intervalIntegral.integral_mono_on
    (show (0 : ℝ) ≤ 1 by norm_num) hconst
    (intervalIntegrable_diagonalSegment hw hp)
    (fun t ht => hweight (diagonalSegment p t)
      (diagonalSegment_mem_closedCoordTriangle hp ht))
  simpa using h

/-- The fixed-interval definition of the weighted mean is continuous on the
closed triangle when the weight is uniformly positive there. -/
theorem continuousOn_weightedDiagonalMean {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContinuousOn (weightedDiagonalMean w f) (closedCoordTriangle a b) := by
  have hnum := continuousOn_integral_diagonalSegment (hw.mul hf)
  have hden := continuousOn_integral_diagonalSegment hw
  have hden_ne : ∀ p ∈ closedCoordTriangle a b,
      (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) ≠ 0 := by
    intro p hp
    exact ne_of_gt (hc.trans_le (integral_diagonalSegment_weight_ge hw hweight hp))
  change ContinuousOn
    (fun p => (∫ t in (0 : ℝ)..1,
      w (diagonalSegment p t) * f (diagonalSegment p t)) /
        (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)))
    (closedCoordTriangle a b)
  have heq :
      (fun p => ∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * f (diagonalSegment p t)) /
        (fun p => ∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) =
      (fun p => (∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * f (diagonalSegment p t)) /
          (∫ t in (0 : ℝ)..1, w (diagonalSegment p t))) := by
    funext p
    rfl
  rw [← heq]
  simpa only [Pi.mul_apply] using hnum.div hden hden_ne

/-- The continuous first jet of a normalized vertical integral. -/
@[expose] noncomputable def integralDiagonalSegmentJet
    (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1,
    (G (diagonalSegment p t)).comp (diagonalSegmentFDeriv t)

private theorem continuous_integralDiagonalSegmentJet_integrand
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ} (hG : Continuous G) :
    Continuous (fun pt : (ℝ × ℝ) × ℝ =>
      (G (diagonalSegment pt.1 pt.2)).comp (diagonalSegmentFDeriv pt.2)) := by
  have h₁ : Continuous (fun pt : (ℝ × ℝ) × ℝ => G (diagonalSegment pt.1 pt.2)) :=
    hG.comp continuous_diagonalSegment_uncurry
  have h₂ : Continuous (fun pt : (ℝ × ℝ) × ℝ => diagonalSegmentFDeriv pt.2) :=
    continuous_diagonalSegmentFDeriv.comp continuous_snd
  exact (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ).continuous₂.comp
    (h₁.prodMk h₂)

private theorem continuousOn_integralDiagonalSegmentJet_integrand
    {a b : ℝ} {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b)) :
    ContinuousOn (fun pt : (ℝ × ℝ) × ℝ =>
      (G (diagonalSegment pt.1 pt.2)).comp (diagonalSegmentFDeriv pt.2))
      (closedCoordTriangle a b ×ˢ Icc (0 : ℝ) 1) := by
  have hmaps : MapsTo
      (fun pt : (ℝ × ℝ) × ℝ => diagonalSegment pt.1 pt.2)
      (closedCoordTriangle a b ×ˢ Icc (0 : ℝ) 1)
      (closedCoordTriangle a b) := by
    intro pt hpt
    exact diagonalSegment_mem_closedCoordTriangle hpt.1 hpt.2
  have h₁ : ContinuousOn (fun pt : (ℝ × ℝ) × ℝ =>
      G (diagonalSegment pt.1 pt.2))
      (closedCoordTriangle a b ×ˢ Icc (0 : ℝ) 1) :=
    hG.comp continuous_diagonalSegment_uncurry.continuousOn hmaps
  have h₂ : ContinuousOn (fun pt : (ℝ × ℝ) × ℝ =>
      diagonalSegmentFDeriv pt.2)
      (closedCoordTriangle a b ×ˢ Icc (0 : ℝ) 1) :=
    (continuous_diagonalSegmentFDeriv.comp continuous_snd).continuousOn
  exact (ContinuousLinearMap.compL ℝ (ℝ × ℝ) (ℝ × ℝ) ℝ).continuous₂.comp_continuousOn
    (h₁.prodMk h₂)

/-- The integrated jet is continuous on the closed triangle whenever its
integrand is continuous there. -/
theorem continuousOn_integralDiagonalSegmentJet {a b : ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b)) :
    ContinuousOn (integralDiagonalSegmentJet G) (closedCoordTriangle a b) := by
  let GK : C(closedCoordTriangle a b, (ℝ × ℝ) →L[ℝ] ℝ) :=
    ⟨_, hG.domRestrict⟩
  obtain ⟨Gext, hGext⟩ :=
    GK.exists_restrict_eq (isClosed_closedCoordTriangle a b)
  have hext : ∀ p ∈ closedCoordTriangle a b, Gext p = G p := by
    intro p hp
    have h := congrArg
      (fun H : C(closedCoordTriangle a b, (ℝ × ℝ) →L[ℝ] ℝ) => H ⟨p, hp⟩) hGext
    simpa [GK] using h
  have hcont : Continuous (integralDiagonalSegmentJet Gext) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact continuous_integralDiagonalSegmentJet_integrand Gext.continuous
  apply hcont.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  change (G (diagonalSegment p t)).comp (diagonalSegmentFDeriv t) =
    (Gext (diagonalSegment p t)).comp (diagonalSegmentFDeriv t)
  rw [hext (diagonalSegment p t) (diagonalSegment_mem_closedCoordTriangle hp ht')]

/-- Differentiation under the normalized vertical integral in the interior
of a coordinate triangle.  The derivative field needs only a continuous
extension to the closed triangle. -/
theorem hasFDerivAt_integral_diagonalSegment {a b : ℝ}
    {f : ℝ × ℝ → ℝ} {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = G p)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    HasFDerivAt (fun q => ∫ t in (0 : ℝ)..1, f (diagonalSegment q t))
      (integralDiagonalSegmentJet G p) p := by
  have hopen : IsOpen (openCoordTriangle a b) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hmemK : ∀ q ∈ openCoordTriangle a b, q ∈ closedCoordTriangle a b := by
    intro q hq
    have hqi : q ∈ interior (closedCoordTriangle a b) := by
      simpa only [interior_closedCoordTriangle] using hq
    exact interior_subset hqi
  obtain ⟨M, hM⟩ := (isCompact_closedCoordTriangle a b).exists_bound_of_continuousOn hG
  obtain ⟨N, hN⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    continuous_diagonalSegmentFDeriv.continuousOn
  have hF_meas : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable
      (fun t => f (diagonalSegment q t)) (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    have hqK := hmemK q hq
    have hseg : Continuous (fun t : ℝ => diagonalSegment q t) := by
      unfold diagonalSegment
      fun_prop
    have hcont : ContinuousOn (fun t => f (diagonalSegment q t))
        (Icc (0 : ℝ) 1) :=
      hf.comp hseg.continuousOn
        (fun t ht => diagonalSegment_mem_closedCoordTriangle hqK ht)
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable (fun t => f (diagonalSegment p t)) volume 0 1 :=
    intervalIntegrable_diagonalSegment hf (hmemK p hp)
  have hF'_meas : AEStronglyMeasurable
      (fun t => (G (diagonalSegment p t)).comp (diagonalSegmentFDeriv t))
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    have hcont := (continuousOn_integralDiagonalSegmentJet_integrand hG).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hmemK p hp, ht⟩)
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
      ∀ q ∈ openCoordTriangle a b,
        ‖(G (diagonalSegment q t)).comp (diagonalSegmentFDeriv t)‖ ≤ M * N := by
    apply ae_of_all
    intro t ht q hq
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact Ioc_subset_Icc_self ht
    have hM' := hM (diagonalSegment q t)
      (diagonalSegment_mem_closedCoordTriangle (hmemK q hq) ht')
    have hN' := hN t ht'
    calc
      ‖(G (diagonalSegment q t)).comp (diagonalSegmentFDeriv t)‖ ≤
          ‖G (diagonalSegment q t)‖ * ‖diagonalSegmentFDeriv t‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * N := by
        have hMnonneg : 0 ≤ M := (norm_nonneg _).trans hM'
        gcongr
  have hbound_int : IntervalIntegrable (fun _ : ℝ => M * N) volume 0 1 := by simp
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
      ∀ q ∈ openCoordTriangle a b,
        HasFDerivAt (fun q => f (diagonalSegment q t))
          ((G (diagonalSegment q t)).comp (diagonalSegmentFDeriv t)) q := by
    apply ae_of_all
    intro t ht q hq
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hseg : diagonalSegment q t ∈ interior (closedCoordTriangle a b) := by
      rw [interior_closedCoordTriangle]
      exact diagonalSegment_mem_openCoordTriangle hq ht'
    have hfAt : DifferentiableAt ℝ f (diagonalSegment q t) :=
      hdiff.differentiableAt (isOpen_interior.mem_nhds hseg)
    have hf' : HasFDerivAt f (G (diagonalSegment q t)) (diagonalSegment q t) := by
      simpa only [hderiv (diagonalSegment q t) hseg] using hfAt.hasFDerivAt
    simpa only [Function.comp_def] using
      hf'.comp q (hasFDerivAt_diagonalSegment q t)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (hopen.mem_nhds hp) hF_meas hF_int hF'_meas hbound hbound_int h_diff

/-- The integrated interior jet extends to a relative derivative at every
point of the closed coordinate triangle. -/
theorem hasFDerivWithinAt_integral_diagonalSegment {a b : ℝ} (hab : a < b)
    {f : ℝ × ℝ → ℝ} {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = G p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    HasFDerivWithinAt (fun q => ∫ t in (0 : ℝ)..1, f (diagonalSegment q t))
      (integralDiagonalSegmentJet G p) (closedCoordTriangle a b) p := by
  let F : ℝ × ℝ → ℝ := fun q => ∫ t in (0 : ℝ)..1, f (diagonalSegment q t)
  have hFcont : ContinuousOn F (closedCoordTriangle a b) :=
    continuousOn_integral_diagonalSegment hf
  have hJcont : ContinuousOn (integralDiagonalSegmentJet G)
      (closedCoordTriangle a b) := continuousOn_integralDiagonalSegmentJet hG
  have hFdiff : DifferentiableOn ℝ F (interior (closedCoordTriangle a b)) := by
    intro q hq
    have hqo : q ∈ openCoordTriangle a b := by
      simpa only [interior_closedCoordTriangle] using hq
    exact (hasFDerivAt_integral_diagonalSegment hf hG hdiff hderiv hqo).differentiableAt
      |>.differentiableWithinAt
  have hFderiv : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ F q = integralDiagonalSegmentJet G q := by
    intro q hq
    have hqo : q ∈ openCoordTriangle a b := by
      simpa only [interior_closedCoordTriangle] using hq
    exact (hasFDerivAt_integral_diagonalSegment hf hG hdiff hderiv hqo).fderiv
  exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hFcont hJcont hFdiff hFderiv hp

/-- A normalized vertical integral of a function with continuous first jet
is `C¹` on a nondegenerate closed coordinate triangle. -/
theorem contDiffOn_integral_diagonalSegment {a b : ℝ} (hab : a < b)
    {f : ℝ × ℝ → ℝ} {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hdiff : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderiv : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = G p) :
    ContDiffOn ℝ 1 (fun q => ∫ t in (0 : ℝ)..1, f (diagonalSegment q t))
      (closedCoordTriangle a b) :=
  contDiffOn_one_of_continuousOn_hasFDerivWithinAt
    (continuousOn_integralDiagonalSegmentJet hG)
    (fun _ hp => hasFDerivWithinAt_integral_diagonalSegment hab hf hG hdiff hderiv hp)

/-- At a diagonal point, the integrated jet averages the two endpoint
directions with coefficients `1` and `1/2`. -/
theorem integralDiagonalSegmentJet_diag_apply
    (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) (u : ℝ) (q : ℝ × ℝ) :
    integralDiagonalSegmentJet G (u, u) q =
      G (u, u) (q.1, q.1 + (q.2 - q.1) / 2) := by
  have hLcont : Continuous (fun t : ℝ => diagonalSegmentFDeriv t q) := by
    exact continuous_diagonalSegmentFDeriv.clm_apply continuous_const
  have hLint : IntervalIntegrable (fun t : ℝ => diagonalSegmentFDeriv t q)
      volume (0 : ℝ) 1 := hLcont.intervalIntegrable 0 1
  have hCLcont : Continuous (fun t : ℝ =>
      (G (u, u)).comp (diagonalSegmentFDeriv t)) := by
    have hconstCL : Continuous (fun _ : ℝ => G (u, u)) := continuous_const
    exact hconstCL.clm_comp continuous_diagonalSegmentFDeriv
  have hCLint : IntervalIntegrable (fun t : ℝ =>
      (G (u, u)).comp (diagonalSegmentFDeriv t)) volume 0 1 :=
    hCLcont.intervalIntegrable 0 1
  have hvec : (∫ t in (0 : ℝ)..1, diagonalSegmentFDeriv t q) =
      (q.1, q.1 + (q.2 - q.1) / 2) := by
    apply Prod.ext
    · have hfst := (ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hLint
      have hconst : (∫ _t in (0 : ℝ)..1, q.1) = q.1 := by simp
      simpa [diagonalSegmentFDeriv_apply, hconst] using hfst.symm
    · have hsnd := (ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hLint
      have hconst : (∫ _t in (0 : ℝ)..1, q.1) = q.1 := by simp
      have hid : (∫ t in (0 : ℝ)..1, t) = (1 : ℝ) / 2 := by
        norm_num [integral_id]
      simpa [diagonalSegmentFDeriv_apply, intervalIntegral.integral_add,
        intervalIntegral.integral_mul_const, hconst, hid, div_eq_mul_inv, mul_comm] using hsnd.symm
  have happ := ContinuousLinearMap.intervalIntegral_apply hCLint q
  have hcomp := (G (u, u)).intervalIntegral_comp_comm hLint
  simp only [integralDiagonalSegmentJet, diagonalSegment, sub_self, mul_zero, add_zero] at happ ⊢
  rw [happ]
  simp_rw [ContinuousLinearMap.comp_apply]
  rw [hcomp, hvec]

/-- Above the diagonal, the fixed-interval mean is the quotient of the two
moving-endpoint integrals. -/
theorem weightedDiagonalMean_eq_div {w f : ℝ × ℝ → ℝ}
    {u v : ℝ} (huv : u ≠ v) :
    weightedDiagonalMean w f (u, v) =
      weightedDiagonalNumerator w f (u, v) / weightedDiagonalRadius w (u, v) := by
  have hd : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  rw [weightedDiagonalNumerator_eq_mul_integral,
    weightedDiagonalRadius_eq_mul_integral]
  simp only [weightedDiagonalMean]
  rw [mul_div_mul_left _ _ hd]

/-- The mean takes the value of the function on the diagonal whenever the
weight there is nonzero. -/
theorem weightedDiagonalMean_diag {w f : ℝ × ℝ → ℝ} {u : ℝ}
    (hw : w (u, u) ≠ 0) : weightedDiagonalMean w f (u, u) = f (u, u) := by
  simp [weightedDiagonalMean, diagonalSegment, hw]

/-- The weighted mean error vanishes on the diagonal. -/
theorem weightedDiagonalError_diag {w f : ℝ × ℝ → ℝ} {u : ℝ}
    (hw : w (u, u) ≠ 0) : weightedDiagonalError w f (u, u) = 0 := by
  simp [weightedDiagonalError, weightedDiagonalMean_diag hw]

/-- Cancellation formula for the weighted mean error.  The identity is stated for arbitrary
continuous real functions and is used in local existence. -/
theorem weightedDiagonalError_eq_integral {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u v : ℝ} (hu : a ≤ u) (huv : u < v) (hv : v ≤ b) :
    weightedDiagonalError w f (u, v) =
      (weightedDiagonalRadius w (u, v))⁻¹ *
        ∫ s in u..v, w (u, s) * (f (u, v) - f (u, s)) := by
  have hiw := intervalIntegrable_vertical hw hu huv.le hv
  have hiwf : IntervalIntegrable (fun s => w (u, s) * f (u, s)) volume u v := by
    simpa only [Pi.mul_apply] using intervalIntegrable_vertical (hw.mul hf) hu huv.le hv
  have hconst : IntervalIntegrable (fun s => w (u, s) * f (u, v)) volume u v :=
    hiw.mul_const _
  have hI : (∫ s in u..v, w (u, s) * (f (u, v) - f (u, s))) =
      weightedDiagonalRadius w (u, v) * f (u, v) -
        weightedDiagonalNumerator w f (u, v) := by
    simp only [mul_sub, intervalIntegral.integral_sub hconst hiwf,
      intervalIntegral.integral_mul_const, weightedDiagonalRadius,
      weightedDiagonalNumerator]
  have hr := weightedDiagonalRadius_pos hw hweight hc hu huv hv
  rw [hI, weightedDiagonalError, weightedDiagonalMean_eq_div huv.ne]
  field_simp [hr.ne']

/-- A bound for the vertical component of a relative first jet gives a vertical
Lipschitz estimate on a coordinate triangle. -/
theorem norm_sub_vertical_le_of_jet {a b B : ℝ} {f : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (G p) (closedCoordTriangle a b) p)
    (hbound : ∀ p ∈ closedCoordTriangle a b, ‖G p (0, 1)‖ ≤ B)
    {u s v : ℝ} (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b) :
    ‖f (u, v) - f (u, s)‖ ≤ B * (v - s) := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u v) (closedCoordTriangle a b) := by
    intro t ht
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ u ∧ u ≤ t ∧ t ≤ b from ⟨hu, ht.1, ht.2.trans hv⟩)
  have hderiv : ∀ t ∈ Icc u v,
      HasDerivWithinAt (fun t : ℝ => f (u, t)) (G (u, t) (0, 1)) (Icc u v) t := by
    intro t ht
    have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) t := by
      exact (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
    simpa only [Function.comp_def] using
      (hjet (u, t) (hmap ht)).comp_hasDerivWithinAt t
        hpair.hasDerivWithinAt hmap
  have hb : ∀ t ∈ Icc u v, ‖G (u, t) (0, 1)‖ ≤ B := by
    intro t ht
    exact hbound (u, t) (hmap ht)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hb
    (convex_Icc u v) ⟨hus, hsv⟩ ⟨hus.trans hsv, le_refl v⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsv)] using h

/-- The error of a positive weighted mean is bounded by the vertical jet bound
times the distance from the diagonal. -/
theorem abs_weightedDiagonalError_le_of_jet {a b c B : ℝ}
    {w f : ℝ × ℝ → ℝ} {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) (hB : 0 ≤ B)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (G p) (closedCoordTriangle a b) p)
    (hbound : ∀ p ∈ closedCoordTriangle a b, ‖G p (0, 1)‖ ≤ B)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    |weightedDiagonalError w f (u, v)| ≤ B * (v - u) := by
  rcases eq_or_lt_of_le huv with rfl | huv
  · have hmem : (u, u) ∈ closedCoordTriangle a b := by
      simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
        (show a ≤ u ∧ u ≤ u ∧ u ≤ b from ⟨hu, le_rfl, hv⟩)
    have hwu : w (u, u) ≠ 0 := ne_of_gt (hc.trans_le (hweight (u, u) hmem))
    simp [weightedDiagonalError_diag hwu]
  let D := B * (v - u)
  let I := ∫ s in u..v, w (u, s) * (f (u, v) - f (u, s))
  have hiw := intervalIntegrable_vertical hw hu huv.le hv
  have hiA : IntervalIntegrable (fun s => w (u, s) * (f (u, v) - f (u, s)))
      volume u v :=
    intervalIntegrable_vertical (hw.mul (continuousOn_const.sub hf)) hu huv.le hv
  have hiD : IntervalIntegrable (fun s => D * w (u, s)) volume u v :=
    hiw.const_mul D
  have hpoint : ∀ s ∈ Icc u v,
      |w (u, s) * (f (u, v) - f (u, s))| ≤ D * w (u, s) := by
    intro s hs
    have hws : 0 ≤ w (u, s) :=
      (hc.le.trans (hweight (u, s) (by
        simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
          (show a ≤ u ∧ u ≤ s ∧ s ≤ b from ⟨hu, hs.1, hs.2.trans hv⟩))))
    have hdiff : |f (u, v) - f (u, s)| ≤ D := by
      have h := norm_sub_vertical_le_of_jet hjet hbound hu hs.1 hs.2 hv
      have hdist : B * (v - s) ≤ D :=
        mul_le_mul_of_nonneg_left (by linarith [hs.1]) hB
      exact h.trans hdist
    rw [abs_mul, abs_of_nonneg hws]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdiff hws
  have hupper : I ≤ D * weightedDiagonalRadius w (u, v) := by
    have h := intervalIntegral.integral_mono_on huv.le hiA hiD
      (fun s hs => le_of_abs_le (hpoint s hs))
    simpa [I, weightedDiagonalRadius] using h
  have hlower : -I ≤ D * weightedDiagonalRadius w (u, v) := by
    have h := intervalIntegral.integral_mono_on huv.le hiA.neg hiD
      (fun s hs => by
        have hs' := (abs_le.mp (hpoint s hs)).1
        change -(w (u, s) * (f (u, v) - f (u, s))) ≤ D * w (u, s)
        linarith only [hs'])
    simpa [I, weightedDiagonalRadius] using h
  have hI : |I| ≤ D * weightedDiagonalRadius w (u, v) :=
    abs_le.mpr ⟨by linarith, hupper⟩
  have hr := weightedDiagonalRadius_pos hw hweight hc hu huv hv
  rw [weightedDiagonalError_eq_integral hw hf hweight hc hu huv hv]
  change |(weightedDiagonalRadius w (u, v))⁻¹ * I| ≤ D
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hr.le)]
  calc
    (weightedDiagonalRadius w (u, v))⁻¹ * |I| ≤
        (weightedDiagonalRadius w (u, v))⁻¹ *
          (D * weightedDiagonalRadius w (u, v)) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hr.le)
    _ = D := by field_simp [hr.ne']

/-- The weighted-mean error is controlled by the supremum of the vertical
component of the function's continuous first jet on the compact triangle. -/
theorem abs_weightedDiagonalError_le_csSup_vertical_jet {a b c : ℝ}
    (hab : a < b) {w f : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (G p) (closedCoordTriangle a b) p)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    |weightedDiagonalError w f (u, v)| ≤
      sSup ((fun p => ‖G p (0, 1)‖) '' closedCoordTriangle a b) * (v - u) := by
  have hcont : ContinuousOn (fun p => ‖G p (0, 1)‖)
      (closedCoordTriangle a b) :=
    (hG.clm_apply continuousOn_const).norm
  have hupper : BddAbove ((fun p => ‖G p (0, 1)‖) ''
      closedCoordTriangle a b) :=
    ((isCompact_closedCoordTriangle a b).image_of_continuousOn hcont).bddAbove
  have hp0 : (a, a) ∈ closedCoordTriangle a b := by
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ a ∧ a ≤ a ∧ a ≤ b from ⟨le_rfl, le_rfl, hab.le⟩)
  have hB : 0 ≤ sSup ((fun p => ‖G p (0, 1)‖) ''
      closedCoordTriangle a b) :=
    (norm_nonneg (G (a, a) (0, 1))).trans
      (le_csSup hupper ⟨(a, a), hp0, rfl⟩)
  apply abs_weightedDiagonalError_le_of_jet hw hf hweight hc hB hjet
    (fun p hp => le_csSup hupper ⟨p, hp, rfl⟩) hu huv hv

end intervalIntegral

end
