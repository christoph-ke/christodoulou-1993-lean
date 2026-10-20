module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanDerivativeEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Horizontal derivatives of weighted diagonal means

The normalized interval representation permits differentiation in the first
coordinate without differentiating a moving lower endpoint.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- Integration by parts for the affine weight vanishing at the right endpoint
of the unit interval. -/
theorem integral_one_sub_mul_deriv_eq_integral_sub
    {g g' : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hg' : ContinuousOn g' (Icc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t) :
    (∫ t in (0 : ℝ)..1, (1 - t) * g' t) =
      (∫ t in (0 : ℝ)..1, g t) - g 0 := by
  have hu : ContinuousOn (fun t : ℝ => 1 - t) (Icc 0 1) := by fun_prop
  have hu' : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
    intro t ht
    convert (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t) using 1
    ring
  have hiu : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume 0 1 := by simp
  have hig : IntervalIntegrable g' volume 0 1 := hg'.intervalIntegrable_of_Icc (by norm_num)
  have huI : ContinuousOn (fun t : ℝ => 1 - t) [[0, 1]] := by simpa using hu
  have hgI : ContinuousOn g [[0, 1]] := by simpa using hg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    huI hgI (fun t ht => hu' t (by simpa using ht))
    (fun t ht => hderiv t (by simpa using ht)) hiu hig
  simp only [sub_self, zero_mul, sub_zero, one_mul, neg_one_mul,
    intervalIntegral.integral_neg, zero_sub] at h
  linarith

/-- If a differentiable function has zero average on the unit interval, the
affine-weighted average of its derivative is its negative left trace. -/
theorem integral_one_sub_mul_of_integral_eq_zero
    {g h : ℝ → ℝ} {d : ℝ} (hd : d ≠ 0)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (d * h t) t)
    (hzero : (∫ t in (0 : ℝ)..1, g t) = 0) :
    (∫ t in (0 : ℝ)..1, (1 - t) * h t) = -g 0 / d := by
  have hg' : ContinuousOn (fun t => d * h t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul hh
  have hident := integral_one_sub_mul_deriv_eq_integral_sub hg hg' hderiv
  have heq : (∫ t in (0 : ℝ)..1, (1 - t) * (d * h t)) =
      d * (∫ t in (0 : ℝ)..1, (1 - t) * h t) := by
    simp_rw [show ∀ t : ℝ, (1 - t) * (d * h t) = d * ((1 - t) * h t) from
      fun t => by ring]
    exact integral_const_mul _ _
  rw [heq, hzero] at hident
  exact (eq_div_iff hd).2 (by linarith [hident])

/-- The horizontal component of the jet of a normalized vertical integral.
The point `(1, 1-t)` is the derivative of the segment with respect to its
first endpoint. -/
theorem integralDiagonalSegmentJet_horizontal
    {a b : ℝ} (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (p : ℝ × ℝ) (hp : p ∈ closedCoordTriangle a b) :
    (integralDiagonalSegmentJet G p) (1, 0) =
      ∫ t in (0 : ℝ)..1, G (diagonalSegment p t) (1, 1 - t) := by
  have hint : IntervalIntegrable
      (fun t : ℝ => (G (diagonalSegment p t)).comp (diagonalSegmentFDeriv t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
      unfold diagonalSegment
      fun_prop
    have hGseg : ContinuousOn (fun t : ℝ => G (diagonalSegment p t)) (Icc 0 1) :=
      hG.comp hseg (fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht)
    exact hGseg.clm_comp continuous_diagonalSegmentFDeriv.continuousOn
  rw [integralDiagonalSegmentJet,
    ContinuousLinearMap.intervalIntegral_apply hint]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [ContinuousLinearMap.comp_apply,
    diagonalSegmentFDeriv_apply]
  congr 1
  ext <;> (simp; try ring)

/-- Along a fixed vertical segment, the normalized parameter has velocity
equal to the endpoint gap in the second coordinate. -/
theorem hasDerivAt_diagonalSegment_parameter (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (diagonalSegment p) (0, p.2 - p.1) t := by
  unfold diagonalSegment
  have hfirst : HasDerivAt (fun _ : ℝ => p.1) 0 t := hasDerivAt_const t p.1
  have hsecond : HasDerivAt (fun t : ℝ => p.1 + t * (p.2 - p.1))
      (p.2 - p.1) t := by
    convert (hasDerivAt_const t p.1).add
      ((hasDerivAt_id' t).mul_const (p.2 - p.1)) using 1 <;> ring
  exact hfirst.prodMk hsecond

/-- Split the derivative of a diagonal segment into the coordinate directions. -/
theorem horizontal_segment_direction (G : (ℝ × ℝ) →L[ℝ] ℝ) (t : ℝ) :
    G (1, 1 - t) = G (1, 0) + (1 - t) * G (0, 1) := by
  have hpair : ((1 : ℝ), 1 - t) = ((1 : ℝ), 0) + (1 - t) • ((0 : ℝ), 1) := by
    ext <;> simp
  rw [hpair, map_add, map_smul]
  simp only [smul_eq_mul]

/-- The centered integrand of a normalized weighted mean has integral zero. -/
theorem integral_weight_mul_sub_mean_eq_zero
    {W F : ℝ → ℝ}
    (hW : ContinuousOn W (Icc (0 : ℝ) 1))
    (hF : ContinuousOn F (Icc (0 : ℝ) 1))
    (hden : (∫ t in (0 : ℝ)..1, W t) ≠ 0) :
    (∫ t in (0 : ℝ)..1,
        W t * (F t -
          (∫ s in (0 : ℝ)..1, W s * F s) /
            (∫ s in (0 : ℝ)..1, W s))) = 0 := by
  let m : ℝ := (∫ s in (0 : ℝ)..1, W s * F s) /
    (∫ s in (0 : ℝ)..1, W s)
  have hWi : IntervalIntegrable W volume 0 1 :=
    hW.intervalIntegrable_of_Icc (by norm_num)
  have hWFi : IntervalIntegrable (fun t => W t * F t) volume 0 1 :=
    (hW.mul hF).intervalIntegrable_of_Icc (by norm_num)
  have hident : (∫ t in (0 : ℝ)..1, W t * (F t - m)) =
      (∫ t in (0 : ℝ)..1, W t * F t) -
        m * (∫ t in (0 : ℝ)..1, W t) := by
    simp_rw [mul_sub, mul_comm (W _) m]
    rw [intervalIntegral.integral_sub hWFi (hWi.const_mul m)]
    rw [intervalIntegral.integral_const_mul]
  change (∫ t in (0 : ℝ)..1, W t * (F t - m)) = 0
  rw [hident]
  dsimp [m]
  field_simp [hden]
  ring

/-- A positive weighted average stays within a uniform bound of any fixed
anchor value of the averaged function. -/
theorem abs_weighted_integral_mean_sub_anchor_le
    {W F : ℝ → ℝ} {c M : ℝ}
    (hc : 0 < c)
    (hW : ContinuousOn W (Icc (0 : ℝ) 1))
    (hF : ContinuousOn F (Icc (0 : ℝ) 1))
    (x : ℝ)
    (hweight : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ W t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |F t - F x| ≤ M) :
    |(∫ t in (0 : ℝ)..1, W t * F t) /
        (∫ t in (0 : ℝ)..1, W t) - F x| ≤ M := by
  let D := ∫ t in (0 : ℝ)..1, W t
  let I := ∫ t in (0 : ℝ)..1, W t * (F t - F x)
  have hWi : IntervalIntegrable W volume 0 1 :=
    hW.intervalIntegrable_of_Icc (by norm_num)
  have hIi : IntervalIntegrable (fun t => W t * (F t - F x)) volume 0 1 :=
    (hW.mul (hF.sub continuousOn_const)).intervalIntegrable_of_Icc (by norm_num)
  have hMi : IntervalIntegrable (fun t => M * W t) volume 0 1 := hWi.const_mul M
  have hD : 0 < D := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      (continuous_const.intervalIntegrable _ _) hWi hweight
    have hh : c ≤ D := by simpa [D] using h
    exact hc.trans_le hh
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      |W t * (F t - F x)| ≤ M * W t := by
    intro t ht
    have hwt : 0 ≤ W t := hc.le.trans (hweight t ht)
    rw [abs_mul, abs_of_nonneg hwt]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound t ht) hwt
  have hI : |I| ≤ M * D := by
    have hup := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hIi hMi (fun t ht => le_of_abs_le (hpoint t ht))
    have hlo := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hIi.neg hMi (fun t ht => by
        change -(W t * (F t - F x)) ≤ M * W t
        linarith [(abs_le.mp (hpoint t ht)).1])
    simp only [intervalIntegral.integral_const_mul] at hup hlo
    have hupper : I ≤ M * D := by simpa [I, D] using hup
    have hlower : -I ≤ M * D := by
      simpa [I, D, intervalIntegral.integral_neg] using hlo
    exact abs_le.mpr ⟨by linarith, hupper⟩
  have hident : (∫ t in (0 : ℝ)..1, W t * F t) / D - F x = I / D := by
    have hWFi : IntervalIntegrable (fun t => W t * F t) volume 0 1 :=
      (hW.mul hF).intervalIntegrable_of_Icc (by norm_num)
    have hIeq : I = (∫ t in (0 : ℝ)..1, W t * F t) - F x * D := by
      dsimp [I, D]
      simp_rw [mul_sub, mul_comm (W _) (F x)]
      rw [intervalIntegral.integral_sub hWFi (hWi.const_mul (F x)),
        intervalIntegral.integral_const_mul]
    rw [hIeq]
    field_simp [hD.ne']
  change |(∫ t in (0 : ℝ)..1, W t * F t) / D - F x| ≤ M
  rw [hident, abs_div, abs_of_pos hD]
  exact (div_le_iff₀ hD).2 hI

/-- A positive weighted diagonal mean stays within one vertical Lipschitz
distance of the value at its lower endpoint. -/
theorem abs_weightedDiagonalMean_sub_lower_le_of_jet
    {a b c B : ℝ} {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) (hB : 0 ≤ B)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf p) (closedCoordTriangle a b) p)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    |weightedDiagonalMean w f (u, v) - f (u, u)| ≤ B * (v - u) := by
  let p : ℝ × ℝ := (u, v)
  let W : ℝ → ℝ := fun t => w (diagonalSegment p t)
  let F : ℝ → ℝ := fun t => f (diagonalSegment p t)
  have hp : p ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (diagonalSegment p) (Icc (0 : ℝ) 1)
      (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have hW : ContinuousOn W (Icc (0 : ℝ) 1) := hw.comp hseg hmap
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := hf.comp hseg hmap
  have hWlower : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ W t :=
    fun t ht => hweight _ (hmap ht)
  have hFbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t - F 0| ≤ B * (v - u) := by
    intro t ht
    let s := u + t * (v - u)
    have hd : 0 ≤ v - u := sub_nonneg.mpr huv
    have hus : u ≤ s := by dsimp [s]; nlinarith [mul_nonneg ht.1 hd]
    have hsv : s ≤ v := by
      dsimp [s]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hd]
    have hbound := norm_sub_vertical_le_of_jet hjet
      (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical z hz)
      hu le_rfl hus (hsv.trans hv)
    have hmul : B * (s - u) ≤ B * (v - u) :=
      mul_le_mul_of_nonneg_left (by linarith [hsv]) hB
    have h := hbound.trans hmul
    simpa [F, p, s, diagonalSegment, Real.norm_eq_abs] using h
  have h := abs_weighted_integral_mean_sub_anchor_le hc hW hF 0 hWlower hFbound
  simpa [W, F, p, weightedDiagonalMean, diagonalSegment] using h

/-- A positive weighted diagonal mean is at most one vertical Lipschitz
distance from every point of its averaging segment. -/
theorem abs_weightedDiagonalMean_sub_segment_le_of_jet
    {a b c B : ℝ} {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) (hB : 0 ≤ B)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf p) (closedCoordTriangle a b) p)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    {u v t : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |weightedDiagonalMean w f (u, v) -
      f (diagonalSegment (u, v) t)| ≤ B * (v - u) := by
  let p : ℝ × ℝ := (u, v)
  let s (t : ℝ) := u + t * (v - u)
  let W : ℝ → ℝ := fun t => w (diagonalSegment p t)
  let F : ℝ → ℝ := fun t => f (diagonalSegment p t)
  have hp : p ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (diagonalSegment p) (Icc (0 : ℝ) 1)
      (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have hW : ContinuousOn W (Icc (0 : ℝ) 1) := hw.comp hseg hmap
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := hf.comp hseg hmap
  have hWlower : ∀ x ∈ Icc (0 : ℝ) 1, c ≤ W x :=
    fun x hx => hweight _ (hmap hx)
  have hloc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : u ≤ s x ∧ s x ≤ v := by
    have hd : 0 ≤ v - u := sub_nonneg.mpr huv
    constructor
    · dsimp [s]
      nlinarith [mul_nonneg hx.1 hd]
    · dsimp [s]
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hd]
  have hFbound : ∀ x ∈ Icc (0 : ℝ) 1, |F x - F t| ≤ B * (v - u) := by
    intro x hx
    obtain ⟨hux, hxv⟩ := hloc x hx
    obtain ⟨hut, htv⟩ := hloc t ht
    have hdiff : |f (u, s x) - f (u, s t)| ≤ B * |s x - s t| := by
      rcases le_total (s x) (s t) with hxt | htx
      · have h := norm_sub_vertical_le_of_jet hjet
          (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical z hz)
          hu hux hxt (htv.trans hv)
        simpa only [Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.mpr hxt)] using h
      · have h := norm_sub_vertical_le_of_jet hjet
          (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical z hz)
          hu hut htx (hxv.trans hv)
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr htx)] using h
    have hgap : |s x - s t| ≤ v - u := by
      apply abs_le.mpr
      constructor <;> linarith
    have hmul := mul_le_mul_of_nonneg_left hgap hB
    simpa only [F, p, diagonalSegment, s] using hdiff.trans hmul
  have h := abs_weighted_integral_mean_sub_anchor_le hc hW hF t hWlower hFbound
  simpa only [W, F, p, weightedDiagonalMean] using h

/-- Integration by parts isolates the contribution of the moving lower
endpoint in the horizontal derivative of a normalized weighted mean. -/
theorem integral_one_sub_weighted_vertical_jet_eq_endpoint
    {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
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
    (hc : 0 < c) {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    (∫ t in (0 : ℝ)..1,
      (1 - t) *
        (Gw (diagonalSegment p t) (0, 1) *
            (f (diagonalSegment p t) - weightedDiagonalMean w f p) +
          w (diagonalSegment p t) * Gf (diagonalSegment p t) (0, 1))) =
      w (p.1, p.1) * (weightedDiagonalMean w f p - f (p.1, p.1)) /
        (p.2 - p.1) := by
  let K := closedCoordTriangle a b
  let S : ℝ → ℝ × ℝ := diagonalSegment p
  let W : ℝ → ℝ := fun t => w (S t)
  let F : ℝ → ℝ := fun t => f (S t)
  let m : ℝ := weightedDiagonalMean w f p
  let g : ℝ → ℝ := fun t => W t * (F t - m)
  let h : ℝ → ℝ := fun t =>
    Gw (S t) (0, 1) * (F t - m) + W t * Gf (S t) (0, 1)
  have hpK : p ∈ K := by
    rw [← interior_closedCoordTriangle] at hp
    exact interior_subset hp
  have hpstrict : a < p.1 ∧ p.1 < p.2 ∧ p.2 < b := hp
  have hd : p.2 - p.1 ≠ 0 := (sub_pos.mpr hpstrict.2.1).ne'
  have hseg : ContinuousOn S (Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (p.1, p.1 + t * (p.2 - p.1))) (Icc 0 1)
    fun_prop
  have hmap : MapsTo S (Icc (0 : ℝ) 1) K :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hpK ht
  have hW : ContinuousOn W (Icc (0 : ℝ) 1) := hw.comp hseg hmap
  have hF : ContinuousOn F (Icc (0 : ℝ) 1) := hf.comp hseg hmap
  have hGwS : ContinuousOn (fun t => Gw (S t) (0, 1)) (Icc (0 : ℝ) 1) :=
    (hGw.comp hseg hmap).clm_apply continuousOn_const
  have hGfS : ContinuousOn (fun t => Gf (S t) (0, 1)) (Icc (0 : ℝ) 1) :=
    (hGf.comp hseg hmap).clm_apply continuousOn_const
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := hW.mul (hF.sub continuousOn_const)
  have hh : ContinuousOn h (Icc (0 : ℝ) 1) :=
    (hGwS.mul (hF.sub continuousOn_const)).add (hW.mul hGfS)
  have hWderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt W ((p.2 - p.1) * Gw (S t) (0, 1)) t := by
    have hpt : S t ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact diagonalSegment_mem_openCoordTriangle hp (Ioo_subset_Ioc_self ht)
    have hwAt : HasFDerivAt w (Gw (S t)) (S t) := by
      rw [← hderivw (S t) hpt]
      exact (hdw.differentiableAt (isOpen_interior.mem_nhds hpt)).hasFDerivAt
    have h := hwAt.comp_hasDerivAt t (hasDerivAt_diagonalSegment_parameter p t)
    have heq : ((0 : ℝ), p.2 - p.1) = (p.2 - p.1) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    simpa only [W, S, Function.comp_def, heq, map_smul, smul_eq_mul] using h
  have hFderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F ((p.2 - p.1) * Gf (S t) (0, 1)) t := by
    have hpt : S t ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact diagonalSegment_mem_openCoordTriangle hp (Ioo_subset_Ioc_self ht)
    have hfAt : HasFDerivAt f (Gf (S t)) (S t) := by
      rw [← hderivf (S t) hpt]
      exact (hdf.differentiableAt (isOpen_interior.mem_nhds hpt)).hasFDerivAt
    have h := hfAt.comp_hasDerivAt t (hasDerivAt_diagonalSegment_parameter p t)
    have heq : ((0 : ℝ), p.2 - p.1) = (p.2 - p.1) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    simpa only [F, S, Function.comp_def, heq, map_smul, smul_eq_mul] using h
  have hgderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt g ((p.2 - p.1) * h t) t := by
    intro t ht
    have hderivprod := (hWderiv t ht).mul ((hFderiv t ht).sub_const m)
    convert hderivprod using 1 <;> (dsimp [g, h]; ring)
  have hden : (∫ t in (0 : ℝ)..1, W t) ≠ 0 :=
    ne_of_gt (hc.trans_le (integral_diagonalSegment_weight_ge hw hweight hpK))
  have hzero : (∫ t in (0 : ℝ)..1, g t) = 0 := by
    simpa only [g, W, F, m, S, weightedDiagonalMean] using
      integral_weight_mul_sub_mean_eq_zero hW hF hden
  have hcancel := integral_one_sub_mul_of_integral_eq_zero hd hg hh hgderiv hzero
  change (∫ t in (0 : ℝ)..1, (1 - t) * h t) = _
  rw [hcancel]
  dsimp [g, W, F, S, diagonalSegment, m]
  ring

/-- The horizontal derivative of the weighted diagonal error, expressed using
the first jets of two normalized integrals. This formula holds at every point
of a closed triangle, including the diagonal. -/
theorem fderivWithin_weightedDiagonalError_horizontal_eq
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
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) p) (1, 0) =
      Gf p (1, 0) -
        ((integralDiagonalSegmentJet (w • Gf + f • Gw) p) (1, 0) -
          weightedDiagonalMean w f p *
            (integralDiagonalSegmentJet Gw p) (1, 0)) /
          (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) := by
  let K := closedCoordTriangle a b
  let N : ℝ × ℝ → ℝ := fun z =>
    ∫ t in (0 : ℝ)..1, (w * f) (diagonalSegment z t)
  let D : ℝ × ℝ → ℝ := fun z =>
    ∫ t in (0 : ℝ)..1, w (diagonalSegment z t)
  let Gprod : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := w • Gf + f • Gw
  have hprod : ContinuousOn (w * f) K := hw.mul hf
  have hGprod : ContinuousOn Gprod K := (hw.smul hGf).add (hf.smul hGw)
  have hdiffprod : DifferentiableOn ℝ (w * f) (interior K) := hdw.mul hdf
  have hderivprod : ∀ z ∈ interior K, fderiv ℝ (w * f) z = Gprod z := by
    intro z hz
    have hwAt := hdw.differentiableAt (isOpen_interior.mem_nhds hz)
    have hfAt := hdf.differentiableAt (isOpen_interior.mem_nhds hz)
    change fderiv ℝ (w * f) z = w z • Gf z + f z • Gw z
    rw [← hderivw z hz, ← hderivf z hz]
    exact fderiv_mul hwAt hfAt
  have hN : HasFDerivWithinAt N (integralDiagonalSegmentJet Gprod p) K p :=
    hasFDerivWithinAt_integral_diagonalSegment hab hprod hGprod hdiffprod hderivprod hp
  have hD : HasFDerivWithinAt D (integralDiagonalSegmentJet Gw p) K p :=
    hasFDerivWithinAt_integral_diagonalSegment hab hw hGw hdw hderivw hp
  have hDpos : 0 < D p :=
    hc.trans_le (integral_diagonalSegment_weight_ge hw hweight hp)
  have hF : HasFDerivWithinAt f (Gf p) K p :=
    (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf hGf hdf hderivf hp
  have hInv : HasFDerivWithinAt (fun z => (D z)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(D p ^ 2)⁻¹)).comp
        (integralDiagonalSegmentJet Gw p)) K p := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_inv hDpos.ne').comp_hasFDerivWithinAt p hD
  have hmul := hN.mul hInv
  have hEqMean : EqOn (weightedDiagonalMean w f)
      (N * fun z => (D z)⁻¹) K := by
    intro z hz
    simp [weightedDiagonalMean, N, D, div_eq_mul_inv, Pi.mul_apply]
  have hmean := hmul.congr' hEqMean hp
  have hH := hF.sub hmean
  have hunique : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)) p hp
  have hjet := hH.fderivWithin hunique
  change (fderivWithin ℝ (f - weightedDiagonalMean w f) K p) (1, 0) = _
  rw [hjet]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  have hNval : N p = weightedDiagonalMean w f p * D p := by
    simp only [weightedDiagonalMean, N, D, Pi.mul_apply]
    exact (div_mul_cancel₀ _ hDpos.ne').symm
  rw [hNval]
  dsimp [D]
  field_simp [hDpos.ne']
  ring

/-- The horizontal derivative of the error in normalized integral form. The
integrand separates derivatives of the weight from derivatives of the
averaged function. -/
theorem fderivWithin_weightedDiagonalError_horizontal_eq_integral
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
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) p) (1, 0) =
      Gf p (1, 0) -
        (∫ t in (0 : ℝ)..1,
          Gw (diagonalSegment p t) (1, 1 - t) *
              (f (diagonalSegment p t) - weightedDiagonalMean w f p) +
            w (diagonalSegment p t) *
              Gf (diagonalSegment p t) (1, 1 - t)) /
          (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) := by
  let K := closedCoordTriangle a b
  let Gprod : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := w • Gf + f • Gw
  have hGprod : ContinuousOn Gprod K := (hw.smul hGf).add (hf.smul hGw)
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (fun t : ℝ => diagonalSegment p t) (Icc 0 1) K :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have hdir : Continuous (fun t : ℝ => ((1 : ℝ), 1 - t)) := by fun_prop
  have hintprod : IntervalIntegrable
      (fun t : ℝ => Gprod (diagonalSegment p t) (1, 1 - t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (hGprod.comp hseg hmap).clm_apply hdir.continuousOn
  have hintw : IntervalIntegrable
      (fun t : ℝ => Gw (diagonalSegment p t) (1, 1 - t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (hGw.comp hseg hmap).clm_apply hdir.continuousOn
  rw [fderivWithin_weightedDiagonalError_horizontal_eq hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hp,
    integralDiagonalSegmentJet_horizontal Gprod hGprod p hp,
    integralDiagonalSegmentJet_horizontal Gw hGw p hp]
  congr 1
  congr 1
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hintprod (hintw.const_mul _)]
  apply intervalIntegral.integral_congr
  intro t ht
  simp [Gprod, smul_eq_mul]
  ring

/-- The horizontal derivative formula with the moving lower endpoint made
explicit. The remaining integral is over the fixed unit interval. -/
theorem fderivWithin_weightedDiagonalError_horizontal_eq_endpoint
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
    (hc : 0 < c) {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) p) (1, 0) =
      Gf p (1, 0) -
        (w (p.1, p.1) *
            (weightedDiagonalMean w f p - f (p.1, p.1)) / (p.2 - p.1) +
          ∫ t in (0 : ℝ)..1,
            Gw (diagonalSegment p t) (1, 0) *
                (f (diagonalSegment p t) - weightedDiagonalMean w f p) +
              w (diagonalSegment p t) *
                Gf (diagonalSegment p t) (1, 0)) /
          (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) := by
  let K := closedCoordTriangle a b
  let S : ℝ → ℝ × ℝ := diagonalSegment p
  let m : ℝ := weightedDiagonalMean w f p
  let A : ℝ → ℝ := fun t =>
    Gw (S t) (1, 0) * (f (S t) - m) + w (S t) * Gf (S t) (1, 0)
  let B : ℝ → ℝ := fun t =>
    Gw (S t) (0, 1) * (f (S t) - m) + w (S t) * Gf (S t) (0, 1)
  have hpK : p ∈ K := by
    rw [← interior_closedCoordTriangle] at hp
    exact interior_subset hp
  have hseg : ContinuousOn S (Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (p.1, p.1 + t * (p.2 - p.1))) (Icc 0 1)
    fun_prop
  have hmap : MapsTo S (Icc (0 : ℝ) 1) K :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hpK ht
  have hW : ContinuousOn (fun t => w (S t)) (Icc (0 : ℝ) 1) := hw.comp hseg hmap
  have hF : ContinuousOn (fun t => f (S t)) (Icc (0 : ℝ) 1) := hf.comp hseg hmap
  have hGwU : ContinuousOn (fun t => Gw (S t) (1, 0)) (Icc (0 : ℝ) 1) :=
    (hGw.comp hseg hmap).clm_apply continuousOn_const
  have hGfU : ContinuousOn (fun t => Gf (S t) (1, 0)) (Icc (0 : ℝ) 1) :=
    (hGf.comp hseg hmap).clm_apply continuousOn_const
  have hGwV : ContinuousOn (fun t => Gw (S t) (0, 1)) (Icc (0 : ℝ) 1) :=
    (hGw.comp hseg hmap).clm_apply continuousOn_const
  have hGfV : ContinuousOn (fun t => Gf (S t) (0, 1)) (Icc (0 : ℝ) 1) :=
    (hGf.comp hseg hmap).clm_apply continuousOn_const
  have hA : ContinuousOn A (Icc (0 : ℝ) 1) :=
    (hGwU.mul (hF.sub continuousOn_const)).add (hW.mul hGfU)
  have hB : ContinuousOn B (Icc (0 : ℝ) 1) :=
    (hGwV.mul (hF.sub continuousOn_const)).add (hW.mul hGfV)
  have hAi : IntervalIntegrable A volume 0 1 := hA.intervalIntegrable_of_Icc (by norm_num)
  have hBi : IntervalIntegrable (fun t => (1 - t) * B t) volume 0 1 :=
    ((continuous_const.sub continuous_id).continuousOn.mul hB).intervalIntegrable_of_Icc
      (by norm_num)
  have hsplit :
      (∫ t in (0 : ℝ)..1,
          Gw (S t) (1, 1 - t) * (f (S t) - m) +
            w (S t) * Gf (S t) (1, 1 - t)) =
        (∫ t in (0 : ℝ)..1, A t) + (∫ t in (0 : ℝ)..1, (1 - t) * B t) := by
    rw [← intervalIntegral.integral_add hAi hBi]
    apply intervalIntegral.integral_congr
    intro t ht
    change Gw (S t) (1, 1 - t) * (f (S t) - m) +
      w (S t) * Gf (S t) (1, 1 - t) = A t + (1 - t) * B t
    rw [horizontal_segment_direction (Gw (S t)) t,
      horizontal_segment_direction (Gf (S t)) t]
    dsimp [A, B]
    ring
  have hcancel := integral_one_sub_weighted_vertical_jet_eq_endpoint
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hc hp
  rw [fderivWithin_weightedDiagonalError_horizontal_eq_integral
    hab hw hf hGw hGf hdw hdf hderivw hderivf hweight hc hpK]
  change Gf p (1, 0) -
    (∫ t in (0 : ℝ)..1,
      Gw (S t) (1, 1 - t) * (f (S t) - m) +
        w (S t) * Gf (S t) (1, 1 - t)) /
      (∫ t in (0 : ℝ)..1, w (S t)) = _
  rw [hsplit]
  rw [hcancel]
  simp only [A, S, m]
  ring

end intervalIntegral

end
