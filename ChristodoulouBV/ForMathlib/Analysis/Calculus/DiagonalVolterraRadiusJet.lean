module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelBox
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanHorizontalCalculus
import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Coordinate derivatives of vertical radii

The radius is a vertical integral with a moving lower endpoint. Its first
jet on the closed triangle is expressed by one endpoint value and one
integral of the horizontal weight derivative.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- On the interior of a coordinate triangle, the normalized-integral jet
gives the endpoint formulas for both coordinate derivatives of a vertical
radius. -/
theorem fderivWithin_weightedDiagonalRadius_apply_interior
    {a b : ℝ} (hab : a < b)
    {w : ℝ × ℝ → ℝ} {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    {p : ℝ × ℝ} (hp : p ∈ interior (closedCoordTriangle a b)) :
    (fderivWithin ℝ (weightedDiagonalRadius w) (closedCoordTriangle a b) p) (1, 0) =
      -w (p.1, p.1) + ∫ s in p.1..p.2, Gw (p.1, s) (1, 0) ∧
    (fderivWithin ℝ (weightedDiagonalRadius w) (closedCoordTriangle a b) p) (0, 1) =
      w p := by
  let K := closedCoordTriangle a b
  have hpK : p ∈ K := interior_subset hp
  have hpstrict : a < p.1 ∧ p.1 < p.2 ∧ p.2 < b := by
    simpa only [interior_closedCoordTriangle, openCoordTriangle, Set.mem_ofPred_eq] using hp
  have hpo : p ∈ openCoordTriangle a b := by
    simpa only [interior_closedCoordTriangle] using hp
  let d := p.2 - p.1
  have hd : 0 < d := sub_pos.mpr hpstrict.2.1
  let ρ := normalizedDiagonalRadius w
  let R : ℝ × ℝ → ℝ := weightedDiagonalRadius w
  let S : ℝ → ℝ × ℝ := diagonalSegment p
  let W : ℝ → ℝ := fun t => w (S t)
  let V : ℝ → ℝ := fun t => Gw (S t) (0, 1)
  let U : ℝ → ℝ := fun t => Gw (S t) (1, 0)
  have hseg : ContinuousOn S (Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (p.1, p.1 + t * (p.2 - p.1))) (Icc 0 1)
    fun_prop
  have hmap : MapsTo S (Icc (0 : ℝ) 1) K :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hpK ht
  have hW : ContinuousOn W (Icc (0 : ℝ) 1) := hw.comp hseg hmap
  have hV : ContinuousOn V (Icc (0 : ℝ) 1) :=
    (hGw.comp hseg hmap).clm_apply continuousOn_const
  have hU : ContinuousOn U (Icc (0 : ℝ) 1) :=
    (hGw.comp hseg hmap).clm_apply continuousOn_const
  have hWderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt W (d * V t) t := by
    intro t ht
    have hpt : S t ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact diagonalSegment_mem_openCoordTriangle hpo (Ioo_subset_Ioc_self ht)
    have hwAt : HasFDerivAt w (Gw (S t)) (S t) := by
      rw [← hderivw (S t) hpt]
      exact (hdw.differentiableAt (isOpen_interior.mem_nhds hpt)).hasFDerivAt
    have h := hwAt.comp_hasDerivAt t (hasDerivAt_diagonalSegment_parameter p t)
    have heq : ((0 : ℝ), p.2 - p.1) = d • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp [d]
    simpa only [W, V, S, Function.comp_def, heq, map_smul, smul_eq_mul] using h
  have hV' : ContinuousOn (fun t => d * V t) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul hV
  have hFTC := integral_eq_sub_of_continuousOn_hasDerivAt
    (show (0 : ℝ) ≤ 1 by norm_num) hW hV' hWderiv
  have hparts := integral_one_sub_mul_deriv_eq_integral_sub hW hV' hWderiv
  have hρval : ρ p = ∫ t in (0 : ℝ)..1, W t := rfl
  have hJet : fderivWithin ℝ ρ K p = integralDiagonalSegmentJet Gw p := by
    exact (hasFDerivWithinAt_integral_diagonalSegment hab hw hGw hdw hderivw hpK).fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hpK)
  have hgap : HasFDerivWithinAt (fun z : ℝ × ℝ => z.2 - z.1)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ) - (ContinuousLinearMap.fst ℝ ℝ ℝ)) K p := by
    have heq : (fun z : ℝ × ℝ => z.2 - z.1) =
        (ContinuousLinearMap.snd ℝ ℝ ℝ) - (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
      funext z
      simp
    rw [heq]
    exact ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasFDerivAt.hasFDerivWithinAt
  have hρderiv := hasFDerivWithinAt_integral_diagonalSegment hab hw hGw hdw hderivw hpK
  have hprod := hgap.mul hρderiv
  have heq : EqOn R ((fun z : ℝ × ℝ => z.2 - z.1) * ρ) K := by
    intro z hz
    exact weightedDiagonalRadius_eq_gap_mul_normalized w z.1 z.2
  have hR := hprod.congr' heq hpK
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hpK
  have hRjet : fderivWithin ℝ R K p =
      (ρ p) • ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
        d • integralDiagonalSegmentJet Gw p := by
    have hRjet' := hR.fderivWithin hunique
    change fderivWithin ℝ R K p =
      d • integralDiagonalSegmentJet Gw p +
        (∫ t in (0 : ℝ)..1, W t) •
          ((ContinuousLinearMap.snd ℝ ℝ ℝ) -
            (ContinuousLinearMap.fst ℝ ℝ ℝ)) at hRjet'
    rw [← hρval] at hRjet'
    exact hRjet'.trans (add_comm _ _)
  have hJ_u : (integralDiagonalSegmentJet Gw p) (1, 0) =
      ∫ t in (0 : ℝ)..1, (U t + (1 - t) * V t) := by
    rw [integralDiagonalSegmentJet_horizontal Gw hGw p hpK]
    apply intervalIntegral.integral_congr
    intro t ht
    change Gw (S t) (1, 1 - t) = U t + (1 - t) * V t
    have hdecomp : ((1 : ℝ), 1 - t) =
        ((1 : ℝ), (0 : ℝ)) + (1 - t) • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul]
    simp only [U, V, smul_eq_mul]
  have hJ_v : (integralDiagonalSegmentJet Gw p) (0, 1) =
      ∫ t in (0 : ℝ)..1, t * V t := by
    rw [integralDiagonalSegmentJet]
    have hint : IntervalIntegrable
        (fun t : ℝ => (Gw (S t)).comp (diagonalSegmentFDeriv t)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      exact (hGw.comp hseg hmap).clm_comp continuous_diagonalSegmentFDeriv.continuousOn
    rw [ContinuousLinearMap.intervalIntegral_apply hint]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [ContinuousLinearMap.comp_apply, diagonalSegmentFDeriv_apply]
    have heq : ((0 : ℝ), 0 + t * (1 - 0)) = t • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [heq, map_smul]
    simp only [V, smul_eq_mul]
  have hIu : d * (∫ t in (0 : ℝ)..1, U t) =
      ∫ s in p.1..p.2, Gw (p.1, s) (1, 0) := by
    have h := intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : ℝ => Gw (p.1, s) (1, 0))
      (a := (0 : ℝ)) (b := 1) d p.1
    simpa [U, S, diagonalSegment, d, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using h
  constructor
  · rw [show (fderivWithin ℝ R K p) (1, 0) =
        -(ρ p) + d * (integralDiagonalSegmentJet Gw p) (1, 0) by
          rw [hRjet]; simp]
    rw [hJ_u]
    have hUi : IntervalIntegrable U volume 0 1 := hU.intervalIntegrable_of_Icc (by norm_num)
    have hVi : IntervalIntegrable (fun t => (1 - t) * V t) volume 0 1 :=
      ((by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) (Icc 0 1)).mul hV)
        |>.intervalIntegrable_of_Icc (by norm_num)
    rw [intervalIntegral.integral_add hUi hVi]
    have hparts' : d * (∫ t in (0 : ℝ)..1, (1 - t) * V t) =
        (ρ p) - w (p.1, p.1) := by
      calc
        _ = ∫ t in (0 : ℝ)..1, d * ((1 - t) * V t) := by
          rw [intervalIntegral.integral_const_mul]
        _ = ∫ t in (0 : ℝ)..1, (1 - t) * (d * V t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
        _ = ρ p - w (p.1, p.1) := by
          rw [hparts, ← hρval]
          simp [W, S, diagonalSegment]
    linarith only [hparts', hIu]
  · rw [show (fderivWithin ℝ R K p) (0, 1) =
        ρ p + d * (integralDiagonalSegmentJet Gw p) (0, 1) by
          rw [hRjet]; simp]
    rw [hJ_v]
    have hVi : IntervalIntegrable V volume 0 1 := hV.intervalIntegrable_of_Icc (by norm_num)
    have h1Vi : IntervalIntegrable (fun t => (1 - t) * V t) volume 0 1 :=
      ((by fun_prop : ContinuousOn (fun t : ℝ => 1 - t) (Icc 0 1)).mul hV)
        |>.intervalIntegrable_of_Icc (by norm_num)
    have hsplit : (∫ t in (0 : ℝ)..1, t * V t) =
        (∫ t in (0 : ℝ)..1, V t) -
          (∫ t in (0 : ℝ)..1, (1 - t) * V t) := by
      rw [← intervalIntegral.integral_sub hVi h1Vi]
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    rw [hsplit]
    have hFTC' : d * (∫ t in (0 : ℝ)..1, V t) =
        w p - w (p.1, p.1) := by
      rw [← intervalIntegral.integral_const_mul]
      convert hFTC using 1
      simp [W, S, diagonalSegment]
    have hparts' : d * (∫ t in (0 : ℝ)..1, (1 - t) * V t) =
        ρ p - w (p.1, p.1) := by
      calc
        _ = ∫ t in (0 : ℝ)..1, d * ((1 - t) * V t) := by
          rw [intervalIntegral.integral_const_mul]
        _ = ∫ t in (0 : ℝ)..1, (1 - t) * (d * V t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          ring
        _ = ρ p - w (p.1, p.1) := by
          rw [hparts, ← hρval]
          simp [W, S, diagonalSegment]
    linarith

/-- The vertical radius has the endpoint derivative formulas also on every
edge and corner of the closed coordinate triangle. -/
theorem fderivWithin_weightedDiagonalRadius_apply
    {a b : ℝ} (hab : a < b)
    {w : ℝ × ℝ → ℝ} {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalRadius w) (closedCoordTriangle a b) p) (1, 0) =
      -w (p.1, p.1) + ∫ s in p.1..p.2, Gw (p.1, s) (1, 0) ∧
    (fderivWithin ℝ (weightedDiagonalRadius w) (closedCoordTriangle a b) p) (0, 1) =
      w p := by
  let K := closedCoordTriangle a b
  let Gu : ℝ × ℝ → ℝ := fun z => Gw z (1, 0)
  have hGu : ContinuousOn Gu K := hGw.clm_apply continuousOn_const
  have hgap : ContinuousOn (fun z : ℝ × ℝ => z.2 - z.1) K := by fun_prop
  have hRGu : ContinuousOn (weightedDiagonalRadius Gu) K := by
    apply (hgap.mul (continuousOn_normalizedDiagonalRadius hGu)).congr
    intro z hz
    exact weightedDiagonalRadius_eq_gap_mul_normalized Gu z.1 z.2
  have hdiag : ContinuousOn (fun z : ℝ × ℝ => (z.1, z.1)) K := by fun_prop
  have hdiagmap : MapsTo (fun z : ℝ × ℝ => (z.1, z.1)) K K := by
    intro z hz
    have hcoord : a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := by
      change a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b at hz
      exact hz
    exact ⟨hcoord.1, le_rfl, hcoord.2.1.trans hcoord.2.2⟩
  have hleft : ContinuousOn (fun z =>
      (fderivWithin ℝ (weightedDiagonalRadius w) K z) (1, 0)) K := by
    have hunique : UniqueDiffOn ℝ K :=
      uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    exact ((contDiffOn_weightedDiagonalRadius hab hw hGw hdw hderivw)
      |>.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hright : ContinuousOn (fun z =>
      -w (z.1, z.1) + weightedDiagonalRadius Gu z) K :=
    (hw.comp hdiag hdiagmap).neg.add hRGu
  have hEq : EqOn (fun z =>
      (fderivWithin ℝ (weightedDiagonalRadius w) K z) (1, 0))
      (fun z => -w (z.1, z.1) + weightedDiagonalRadius Gu z)
      (interior K) := by
    intro z hz
    exact (fderivWithin_weightedDiagonalRadius_apply_interior hab hw hGw hdw
      hderivw hz).1
  have hsub : interior K ⊆ K := interior_subset
  have hclosure : K ⊆ closure (interior K) := by
    rw [interior_closedCoordTriangle, closure_openCoordTriangle hab]
  have hu := (hEq.of_subset_closure hleft hright hsub hclosure) hp
  have hv : EqOn (fun z =>
      (fderivWithin ℝ (weightedDiagonalRadius w) K z) (0, 1)) w K := by
    have hleft' : ContinuousOn (fun z =>
        (fderivWithin ℝ (weightedDiagonalRadius w) K z) (0, 1)) K := by
      have hunique : UniqueDiffOn ℝ K :=
        uniqueDiffOn_convex (convex_closedCoordTriangle a b)
          (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      exact ((contDiffOn_weightedDiagonalRadius hab hw hGw hdw hderivw)
        |>.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
    have heq : EqOn (fun z =>
        (fderivWithin ℝ (weightedDiagonalRadius w) K z) (0, 1)) w
        (interior K) := by
      intro z hz
      exact (fderivWithin_weightedDiagonalRadius_apply_interior hab hw hGw hdw
        hderivw hz).2
    exact heq.of_subset_closure hleft' hw hsub hclosure
  exact ⟨hu, hv hp⟩

private theorem abs_integral_le_const_mul_gap
    {u v C : ℝ} {g : ℝ → ℝ} (huv : u ≤ v)
    (hbound : ∀ s ∈ Icc u v, |g s| ≤ C) :
    |∫ s in u..v, g s| ≤ C * (v - u) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := C) (f := g) (by
      intro s hs
      have hs' : s ∈ Icc u v := by
        rw [uIoc_of_le huv] at hs
        exact ⟨hs.1.le, hs.2⟩
      simpa only [Real.norm_eq_abs] using hbound s hs')
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] using h

/-- A bounded weight with bounded horizontal derivative gives the exact
`C + L(v-u)` horizontal and `C` vertical radius-jet bounds. -/
theorem abs_fderivWithin_weightedDiagonalRadius_apply_le
    {a b C L : ℝ} (hab : a < b)
    {w : ℝ × ℝ → ℝ} {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hbound : ∀ p ∈ closedCoordTriangle a b, |w p| ≤ C)
    (hGu : ∀ p ∈ closedCoordTriangle a b, |Gw p (1, 0)| ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalRadius w)
      (closedCoordTriangle a b) p) (1, 0)| ≤ C + L * (p.2 - p.1) ∧
    |(fderivWithin ℝ (weightedDiagonalRadius w)
      (closedCoordTriangle a b) p) (0, 1)| ≤ C := by
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
    exact hp
  have hdiag : (p.1, p.1) ∈ closedCoordTriangle a b :=
    ⟨hcoord.1, le_rfl, hcoord.2.1.trans hcoord.2.2⟩
  have hint : |∫ s in p.1..p.2, Gw (p.1, s) (1, 0)| ≤
      L * (p.2 - p.1) := by
    apply abs_integral_le_const_mul_gap hcoord.2.1
    intro s hs
    exact hGu (p.1, s) ⟨hcoord.1, hs.1, hs.2.trans hcoord.2.2⟩
  have hform := fderivWithin_weightedDiagonalRadius_apply hab hw hGw hdw hderivw hp
  constructor
  · rw [hform.1]
    have h := abs_add_le (-w (p.1, p.1))
      (∫ s in p.1..p.2, Gw (p.1, s) (1, 0))
    rw [abs_neg] at h
    exact h.trans (add_le_add (hbound _ hdiag) hint)
  · rw [hform.2]
    exact hbound p hp

/-- Differences of two vertical radius jets are controlled by the weight
value and horizontal-derivative differences, with one interval-length factor
on the latter. -/
theorem abs_fderivWithin_weightedDiagonalRadius_sub_le
    {a b D : ℝ} (hab : a < b)
    {w₁ w₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    (hGudiff : ∀ p ∈ closedCoordTriangle a b,
      |Gw₁ p (1, 0) - Gw₂ p (1, 0)| ≤ D)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalRadius w₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalRadius w₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      (1 + (p.2 - p.1)) * D ∧
    |(fderivWithin ℝ (weightedDiagonalRadius w₁)
        (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalRadius w₂)
        (closedCoordTriangle a b) p) (0, 1)| ≤ D := by
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
    exact hp
  have hdiag : (p.1, p.1) ∈ closedCoordTriangle a b :=
    ⟨hcoord.1, le_rfl, hcoord.2.1.trans hcoord.2.2⟩
  have hG₁i : IntervalIntegrable (fun s => Gw₁ (p.1, s) (1, 0)) volume p.1 p.2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcoord.2.1
    exact (hGw₁.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hcoord.1, hs.1, hs.2.trans hcoord.2.2⟩))
      |>.clm_apply continuousOn_const
  have hG₂i : IntervalIntegrable (fun s => Gw₂ (p.1, s) (1, 0)) volume p.1 p.2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcoord.2.1
    exact (hGw₂.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hcoord.1, hs.1, hs.2.trans hcoord.2.2⟩))
      |>.clm_apply continuousOn_const
  have hint : |∫ s in p.1..p.2,
      (Gw₁ (p.1, s) (1, 0) - Gw₂ (p.1, s) (1, 0))| ≤
      D * (p.2 - p.1) := by
    apply abs_integral_le_const_mul_gap hcoord.2.1
    intro s hs
    exact hGudiff (p.1, s) ⟨hcoord.1, hs.1, hs.2.trans hcoord.2.2⟩
  have hform₁ := fderivWithin_weightedDiagonalRadius_apply hab hw₁ hGw₁ hdw₁ hderivw₁ hp
  have hform₂ := fderivWithin_weightedDiagonalRadius_apply hab hw₂ hGw₂ hdw₂ hderivw₂ hp
  constructor
  · rw [hform₁.1, hform₂.1]
    have htri := abs_add_le (-(w₁ (p.1, p.1) - w₂ (p.1, p.1)))
      (∫ s in p.1..p.2,
        (Gw₁ (p.1, s) (1, 0) - Gw₂ (p.1, s) (1, 0)))
    have heq : (-w₁ (p.1, p.1) +
        ∫ s in p.1..p.2, Gw₁ (p.1, s) (1, 0)) -
        (-w₂ (p.1, p.1) +
        ∫ s in p.1..p.2, Gw₂ (p.1, s) (1, 0)) =
        -(w₁ (p.1, p.1) - w₂ (p.1, p.1)) +
          ∫ s in p.1..p.2,
            (Gw₁ (p.1, s) (1, 0) - Gw₂ (p.1, s) (1, 0)) := by
      rw [intervalIntegral.integral_sub hG₁i hG₂i]
      ring
    rw [heq]
    rw [abs_neg] at htri
    have h := htri.trans (add_le_add (hwdiff _ hdiag) hint)
    nlinarith only [h]
  · rw [hform₁.2, hform₂.2]
    exact hwdiff p hp

/-- The three-jet box controls the radius value difference and both radius
derivative differences. For a box of width at most one, the horizontal
derivative coefficient is exactly two. -/
theorem weightedDiagonalRadius_difference_bounds_threeJetDistanceOn
    {a b D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ g₁ g₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hD : D = threeJetDistanceOn (closedCoordTriangle a b)
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |weightedDiagonalRadius w₁ p - weightedDiagonalRadius w₂ p| ≤
      (p.2 - p.1) * D ∧
    |(fderivWithin ℝ (weightedDiagonalRadius w₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalRadius w₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤ 2 * D ∧
    |(fderivWithin ℝ (weightedDiagonalRadius w₁)
        (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalRadius w₂)
        (closedCoordTriangle a b) p) (0, 1)| ≤ D := by
  let K := closedCoordTriangle a b
  have hK : IsCompact K := isCompact_closedCoordTriangle a b
  have hne : K.Nonempty := by
    refine ⟨(a, a), ?_⟩
    exact ⟨le_rfl, le_rfl, hab.le⟩
  have hDw : coordinateJetDistanceOn K w₁ w₂ Gw₁ Gw₂ ≤ D := by
    rw [hD]
    exact coordinateJetDistanceOn_first_le_threeJetDistanceOn K
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂
  have hDnonneg : 0 ≤ D :=
    (coordinateJetDistanceOn_nonneg hK hne hw₁ hw₂ hGw₁ hGw₂).trans hDw
  have hwdiff : ∀ z ∈ K, |w₁ z - w₂ z| ≤ D := by
    intro z hz
    exact (abs_value_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hz).trans hDw
  have hGudiff : ∀ z ∈ K, |Gw₁ z (1, 0) - Gw₂ z (1, 0)| ≤ D := by
    intro z hz
    exact (abs_horizontal_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hz).trans hDw
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
    exact hp
  have hdle : p.2 - p.1 ≤ 1 := by linarith
  have hval := abs_weightedDiagonalRadius_sub_le hw₁ hw₂ hwdiff
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hderiv := abs_fderivWithin_weightedDiagonalRadius_sub_le hab
    hw₁ hw₂ hGw₁ hGw₂ hdw₁ hdw₂ hderivw₁ hderivw₂
    hwdiff hGudiff hp
  refine ⟨?_, ?_, hderiv.2⟩
  · simpa only [mul_comm] using hval
  · have hcoef : (1 + (p.2 - p.1)) * D ≤ 2 * D := by
      nlinarith only [hdle, hDnonneg]
    exact hderiv.1.trans hcoef

end intervalIntegral

end
