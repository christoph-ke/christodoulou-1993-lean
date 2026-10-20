module

public import ChristodoulouBV.C1Solution.RectangleSolution
import ChristodoulouBV.C1Solution.RectangleSeams
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Characteristic data for the Route B lower tiles

The incoming pair is prescribed on `u = 0`, and the outgoing quintuple on
`v = vStar`. The functions in this record are global representatives of the
edge data; only their values and derivatives on the stated edges matter.
Clipping supplies such representatives from relative C¹ edge data.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Minimal characteristic edge data on the compact lower base. The full
seven-state trace is kept so that later tile theorems can compare all values
on the terminal seam. -/
structure LowerTileEdgeData (a vStar L : ℝ) where
  base : ℝ → C1Solution.RectangleState
  baseOutgoingPrime : ℝ → C1Solution.OutgoingState
  initialIncoming : ℝ → C1Solution.IncomingState
  initialIncomingPrime : ℝ → C1Solution.IncomingState
  base_cont : Continuous base
  initial_cont : Continuous initialIncoming
  baseOutgoingPrime_cont : ContinuousOn baseOutgoingPrime (Icc 0 a)
  initialIncomingPrime_cont :
    ContinuousOn initialIncomingPrime (Icc vStar (vStar + L))
  baseOutgoing_deriv : ∀ u ∈ Icc 0 a,
    HasDerivWithinAt (fun t => (base t).2) (baseOutgoingPrime u) (Icc 0 a) u
  baseIncoming_deriv : ∀ u ∈ Icc 0 a,
    HasDerivWithinAt (fun t => (base t).1)
      (C1Solution.rectangleF (base u)) (Icc 0 a) u
  initialIncoming_deriv : ∀ v ∈ Icc vStar (vStar + L),
    HasDerivWithinAt initialIncoming (initialIncomingPrime v)
      (Icc vStar (vStar + L)) v
  corner : initialIncoming vStar = (base 0).1

/-- A safe corner and continuous characteristic data admit one nondegenerate
off-axis rectangle. The whole mixed trace is shown to fit in the safe box;
it is not an extra input. -/
theorem LowerTileEdgeData.exists_first_tile
    {a vStar L : ℝ} (D : LowerTileEdgeData a vStar L)
    (ha : 0 < a) (hL : 0 < L) (hoff : a < vStar)
    (B : C1Solution.SafeRectangleBox)
    (hcenter : B.center = D.base 0) :
    ∃ h : ℝ, 0 < h ∧ h < a ∧ h < L ∧
      ∃ X : ℝ × ℝ → C1Solution.IncomingState,
      ∃ Y : ℝ × ℝ → C1Solution.OutgoingState,
        Continuous X ∧ Continuous Y ∧
        (∀ p ∈ Goursat.rectangle 0 h vStar (vStar + h),
          dist (X p, Y p) B.center ≤ B.radius) ∧
        (∀ p ∈ Goursat.rectangle 0 h vStar (vStar + h),
          X p = D.initialIncoming p.2 + ∫ s in (0 : ℝ)..p.1,
            C1Solution.rectangleF (X (s, p.2), Y (s, p.2)) ∧
          Y p = (D.base p.1).2 + ∫ t in vStar..p.2,
            C1Solution.rectangleG (X (p.1, t), Y (p.1, t))) ∧
        ContDiffOn ℝ 1 X (Goursat.rectangle 0 h vStar (vStar + h)) ∧
        ContDiffOn ℝ 1 Y (Goursat.rectangle 0 h vStar (vStar + h)) ∧
        (∀ u ∈ Icc 0 h, ∀ v ∈ Icc vStar (vStar + h),
          HasDerivWithinAt (fun s => X (s, v))
            (C1Solution.rectangleF (X (u, v), Y (u, v))) (Icc 0 h) u ∧
          HasDerivWithinAt (fun t => Y (u, t))
            (C1Solution.rectangleG (X (u, v), Y (u, v)))
              (Icc vStar (vStar + h)) v) ∧
        (∀ u ∈ Icc 0 h, (X (u, vStar), Y (u, vStar)) = D.base u) := by
  let mixed : ℝ × ℝ → C1Solution.RectangleState :=
    fun p => (D.initialIncoming p.2, (D.base p.1).2)
  have hmixed : Continuous mixed :=
    (D.initial_cont.comp continuous_snd).prodMk
      ((D.base_cont.comp continuous_fst).snd)
  have hcorner : mixed (0, vStar) = B.center := by
    change (D.initialIncoming vStar, (D.base 0).2) = B.center
    rw [D.corner, hcenter]
  have hrad2 : 0 < B.radius / 2 := by linarith only [B.radius_pos]
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.continuousAt_iff.mp
      (show ContinuousAt mixed (0, vStar) from hmixed.continuousAt))
      (B.radius / 2) hrad2
  obtain ⟨δbase, hδbase, hbaseNear⟩ :=
    (Metric.continuousAt_iff.mp
      (show ContinuousAt D.base 0 from D.base_cont.continuousAt))
      (B.radius / 2) hrad2
  obtain ⟨PX, hPX⟩ :=
    (isCompact_Icc : IsCompact (Icc vStar (vStar + L))).exists_bound_of_continuousOn
      D.initialIncomingPrime_cont
  obtain ⟨QY, hQY⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 a)).exists_bound_of_continuousOn
      D.baseOutgoingPrime_cont
  have hvalue : 0 ≤ B.valueBound := le_max_left _ _
  have hderiv : 0 ≤ (B.derivBound : ℝ) := by positivity
  let h : ℝ := min (a / 2)
    (min (L / 2)
      (min (δ / 2)
        (min (δbase / 2)
          (min (B.radius / (4 * (B.valueBound + 1)))
            (1 / (2 * ((B.derivBound : ℝ) + 1)))))))
  have hh : 0 < h := by
    dsimp [h]
    apply lt_min (by linarith only [ha])
    apply lt_min (by linarith only [hL])
    apply lt_min (by linarith only [hδ])
    apply lt_min (by linarith only [hδbase])
    apply lt_min
    · exact div_pos B.radius_pos (by positivity)
    · exact div_pos (by norm_num) (by positivity)
  have ha' : h ≤ a / 2 := by dsimp [h]; exact min_le_left _ _
  have hL' : h ≤ L / 2 := by
    dsimp [h]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ' : h ≤ δ / 2 := by
    dsimp [h]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hδbase' : h ≤ δbase / 2 := by
    dsimp [h]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hvalue' : h ≤ B.radius / (4 * (B.valueBound + 1)) := by
    dsimp [h]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hderiv' : h ≤ 1 / (2 * ((B.derivBound : ℝ) + 1)) := by
    dsimp [h]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
  have hha : h < a := by linarith only [ha, ha']
  have hhL : h < L := by linarith only [hL, hL']
  have hhoff : h < vStar := hha.trans hoff
  have hdata : ∀ p ∈ Goursat.rectangle 0 h vStar (vStar + h),
      dist (D.initialIncoming p.2, (D.base p.1).2) B.center ≤ B.radius / 2 := by
    intro p hp
    have hp' : p ∈ Icc 0 h ×ˢ Icc vStar (vStar + h) := by
      simpa only [Goursat.rectangle] using hp
    have hu : p.1 ∈ Icc 0 h := hp'.1
    have hv : p.2 ∈ Icc vStar (vStar + h) := hp'.2
    have hpdist : dist p (0, vStar) ≤ h := by
      rw [dist_eq_norm, Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs]
      rw [abs_of_nonneg hu.1, abs_of_nonneg (sub_nonneg.mpr hv.1)]
      exact max_le hu.2 (by linarith only [hv.2])
    have hpd : dist p (0, vStar) < δ := by
      linarith only [hpdist, hδ', hδ]
    have hmix := hnear hpd
    rw [hcorner] at hmix
    exact hmix.le
  have hsize : B.radius / 2 + B.valueBound *
      max (h - 0) ((vStar + h) - vStar) < B.radius := by
    have hmul := mul_le_mul_of_nonneg_left hvalue'
      (by linarith only [hvalue])
    have hden : 0 < 4 * (B.valueBound + 1) := by positivity
    have hcancel :
        (B.radius / (4 * (B.valueBound + 1))) *
            (4 * (B.valueBound + 1)) = B.radius := by
      field_simp
    have hq : 0 ≤ B.radius / (4 * (B.valueBound + 1)) :=
      div_nonneg B.radius_pos.le hden.le
    have hfrac : B.valueBound *
        (B.radius / (4 * (B.valueBound + 1))) ≤ B.radius / 4 := by
      nlinarith only [hcancel, hq]
    have hbasic : B.valueBound * h ≤ B.radius / 4 := by
      exact hmul.trans hfrac
    have hmax : max (h - 0) ((vStar + h) - vStar) = h := by
      simp
    rw [hmax]
    linarith only [hbasic, B.radius_pos]
  have hsmall : (B.derivBound : ℝ) *
      max (h - 0) ((vStar + h) - vStar) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left hderiv'
      (by linarith only [hderiv])
    have hden : 0 < 2 * ((B.derivBound : ℝ) + 1) := by positivity
    have hcancel :
        (1 / (2 * ((B.derivBound : ℝ) + 1))) *
            (2 * ((B.derivBound : ℝ) + 1)) = 1 := by
      field_simp
    have hq : 0 ≤ 1 / (2 * ((B.derivBound : ℝ) + 1)) :=
      div_nonneg (by norm_num) hden.le
    have hfrac : (B.derivBound : ℝ) *
        (1 / (2 * ((B.derivBound : ℝ) + 1))) ≤ 1 / 2 := by
      nlinarith only [hcancel, hq]
    have hbasic : (B.derivBound : ℝ) * h ≤ 1 / 2 := by
      exact hmul.trans hfrac
    have hmax : max (h - 0) ((vStar + h) - vStar) = h := by
      simp
    rw [hmax]
    linarith only [hbasic]
  have hinitialDeriv : ∀ v ∈ Icc vStar (vStar + h),
      HasDerivWithinAt D.initialIncoming (D.initialIncomingPrime v)
        (Icc vStar (vStar + h)) v := by
    intro v hv
    have hvL : v ∈ Icc vStar (vStar + L) := by
      constructor
      · exact hv.1
      · linarith only [hv.2, hhL]
    exact (D.initialIncoming_deriv v hvL).mono (by
      intro t ht
      exact ⟨ht.1, by linarith only [ht.2, hhL]⟩)
  have hbaseDeriv : ∀ u ∈ Icc 0 h,
      HasDerivWithinAt (fun t => (D.base t).2) (D.baseOutgoingPrime u)
        (Icc 0 h) u := by
    intro u hu
    have hua : u ∈ Icc 0 a := ⟨hu.1, hu.2.trans hha.le⟩
    exact (D.baseOutgoing_deriv u hua).mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans hha.le⟩)
  obtain ⟨X, Y, hX, hY, hball, heq, hCX, hCY, hjet, _⟩ :=
    C1Solution.exists_unique_rectangle_solution
      0 h vStar (vStar + h) hh (by linarith only [hh]) hhoff
      D.initialIncoming D.initialIncomingPrime
      (fun u => (D.base u).2) D.baseOutgoingPrime
      D.initial_cont D.base_cont.snd
      (D.initialIncomingPrime_cont.mono (by
        intro v hv
        exact ⟨hv.1, by linarith only [hv.2, hhL]⟩))
      (D.baseOutgoingPrime_cont.mono (by
        intro u hu
        exact ⟨hu.1, hu.2.trans hha.le⟩))
      hinitialDeriv hbaseDeriv B (B.radius / 2) PX QY
      hdata
      (by
        intro v hv
        exact hPX v ⟨hv.1, by linarith only [hv.2, hhL]⟩)
      (by
        intro u hu
        exact hQY u ⟨hu.1, hu.2.trans hha.le⟩)
      hsize hsmall
  have hYedge : ∀ u ∈ Icc 0 h, Y (u, vStar) = (D.base u).2 := by
    intro u hu
    have hp : (u, vStar) ∈ Goursat.rectangle 0 h vStar (vStar + h) :=
      Goursat.pair_mem_rectangle hu ⟨le_rfl, by linarith only [hh]⟩
    have hy := (heq (u, vStar) hp).2
    simpa only [intervalIntegral.integral_same, add_zero] using hy
  have hXedge : ∀ v ∈ Icc vStar (vStar + h),
      X (0, v) = D.initialIncoming v := by
    intro v hv
    have hp : (0, v) ∈ Goursat.rectangle 0 h vStar (vStar + h) :=
      Goursat.pair_mem_rectangle ⟨le_rfl, hh.le⟩ hv
    have hx := (heq (0, v) hp).1
    simpa only [intervalIntegral.integral_same, add_zero] using hx
  have hbaseBall : ∀ u ∈ Icc 0 h, D.base u ∈ B.carrier := by
    intro u hu
    have hud : dist u 0 < δbase := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
      linarith only [hu.2, hδbase', hδbase]
    have hd := (hbaseNear hud).le
    rw [← hcenter] at hd
    apply Metric.mem_closedBall.mpr
    exact hd.trans (by linarith only [B.radius_pos])
  have hbottom := C1Solution.bottom_full_trace_eq hh B
      (fun u => (D.base u).2) X Y D.base
      ((hX.comp (continuous_id.prodMk continuous_const)).continuousOn)
      D.base_cont.fst.continuousOn hYedge
      (fun u hu => rfl)
      (by
        intro u hu
        have hp : (u, vStar) ∈ Goursat.rectangle 0 h vStar (vStar + h) :=
          Goursat.pair_mem_rectangle hu ⟨le_rfl, by linarith only [hh]⟩
        have hz := hball (u, vStar) hp
        rw [hYedge u hu] at hz
        simpa only [C1Solution.SafeRectangleBox.carrier, Metric.mem_closedBall] using hz)
      hbaseBall
      (by
        intro u hu
        have hj := (hjet u hu vStar ⟨le_rfl, by linarith only [hh]⟩).1
        rw [hYedge u hu] at hj
        exact hj)
      (by
        intro u hu
        exact (D.baseIncoming_deriv u ⟨hu.1, hu.2.trans hha.le⟩).mono
          (by
            intro t ht
            exact ⟨ht.1, ht.2.trans hha.le⟩))
      (by
        rw [hXedge vStar ⟨le_rfl, by linarith only [hh]⟩, D.corner])
  exact ⟨h, hh, hha, hhL, X, Y, hX, hY, hball, heq, hCX, hCY, hjet,
    hbottom⟩

end ChristodoulouBV.Uniqueness

end
