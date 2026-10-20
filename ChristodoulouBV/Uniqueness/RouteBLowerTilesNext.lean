module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesMarchBounds
import ChristodoulouBV.C1Solution.RectangleJetSeams
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# One successor tile in the Route B lower cover

A short fixed base interval and a continuous incoming trace from the previous
tile produce the next safe rectangle after reducing the common height.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Relative `C¹` regularity of one tile supplies the continuous vertical
derivative data required for the next tile's incoming edge. -/
theorem exists_vertical_edge_derivative_data
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    (X : ℝ × ℝ → C1Solution.IncomingState)
    (hX : ContDiffOn ℝ 1 X (Goursat.rectangle u₀ u₁ v₀ v₁))
    {u : ℝ} (hu' : u ∈ Icc u₀ u₁) :
    ∃ x₀' : ℝ → C1Solution.IncomingState,
      ContinuousOn x₀' (Icc v₀ v₁) ∧
      ∀ v ∈ Icc v₀ v₁,
        HasDerivWithinAt (fun t => X (u, t)) (x₀' v) (Icc v₀ v₁) v := by
  let R := Goursat.rectangle u₀ u₁ v₀ v₁
  let x₀' : ℝ → C1Solution.IncomingState :=
    fun v => (fderivWithin ℝ X R (u, v)) (0, 1)
  have hjet : ContinuousOn (fderivWithin ℝ X R) R :=
    hX.continuousOn_fderivWithin
      (C1Solution.uniqueDiffOn_rectangle hu hv) (by norm_num)
  have hcont : ContinuousOn x₀' (Icc v₀ v₁) :=
    (hjet.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv' => Goursat.pair_mem_rectangle hu' hv')).clm_apply
        continuousOn_const
  refine ⟨x₀', hcont, ?_⟩
  intro v hv'
  exact (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    hu hv hX hu' hv').2

/-- Local successor-tile existence with a positive height below the supplied
incoming edge height. The full terminal state agrees with the canonical base
by uniqueness of the incoming characteristic ODE. -/
theorem LowerCoverBaseData.exists_next_tile
    {a vStar L u₀ u₁ H : ℝ} (D : LowerCoverBaseData a vStar L)
    (hu₀ : 0 ≤ u₀) (hu : u₀ < u₁) (hu₁a : u₁ ≤ a)
    (hoff : u₁ < vStar) (hH : 0 < H)
    (B : C1Solution.SafeRectangleBox)
    (hcenter : B.center = D.base u₀)
    (hbaseNear : ∀ u ∈ Icc u₀ u₁,
      dist (D.base u) (D.base u₀) ≤ B.radius / 4)
    (hwidthSize : B.radius / 2 + B.valueBound * (u₁ - u₀) < B.radius)
    (hwidthSmall : (B.derivBound : ℝ) * (u₁ - u₀) < 1)
    (x₀ x₀' : ℝ → C1Solution.IncomingState)
    (hx₀ : Continuous x₀)
    (hx₀' : ContinuousOn x₀' (Icc vStar (vStar + H)))
    (hdx₀ : ∀ v ∈ Icc vStar (vStar + H),
      HasDerivWithinAt x₀ (x₀' v) (Icc vStar (vStar + H)) v)
    (hcorner : x₀ vStar = (D.base u₀).1) :
    ∃ η : ℝ, 0 < η ∧ η < H ∧
      ∃ X : ℝ × ℝ → C1Solution.IncomingState,
      ∃ Y : ℝ × ℝ → C1Solution.OutgoingState,
        Continuous X ∧ Continuous Y ∧
        (∀ p ∈ Goursat.rectangle u₀ u₁ vStar (vStar + η),
          (X p, Y p) ∈ B.carrier) ∧
        ContDiffOn ℝ 1 X (Goursat.rectangle u₀ u₁ vStar (vStar + η)) ∧
        ContDiffOn ℝ 1 Y (Goursat.rectangle u₀ u₁ vStar (vStar + η)) ∧
        (∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + η),
          HasDerivWithinAt (fun s => X (s, v))
            (C1Solution.rectangleF (X (u, v), Y (u, v))) (Icc u₀ u₁) u ∧
          HasDerivWithinAt (fun t => Y (u, t))
            (C1Solution.rectangleG (X (u, v), Y (u, v)))
              (Icc vStar (vStar + η)) v) ∧
        (∀ v ∈ Icc vStar (vStar + η), X (u₀, v) = x₀ v) ∧
        (∀ u ∈ Icc u₀ u₁, (X (u, vStar), Y (u, vStar)) = D.base u) := by
  obtain ⟨η₀, hη₀, hη₀H, hmargin⟩ :=
    exists_height_mixed_trace_margin hH B D.base x₀ hcenter hcorner
      hx₀.continuousAt hbaseNear
  let η := min (η₀ / 2) ((u₁ - u₀) / 2)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by linarith only [hη₀]) (by linarith only [hu])
  have hηH : η < H := by
    have hle : η ≤ η₀ / 2 := min_le_left _ _
    linarith only [hle, hη₀H, hη₀]
  have hη₀' : η ≤ η₀ := by
    have hle : η ≤ η₀ / 2 := min_le_left _ _
    linarith only [hle, hη₀]
  have hηw : η ≤ u₁ - u₀ := by
    have hle : η ≤ (u₁ - u₀) / 2 := min_le_right _ _
    linarith only [hle, hu]
  have hmax : max (u₁ - u₀) ((vStar + η) - vStar) = u₁ - u₀ := by
    have hsub : (vStar + η) - vStar = η := by ring
    rw [hsub]
    exact max_eq_left hηw
  obtain ⟨PX, hPX⟩ :=
    (isCompact_Icc : IsCompact (Icc vStar (vStar + H))).exists_bound_of_continuousOn
      hx₀'
  obtain ⟨QY, hQY⟩ :=
    (isCompact_Icc : IsCompact (Icc 0 a)).exists_bound_of_continuousOn
      D.baseOutgoingPrime_cont
  have hdx : ∀ v ∈ Icc vStar (vStar + η),
      HasDerivWithinAt x₀ (x₀' v) (Icc vStar (vStar + η)) v := by
    intro v hv
    exact (hdx₀ v ⟨hv.1, by linarith only [hv.2, hηH]⟩).mono
      (fun _ ht => ⟨ht.1, by linarith only [ht.2, hηH]⟩)
  have hdy : ∀ u ∈ Icc u₀ u₁,
      HasDerivWithinAt (fun t => (D.base t).2)
        (D.baseOutgoingPrime u) (Icc u₀ u₁) u := by
    intro u hu'
    exact (D.baseOutgoing_deriv u ⟨hu₀.trans hu'.1,
      hu'.2.trans hu₁a⟩).mono (fun _ ht =>
      ⟨hu₀.trans ht.1, ht.2.trans hu₁a⟩)
  have hdata : ∀ p ∈ Goursat.rectangle u₀ u₁ vStar (vStar + η),
      dist (x₀ p.2, (D.base p.1).2) B.center ≤ B.radius / 2 := by
    intro p hp
    have hp' : p ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + η) := hp
    exact hmargin p.1 hp'.1 p.2
      ⟨hp'.2.1, by linarith only [hp'.2.2, hη₀']⟩
  obtain ⟨X, Y, hX, hY, hball, heq, hCX, hCY, hjet, _⟩ :=
    C1Solution.exists_unique_rectangle_solution
      u₀ u₁ vStar (vStar + η) hu (by linarith only [hη]) hoff
      x₀ x₀' (fun u => (D.base u).2) D.baseOutgoingPrime
      hx₀ D.base_cont.snd
      (hx₀'.mono (fun _ hv => ⟨hv.1, by linarith only [hv.2, hηH]⟩))
      (D.baseOutgoingPrime_cont.mono (fun _ hu' =>
        ⟨hu₀.trans hu'.1, hu'.2.trans hu₁a⟩))
      hdx hdy B (B.radius / 2) PX QY hdata
      (fun v hv => hPX v ⟨hv.1, by linarith only [hv.2, hηH]⟩)
      (fun u hu' => hQY u ⟨hu₀.trans hu'.1, hu'.2.trans hu₁a⟩)
      (by rw [hmax]; exact hwidthSize)
      (by rw [hmax]; exact hwidthSmall)
  have hleft : ∀ v ∈ Icc vStar (vStar + η), X (u₀, v) = x₀ v := by
    intro v hv
    have he := (heq (u₀, v)
      (Goursat.pair_mem_rectangle ⟨le_rfl, hu.le⟩ hv)).1
    simpa only [intervalIntegral.integral_same, add_zero] using he
  have hYedge : ∀ u ∈ Icc u₀ u₁, Y (u, vStar) = (D.base u).2 := by
    intro u hu'
    have he := (heq (u, vStar)
      (Goursat.pair_mem_rectangle hu' ⟨le_rfl, by linarith only [hη]⟩)).2
    simpa only [intervalIntegral.integral_same, add_zero] using he
  have hbaseBall : ∀ u ∈ Icc u₀ u₁, D.base u ∈ B.carrier := by
    intro u hu'
    rw [C1Solution.SafeRectangleBox.carrier, Metric.mem_closedBall, hcenter]
    exact (hbaseNear u hu').trans (by linarith only [B.radius_pos])
  have hbottom := C1Solution.bottom_full_trace_eq hu B
      (fun u => (D.base u).2) X Y D.base
      ((hX.comp (continuous_id.prodMk continuous_const)).continuousOn)
      D.base_cont.fst.continuousOn hYedge
      (fun u hu' => rfl)
      (by
        intro u hu'
        have hp := Goursat.pair_mem_rectangle hu'
          (show vStar ∈ Icc vStar (vStar + η) from
            ⟨le_rfl, by linarith only [hη]⟩)
        have hz := hball (u, vStar) hp
        rw [hYedge u hu'] at hz
        simpa only [C1Solution.SafeRectangleBox.carrier,
          Metric.mem_closedBall] using hz)
      hbaseBall
      (by
        intro u hu'
        have hj := (hjet u hu' vStar
          ⟨le_rfl, by linarith only [hη]⟩).1
        rw [hYedge u hu'] at hj
        exact hj)
      (by
        intro u hu'
        exact (D.baseIncoming_deriv u
          ⟨hu₀.trans hu'.1, hu'.2.trans hu₁a⟩).mono
            (fun _ ht => ⟨hu₀.trans ht.1, ht.2.trans hu₁a⟩))
      (by rw [hleft vStar ⟨le_rfl, by linarith only [hη]⟩, hcorner])
  refine ⟨η, hη, hηH, X, Y, hX, hY, ?_, hCX, hCY, hjet,
    hleft, hbottom⟩
  intro p hp
  simpa only [C1Solution.SafeRectangleBox.carrier,
    Metric.mem_closedBall] using hball p hp

end ChristodoulouBV.Uniqueness

end
