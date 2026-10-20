module

public import ChristodoulouBV.C1Solution.RectangleConstraints
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Full first jets at off-axis rectangle seams

The transverse coordinate jets satisfy linear edge equations. Uniqueness of
those equations gives the missing transverse equality once the edge values
and corner jet agree. Equality on both coordinate directions then identifies
the entire continuous linear first jet.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- Two Banach-valued transverse jets satisfying the same affine linear edge
equation and the same corner value agree on the whole closed edge. -/
theorem eq_on_of_linear_vertical_edge_equations
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {b₀ b₁ : ℝ} (_hbb : b₀ ≤ b₁)
    {q₁ q₂ h : ℝ → E} {A : ℝ → E →L[ℝ] E}
    (hq₁ : ContinuousOn q₁ (Icc b₀ b₁))
    (hq₂ : ContinuousOn q₂ (Icc b₀ b₁))
    (hA : ContinuousOn A (Icc b₀ b₁))
    (hd₁ : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt q₁ (A v (q₁ v) + h v) (Icc b₀ b₁) v)
    (hd₂ : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt q₂ (A v (q₂ v) + h v) (Icc b₀ b₁) v)
    (hcorner : q₁ b₀ = q₂ b₀) :
    ∀ v ∈ Icc b₀ b₁, q₁ v = q₂ v := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let q : ℝ → E := fun v => q₁ v - q₂ v
  have hq : ContinuousOn q (Icc b₀ b₁) := hq₁.sub hq₂
  have hzero : q b₀ = 0 := sub_eq_zero.mpr hcorner
  have hderiv (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt q (A v (q v)) (Icc b₀ b₁) v := by
    convert (hd₁ v hv).sub (hd₂ v hv) using 1
    simp only [q, map_sub]
    abel
  have hright : ∀ v ∈ Ico b₀ b₁,
      HasDerivWithinAt q (A v (q v)) (Ici v) v := by
    intro v hv
    exact (hderiv v ⟨hv.1, hv.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hv)
  have hbound : ∀ v ∈ Ico b₀ b₁, ‖A v (q v)‖ ≤ M * ‖q v‖ := by
    intro v hv
    exact (ContinuousLinearMap.le_opNorm (A v) (q v)).trans
      (mul_le_mul_of_nonneg_right (hM v ⟨hv.1, hv.2.le⟩) (norm_nonneg _))
  have hzeroedge := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (K := M) (f' := fun v => A v (q v)) hq hright hzero hbound
  intro v hv
  exact sub_eq_zero.mp (hzeroedge v hv)

/-- A continuous linear map from the two coordinate directions is determined
by its values on the horizontal and vertical unit vectors. -/
theorem continuousLinearMap_ext_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L M : (ℝ × ℝ) →L[ℝ] E}
    (hu : L (1, 0) = M (1, 0))
    (hv : L (0, 1) = M (0, 1)) : L = M := by
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  have hdecomp : (u, v) = u • (1, (0 : ℝ)) + v • ((0 : ℝ), 1) := by
    ext <;> simp
  calc
    L (u, v) = L (u • (1, (0 : ℝ)) + v • ((0 : ℝ), 1)) := by rw [hdecomp]
    _ = u • L (1, 0) + v • L (0, 1) := by simp only [map_add, map_smul]
    _ = u • M (1, 0) + v • M (0, 1) := by rw [hu, hv]
    _ = M (u, v) := by rw [hdecomp]; simp only [map_add, map_smul]

/-- Equality of the two coordinate jets on an overlap is equality of the full
first jet required by finite closed-convex gluing. -/
theorem full_first_jet_eq_of_coordinate_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ × ℝ → E} {K L : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hu : (fderivWithin ℝ f K p) (1, 0) =
      (fderivWithin ℝ g L p) (1, 0))
    (hv : (fderivWithin ℝ f K p) (0, 1) =
      (fderivWithin ℝ g L p) (0, 1)) :
    fderivWithin ℝ f K p = fderivWithin ℝ g L p :=
  continuousLinearMap_ext_coordinate hu hv

/-- A compatible full trace on the incoming data edge is recovered from the
minimal trace. The five unprescribed values solve the same outgoing ODE from
the common corner. Its hypotheses are exactly the five tangential outgoing
equations and safe-state bounds for the proposed full trace. -/
theorem left_full_trace_eq
    {a₀ b₀ b₁ : ℝ} (_hbb : b₀ < b₁)
    (B : SafeRectangleBox) (x₀ : ℝ → IncomingState)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (T : ℝ → RectangleState)
    (hY : ContinuousOn (fun v => Y (a₀, v)) (Icc b₀ b₁))
    (hT : ContinuousOn (fun v => (T v).2) (Icc b₀ b₁))
    (hXedge : ∀ v ∈ Icc b₀ b₁, X (a₀, v) = x₀ v)
    (hTedge : ∀ v ∈ Icc b₀ b₁, (T v).1 = x₀ v)
    (hYball : ∀ v ∈ Icc b₀ b₁, (x₀ v, Y (a₀, v)) ∈ B.carrier)
    (hTball : ∀ v ∈ Icc b₀ b₁, T v ∈ B.carrier)
    (hYderiv : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun t => Y (a₀, t))
        (rectangleG (x₀ v, Y (a₀, v))) (Icc b₀ b₁) v)
    (hTderiv : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun t => (T t).2)
        (rectangleG (T v)) (Icc b₀ b₁) v)
    (hcorner : Y (a₀, b₀) = (T b₀).2) :
    ∀ v ∈ Icc b₀ b₁, (X (a₀, v), Y (a₀, v)) = T v := by
  have hLip (v : ℝ) (hv : v ∈ Ico b₀ b₁) :
      LipschitzOnWith B.derivBound (fun y => rectangleG (x₀ v, y))
        {y | (x₀ v, y) ∈ B.carrier} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy y' hy'
    have hdist := B.dist_rectangleG_le hy hy'
    have hpair : dist (x₀ v, y) (x₀ v, y') = dist y y' := by
      simp [dist_eq_norm, Prod.norm_def]
    rw [hpair] at hdist
    exact hdist
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun t y => rectangleG (x₀ t, y))
    (s := fun t => {y | (x₀ t, y) ∈ B.carrier})
    (K := B.derivBound) hLip hY
    (by
      intro v hv
      exact (hYderiv v ⟨hv.1, hv.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hv))
    (fun v hv => hYball v ⟨hv.1, hv.2.le⟩)
    hT
    (by
      intro v hv
      have h := hTderiv v ⟨hv.1, hv.2.le⟩
      have hTv : T v = (x₀ v, (T v).2) := by
        apply Prod.ext
        · exact hTedge v ⟨hv.1, hv.2.le⟩
        · rfl
      rw [hTv] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv))
    (fun v hv => by
      have hTv : T v = (x₀ v, (T v).2) := by
        apply Prod.ext
        · exact hTedge v ⟨hv.1, hv.2.le⟩
        · rfl
      have h := hTball v ⟨hv.1, hv.2.le⟩
      rw [hTv] at h
      exact h)
    hcorner
  intro v hv
  apply Prod.ext
  · exact (hXedge v hv).trans (hTedge v hv).symm
  · exact heq hv

/-- A compatible full trace on the outgoing data edge is recovered from the
minimal trace. The two unprescribed values solve the same incoming ODE from
the common corner. Its hypotheses are the two tangential incoming equations
and the safe-state bounds for the proposed full trace. -/
theorem bottom_full_trace_eq
    {a₀ a₁ b₀ : ℝ} (_haa : a₀ < a₁)
    (B : SafeRectangleBox) (y₀ : ℝ → OutgoingState)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (T : ℝ → RectangleState)
    (hX : ContinuousOn (fun u => X (u, b₀)) (Icc a₀ a₁))
    (hT : ContinuousOn (fun u => (T u).1) (Icc a₀ a₁))
    (hYedge : ∀ u ∈ Icc a₀ a₁, Y (u, b₀) = y₀ u)
    (hTedge : ∀ u ∈ Icc a₀ a₁, (T u).2 = y₀ u)
    (hXball : ∀ u ∈ Icc a₀ a₁, (X (u, b₀), y₀ u) ∈ B.carrier)
    (hTball : ∀ u ∈ Icc a₀ a₁, T u ∈ B.carrier)
    (hXderiv : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt (fun t => X (t, b₀))
        (rectangleF (X (u, b₀), y₀ u)) (Icc a₀ a₁) u)
    (hTderiv : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt (fun t => (T t).1)
        (rectangleF (T u)) (Icc a₀ a₁) u)
    (hcorner : X (a₀, b₀) = (T a₀).1) :
    ∀ u ∈ Icc a₀ a₁, (X (u, b₀), Y (u, b₀)) = T u := by
  have hLip (u : ℝ) (hu : u ∈ Ico a₀ a₁) :
      LipschitzOnWith B.derivBound (fun x => rectangleF (x, y₀ u))
        {x | (x, y₀ u) ∈ B.carrier} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx x' hx'
    have hdist := B.dist_rectangleF_le hx hx'
    have hpair : dist (x, y₀ u) (x', y₀ u) = dist x x' := by
      simp [dist_eq_norm, Prod.norm_def]
    rw [hpair] at hdist
    exact hdist
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun t x => rectangleF (x, y₀ t))
    (s := fun t => {x | (x, y₀ t) ∈ B.carrier})
    (K := B.derivBound) hLip hX
    (by
      intro u hu
      exact (hXderiv u ⟨hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hu))
    (fun u hu => hXball u ⟨hu.1, hu.2.le⟩)
    hT
    (by
      intro u hu
      have h := hTderiv u ⟨hu.1, hu.2.le⟩
      have hTu : T u = ((T u).1, y₀ u) := by
        apply Prod.ext
        · rfl
        · exact hTedge u ⟨hu.1, hu.2.le⟩
      rw [hTu] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hu))
    (fun u hu => by
      have hTu : T u = ((T u).1, y₀ u) := by
        apply Prod.ext
        · rfl
        · exact hTedge u ⟨hu.1, hu.2.le⟩
      have h := hTball u ⟨hu.1, hu.2.le⟩
      rw [hTu] at h
      exact h)
    hcorner
  intro u hu
  apply Prod.ext
  · exact heq hu
  · exact (hYedge u hu).trans (hTedge u hu).symm

/-- The minimal-data rectangle equations reproduce compatible full traces
on both data edges. The additional hypotheses on the proposed traces are
their five outgoing and two incoming tangential evolution equations; the
three incoming lower-edge constraints are separate propagation conditions. -/
theorem rectangle_solution_full_traces
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (B : SafeRectangleBox)
    (x₀ : ℝ → IncomingState) (y₀ : ℝ → OutgoingState)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      (X p, Y p) ∈ B.carrier)
    (heq : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      X p = x₀ p.2 + ∫ s in a₀..p.1,
        rectangleF (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in b₀..p.2,
        rectangleG (X (p.1, t), Y (p.1, t)))
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    (Tleft : ℝ → RectangleState)
    (hTleft : ContinuousOn (fun v => (Tleft v).2) (Icc b₀ b₁))
    (hTleftX : ∀ v ∈ Icc b₀ b₁, (Tleft v).1 = x₀ v)
    (hTleftBall : ∀ v ∈ Icc b₀ b₁, Tleft v ∈ B.carrier)
    (hTleftDeriv : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun t => (Tleft t).2)
        (rectangleG (Tleft v)) (Icc b₀ b₁) v)
    (Tbottom : ℝ → RectangleState)
    (hTbottom : ContinuousOn (fun u => (Tbottom u).1) (Icc a₀ a₁))
    (hTbottomY : ∀ u ∈ Icc a₀ a₁, (Tbottom u).2 = y₀ u)
    (hTbottomBall : ∀ u ∈ Icc a₀ a₁, Tbottom u ∈ B.carrier)
    (hTbottomDeriv : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt (fun t => (Tbottom t).1)
        (rectangleF (Tbottom u)) (Icc a₀ a₁) u)
    (hcorner : Tleft b₀ = Tbottom a₀) :
    (∀ v ∈ Icc b₀ b₁, (X (a₀, v), Y (a₀, v)) = Tleft v) ∧
    (∀ u ∈ Icc a₀ a₁, (X (u, b₀), Y (u, b₀)) = Tbottom u) := by
  have hXedge (v : ℝ) (hv : v ∈ Icc b₀ b₁) : X (a₀, v) = x₀ v := by
    have h := (heq (a₀, v)
      (Goursat.pair_mem_rectangle ⟨le_rfl, haa.le⟩ hv)).1
    simpa only [intervalIntegral.integral_same, add_zero] using h
  have hYedge (u : ℝ) (hu : u ∈ Icc a₀ a₁) : Y (u, b₀) = y₀ u := by
    have h := (heq (u, b₀)
      (Goursat.pair_mem_rectangle hu ⟨le_rfl, hbb.le⟩)).2
    simpa only [intervalIntegral.integral_same, add_zero] using h
  have hcornerY : Y (a₀, b₀) = (Tleft b₀).2 := by
    rw [hYedge a₀ ⟨le_rfl, haa.le⟩]
    calc
      y₀ a₀ = (Tbottom a₀).2 := (hTbottomY a₀ ⟨le_rfl, haa.le⟩).symm
      _ = (Tleft b₀).2 := congrArg Prod.snd hcorner.symm
  have hcornerX : X (a₀, b₀) = (Tbottom a₀).1 := by
    rw [hXedge b₀ ⟨le_rfl, hbb.le⟩]
    calc
      x₀ b₀ = (Tleft b₀).1 := (hTleftX b₀ ⟨le_rfl, hbb.le⟩).symm
      _ = (Tbottom a₀).1 := congrArg Prod.fst hcorner
  constructor
  · apply left_full_trace_eq hbb B x₀ X Y Tleft
      (hY.comp (continuous_const.prodMk continuous_id)).continuousOn
      hTleft hXedge hTleftX
    · intro v hv
      have h := hball (a₀, v)
        (Goursat.pair_mem_rectangle ⟨le_rfl, haa.le⟩ hv)
      rw [hXedge v hv] at h
      exact h
    · exact hTleftBall
    · intro v hv
      have h := (hjet a₀ ⟨le_rfl, haa.le⟩ v hv).2
      rw [hXedge v hv] at h
      exact h
    · exact hTleftDeriv
    · exact hcornerY
  · apply bottom_full_trace_eq haa B y₀ X Y Tbottom
      (hX.comp (continuous_id.prodMk continuous_const)).continuousOn
      hTbottom hYedge hTbottomY
    · intro u hu
      have h := hball (u, b₀)
        (Goursat.pair_mem_rectangle hu ⟨le_rfl, hbb.le⟩)
      rw [hYedge u hu] at h
      exact h
    · exact hTbottomBall
    · intro u hu
      have h := (hjet u hu b₀ ⟨le_rfl, hbb.le⟩).1
      rw [hYedge u hu] at h
      exact h
    · exact hTbottomDeriv
    · exact hcornerX

end ChristodoulouBV.C1Solution

end
