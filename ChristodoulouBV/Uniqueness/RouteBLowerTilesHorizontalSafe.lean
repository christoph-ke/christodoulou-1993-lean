module

public import ChristodoulouBV.C1Solution.RectangleJetSeamsHorizontal
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Transverse jets with a pointwise safe state

The horizontal seam argument only needs safety at each state. A compact
terminal base generally has no single safe ball containing every state.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- Differentiating the incoming equation in the vertical direction gives
the linear transverse equation for the incoming vertical jet. -/
theorem incoming_vertical_jet_horizontal_equation_safe
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (hX : ContDiffOn ℝ 1 X (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hsafe : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      IsSafeRectangleState (X p, Y p))
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    {u v : ℝ} (hu : u ∈ Icc a₀ a₁) (hv : v ∈ Icc b₀ b₁) :
    HasDerivWithinAt
      (fun s => (fderivWithin ℝ X
        (Goursat.rectangle a₀ a₁ b₀ b₁) (s, v)) (0, 1))
      ((fderiv ℝ rectangleF (X (u, v), Y (u, v)))
        ((fderivWithin ℝ X
          (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (0, 1),
          rectangleG (X (u, v), Y (u, v))))
      (Icc a₀ a₁) u := by
  let R := Goursat.rectangle a₀ a₁ b₀ b₁
  let Z : ℝ × ℝ → RectangleState := fun p => (X p, Y p)
  let p : ℝ × ℝ → IncomingState := fun q =>
    (fderivWithin ℝ X R q) (0, 1)
  let H : ℝ → ℝ → IncomingState := fun s t => rectangleF (Z (s, t))
  let Hv : ℝ → ℝ → IncomingState := fun s t =>
    (fderiv ℝ rectangleF (Z (s, t)))
      (p (s, t), rectangleG (Z (s, t)))
  have hZcont : ContinuousOn Z R := hX.continuousOn.prodMk hY.continuousOn
  have hpcont : ContinuousOn p R :=
    (hX.continuousOn_fderivWithin (uniqueDiffOn_rectangle haa hbb)
      (by norm_num)).clm_apply continuousOn_const
  have hFsafe : ContinuousOn rectangleF {z | IsSafeRectangleState z} := by
    intro z hz
    exact ((contDiffAt_rectangleF (hz)).continuousAt).continuousWithinAt
  have hGsafe : ContinuousOn rectangleG {z | IsSafeRectangleState z} := by
    intro z hz
    exact ((contDiffAt_rectangleG (hz)).continuousAt).continuousWithinAt
  have hDFsafe : ContinuousOn (fderiv ℝ rectangleF) {z | IsSafeRectangleState z} := by
    intro z hz
    exact ((contDiffAt_rectangleF (hz)).continuousAt_fderiv
      (by decide)).continuousWithinAt
  have hHcont : ContinuousOn (fun q => H q.1 q.2) R :=
    hFsafe.comp hZcont hsafe
  have hGcont : ContinuousOn (fun q => rectangleG (Z q)) R :=
    hGsafe.comp hZcont hsafe
  have hDFcont : ContinuousOn (fun q => fderiv ℝ rectangleF (Z q)) R :=
    hDFsafe.comp hZcont hsafe
  have hHvcont : ContinuousOn (fun q => Hv q.1 q.2) R :=
    hDFcont.clm_apply (hpcont.prodMk hGcont)
  have hpderiv (s : ℝ) (hs : s ∈ Icc a₀ a₁)
      (t : ℝ) (ht : t ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun w => X (s, w)) (p (s, t)) (Icc b₀ b₁) t :=
    (coordinate_derivatives_of_contDiffOn_rectangle haa hbb hX hs ht).2
  have hHvderiv (s : ℝ) (hs : s ∈ Icc a₀ a₁)
      (t : ℝ) (ht : t ∈ Icc b₀ b₁) :
      HasDerivWithinAt (H s) (Hv s t) (Icc b₀ b₁) t := by
    have hZv : HasDerivWithinAt (fun w => Z (s, w))
        (p (s, t), rectangleG (Z (s, t))) (Icc b₀ b₁) t :=
      (hpderiv s hs t ht).prodMk (hjet s hs t ht).2
    have hstate := hsafe (s, t) (Goursat.pair_mem_rectangle hs ht)
    have hDF := (contDiffAt_rectangleF hstate).differentiableAt_one.hasFDerivAt
    exact hDF.comp_hasDerivWithinAt t hZv
  exact hasDerivWithinAt_vertical_jet_of_horizontal_equation
    (f := fun s t => X (s, t)) (fv := fun s t => p (s, t))
    (H := H) (Hv := Hv) haa hbb
    (by simpa only [R, Goursat.rectangle] using hX.continuousOn)
    (by simpa only [R, Goursat.rectangle] using hHcont)
    (by simpa only [R, Goursat.rectangle] using hHvcont)
    hpderiv (fun s hs t ht => (hjet s hs t ht).1) hHvderiv hu hv


/-- Two adjacent off-axis rectangle solutions with a common horizontal state
trace and matching corner transverse jet have matching full first jets along
the entire seam, including both corners. -/
theorem full_first_jets_eq_on_horizontal_seam_safe
    {a₀ a₁ b₀ b b₁ : ℝ}
    (haa : a₀ < a₁) (hb₀ : b₀ < b) (hb₁ : b < b₁)
    (X₁ : ℝ × ℝ → IncomingState) (Y₁ : ℝ × ℝ → OutgoingState)
    (X₂ : ℝ × ℝ → IncomingState) (Y₂ : ℝ × ℝ → OutgoingState)
    (hX₁ : ContDiffOn ℝ 1 X₁ (Goursat.rectangle a₀ a₁ b₀ b))
    (hY₁ : ContDiffOn ℝ 1 Y₁ (Goursat.rectangle a₀ a₁ b₀ b))
    (hX₂ : ContDiffOn ℝ 1 X₂ (Goursat.rectangle a₀ a₁ b b₁))
    (hY₂ : ContDiffOn ℝ 1 Y₂ (Goursat.rectangle a₀ a₁ b b₁))
    (hsafe₁ : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b,
      IsSafeRectangleState (X₁ p, Y₁ p))
    (hsafe₂ : ∀ p ∈ Goursat.rectangle a₀ a₁ b b₁,
      IsSafeRectangleState (X₂ p, Y₂ p))
    (hjet₁ : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b,
      HasDerivWithinAt (fun s => X₁ (s, v))
        (rectangleF (X₁ (u, v), Y₁ (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y₁ (u, t))
        (rectangleG (X₁ (u, v), Y₁ (u, v))) (Icc b₀ b) v)
    (hjet₂ : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b b₁,
      HasDerivWithinAt (fun s => X₂ (s, v))
        (rectangleF (X₂ (u, v), Y₂ (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y₂ (u, t))
        (rectangleG (X₂ (u, v), Y₂ (u, v))) (Icc b b₁) v)
    (htrace : ∀ u ∈ Icc a₀ a₁,
      (X₁ (u, b), Y₁ (u, b)) = (X₂ (u, b), Y₂ (u, b)))
    (hcorner :
      (fderivWithin ℝ X₁ (Goursat.rectangle a₀ a₁ b₀ b) (a₀, b)) (0, 1) =
      (fderivWithin ℝ X₂ (Goursat.rectangle a₀ a₁ b b₁) (a₀, b)) (0, 1)) :
    ∀ u ∈ Icc a₀ a₁,
      fderivWithin ℝ X₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b) =
        fderivWithin ℝ X₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b) ∧
      fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b) =
        fderivWithin ℝ Y₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b) := by
  let z : ℝ → RectangleState := fun u => (X₁ (u, b), Y₁ (u, b))
  let p₁ : ℝ → IncomingState := fun u =>
    (fderivWithin ℝ X₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b)) (0, 1)
  let p₂ : ℝ → IncomingState := fun u =>
    (fderivWithin ℝ X₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b)) (0, 1)
  let L : IncomingState →L[ℝ] RectangleState :=
    ContinuousLinearMap.inl ℝ IncomingState OutgoingState
  let A : ℝ → IncomingState →L[ℝ] IncomingState := fun u =>
    (fderiv ℝ rectangleF (z u)).comp L
  let h : ℝ → IncomingState := fun u =>
    (fderiv ℝ rectangleF (z u)) (0, rectangleG (z u))
  have hbL : b ∈ Icc b₀ b := ⟨hb₀.le, le_rfl⟩
  have hbR : b ∈ Icc b b₁ := ⟨le_rfl, hb₁.le⟩
  have hzcont : ContinuousOn z (Icc a₀ a₁) := by
    have hZ : ContinuousOn
        (fun p => (X₁ p, Y₁ p)) (Goursat.rectangle a₀ a₁ b₀ b) :=
      hX₁.continuousOn.prodMk hY₁.continuousOn
    exact hZ.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => Goursat.pair_mem_rectangle hu hbL)
  have hzsafe : ∀ u ∈ Icc a₀ a₁, z u ∈ {z | IsSafeRectangleState z} := by
    intro u hu
    exact hsafe₁ (u, b) (Goursat.pair_mem_rectangle hu hbL)
  have hDFsafe : ContinuousOn (fderiv ℝ rectangleF) {z | IsSafeRectangleState z} := by
    intro w hw
    exact ((contDiffAt_rectangleF (hw)).continuousAt_fderiv
      (by decide)).continuousWithinAt
  have hDF : ContinuousOn (fun u => fderiv ℝ rectangleF (z u))
      (Icc a₀ a₁) := hDFsafe.comp hzcont hzsafe
  have hGsafe : ContinuousOn rectangleG {z | IsSafeRectangleState z} := by
    intro w hw
    exact ((contDiffAt_rectangleG (hw)).continuousAt).continuousWithinAt
  have hG : ContinuousOn (fun u => rectangleG (z u)) (Icc a₀ a₁) :=
    hGsafe.comp hzcont hzsafe
  have hA : ContinuousOn A (Icc a₀ a₁) :=
    hDF.clm_comp continuousOn_const
  have hh : ContinuousOn h (Icc a₀ a₁) :=
    hDF.clm_apply (continuousOn_const.prodMk hG)
  have hp₁ : ContinuousOn p₁ (Icc a₀ a₁) :=
    ((hX₁.continuousOn_fderivWithin
      (uniqueDiffOn_rectangle haa hb₀) (by norm_num)).clm_apply continuousOn_const).comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => Goursat.pair_mem_rectangle hu hbL)
  have hp₂ : ContinuousOn p₂ (Icc a₀ a₁) :=
    ((hX₂.continuousOn_fderivWithin
      (uniqueDiffOn_rectangle haa hb₁) (by norm_num)).clm_apply continuousOn_const).comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => Goursat.pair_mem_rectangle hu hbR)
  have hsplit (u : ℝ) (_hu : u ∈ Icc a₀ a₁) (p : IncomingState) :
      (fderiv ℝ rectangleF (z u)) (p, rectangleG (z u)) =
        A u p + h u := by
    have hdecomp : (p, rectangleG (z u)) =
        L p + ((0 : IncomingState), rectangleG (z u)) := by
      ext <;> simp [L]
    rw [hdecomp, map_add]
    rfl
  have hODE₁ (u : ℝ) (hu : u ∈ Icc a₀ a₁) :
      HasDerivWithinAt p₁ (A u (p₁ u) + h u) (Icc a₀ a₁) u := by
    have h := incoming_vertical_jet_horizontal_equation_safe haa hb₀ X₁ Y₁
      hX₁ hY₁ hsafe₁ hjet₁ hu hbL
    exact (hsplit u hu (p₁ u)) ▸ h
  have hODE₂ (u : ℝ) (hu : u ∈ Icc a₀ a₁) :
      HasDerivWithinAt p₂ (A u (p₂ u) + h u) (Icc a₀ a₁) u := by
    have h := incoming_vertical_jet_horizontal_equation_safe haa hb₁ X₂ Y₂
      hX₂ hY₂ hsafe₂ hjet₂ hu hbR
    have hz : (X₂ (u, b), Y₂ (u, b)) = z u := (htrace u hu).symm
    rw [hz] at h
    exact (hsplit u hu (p₂ u)) ▸ h
  have hpeq := eq_on_of_linear_vertical_edge_equations haa.le hp₁ hp₂
    hA hODE₁ hODE₂ hcorner
  intro u hu
  have hXcoord₁ := coordinate_derivatives_of_contDiffOn_rectangle
    haa hb₀ hX₁ hu hbL
  have hXcoord₂ := coordinate_derivatives_of_contDiffOn_rectangle
    haa hb₁ hX₂ hu hbR
  have hYcoord₁ := coordinate_derivatives_of_contDiffOn_rectangle
    haa hb₀ hY₁ hu hbL
  have hYcoord₂ := coordinate_derivatives_of_contDiffOn_rectangle
    haa hb₁ hY₂ hu hbR
  have hXu₁ :
      (fderivWithin ℝ X₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b)) (1, 0) =
        rectangleF (X₁ (u, b), Y₁ (u, b)) :=
    (hXcoord₁.1.derivWithin ((uniqueDiffOn_Icc haa) u hu)).symm.trans
      ((hjet₁ u hu b hbL).1.derivWithin ((uniqueDiffOn_Icc haa) u hu))
  have hXu₂ :
      (fderivWithin ℝ X₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b)) (1, 0) =
        rectangleF (X₂ (u, b), Y₂ (u, b)) :=
    (hXcoord₂.1.derivWithin ((uniqueDiffOn_Icc haa) u hu)).symm.trans
      ((hjet₂ u hu b hbR).1.derivWithin ((uniqueDiffOn_Icc haa) u hu))
  have hYu :
      (fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b)) (1, 0) =
      (fderivWithin ℝ Y₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b)) (1, 0) := by
    have htraceY (s : ℝ) (hs : s ∈ Icc a₀ a₁) : Y₁ (s, b) = Y₂ (s, b) :=
      congrArg Prod.snd (htrace s hs)
    have h := hYcoord₁.1.congr
      (fun s hs => (htraceY s hs).symm) (htraceY u hu).symm
    exact (h.derivWithin ((uniqueDiffOn_Icc haa) u hu)).symm.trans
      (hYcoord₂.1.derivWithin ((uniqueDiffOn_Icc haa) u hu))
  have hYv₁ :
      (fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b)) (0, 1) =
        rectangleG (X₁ (u, b), Y₁ (u, b)) :=
    (hYcoord₁.2.derivWithin ((uniqueDiffOn_Icc hb₀) b hbL)).symm.trans
      ((hjet₁ u hu b hbL).2.derivWithin ((uniqueDiffOn_Icc hb₀) b hbL))
  have hYv₂ :
      (fderivWithin ℝ Y₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b)) (0, 1) =
        rectangleG (X₂ (u, b), Y₂ (u, b)) :=
    (hYcoord₂.2.derivWithin ((uniqueDiffOn_Icc hb₁) b hbR)).symm.trans
      ((hjet₂ u hu b hbR).2.derivWithin ((uniqueDiffOn_Icc hb₁) b hbR))
  constructor
  · apply full_first_jet_eq_of_coordinate_jets
    · rw [hXu₁, hXu₂, htrace u hu]
    · exact hpeq u hu
  · apply full_first_jet_eq_of_coordinate_jets hYu
    rw [hYv₁, hYv₂, htrace u hu]


/-- Matching tangential derivatives of the left-edge incoming data supply
the corner transverse jet used by the horizontal seam theorem. -/
theorem full_first_jets_eq_on_horizontal_seam_of_corner_data_safe
    {a₀ a₁ b₀ b b₁ : ℝ}
    (haa : a₀ < a₁) (hb₀ : b₀ < b) (hb₁ : b < b₁)
    (X₁ : ℝ × ℝ → IncomingState) (Y₁ : ℝ × ℝ → OutgoingState)
    (X₂ : ℝ × ℝ → IncomingState) (Y₂ : ℝ × ℝ → OutgoingState)
    (hX₁ : ContDiffOn ℝ 1 X₁ (Goursat.rectangle a₀ a₁ b₀ b))
    (hY₁ : ContDiffOn ℝ 1 Y₁ (Goursat.rectangle a₀ a₁ b₀ b))
    (hX₂ : ContDiffOn ℝ 1 X₂ (Goursat.rectangle a₀ a₁ b b₁))
    (hY₂ : ContDiffOn ℝ 1 Y₂ (Goursat.rectangle a₀ a₁ b b₁))
    (hsafe₁ : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b,
      IsSafeRectangleState (X₁ p, Y₁ p))
    (hsafe₂ : ∀ p ∈ Goursat.rectangle a₀ a₁ b b₁,
      IsSafeRectangleState (X₂ p, Y₂ p))
    (hjet₁ : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b,
      HasDerivWithinAt (fun s => X₁ (s, v))
        (rectangleF (X₁ (u, v), Y₁ (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y₁ (u, t))
        (rectangleG (X₁ (u, v), Y₁ (u, v))) (Icc b₀ b) v)
    (hjet₂ : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b b₁,
      HasDerivWithinAt (fun s => X₂ (s, v))
        (rectangleF (X₂ (u, v), Y₂ (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y₂ (u, t))
        (rectangleG (X₂ (u, v), Y₂ (u, v))) (Icc b b₁) v)
    (htrace : ∀ u ∈ Icc a₀ a₁,
      (X₁ (u, b), Y₁ (u, b)) = (X₂ (u, b), Y₂ (u, b)))
    (p₀ : IncomingState)
    (hcorner₁ : HasDerivWithinAt (fun t => X₁ (a₀, t)) p₀ (Icc b₀ b) b)
    (hcorner₂ : HasDerivWithinAt (fun t => X₂ (a₀, t)) p₀ (Icc b b₁) b) :
    ∀ u ∈ Icc a₀ a₁,
      fderivWithin ℝ X₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b) =
        fderivWithin ℝ X₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b) ∧
      fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a₁ b₀ b) (u, b) =
        fderivWithin ℝ Y₂ (Goursat.rectangle a₀ a₁ b b₁) (u, b) := by
  have ha : a₀ ∈ Icc a₀ a₁ := ⟨le_rfl, haa.le⟩
  have hbL : b ∈ Icc b₀ b := ⟨hb₀.le, le_rfl⟩
  have hbR : b ∈ Icc b b₁ := ⟨le_rfl, hb₁.le⟩
  have hp₁ := (coordinate_derivatives_of_contDiffOn_rectangle
    haa hb₀ hX₁ ha hbL).2
  have hp₂ := (coordinate_derivatives_of_contDiffOn_rectangle
    haa hb₁ hX₂ ha hbR).2
  have hp₁eq := (hp₁.derivWithin ((uniqueDiffOn_Icc hb₀) b hbL)).symm.trans
    (hcorner₁.derivWithin ((uniqueDiffOn_Icc hb₀) b hbL))
  have hp₂eq := (hp₂.derivWithin ((uniqueDiffOn_Icc hb₁) b hbR)).symm.trans
    (hcorner₂.derivWithin ((uniqueDiffOn_Icc hb₁) b hbR))
  exact full_first_jets_eq_on_horizontal_seam_safe haa hb₀ hb₁
    X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ hsafe₁ hsafe₂ hjet₁ hjet₂
    htrace (hp₁eq.trans hp₂eq.symm)

end ChristodoulouBV.C1Solution

end
