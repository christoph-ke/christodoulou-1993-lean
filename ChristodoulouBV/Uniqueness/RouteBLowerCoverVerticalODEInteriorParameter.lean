module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverVerticalODE
import Mathlib.Tactic.Linarith

/-!
# Terminal traces with interior parameter transport

The old incoming derivative is naturally defined as a relative derivative at
the two incoming endpoints. The outgoing ODE need only be checked for strict
interior incoming parameters; continuity then identifies both endpoint slices.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- An outgoing linear ODE for strict interior incoming parameters has a
jointly continuous terminal trace when the old jets are continuous up to
the two parameter endpoints below the terminal edge. -/
theorem exists_continuousOn_terminal_of_interior_parameter_linear_ode
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    {a b : ℝ × ℝ → ℝ} {y₀ : ℝ → ℝ} {y : ℝ × ℝ → ℝ}
    (ha : ContinuousOn a (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hb : ContinuousOn b (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hy₀ : ContinuousOn y₀ (Icc u₀ u₁))
    (hy : ∀ u ∈ Ioo u₀ u₁,
      ContinuousOn (fun v => y (u, v)) (Ico v₀ v₁))
    (hyparameter : ∀ v ∈ Ico v₀ v₁,
      ContinuousOn (fun u => y (u, v)) (Icc u₀ u₁))
    (hyinit : ∀ u ∈ Ioo u₀ u₁, y (u, v₀) = y₀ u)
    (hderiv : ∀ u ∈ Ioo u₀ u₁, ∀ v ∈ Ioo v₀ v₁,
      HasDerivAt (fun t => y (u, t))
        (a (u, v) * y (u, v) + b (u, v)) v) :
    ∃ Y : ℝ × ℝ → ℝ,
      ContinuousOn Y (Icc u₀ u₁ ×ˢ Icc v₀ v₁) ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ico v₀ v₁,
        Y (u, v) = y (u, v) := by
  let U := Goursat.clip u₀ u₁
  let V := Goursat.clip v₀ v₁
  let A : ℝ × ℝ → ℝ := fun p => a (U p.1, V p.2)
  let B : ℝ × ℝ → ℝ := fun p => b (U p.1, V p.2)
  let Y₀ : ℝ → ℝ := fun u => y₀ (U u)
  have hclip : Continuous (fun p : ℝ × ℝ => (U p.1, V p.2)) :=
    ((Goursat.continuous_clip u₀ u₁).comp continuous_fst).prodMk
      ((Goursat.continuous_clip v₀ v₁).comp continuous_snd)
  have hA : Continuous A := ha.comp_continuous hclip (fun p =>
    ⟨Goursat.clip_mem_Icc hu.le p.1, Goursat.clip_mem_Icc hv.le p.2⟩)
  have hB : Continuous B := hb.comp_continuous hclip (fun p =>
    ⟨Goursat.clip_mem_Icc hu.le p.1, Goursat.clip_mem_Icc hv.le p.2⟩)
  have hY₀ : Continuous Y₀ := hy₀.comp_continuous
    (Goursat.continuous_clip u₀ u₁) (Goursat.clip_mem_Icc hu.le)
  let K : ℝ × ℝ → ℝ := fun p => ∫ s in v₀..p.2, A (p.1, s)
  have hAKernel : Continuous (fun q : (ℝ × ℝ) × ℝ => A (q.1.1, q.2)) :=
    hA.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hK : Continuous K :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hAKernel continuous_snd
  let C : ℝ × ℝ → ℝ := fun p => Real.exp (-(K p)) * B p
  have hC : Continuous C := (Real.continuous_exp.comp hK.neg).mul hB
  let H : ℝ × ℝ → ℝ := fun p => ∫ s in v₀..p.2, C (p.1, s)
  have hCKernel : Continuous (fun q : (ℝ × ℝ) × ℝ => C (q.1.1, q.2)) :=
    hC.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hH : Continuous H :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hCKernel continuous_snd
  let Y : ℝ × ℝ → ℝ := fun p => Real.exp (K p) * (Y₀ p.1 + H p)
  have hY : Continuous Y :=
    (Real.continuous_exp.comp hK).mul
      ((hY₀.comp continuous_fst).add hH)
  have hEqInterior : ∀ u ∈ Ioo u₀ u₁, ∀ v ∈ Ico v₀ v₁,
      Y (u, v) = y (u, v) := by
    intro u hu' v hv'
    have huClosed : u ∈ Icc u₀ u₁ := ⟨hu'.1.le, hu'.2.le⟩
    have hclipU : U u = u := Goursat.clip_eq_self huClosed
    have hclipV (s : ℝ) (hs : s ∈ Icc v₀ v) : V s = s :=
      Goursat.clip_eq_self ⟨hs.1, hs.2.trans hv'.2.le⟩
    have hAeq (s : ℝ) (hs : s ∈ Icc v₀ v) : A (u, s) = a (u, s) := by
      simp only [A, hclipU, hclipV s hs]
    have hBeq (s : ℝ) (hs : s ∈ Icc v₀ v) : B (u, s) = b (u, s) := by
      simp only [B, hclipU, hclipV s hs]
    have hKslice (s : ℝ) (hs : s ∈ Icc v₀ v) :
        K (u, s) = ∫ t in v₀..s, a (u, t) := by
      dsimp [K]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc v₀ s := by
        simpa only [uIcc_of_le hs.1] using ht
      exact hAeq t ⟨ht'.1, ht'.2.trans hs.2⟩
    have hAslice : ContinuousOn (fun s => a (u, s)) (Icc v₀ v) :=
      (ha.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨huClosed, ⟨hs.1, hs.2.trans hv'.2.le⟩⟩))
    have hBslice : ContinuousOn (fun s => b (u, s)) (Icc v₀ v) :=
      (hb.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨huClosed, ⟨hs.1, hs.2.trans hv'.2.le⟩⟩))
    have hyslice : ContinuousOn (fun s => y (u, s)) (Icc v₀ v) :=
      (hy u hu').mono (fun s hs => ⟨hs.1, hs.2.trans_lt hv'.2⟩)
    have hsource : ContinuousOn
        (fun s => a (u, s) * y (u, s) + b (u, s)) (Icc v₀ v) :=
      (hAslice.mul hyslice).add hBslice
    have hint : IntervalIntegrable
        (fun s => a (u, s) * y (u, s) + b (u, s)) volume v₀ v :=
      hsource.intervalIntegrable_of_Icc hv'.1
    have heq : ∀ s ∈ Icc v₀ v,
        y (u, s) - y (u, v₀) =
          ∫ t in v₀..s, a (u, t) * y (u, t) + b (u, t) := by
      intro s hs
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        hs.1 (hyslice.mono (fun t ht => ⟨ht.1, ht.2.trans hs.2⟩))
      · intro t ht
        exact hderiv u hu' t ⟨ht.1, (ht.2.trans_le hs.2).trans hv'.2⟩
      · exact (hsource.mono (fun t ht => ⟨ht.1, ht.2.trans hs.2⟩))
          |>.intervalIntegrable_of_Icc hs.1
    have hki : IntervalIntegrable (fun s => a (u, s)) volume v₀ v :=
      hAslice.intervalIntegrable_of_Icc hv'.1
    have hbi : IntervalIntegrable (fun s => b (u, s)) volume v₀ v :=
      hBslice.intervalIntegrable_of_Icc hv'.1
    have hkyi : IntervalIntegrable
        (fun s => a (u, s) * y (u, s)) volume v₀ v :=
      (hAslice.mul hyslice).intervalIntegrable_of_Icc hv'.1
    have hformula := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
      hv'.1 hki hbi hkyi heq ⟨hv'.1, le_rfl⟩
    have hCeq (s : ℝ) (hs : s ∈ Icc v₀ v) :
        C (u, s) = Real.exp (-(∫ t in v₀..s, a (u, t))) * b (u, s) := by
      simp only [C, hKslice s hs, hBeq s hs]
    have hHeq : H (u, v) =
        ∫ s in v₀..v, Real.exp (-(∫ t in v₀..s, a (u, t))) * b (u, s) := by
      dsimp [H]
      apply intervalIntegral.integral_congr
      intro s hs
      exact hCeq s (by simpa only [uIcc_of_le hv'.1] using hs)
    dsimp [Y]
    rw [hKslice v ⟨hv'.1, le_rfl⟩, hHeq]
    change Real.exp (∫ s in v₀..v, a (u, s)) *
        (y₀ (U u) + ∫ s in v₀..v,
          Real.exp (-(∫ t in v₀..s, a (u, t))) * b (u, s)) = y (u, v)
    rw [hclipU, ← hyinit u hu']
    exact hformula.symm
  refine ⟨Y, hY.continuousOn, ?_⟩
  intro u hu' v hv'
  have hYslice : ContinuousOn (fun t => Y (t, v)) (Icc u₀ u₁) :=
    (hY.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hEq : EqOn (fun t => Y (t, v)) (fun t => y (t, v))
      (Ioo u₀ u₁) := fun t ht => hEqInterior t ht v hv'
  exact (hEq.of_subset_closure hYslice (hyparameter v hv')
    (fun _ ht => ⟨ht.1.le, ht.2.le⟩)
    (by rw [closure_Ioo hu.ne])) hu'

end ChristodoulouBV.Uniqueness

end
