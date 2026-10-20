module

public import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation
public import ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic.Linarith

/-!
# Continuous terminal traces for parameter-dependent linear Volterra equations

A scalar linear equation on the half-open top of a compact rectangle has a
continuous extension when its coefficients and initial data extend to the
closed rectangle. The extension is the variation-of-constants expression.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace intervalIntegral

/-- A solution of a parameter-dependent linear incoming Volterra equation
extends continuously to the top edge. The equation and the given solution are
needed only for parameters strictly below the top edge. -/
theorem exists_continuousOn_closed_rectangle_of_linear_volterra
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ < v₁)
    {a b : ℝ × ℝ → ℝ} {y₀ : ℝ → ℝ} {y : ℝ × ℝ → ℝ}
    (ha : ContinuousOn a (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hb : ContinuousOn b (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hy₀ : ContinuousOn y₀ (Icc v₀ v₁))
    (hy : ∀ v ∈ Ico v₀ v₁,
      ContinuousOn (fun u => y (u, v)) (Icc u₀ u₁))
    (hyinit : ∀ v ∈ Ico v₀ v₁, y (u₀, v) = y₀ v)
    (heq : ∀ v ∈ Ico v₀ v₁, ∀ u ∈ Icc u₀ u₁,
      y (u, v) - y (u₀, v) =
        ∫ s in u₀..u, a (s, v) * y (s, v) + b (s, v)) :
    ∃ Y : ℝ × ℝ → ℝ,
      ContinuousOn Y (Icc u₀ u₁ ×ˢ Icc v₀ v₁) ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ico v₀ v₁, Y (u, v) = y (u, v) := by
  let U := Goursat.clip u₀ u₁
  let V := Goursat.clip v₀ v₁
  let A : ℝ × ℝ → ℝ := fun p => a (U p.1, V p.2)
  let B : ℝ × ℝ → ℝ := fun p => b (U p.1, V p.2)
  let Y₀ : ℝ → ℝ := fun v => y₀ (V v)
  have hclip : Continuous (fun p : ℝ × ℝ => (U p.1, V p.2)) :=
    ((Goursat.continuous_clip u₀ u₁).comp continuous_fst).prodMk
      ((Goursat.continuous_clip v₀ v₁).comp continuous_snd)
  have hA : Continuous A := ha.comp_continuous hclip (fun p =>
    ⟨Goursat.clip_mem_Icc hu p.1, Goursat.clip_mem_Icc hv.le p.2⟩)
  have hB : Continuous B := hb.comp_continuous hclip (fun p =>
    ⟨Goursat.clip_mem_Icc hu p.1, Goursat.clip_mem_Icc hv.le p.2⟩)
  have hY₀ : Continuous Y₀ := hy₀.comp_continuous
    (Goursat.continuous_clip v₀ v₁) (Goursat.clip_mem_Icc hv.le)
  let K : ℝ × ℝ → ℝ := fun p => ∫ s in u₀..p.1, A (s, p.2)
  have hAKernel : Continuous (fun q : (ℝ × ℝ) × ℝ => A (q.2, q.1.2)) :=
    hA.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have hK : Continuous K :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hAKernel continuous_fst
  let C : ℝ × ℝ → ℝ := fun p => Real.exp (-(K p)) * B p
  have hC : Continuous C := (Real.continuous_exp.comp hK.neg).mul hB
  let H : ℝ × ℝ → ℝ := fun p => ∫ s in u₀..p.1, C (s, p.2)
  have hCKernel : Continuous (fun q : (ℝ × ℝ) × ℝ => C (q.2, q.1.2)) :=
    hC.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  have hH : Continuous H :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hCKernel continuous_fst
  let Y : ℝ × ℝ → ℝ := fun p => Real.exp (K p) * (Y₀ p.2 + H p)
  have hY : Continuous Y :=
    (Real.continuous_exp.comp hK).mul
      ((hY₀.comp continuous_snd).add hH)
  refine ⟨Y, hY.continuousOn, ?_⟩
  intro u hu' v hv'
  have hvClosed : v ∈ Icc v₀ v₁ := ⟨hv'.1, hv'.2.le⟩
  have hclipU (s : ℝ) (hs : s ∈ Icc u₀ u) : U s = s :=
    Goursat.clip_eq_self ⟨hs.1, hs.2.trans hu'.2⟩
  have hclipV : V v = v := Goursat.clip_eq_self hvClosed
  have hAeq (s : ℝ) (hs : s ∈ Icc u₀ u) : A (s, v) = a (s, v) := by
    simp only [A, hclipU s hs, hclipV]
  have hBeq (s : ℝ) (hs : s ∈ Icc u₀ u) : B (s, v) = b (s, v) := by
    simp only [B, hclipU s hs, hclipV]
  have hKslice (s : ℝ) (hs : s ∈ Icc u₀ u) :
      K (s, v) = ∫ t in u₀..s, a (t, v) := by
    dsimp [K]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc u₀ s := by
      simpa only [uIcc_of_le hs.1] using ht
    exact hAeq t ⟨ht'.1, ht'.2.trans hs.2⟩
  have hAslice : ContinuousOn (fun s => a (s, v)) (Icc u₀ u₁) :=
    ha.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hvClosed⟩)
  have hBslice : ContinuousOn (fun s => b (s, v)) (Icc u₀ u₁) :=
    hb.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hvClosed⟩)
  have hki : IntervalIntegrable (fun s => a (s, v)) volume u₀ u₁ :=
    hAslice.intervalIntegrable_of_Icc hu
  have hbi : IntervalIntegrable (fun s => b (s, v)) volume u₀ u₁ :=
    hBslice.intervalIntegrable_of_Icc hu
  have hkyi : IntervalIntegrable (fun s => a (s, v) * y (s, v))
      volume u₀ u₁ :=
    (hAslice.mul (hy v hv')).intervalIntegrable_of_Icc hu
  have hEqSlice : ∀ s ∈ Icc u₀ u₁,
      y (s, v) - y (u₀, v) =
        ∫ t in u₀..s, a (t, v) * y (t, v) + b (t, v) :=
    heq v hv'
  have hformula := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    hu hki hbi hkyi hEqSlice hu'
  have hCeq (s : ℝ) (hs : s ∈ Icc u₀ u) :
      C (s, v) = Real.exp (-(∫ t in u₀..s, a (t, v))) * b (s, v) := by
    simp only [C, hKslice s hs, hBeq s hs]
  have hHeq : H (u, v) =
      ∫ s in u₀..u, Real.exp (-(∫ t in u₀..s, a (t, v))) * b (s, v) := by
    dsimp [H]
    apply intervalIntegral.integral_congr
    intro s hs
    exact hCeq s (by simpa only [uIcc_of_le hu'.1] using hs)
  dsimp [Y]
  rw [hKslice u ⟨hu'.1, le_rfl⟩, hHeq]
  change Real.exp (∫ s in u₀..u, a (s, v)) *
      (y₀ (V v) + ∫ s in u₀..u,
        Real.exp (-(∫ t in u₀..s, a (t, v))) * b (s, v)) = y (u, v)
  rw [hclipV, ← hyinit v hv']
  exact hformula.symm

end intervalIntegral

end
