module

public import Mathlib.Topology.CompactOpen
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Picard
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Passing characteristic integral jets to uniform limits

These lemmas recover transverse derivatives on a closed rectangle from integral
identities of uniformly convergent continuous approximations and uniformly convergent
continuous jets.  They include one-sided derivatives at the edges and corners.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Membership of a pair in a closed rectangle from membership of its coordinates. -/
theorem pair_mem_rectangle {u₀ u₁ v₀ v₁ u v : ℝ}
    (hu : u ∈ Icc u₀ u₁) (hv : v ∈ Icc v₀ v₁) :
    (u, v) ∈ rectangle u₀ u₁ v₀ v₁ := by
  simpa only [rectangle] using
    (show (u, v) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨hu, hv⟩)

/-- Uniform limits of continuous vertical primitives and their continuous integrands
satisfy the prescribed vertical derivative identity throughout the closed rectangle. -/
theorem hasDerivWithinAt_vertical_of_tendsto_integral_eq
    {u₀ u₁ v₀ v₁ : ℝ} (hv : v₀ ≤ v₁)
    (Xn Pn : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (X P : C(rectangle u₀ u₁ v₀ v₁, E))
    (hX : Tendsto Xn atTop (𝓝 X)) (hP : Tendsto Pn atTop (𝓝 P))
    (heq : ∀ n (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
      Xn n ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
        Xn n ⟨(u, v₀), pair_mem_rectangle hu' ⟨le_rfl, hv⟩⟩ +
        ∫ t in v₀..v, Pn n ⟨(u, clip v₀ v₁ t),
          pair_mem_rectangle hu' (clip_mem_Icc hv t)⟩)
    {u v : ℝ} (hu' : u ∈ Icc u₀ u₁) (hv' : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt (fun t => X ⟨(u, clip v₀ v₁ t),
      pair_mem_rectangle hu' (clip_mem_Icc hv t)⟩)
      (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v := by
  let σ : C(Icc v₀ v₁, rectangle u₀ u₁ v₀ v₁) :=
    ⟨fun t => ⟨(u, t.1), pair_mem_rectangle hu' t.2⟩,
      Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _⟩
  have hXslice : Tendsto (fun n => (Xn n).comp σ) atTop (𝓝 (X.comp σ)) := by
    simpa only [Function.comp_def] using
      ((ContinuousMap.continuous_precomp σ).tendsto X).comp hX
  have hPslice : Tendsto (fun n => (Pn n).comp σ) atTop (𝓝 (P.comp σ)) := by
    simpa only [Function.comp_def] using
      ((ContinuousMap.continuous_precomp σ).tendsto P).comp hP
  have hEqSlice (n : ℕ) (t : ℝ) (ht : t ∈ Icc v₀ v₁) :
      (Xn n).comp σ ⟨t, ht⟩ =
        (Xn n).comp σ ⟨v₀, ⟨le_rfl, hv⟩⟩ +
        ∫ s in v₀..t, (Pn n).comp σ ⟨clip v₀ v₁ s,
          clip_mem_Icc hv s⟩ :=
    heq n u hu' t ht
  have h := intervalIntegral.hasDerivWithinAt_of_tendsto_integral_eq hv
    (fun n => (Xn n).comp σ) (fun n => (Pn n).comp σ)
    (X.comp σ) (P.comp σ) hXslice hPslice hEqSlice hv'
  exact h

/-- Uniform limits of continuous horizontal primitives and their continuous integrands
satisfy the prescribed horizontal derivative identity throughout the closed rectangle. -/
theorem hasDerivWithinAt_horizontal_of_tendsto_integral_eq
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁)
    (Xn Pn : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (X P : C(rectangle u₀ u₁ v₀ v₁, E))
    (hX : Tendsto Xn atTop (𝓝 X)) (hP : Tendsto Pn atTop (𝓝 P))
    (heq : ∀ n (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
      Xn n ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
        Xn n ⟨(u₀, v), pair_mem_rectangle ⟨le_rfl, hu⟩ hv'⟩ +
        ∫ s in u₀..u, Pn n ⟨(clip u₀ u₁ s, v),
          pair_mem_rectangle (clip_mem_Icc hu s) hv'⟩)
    {u v : ℝ} (hu' : u ∈ Icc u₀ u₁) (hv' : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt (fun s => X ⟨(clip u₀ u₁ s, v),
      pair_mem_rectangle (clip_mem_Icc hu s) hv'⟩)
      (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u := by
  let σ : C(Icc u₀ u₁, rectangle u₀ u₁ v₀ v₁) :=
    ⟨fun t => ⟨(t.1, v), pair_mem_rectangle t.2 hv'⟩,
      Continuous.subtype_mk (continuous_subtype_val.prodMk continuous_const) _⟩
  have hXslice : Tendsto (fun n => (Xn n).comp σ) atTop (𝓝 (X.comp σ)) := by
    simpa only [Function.comp_def] using
      ((ContinuousMap.continuous_precomp σ).tendsto X).comp hX
  have hPslice : Tendsto (fun n => (Pn n).comp σ) atTop (𝓝 (P.comp σ)) := by
    simpa only [Function.comp_def] using
      ((ContinuousMap.continuous_precomp σ).tendsto P).comp hP
  have hEqSlice (n : ℕ) (t : ℝ) (ht : t ∈ Icc u₀ u₁) :
      (Xn n).comp σ ⟨t, ht⟩ =
        (Xn n).comp σ ⟨u₀, ⟨le_rfl, hu⟩⟩ +
        ∫ s in u₀..t, (Pn n).comp σ ⟨clip u₀ u₁ s,
          clip_mem_Icc hu s⟩ :=
    heq n t ht v hv'
  have h := intervalIntegral.hasDerivWithinAt_of_tendsto_integral_eq hu
    (fun n => (Xn n).comp σ) (fun n => (Pn n).comp σ)
    (X.comp σ) (P.comp σ) hXslice hPslice hEqSlice hu'
  exact h

end Goursat

end
