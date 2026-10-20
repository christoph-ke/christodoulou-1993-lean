module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseConvergence
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Uniform convergence of state-dependent fields

On a compact rectangle, uniform convergence of continuous states is preserved
when a jointly continuous field is evaluated at the coordinate and state.
-/

public section

open Set Filter
open scoped Topology

namespace Goursat

variable {S T : Type*} [NormedAddCommGroup S] [NormedAddCommGroup T]

/-- Uniformly convergent states on a rectangle remain uniformly convergent
after evaluation in a jointly continuous global field. -/
theorem tendsto_field_comp_state_on_rectangle
    {u₀ u₁ v₀ v₁ : ℝ}
    (H : (ℝ × ℝ) × S → T) (hH : Continuous H)
    (Z : ℕ → C(rectangle u₀ u₁ v₀ v₁, S))
    (Z_lim : C(rectangle u₀ u₁ v₀ v₁, S))
    (hZ : Tendsto Z atTop (𝓝 Z_lim)) :
    Tendsto
      (fun n => (⟨fun p : rectangle u₀ u₁ v₀ v₁ => H (p.1, Z n p),
        hH.comp (continuous_subtype_val.prodMk (Z n).continuous)⟩ :
          C(rectangle u₀ u₁ v₀ v₁, T)))
      atTop
      (𝓝 (⟨fun p : rectangle u₀ u₁ v₀ v₁ => H (p.1, Z_lim p),
        hH.comp (continuous_subtype_val.prodMk Z_lim.continuous)⟩ :
          C(rectangle u₀ u₁ v₀ v₁, T))) := by
  let W : ℕ → C(rectangle u₀ u₁ v₀ v₁, (ℝ × ℝ) × S) :=
    fun n => ⟨fun p => (p.1, Z n p),
      continuous_subtype_val.prodMk (Z n).continuous⟩
  let W_lim : C(rectangle u₀ u₁ v₀ v₁, (ℝ × ℝ) × S) :=
    ⟨fun p => (p.1, Z_lim p),
      continuous_subtype_val.prodMk Z_lim.continuous⟩
  have hWbound : ∀ n, dist (W n) W_lim ≤ dist (Z n) Z_lim := by
    intro n
    apply (ContinuousMap.dist_le dist_nonneg).2
    intro p
    change dist (p.1, Z n p) (p.1, Z_lim p) ≤ _
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
      (ContinuousMap.dist_apply_le_dist p :
        dist (Z n p) (Z_lim p) ≤ dist (Z n) Z_lim)
  have hW : Tendsto W atTop (𝓝 W_lim) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun n => dist_nonneg) hWbound
        (tendsto_iff_dist_tendsto_zero.mp hZ))
  let Hc : C((ℝ × ℝ) × S, T) := ⟨H, hH⟩
  have hraw : Tendsto (fun n => Hc.comp (W n)) atTop
      (𝓝 (Hc.comp W_lim)) := by
    simpa only [Function.comp_def] using
      (Hc.continuous_postcomp.tendsto W_lim).comp hW
  convert hraw using 1
  · funext n
    ext p
    rfl
  · ext p
    rfl


/-- Uniform convergence is preserved by a field continuous only on a
rectangle times a closed state ball, provided all states stay in that ball. -/
theorem tendsto_field_comp_state_on_rectangle_ball
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    [NormedSpace ℝ S]
    (c : S) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ × ℝ → S → T)
    (hf : ContinuousOn f.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (Z : ℕ → C(rectangle u₀ u₁ v₀ v₁, S))
    (Z_lim : C(rectangle u₀ u₁ v₀ v₁, S))
    (hZ : Tendsto Z atTop (𝓝 Z_lim))
    (hball : ∀ n p, dist (Z n p) c ≤ ρ)
    (hball_lim : ∀ p, dist (Z_lim p) c ≤ ρ) :
    Tendsto
      (fun n => (⟨fun p : rectangle u₀ u₁ v₀ v₁ => f p.1 (Z n p),
        hf.comp_continuous
          (continuous_subtype_val.prodMk (Z n).continuous)
          (fun p => ⟨p.2, hball n p⟩)⟩ :
          C(rectangle u₀ u₁ v₀ v₁, T)))
      atTop
      (𝓝 (⟨fun p : rectangle u₀ u₁ v₀ v₁ => f p.1 (Z_lim p),
        hf.comp_continuous
          (continuous_subtype_val.prodMk Z_lim.continuous)
          (fun p => ⟨p.2, hball_lim p⟩)⟩ :
          C(rectangle u₀ u₁ v₀ v₁, T))) := by
  let H : (ℝ × ℝ) × S → T := (extendRectangleBall hu hv c ρ f).uncurry
  have hH : Continuous H :=
    continuous_extendRectangleBall hu hv c ρ hρ f hf
  have h := tendsto_field_comp_state_on_rectangle H hH Z Z_lim hZ
  convert h using 1
  · funext n
    ext p
    exact (extendRectangleBall_eq hu hv c ρ hρ f p.2 (hball n p)).symm
  · congr 1
    ext p
    exact (extendRectangleBall_eq hu hv c ρ hρ f p.2 (hball_lim p)).symm


/-- Pairing two uniformly convergent sequences of continuous maps preserves
uniform convergence on a compact domain. -/
theorem tendsto_continuousMap_prodMk
    {K U V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup U] [NormedAddCommGroup V]
    (f : ℕ → C(K, U)) (g : ℕ → C(K, V))
    (f_lim : C(K, U)) (g_lim : C(K, V))
    (hf : Tendsto f atTop (𝓝 f_lim))
    (hg : Tendsto g atTop (𝓝 g_lim)) :
    Tendsto (fun n => (f n).prodMk (g n)) atTop
      (𝓝 (f_lim.prodMk g_lim)) := by
  have hbound : ∀ n,
      dist ((f n).prodMk (g n)) (f_lim.prodMk g_lim) ≤
        max (dist (f n) f_lim) (dist (g n) g_lim) := by
    intro n
    apply (ContinuousMap.dist_le (le_max_of_le_left dist_nonneg)).2
    intro p
    change dist (f n p, g n p) (f_lim p, g_lim p) ≤ _
    rw [Prod.dist_eq]
    exact max_le
      ((ContinuousMap.dist_apply_le_dist p).trans (le_max_left _ _))
      ((ContinuousMap.dist_apply_le_dist p).trans (le_max_right _ _))
  have hmax : Tendsto (fun n =>
      max (dist (f n) f_lim) (dist (g n) g_lim)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, max_self] using
      (continuous_max.tendsto (0, 0)).comp
        ((tendsto_iff_dist_tendsto_zero.mp hf).prodMk_nhds
          (tendsto_iff_dist_tendsto_zero.mp hg))
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun n => dist_nonneg) hbound hmax)


/-- Applying uniformly convergent continuous operator fields to uniformly
convergent continuous vector fields preserves uniform convergence. -/
theorem tendsto_continuousMap_clm_apply
    {K U V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ℕ → C(K, U →L[ℝ] V)) (x : ℕ → C(K, U))
    (A_lim : C(K, U →L[ℝ] V)) (x_lim : C(K, U))
    (hA : Tendsto A atTop (𝓝 A_lim))
    (hx : Tendsto x atTop (𝓝 x_lim)) :
    Tendsto
      (fun n => (⟨fun p => A n p (x n p),
        ((A n).continuous.clm_apply (x n).continuous)⟩ : C(K, V)))
      atTop
      (𝓝 (⟨fun p => A_lim p (x_lim p),
        (A_lim.continuous.clm_apply x_lim.continuous)⟩ : C(K, V))) := by
  let H : C((U →L[ℝ] V) × U, V) :=
    ⟨fun q => q.1 q.2,
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (F := V)).continuous⟩
  have hpair := tendsto_continuousMap_prodMk A x A_lim x_lim hA hx
  have h := (H.continuous_postcomp.tendsto (A_lim.prodMk x_lim)).comp hpair
  convert h using 1
  · funext n
    ext p
    rfl
  · congr 1


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Insert a first-state variation into the full coordinate and state
space while keeping the coordinate and second-state variations zero. -/
@[expose] def firstStateInclusion :
    E →L[ℝ] (ℝ × ℝ) × (E × F) :=
  (0 : E →L[ℝ] ℝ × ℝ).prod (ContinuousLinearMap.inl ℝ E F)

/-- Insert a second-state variation into the full coordinate and state
space while keeping the coordinate and first-state variations zero. -/
@[expose] def secondStateInclusion :
    F →L[ℝ] (ℝ × ℝ) × (E × F) :=
  (0 : F →L[ℝ] ℝ × ℝ).prod (ContinuousLinearMap.inr ℝ E F)

/-- The first-state inclusion preserves the norm in the max product norm. -/
theorem norm_firstStateInclusion (x : E) :
    ‖(firstStateInclusion (E := E) (F := F)) x‖ = ‖x‖ := by
  simp [firstStateInclusion, Prod.norm_def]

/-- The second-state inclusion preserves the norm in the max product norm. -/
theorem norm_secondStateInclusion (y : F) :
    ‖(secondStateInclusion (E := E) (F := F)) y‖ = ‖y‖ := by
  simp [secondStateInclusion, Prod.norm_def]

/-- A bound on the first-state directional derivative bounds the corresponding
continuous linear operator. -/
theorem norm_firstState_comp_le
    (L : ((ℝ × ℝ) × (E × F)) →L[ℝ] E) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (hL : ∀ x : E, ‖L ((0, 0), (x, 0))‖ ≤ κ * ‖x‖) :
    ‖L.comp (firstStateInclusion (E := E) (F := F))‖ ≤ κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hκ
  intro x
  have hz : ((0, 0) : ℝ × ℝ) = 0 := by ext <;> simp
  simpa only [firstStateInclusion, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.inl_apply, hz] using hL x

/-- A bound on the second-state directional derivative bounds its operator. -/
theorem norm_secondState_comp_le
    (L : ((ℝ × ℝ) × (E × F)) →L[ℝ] F) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (hL : ∀ y : F, ‖L ((0, 0), (0, y))‖ ≤ κ * ‖y‖) :
    ‖L.comp (secondStateInclusion (E := E) (F := F))‖ ≤ κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hκ
  intro y
  have hz : ((0, 0) : ℝ × ℝ) = 0 := by ext <;> simp
  simpa only [secondStateInclusion, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.inr_apply, hz] using hL y

end Goursat

end
