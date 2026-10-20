module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransversePrimitive
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Convergence of characteristic jets in a Goursat iteration

The characteristic jets of the next Picard iterate are the nonlinear fields
at the preceding state. Uniform state convergence therefore gives uniform
convergence of these jets by continuity on the visited state ball.
-/

public section

open Set Filter
open scoped Topology

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A characteristic jet sequence converges uniformly when each successor
is the evaluation of a continuous local field at the preceding state. -/
theorem tendsto_characteristic_jet_of_picard_states
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (c : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    {T : Type*} [NormedAddCommGroup T]
    (f : ℝ × ℝ → E × F → T)
    (hf : ContinuousOn f.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (Z : ℕ → C(rectangle u₀ u₁ v₀ v₁, E × F))
    (Z_lim : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hZ : Tendsto Z atTop (𝓝 Z_lim))
    (hball : ∀ n p, dist (Z n p) c ≤ ρ)
    (hball_lim : ∀ p, dist (Z_lim p) c ≤ ρ)
    (J : ℕ → C(rectangle u₀ u₁ v₀ v₁, T))
    (hJ : ∀ n p, J (n + 1) p = f p.1 (Z n p)) :
    Tendsto J atTop
      (𝓝 (⟨fun p : rectangle u₀ u₁ v₀ v₁ => f p.1 (Z_lim p),
        hf.comp_continuous
          (continuous_subtype_val.prodMk Z_lim.continuous)
          (fun p => ⟨p.2, hball_lim p⟩)⟩ :
          C(rectangle u₀ u₁ v₀ v₁, T))) := by
  let J_lim : C(rectangle u₀ u₁ v₀ v₁, T) :=
    ⟨fun p => f p.1 (Z_lim p),
      hf.comp_continuous
        (continuous_subtype_val.prodMk Z_lim.continuous)
        (fun p => ⟨p.2, hball_lim p⟩)⟩
  have hfield := tendsto_field_comp_state_on_rectangle_ball hu hv c ρ hρ
    f hf Z Z_lim hZ hball hball_lim
  have hshift : (fun n => J (n + 1)) =
      (fun n => (⟨fun p : rectangle u₀ u₁ v₀ v₁ => f p.1 (Z n p),
        hf.comp_continuous
          (continuous_subtype_val.prodMk (Z n).continuous)
          (fun p => ⟨p.2, hball n p⟩)⟩ :
          C(rectangle u₀ u₁ v₀ v₁, T))) := by
    funext n
    ext p
    exact hJ n p
  rw [← hshift] at hfield
  exact (tendsto_add_atTop_iff_nat 1).1 hfield

end Goursat

end
