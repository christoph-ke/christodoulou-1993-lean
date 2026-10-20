module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseStep
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Global representatives of rectangle-valued Goursat iterates

Coordinate clipping extends a continuous state on a closed rectangle to a
continuous pair on the plane. The representatives agree with the original
state throughout the rectangle and make the local Picard recursion available
as an ordinary integral equation.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first component of a rectangle-valued state, extended by coordinate clipping. -/
@[expose] noncomputable def clippedFirst
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Z : C(rectangle u₀ u₁ v₀ v₁, E × F)) : ℝ × ℝ → E :=
  fun p => (Z (clippedPoint hu hv p)).1

/-- The second component of a rectangle-valued state, extended by coordinate clipping. -/
@[expose] noncomputable def clippedSecond
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Z : C(rectangle u₀ u₁ v₀ v₁, E × F)) : ℝ × ℝ → F :=
  fun p => (Z (clippedPoint hu hv p)).2

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Clipping a continuous state gives a globally continuous first component. -/
theorem continuous_clippedFirst
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Z : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    Continuous (clippedFirst hu hv Z) :=
  (continuous_fst.comp Z.continuous).comp (continuous_clippedPoint hu hv)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Clipping a continuous state gives a globally continuous second component. -/
theorem continuous_clippedSecond
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Z : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    Continuous (clippedSecond hu hv Z) :=
  (continuous_snd.comp Z.continuous).comp (continuous_clippedPoint hu hv)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- On the rectangle the clipped first component equals the original one. -/
theorem clippedFirst_eq
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (p : rectangle u₀ u₁ v₀ v₁) :
    clippedFirst hu hv Z p.1 = (Z p).1 := by
  simp only [clippedFirst, clippedPoint_eq_self hu hv p]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- On the rectangle the clipped second component equals the original one. -/
theorem clippedSecond_eq
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (p : rectangle u₀ u₁ v₀ v₁) :
    clippedSecond hu hv Z p.1 = (Z p).2 := by
  simp only [clippedSecond, clippedPoint_eq_self hu hv p]

/-- The local zeroth Picard iterate has the prescribed mixed edge trace. -/
theorem picardIterateOnBall_zero_apply
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (p : rectangle u₀ u₁ v₀ v₁) :
    picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY 0 p = (x₀ p.1.2, y₀ p.1.1) := by
  unfold picardIterateOnBall
  exact picardIterate_zero_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀
    (extendRectangleBall hu hv c ρ fX)
    (extendRectangleBall hu hv c ρ fY) hx₀ hy₀
    (continuous_extendRectangleBall hu hv c ρ hρ fX hfX)
    (continuous_extendRectangleBall hu hv c ρ hρ fY hfY) p

/-- In the state ball, each local Picard successor obeys the original
characteristic equations for its globally clipped predecessor. -/
theorem picardIterateOnBall_succ_apply_clipped
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (r M : ℝ) (hM : 0 ≤ M)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (n : ℕ) (p : rectangle u₀ u₁ v₀ v₁) :
    let Z := picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY
    Z (n + 1) p =
      (x₀ p.1.2 + ∫ s in u₀..p.1.1,
        fX (s, p.1.2) (clippedFirst hu hv (Z n) (s, p.1.2),
          clippedSecond hu hv (Z n) (s, p.1.2)),
       y₀ p.1.1 + ∫ t in v₀..p.1.2,
        fY (p.1.1, t) (clippedFirst hu hv (Z n) (p.1.1, t),
          clippedSecond hu hv (Z n) (p.1.1, t))) := by
  dsimp only
  simpa only [clippedFirst, clippedSecond, Prod.mk.eta] using
    (picardIterateOnBall_succ_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀
      hx₀ hy₀ c ρ hρ fX fY hfX hfY r M hM hdata hMX hMY hsize n p)

end Goursat

end
