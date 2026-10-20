module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Final
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartialBanach
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Continuous extension for local Goursat nonlinearities

A radial retraction onto a closed state ball and coordinate clipping extend
nonlinearities that are continuous on a rectangle times that ball to globally
continuous functions. The extension agrees with the original function on its
domain, so the already established ball-preserving Picard theory applies.
-/

public section

open Set Filter
open scoped Topology

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction onto a closed ball of positive radius. -/
@[expose] noncomputable def ballRetract (c : E) (ρ : ℝ) (z : E) : E :=
  c + (ρ / max ρ ‖z - c‖) • (z - c)

/-- The radial retraction is continuous for positive radius. -/
theorem continuous_ballRetract (c : E) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (ballRetract c ρ) := by
  have hdenom : ∀ z : E, max ρ ‖z - c‖ ≠ 0 := by
    intro z
    exact ne_of_gt (lt_of_lt_of_le hρ (le_max_left _ _))
  unfold ballRetract
  exact continuous_const.add
    ((continuous_const.div (continuous_const.max
      ((continuous_id.sub continuous_const).norm)) hdenom).smul
      (continuous_id.sub continuous_const))

/-- Retraction is the identity on its closed ball. -/
@[simp] theorem ballRetract_eq_self (c : E) (ρ : ℝ) (hρ : 0 < ρ)
    {z : E} (hz : dist z c ≤ ρ) : ballRetract c ρ z = z := by
  have hn : ‖z - c‖ ≤ ρ := by simpa only [dist_eq_norm] using hz
  simp only [ballRetract, max_eq_left hn, div_self (ne_of_gt hρ), one_smul]
  abel

/-- Retraction lands in the closed ball. -/
theorem dist_ballRetract_le (c : E) (ρ : ℝ) (hρ : 0 < ρ) (z : E) :
    dist (ballRetract c ρ z) c ≤ ρ := by
  by_cases hz : ‖z - c‖ ≤ ρ
  · rw [ballRetract_eq_self c ρ hρ (by simpa only [dist_eq_norm] using hz)]
    simpa only [dist_eq_norm] using hz
  · have hn : ρ ≤ ‖z - c‖ := le_of_lt (lt_of_not_ge hz)
    have hn0 : ‖z - c‖ ≠ 0 := ne_of_gt (hρ.trans_le hn)
    have heq : c + (ρ / max ρ ‖z - c‖) • (z - c) - c =
        (ρ / max ρ ‖z - c‖) • (z - c) := by abel
    rw [ballRetract, dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      max_eq_right hn, abs_of_nonneg (div_nonneg hρ.le (norm_nonneg _)),
      div_mul_cancel₀ ρ hn0]

/-- Clip the coordinates and retract the state to obtain a globally continuous
extension of a nonlinearity given continuously on a rectangle times a ball. -/
@[expose] noncomputable def extendRectangleBall
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (c : E) (ρ : ℝ) {T : Type*} [TopologicalSpace T]
    (f : ℝ × ℝ → E → T) : ℝ × ℝ → E → T :=
  fun p z => f (clippedPoint hu hv p).1 (ballRetract c ρ z)

/-- The clipped extension is globally continuous when the original function
is continuous on the rectangle times the closed state ball. -/
theorem continuous_extendRectangleBall
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (c : E) (ρ : ℝ) (hρ : 0 < ρ)
    {T : Type*} [TopologicalSpace T] (f : ℝ × ℝ → E → T)
    (hf : ContinuousOn f.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ})) :
    Continuous (extendRectangleBall hu hv c ρ f).uncurry := by
  let r : (ℝ × ℝ) × E → (ℝ × ℝ) × E :=
    fun q => ((clippedPoint hu hv q.1).1, ballRetract c ρ q.2)
  have hr : Continuous r :=
    ((continuous_subtype_val.comp
      ((continuous_clippedPoint hu hv).comp continuous_fst)).prodMk
      ((continuous_ballRetract c ρ hρ).comp continuous_snd))
  have hmap : ∀ q, r q ∈ rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ} := by
    intro q
    exact ⟨(clippedPoint hu hv q.1).2, dist_ballRetract_le c ρ hρ q.2⟩
  have h : Continuous (f.uncurry ∘ r) :=
    continuousOn_univ.mp
      (hf.comp hr.continuousOn (fun q _ => hmap q))
  exact h

/-- The global extension agrees with the original nonlinearity on the
rectangle and closed state ball. -/
@[simp] theorem extendRectangleBall_eq
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (c : E) (ρ : ℝ) (hρ : 0 < ρ)
    {T : Type*} [TopologicalSpace T] (f : ℝ × ℝ → E → T)
    {p : ℝ × ℝ} (hp : p ∈ rectangle u₀ u₁ v₀ v₁)
    {z : E} (hz : dist z c ≤ ρ) :
    extendRectangleBall hu hv c ρ f p z = f p z := by
  simp only [extendRectangleBall, ballRetract_eq_self c ρ hρ hz]
  have hclip := clippedPoint_eq_self hu hv ⟨p, hp⟩
  exact congrArg (fun q : rectangle u₀ u₁ v₀ v₁ => f q.1 z) hclip

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Picard iterates for nonlinearities continuous only on a closed rectangle
times a state ball. Their globalized nonlinearities are obtained by clipping. -/
@[expose] noncomputable def picardIterateOnBall
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (n : ℕ) : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
  picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀
    (extendRectangleBall hu hv c ρ fX)
    (extendRectangleBall hu hv c ρ fY) hx₀ hy₀
    (continuous_extendRectangleBall hu hv c ρ hρ fX hfX)
    (continuous_extendRectangleBall hu hv c ρ hρ fY hfY) n

/-- The local Picard iterates stay in the prescribed state ball when the
full mixed characteristic trace has the usual margin. -/
theorem picardIterateOnBall_mem_ball
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
    dist (picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY n p) c ≤ ρ := by
  unfold picardIterateOnBall
  apply picardIterate_mem_ball u₀ u₁ v₀ v₁ hu hv x₀ y₀
    (extendRectangleBall hu hv c ρ fX)
    (extendRectangleBall hu hv c ρ fY) hx₀ hy₀
    (continuous_extendRectangleBall hu hv c ρ hρ fX hfX)
    (continuous_extendRectangleBall hu hv c ρ hρ fY hfY)
    c ρ r M hM hdata
  · intro q hq z hz
    rw [extendRectangleBall_eq hu hv c ρ hρ fX hq hz]
    exact hMX q hq z hz
  · intro q hq z hz
    rw [extendRectangleBall_eq hu hv c ρ hρ fY hq hz]
    exact hMY q hq z hz
  · exact hsize

/-- The local Picard successor uses the original nonlinearities along its
characteristic integration paths, since the preceding iterate stays in the
ball and the paths lie in the rectangle. -/
theorem picardIterateOnBall_succ_apply
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
    picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY (n + 1) p =
      (x₀ p.1.2 + ∫ s in u₀..p.1.1,
        fX (s, p.1.2) (picardIterateOnBall u₀ u₁ v₀ v₁ hu hv
          x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY n
            (clippedPoint hu hv (s, p.1.2))),
       y₀ p.1.1 + ∫ t in v₀..p.1.2,
        fY (p.1.1, t) (picardIterateOnBall u₀ u₁ v₀ v₁ hu hv
          x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY n
            (clippedPoint hu hv (p.1.1, t)))) := by
  have hbase := picardIterate_succ_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀
    (extendRectangleBall hu hv c ρ fX)
    (extendRectangleBall hu hv c ρ fY) hx₀ hy₀
    (continuous_extendRectangleBall hu hv c ρ hρ fX hfX)
    (continuous_extendRectangleBall hu hv c ρ hρ fY hfY) n p
  change picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY (n + 1) p = _
  rw [show picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY (n + 1) p = _ from hbase]
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu⟩ p.2.1 hs
    have hq : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI p.2.2
    simpa only [picardIterateOnBall] using
      (extendRectangleBall_eq hu hv c ρ hρ fX hq
        (picardIterateOnBall_mem_ball u₀ u₁ v₀ v₁ hu hv x₀ y₀
          hx₀ hy₀ c ρ hρ fX fY hfX hfY r M hM hdata hMX hMY hsize
          n (clippedPoint hu hv (s, p.1.2))))
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hv⟩ p.2.2 ht
    have hq : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle p.2.1 htI
    simpa only [picardIterateOnBall] using
      (extendRectangleBall_eq hu hv c ρ hρ fY hq
        (picardIterateOnBall_mem_ball u₀ u₁ v₀ v₁ hu hv x₀ y₀
          hx₀ hy₀ c ρ hρ fX fY hfX hfY r M hM hdata hMX hMY hsize
          n (clippedPoint hu hv (p.1.1, t))))

/-- The ball-preserving local Picard iterates converge uniformly to any
continuous, ball-valued solution of the characteristic integral equations. -/
theorem tendsto_picardIterateOnBall_of_integral_equations
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ : ℝ) (hρ : 0 < ρ)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (r M : ℝ) (hM : 0 ≤ M) (κ : NNReal)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z')
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z')
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t))) :
    Tendsto (picardIterateOnBall u₀ u₁ v₀ v₁ hu hv x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY) atTop
      (𝓝 (⟨fun p : rectangle u₀ u₁ v₀ v₁ => (X p.1, Y p.1),
        ((hX.prodMk hY).comp continuous_subtype_val)⟩ :
        C(rectangle u₀ u₁ v₀ v₁, E × F))) := by
  have hMX' : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖extendRectangleBall hu hv c ρ fX q z‖ ≤ M := by
    intro q hq z hz
    rw [extendRectangleBall_eq hu hv c ρ hρ fX hq hz]
    exact hMX q hq z hz
  have hMY' : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖extendRectangleBall hu hv c ρ fY q z‖ ≤ M := by
    intro q hq z hz
    rw [extendRectangleBall_eq hu hv c ρ hρ fY hq hz]
    exact hMY q hq z hz
  have hLX' : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (extendRectangleBall hu hv c ρ fX q z)
        (extendRectangleBall hu hv c ρ fX q z') ≤ (κ : ℝ) * dist z z' := by
    intro q hq z z' hz hz'
    rw [extendRectangleBall_eq hu hv c ρ hρ fX hq hz,
      extendRectangleBall_eq hu hv c ρ hρ fX hq hz']
    exact hLX q hq z z' hz hz'
  have hLY' : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (extendRectangleBall hu hv c ρ fY q z)
        (extendRectangleBall hu hv c ρ fY q z') ≤ (κ : ℝ) * dist z z' := by
    intro q hq z z' hz hz'
    rw [extendRectangleBall_eq hu hv c ρ hρ fY hq hz,
      extendRectangleBall_eq hu hv c ρ hρ fY hq hz']
    exact hLY q hq z z' hz hz'
  have heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        extendRectangleBall hu hv c ρ fX (s, p.2)
          (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        extendRectangleBall hu hv c ρ fY (p.1, t)
          (X (p.1, t), Y (p.1, t)) := by
    intro p hp
    simp only [rectangle, mem_prod] at hp
    constructor
    · rw [(heq p hp).1]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Icc u₀ u₁ :=
        Set.uIcc_subset_Icc ⟨le_rfl, hu⟩ hp.1 hs
      have hq : (s, p.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
        pair_mem_rectangle hsI hp.2
      exact (extendRectangleBall_eq hu hv c ρ hρ fX hq (hball _ hq)).symm
    · rw [(heq p hp).2]
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Icc v₀ v₁ :=
        Set.uIcc_subset_Icc ⟨le_rfl, hv⟩ hp.2 ht
      have hq : (p.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
        pair_mem_rectangle hp.1 htI
      exact (extendRectangleBall_eq hu hv c ρ hρ fY hq (hball _ hq)).symm
  have ht := tendsto_picardIterate_of_integral_equations_on_ball
    u₀ u₁ v₀ v₁ hu hv x₀ y₀
    (extendRectangleBall hu hv c ρ fX)
    (extendRectangleBall hu hv c ρ fY) hx₀ hy₀
    (continuous_extendRectangleBall hu hv c ρ hρ fX hfX)
    (continuous_extendRectangleBall hu hv c ρ hρ fY hfY)
    c ρ r M hM κ hdata hMX' hMY' hLX' hLY' hsize hsmall
    X Y hX hY hball heq'
  exact ht

/-- A pair of decoupled linear Volterra equations on a short Goursat
rectangle has continuous solutions, even when the coefficients are given
continuously only on the closed rectangle. -/
theorem exists_continuous_linear_solution_on_rectangle
    [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (p₀ : ℝ → E) (q₀ : ℝ → F)
    (hp₀ : Continuous p₀) (hq₀ : Continuous q₀)
    (A : ℝ × ℝ → E →L[ℝ] E) (B : ℝ × ℝ → F →L[ℝ] F)
    (H : ℝ × ℝ → E) (K : ℝ × ℝ → F)
    (hA : ContinuousOn A (rectangle u₀ u₁ v₀ v₁))
    (hB : ContinuousOn B (rectangle u₀ u₁ v₀ v₁))
    (hH : ContinuousOn H (rectangle u₀ u₁ v₀ v₁))
    (hK : ContinuousOn K (rectangle u₀ u₁ v₀ v₁))
    (κ : NNReal)
    (hκA : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ‖A p‖ ≤ (κ : ℝ))
    (hκB : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ‖B p‖ ≤ (κ : ℝ))
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ P : ℝ × ℝ → E, ∃ Q : ℝ × ℝ → F,
      Continuous P ∧ Continuous Q ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        P p = p₀ p.2 + ∫ s in u₀..p.1, A (s, p.2) (P (s, p.2)) + H (s, p.2) ∧
        Q p = q₀ p.1 + ∫ t in v₀..p.2, B (p.1, t) (Q (p.1, t)) + K (p.1, t) := by
  let Ac : ℝ × ℝ → E →L[ℝ] E := fun p => A (clippedPoint hu hv p).1
  let Bc : ℝ × ℝ → F →L[ℝ] F := fun p => B (clippedPoint hu hv p).1
  let Hc : ℝ × ℝ → E := fun p => H (clippedPoint hu hv p).1
  let Kc : ℝ × ℝ → F := fun p => K (clippedPoint hu hv p).1
  have hAc : Continuous Ac := hA.comp_continuous
    ((continuous_clippedPoint hu hv).subtype_val) (fun p => (clippedPoint hu hv p).2)
  have hBc : Continuous Bc := hB.comp_continuous
    ((continuous_clippedPoint hu hv).subtype_val) (fun p => (clippedPoint hu hv p).2)
  have hHc : Continuous Hc := hH.comp_continuous
    ((continuous_clippedPoint hu hv).subtype_val) (fun p => (clippedPoint hu hv p).2)
  have hKc : Continuous Kc := hK.comp_continuous
    ((continuous_clippedPoint hu hv).subtype_val) (fun p => (clippedPoint hu hv p).2)
  let fX : ℝ × ℝ → E × F → E := fun p z => Ac p z.1 + Hc p
  let fY : ℝ × ℝ → E × F → F := fun p z => Bc p z.2 + Kc p
  have hfX : Continuous fX.uncurry :=
    ((hAc.comp continuous_fst).clm_apply (continuous_snd.fst)).add
      (hHc.comp continuous_fst)
  have hfY : Continuous fY.uncurry :=
    ((hBc.comp continuous_fst).clm_apply (continuous_snd.snd)).add
      (hKc.comp continuous_fst)
  have hLX : ∀ p z z', dist (fX p z) (fX p z') ≤ (κ : ℝ) * dist z z' := by
    intro p z z'
    have hbound : ‖Ac p‖ ≤ (κ : ℝ) := hκA _ (clippedPoint hu hv p).2
    have hcoord : dist z.1 z'.1 ≤ dist z z' := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    calc
      dist (fX p z) (fX p z') = ‖Ac p (z.1 - z'.1)‖ := by
        simp only [fX, dist_eq_norm, map_sub]
        congr 1
        abel
      _ ≤ ‖Ac p‖ * ‖z.1 - z'.1‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (κ : ℝ) * dist z z' := by
        rw [← dist_eq_norm]
        exact (mul_le_mul_of_nonneg_right hbound dist_nonneg).trans
          (mul_le_mul_of_nonneg_left hcoord κ.coe_nonneg)
  have hLY : ∀ p z z', dist (fY p z) (fY p z') ≤ (κ : ℝ) * dist z z' := by
    intro p z z'
    have hbound : ‖Bc p‖ ≤ (κ : ℝ) := hκB _ (clippedPoint hu hv p).2
    have hcoord : dist z.2 z'.2 ≤ dist z z' := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    calc
      dist (fY p z) (fY p z') = ‖Bc p (z.2 - z'.2)‖ := by
        simp only [fY, dist_eq_norm, map_sub]
        congr 1
        abel
      _ ≤ ‖Bc p‖ * ‖z.2 - z'.2‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (κ : ℝ) * dist z z' := by
        rw [← dist_eq_norm]
        exact (mul_le_mul_of_nonneg_right hbound dist_nonneg).trans
          (mul_le_mul_of_nonneg_left hcoord κ.coe_nonneg)
  obtain ⟨P, Q, hP, hQ, heq⟩ := exists_continuous_solution_on_rectangle
    u₀ u₁ v₀ v₁ hu hv p₀ q₀ fX fY hp₀ hq₀ hfX hfY κ hLX hLY hsmall
  refine ⟨P, Q, hP, hQ, ?_⟩
  intro p hp
  obtain ⟨hPeq, hQeq⟩ := heq p hp
  constructor
  · rw [hPeq]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu⟩
        (by simpa only [rectangle, mem_prod] using hp.1) hs
    have hq : (s, p.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI (by simpa only [rectangle, mem_prod] using hp.2)
    have hclip := clippedPoint_eq_self hu hv ⟨(s, p.2), hq⟩
    simp only [fX, Ac, Hc]
    rw [show (clippedPoint hu hv (s, p.2)).1 = (s, p.2) from congrArg Subtype.val hclip]
  · rw [hQeq]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hv⟩
        (by simpa only [rectangle, mem_prod] using hp.2) ht
    have hq : (p.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle (by simpa only [rectangle, mem_prod] using hp.1) htI
    have hclip := clippedPoint_eq_self hu hv ⟨(p.1, t), hq⟩
    simp only [fY, Bc, Kc]
    rw [show (clippedPoint hu hv (p.1, t)).1 = (p.1, t) from congrArg Subtype.val hclip]

end Goursat

end
