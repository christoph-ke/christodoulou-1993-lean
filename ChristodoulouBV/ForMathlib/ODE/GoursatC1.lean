module

public import Mathlib.Analysis.Calculus.MeanValue
public import ChristodoulouBV.ForMathlib.ODE.GoursatLocal
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Differentiable nonlinearities in Goursat integral equations

The derivative bounds here concern the state variable. The datum margin is measured over the
whole mixed trace of the two characteristic edges, as required by the ball fixed point argument.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The largest distance from the ball center of the mixed characteristic base trace
`(x₀(v), y₀(u))` over a closed rectangle. -/
@[expose] noncomputable def mixedTraceRadius (u₀ u₁ v₀ v₁ : ℝ)
    (x₀ : ℝ → E) (y₀ : ℝ → F) (c : E × F) : ℝ :=
  sSup (Set.range (fun p : rectangle u₀ u₁ v₀ v₁ => dist (x₀ p.1.2, y₀ p.1.1) c))

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Every mixed edge datum is bounded by its full-trace radius. -/
theorem dist_mixedTrace_le_mixedTraceRadius
    (u₀ u₁ v₀ v₁ : ℝ) (x₀ : ℝ → E) (y₀ : ℝ → F) (c : E × F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (p : ℝ × ℝ) (hp : p ∈ rectangle u₀ u₁ v₀ v₁) :
    dist (x₀ p.2, y₀ p.1) c ≤ mixedTraceRadius u₀ u₁ v₀ v₁ x₀ y₀ c := by
  let f : rectangle u₀ u₁ v₀ v₁ → ℝ :=
    fun q => dist (x₀ q.1.2, y₀ q.1.1) c
  have hf : Continuous f := by
    fun_prop
  have hbdd : BddAbove (Set.range f) := (isCompact_range hf).bddAbove
  exact le_csSup hbdd ⟨⟨p, hp⟩, rfl⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- A state derivative bound on a convex ball gives a Lipschitz bound between any two states
in that ball. -/
theorem dist_nonlinearity_le_of_fderiv_le
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (f : E × F → T) (c : E × F) (ρ : ℝ) (κ : NNReal)
    (hdiff : ∀ z, dist z c ≤ ρ → DifferentiableAt ℝ f z)
    (hbound : ∀ z, dist z c ≤ ρ → ‖fderiv ℝ f z‖ ≤ (κ : ℝ))
    {z z' : E × F} (hz : dist z c ≤ ρ) (hz' : dist z' c ≤ ρ) :
    dist (f z) (f z') ≤ (κ : ℝ) * dist z z' := by
  let S : Set (E × F) := {w | dist w c ≤ ρ}
  have hconv : Convex ℝ S := convex_closedBall c ρ
  have h := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := (κ : ℝ)) (fun w hw => hdiff w hw)
    (fun w hw => hbound w hw) hz' hz
  simpa only [dist_eq_norm] using h

/-- A continuous Goursat solution in a state ball exists when the whole mixed edge trace
has a margin and the state derivatives are uniformly bounded. The two state spaces may be
arbitrary real Banach spaces. -/
theorem exists_continuous_solution_on_rectangle_of_fderiv_le
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ r M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (κ : NNReal)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hdiffX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      DifferentiableAt ℝ (fX q) z)
    (hdiffY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      DifferentiableAt ℝ (fY q) z)
    (hDX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      ‖fderiv ℝ (fX q) z‖ ≤ (κ : ℝ))
    (hDY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      ‖fderiv ℝ (fY q) z‖ ≤ (κ : ℝ))
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) < ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
      Continuous X ∧ Continuous Y ∧
      (∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ) ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)) := by
  apply exists_continuous_solution_on_rectangle_of_lipschitzOn_ball
    u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ c ρ r M hρ hM κ
    hfX hfY hdata hMX hMY
  · intro q hq z z' hz hz'
    exact dist_nonlinearity_le_of_fderiv_le (fX q) c ρ κ
      (hdiffX q hq) (hDX q hq) hz hz'
  · intro q hq z z' hz hz'
    exact dist_nonlinearity_le_of_fderiv_le (fY q) c ρ κ
      (hdiffY q hq) (hDY q hq) hz hz'
  · exact hsize.le
  · exact hsmall

/-- Existence with the margin expressed using the supremum of the full mixed edge trace. -/
theorem exists_continuous_solution_on_rectangle_of_mixedTraceRadius
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (κ : NNReal)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hdiffX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      DifferentiableAt ℝ (fX q) z)
    (hdiffY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      DifferentiableAt ℝ (fY q) z)
    (hDX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      ‖fderiv ℝ (fX q) z‖ ≤ (κ : ℝ))
    (hDY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      ‖fderiv ℝ (fY q) z‖ ≤ (κ : ℝ))
    (hsize : mixedTraceRadius u₀ u₁ v₀ v₁ x₀ y₀ c +
      M * max (u₁ - u₀) (v₁ - v₀) < ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
      Continuous X ∧ Continuous Y ∧
      (∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ) ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)) := by
  apply exists_continuous_solution_on_rectangle_of_fderiv_le
    u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ c ρ
    (mixedTraceRadius u₀ u₁ v₀ v₁ x₀ y₀ c) M hρ hM κ hfX hfY
  · intro p hp
    exact dist_mixedTrace_le_mixedTraceRadius u₀ u₁ v₀ v₁ x₀ y₀ c hx₀ hy₀ p hp
  · exact hMX
  · exact hMY
  · exact hdiffX
  · exact hdiffY
  · exact hDX
  · exact hDY
  · exact hsize
  · exact hsmall

omit [CompleteSpace E] [CompleteSpace F] in
/-- The integral equations sharpen the state-ball bound to the base-trace radius plus the
maximum characteristic excursion. In particular, a strict margin keeps the solution in the
open ball. -/
theorem dist_solution_le_base_add
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (c : E × F) (ρ r M : ℝ) (hM : 0 ≤ M)
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (p : ℝ × ℝ) (hp : p ∈ rectangle u₀ u₁ v₀ v₁) :
    dist (X p, Y p) c ≤ r + M * max (u₁ - u₀) (v₁ - v₀) := by
  have hIX : ‖∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2))‖ ≤
      M * (p.1 - u₀) := by
    have hb : ∀ s ∈ Set.uIoc u₀ p.1,
        ‖fX (s, p.2) (X (s, p.2), Y (s, p.2))‖ ≤ M := by
      intro s hs
      have hsI : s ∈ Icc u₀ u₁ :=
        Set.uIcc_subset_Icc ⟨le_refl u₀, hu⟩ hp.1 (Set.uIoc_subset_uIcc hs)
      have hq : (s, p.2) ∈ rectangle u₀ u₁ v₀ v₁ := ⟨hsI, hp.2⟩
      exact hMX _ hq _ (hball _ hq)
    simpa [abs_of_nonneg (sub_nonneg.mpr hp.1.1)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := u₀) (b := p.1) (C := M)
        (f := fun s => fX (s, p.2) (X (s, p.2), Y (s, p.2))) hb)
  have hIY : ‖∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t))‖ ≤
      M * (p.2 - v₀) := by
    have hb : ∀ t ∈ Set.uIoc v₀ p.2,
        ‖fY (p.1, t) (X (p.1, t), Y (p.1, t))‖ ≤ M := by
      intro t ht
      have htI : t ∈ Icc v₀ v₁ :=
        Set.uIcc_subset_Icc ⟨le_refl v₀, hv⟩ hp.2 (Set.uIoc_subset_uIcc ht)
      have hq : (p.1, t) ∈ rectangle u₀ u₁ v₀ v₁ := ⟨hp.1, htI⟩
      exact hMY _ hq _ (hball _ hq)
    simpa [abs_of_nonneg (sub_nonneg.mpr hp.2.1)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := v₀) (b := p.2) (C := M)
        (f := fun t => fY (p.1, t) (X (p.1, t), Y (p.1, t))) hb)
  have hXbase : dist (X p) (x₀ p.2) ≤ M * (p.1 - u₀) := by
    rw [(heq p hp).1, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hIX
  have hYbase : dist (Y p) (y₀ p.1) ≤ M * (p.2 - v₀) := by
    rw [(heq p hp).2, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hIY
  have hbase : dist (X p, Y p) (x₀ p.2, y₀ p.1) ≤
      M * max (u₁ - u₀) (v₁ - v₀) := by
    rw [Prod.dist_eq]
    apply max_le
    · calc
        dist (X p) (x₀ p.2) ≤ M * (p.1 - u₀) := hXbase
        _ ≤ M * max (u₁ - u₀) (v₁ - v₀) := by
          gcongr
          exact le_max_of_le_left (sub_le_sub_right hp.1.2 _)
    · calc
        dist (Y p) (y₀ p.1) ≤ M * (p.2 - v₀) := hYbase
        _ ≤ M * max (u₁ - u₀) (v₁ - v₀) := by
          gcongr
          exact le_max_of_le_right (sub_le_sub_right hp.2.2 _)
  exact (dist_triangle _ _ _).trans ((add_le_add hbase (hdata p hp)).trans_eq (add_comm _ _))

omit [CompleteSpace E] [CompleteSpace F] in
/-- Two globally continuous solutions in the same closed state ball agree when the two
nonlinearities have a common state Lipschitz bound and the rectangle is small enough. -/
theorem eq_on_rectangle_of_integral_equations_of_lipschitzOn_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (_hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : Continuous X) (hX' : Continuous X')
    (hY : Continuous Y) (hY' : Continuous Y')
    (c : E × F) (ρ : ℝ) (κ : NNReal)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (hball' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X' p, Y' p) c ≤ ρ)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z')
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z')
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p := by
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1), ((hX.prodMk hY).comp continuous_subtype_val)⟩
  let z : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X' p.1, Y' p.1), ((hX'.prodMk hY').comp continuous_subtype_val)⟩
  let D : ℝ := dist w z
  have hpoint (p : rectangle u₀ u₁ v₀ v₁) :
      dist (X p.1, Y p.1) (X' p.1, Y' p.1) ≤ D := by
    change dist (w p) (z p) ≤ D
    exact ContinuousMap.dist_apply_le_dist p
  have hcontX (U : ℝ × ℝ → E) (V : ℝ × ℝ → F)
      (hU : Continuous U) (hV : Continuous V)
      (hB : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (U p, V p) c ≤ ρ)
      (p : rectangle u₀ u₁ v₀ v₁) :
      ContinuousOn (fun s => fX (s, p.1.2) (U (s, p.1.2), V (s, p.1.2)))
        (Icc u₀ p.1.1) := by
    have hp : Continuous (fun s : ℝ => ((s, p.1.2), (U (s, p.1.2), V (s, p.1.2)))) := by
      fun_prop
    apply hfX.comp hp.continuousOn
    intro s hs
    have hsR : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      ⟨⟨hs.1, hs.2.trans p.2.1.2⟩, p.2.2⟩
    exact ⟨hsR, hB _ hsR⟩
  have hcontY (U : ℝ × ℝ → E) (V : ℝ × ℝ → F)
      (hU : Continuous U) (hV : Continuous V)
      (hB : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (U p, V p) c ≤ ρ)
      (p : rectangle u₀ u₁ v₀ v₁) :
      ContinuousOn (fun t => fY (p.1.1, t) (U (p.1.1, t), V (p.1.1, t)))
        (Icc v₀ p.1.2) := by
    have hp : Continuous (fun t : ℝ => ((p.1.1, t), (U (p.1.1, t), V (p.1.1, t)))) := by
      fun_prop
    apply hfY.comp hp.continuousOn
    intro t ht
    have htR : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      ⟨p.2.1, ⟨ht.1, ht.2.trans p.2.2.2⟩⟩
    exact ⟨htR, hB _ htR⟩
  have hdistX (p : rectangle u₀ u₁ v₀ v₁) :
      dist (X p.1) (X' p.1) ≤ (κ : ℝ) * D * (p.1.1 - u₀) := by
    rw [(heq p.1 p.2).1, (heq' p.1 p.2).1, dist_eq_norm, add_sub_add_left_eq_sub]
    apply norm_integral_sub_le_of_norm_sub_le p.2.1.1 _ _
      ((hcontX X Y hX hY hball p).intervalIntegrable_of_Icc p.2.1.1)
      ((hcontX X' Y' hX' hY' hball' p).intervalIntegrable_of_Icc p.2.1.1)
    intro s hs
    rw [← dist_eq_norm]
    have hsR : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      ⟨⟨hs.1, hs.2.trans p.2.1.2⟩, p.2.2⟩
    calc
      dist (fX (s, p.1.2) (X (s, p.1.2), Y (s, p.1.2)))
          (fX (s, p.1.2) (X' (s, p.1.2), Y' (s, p.1.2))) ≤
          (κ : ℝ) * dist (X (s, p.1.2), Y (s, p.1.2))
            (X' (s, p.1.2), Y' (s, p.1.2)) :=
        hLX _ hsR _ _ (hball _ hsR) (hball' _ hsR)
      _ ≤ (κ : ℝ) * D :=
        mul_le_mul_of_nonneg_left (hpoint ⟨_, hsR⟩) κ.coe_nonneg
  have hdistY (p : rectangle u₀ u₁ v₀ v₁) :
      dist (Y p.1) (Y' p.1) ≤ (κ : ℝ) * D * (p.1.2 - v₀) := by
    rw [(heq p.1 p.2).2, (heq' p.1 p.2).2, dist_eq_norm, add_sub_add_left_eq_sub]
    apply norm_integral_sub_le_of_norm_sub_le p.2.2.1 _ _
      ((hcontY X Y hX hY hball p).intervalIntegrable_of_Icc p.2.2.1)
      ((hcontY X' Y' hX' hY' hball' p).intervalIntegrable_of_Icc p.2.2.1)
    intro t ht
    rw [← dist_eq_norm]
    have htR : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      ⟨p.2.1, ⟨ht.1, ht.2.trans p.2.2.2⟩⟩
    calc
      dist (fY (p.1.1, t) (X (p.1.1, t), Y (p.1.1, t)))
          (fY (p.1.1, t) (X' (p.1.1, t), Y' (p.1.1, t))) ≤
          (κ : ℝ) * dist (X (p.1.1, t), Y (p.1.1, t))
            (X' (p.1.1, t), Y' (p.1.1, t)) :=
        hLY _ htR _ _ (hball _ htR) (hball' _ htR)
      _ ≤ (κ : ℝ) * D :=
        mul_le_mul_of_nonneg_left (hpoint ⟨_, htR⟩) κ.coe_nonneg
  have hD : D ≤ ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * D := by
    apply (ContinuousMap.dist_le (mul_nonneg
      (mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu)))
      dist_nonneg)).2
    intro p
    change dist (X p.1, Y p.1) (X' p.1, Y' p.1) ≤ _
    rw [Prod.dist_eq]
    apply max_le
    · calc
        dist (X p.1) (X' p.1) ≤ (κ : ℝ) * D * (p.1.1 - u₀) := hdistX p
        _ ≤ (κ : ℝ) * D * max (u₁ - u₀) (v₁ - v₀) := by
          gcongr
          exact le_max_of_le_left (sub_le_sub_right p.2.1.2 _)
        _ = ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * D := by ring
    · calc
        dist (Y p.1) (Y' p.1) ≤ (κ : ℝ) * D * (p.1.2 - v₀) := hdistY p
        _ ≤ (κ : ℝ) * D * max (u₁ - u₀) (v₁ - v₀) := by
          gcongr
          exact le_max_of_le_right (sub_le_sub_right p.2.2.2 _)
        _ = ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * D := by ring
  have hDzero : D = 0 := by
    have hn : 0 ≤ D := dist_nonneg
    nlinarith
  have hwz : w = z := dist_eq_zero.mp hDzero
  intro p hp
  exact Prod.mk.inj (congrArg (fun f : C(rectangle u₀ u₁ v₀ v₁, E × F) => f ⟨p, hp⟩) hwz)

omit [CompleteSpace E] [CompleteSpace F] in
/-- State derivative bounds give uniqueness among continuous integral solutions whose values
remain in the same closed ball. -/
theorem eq_on_rectangle_of_integral_equations_of_fderiv_le
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : Continuous X) (hX' : Continuous X')
    (hY : Continuous Y) (hY' : Continuous Y')
    (c : E × F) (ρ : ℝ) (κ : NNReal)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (hball' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X' p, Y' p) c ≤ ρ)
    (hdiffX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      DifferentiableAt ℝ (fX q) z)
    (hdiffY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      DifferentiableAt ℝ (fY q) z)
    (hDX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      ‖fderiv ℝ (fX q) z‖ ≤ (κ : ℝ))
    (hDY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z, dist z c ≤ ρ →
      ‖fderiv ℝ (fY q) z‖ ≤ (κ : ℝ))
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p := by
  apply eq_on_rectangle_of_integral_equations_of_lipschitzOn_ball
    u₀ u₁ v₀ v₁ hu hv X X' Y Y' x₀ y₀ fX fY hX hX' hY hY'
    c ρ κ hfX hfY hball hball'
  · intro q hq z z' hz hz'
    exact dist_nonlinearity_le_of_fderiv_le (fX q) c ρ κ
      (hdiffX q hq) (hDX q hq) hz hz'
  · intro q hq z z' hz hz'
    exact dist_nonlinearity_le_of_fderiv_le (fY q) c ρ κ
      (hdiffY q hq) (hDY q hq) hz hz'
  · exact hsmall
  · exact heq
  · exact heq'

omit [CompleteSpace E] in
/-- A small interval gives a uniform bound for a continuous vector-valued Volterra equation.
Applied to the transverse Goursat jets, the source bound is `H + κ M`. -/
theorem norm_le_of_volterra_of_small
    (a b : ℝ) (hab : a ≤ b) (z h : ℝ → E)
    (A : ℝ → E →L[ℝ] E) (d : E) (P B κ : ℝ)
    (hz : ContinuousOn z (Icc a b))
    (hP : ‖d‖ ≤ P) (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hA : ∀ s ∈ Icc a b, ‖A s‖ ≤ κ)
    (hh : ∀ s ∈ Icc a b, ‖h s‖ ≤ B)
    (heq : ∀ t ∈ Icc a b,
      z t = d + ∫ s in a..t, A s (z s) + h s)
    (hsmall : κ * (b - a) < 1)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖z t‖ ≤ (P + B * (b - a)) / (1 - κ * (b - a)) := by
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) hz.norm
  have hzr : 0 ≤ ‖z r‖ := norm_nonneg _
  have hsource (s : ℝ) (hs : s ∈ Icc a r) :
      ‖A s (z s) + h s‖ ≤ κ * ‖z r‖ + B := by
    have hsI : s ∈ Icc a b := ⟨hs.1, hs.2.trans hr.2⟩
    calc
      ‖A s (z s) + h s‖ ≤ ‖A s (z s)‖ + ‖h s‖ := norm_add_le _ _
      _ ≤ ‖A s‖ * ‖z s‖ + B :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (hh s hsI)
      _ ≤ κ * ‖z r‖ + B := by
        gcongr
        · exact hA s hsI
        · exact hmax hsI
  have hint : ‖∫ s in a..r, A s (z s) + h s‖ ≤
      (κ * ‖z r‖ + B) * (r - a) := by
    have hbound : ∀ s ∈ Set.uIoc a r, ‖A s (z s) + h s‖ ≤ κ * ‖z r‖ + B := by
      intro s hs
      exact hsource s (by simpa only [Set.uIcc_of_le hr.1] using Set.uIoc_subset_uIcc hs)
    simpa [abs_of_nonneg (sub_nonneg.mpr hr.1)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := r) (C := κ * ‖z r‖ + B)
        (f := fun s => A s (z s) + h s) hbound)
  have hmain : ‖z r‖ ≤ P + (κ * ‖z r‖ + B) * (b - a) := by
    calc
      ‖z r‖ = ‖d + ∫ s in a..r, A s (z s) + h s‖ := by rw [heq r hr]
      _ ≤ ‖d‖ + ‖∫ s in a..r, A s (z s) + h s‖ := norm_add_le _ _
      _ ≤ P + (κ * ‖z r‖ + B) * (r - a) := add_le_add hP hint
      _ ≤ P + (κ * ‖z r‖ + B) * (b - a) := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hr.2 a)
            (add_nonneg (mul_nonneg hκ hzr) hB)) P
  have hden : 0 < 1 - κ * (b - a) := by linarith
  have hR : ‖z r‖ ≤ (P + B * (b - a)) / (1 - κ * (b - a)) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  exact (hmax ht).trans hR

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The first characteristic derivative exists at interior points even when the nonlinearity
is continuous only on the rectangle and the visited part of the state ball. -/
theorem hasDerivAt_first_of_integral_equation_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (_hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (x₀ : ℝ → E)
    (fX : ℝ × ℝ → E × F → E) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)))
    {u v : ℝ} (huI : u ∈ Ioo u₀ u₁) (hvI : v ∈ Icc v₀ v₁) :
    HasDerivAt (fun s => X (s, v)) (fX (u, v) (X (u, v), Y (u, v))) u := by
  let g : ℝ → E := fun s =>
    fX (clip u₀ u₁ s, v) (X (clip u₀ u₁ s, v), Y (clip u₀ u₁ s, v))
  have hmap : Continuous (fun s : ℝ =>
      ((clip u₀ u₁ s, v), (X (clip u₀ u₁ s, v), Y (clip u₀ u₁ s, v)))) := by
    have hcoord : Continuous (fun s : ℝ => (clip u₀ u₁ s, v)) :=
      (continuous_clip u₀ u₁).prodMk continuous_const
    exact hcoord.prodMk ((hX.comp hcoord).prodMk (hY.comp hcoord))
  have hg : Continuous g := by
    apply hfX.comp_continuous hmap
    intro s
    have hsR : (clip u₀ u₁ s, v) ∈ rectangle u₀ u₁ v₀ v₁ :=
      ⟨clip_mem_Icc hu s, hvI⟩
    exact ⟨hsR, hball _ hsR⟩
  have hline : ∀ t ∈ Icc u₀ u₁, X (t, v) = x₀ v + ∫ s in u₀..t, g s := by
    intro t ht
    rw [heq (t, v) ⟨ht, hvI⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_refl u₀, hu⟩ ht hs
    simp only [g, clip_eq_self hsI]
  have h := hasDerivAt_of_eq_integral_on_Icc huI
    (fun t => X (t, v)) g (x₀ v) hg hline
  simpa only [g, clip_eq_self (Set.mem_Icc_of_Ioo huI)] using h

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The second characteristic derivative exists at interior points under local continuity
on the rectangle and the visited part of the state ball. -/
theorem hasDerivAt_second_of_integral_equation_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (_hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (y₀ : ℝ → F)
    (fY : ℝ × ℝ → E × F → F) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    {u v : ℝ} (huI : u ∈ Icc u₀ u₁) (hvI : v ∈ Ioo v₀ v₁) :
    HasDerivAt (fun t => Y (u, t)) (fY (u, v) (X (u, v), Y (u, v))) v := by
  let g : ℝ → F := fun t =>
    fY (u, clip v₀ v₁ t) (X (u, clip v₀ v₁ t), Y (u, clip v₀ v₁ t))
  have hmap : Continuous (fun t : ℝ =>
      ((u, clip v₀ v₁ t), (X (u, clip v₀ v₁ t), Y (u, clip v₀ v₁ t)))) := by
    have hcoord : Continuous (fun t : ℝ => (u, clip v₀ v₁ t)) :=
      continuous_const.prodMk (continuous_clip v₀ v₁)
    exact hcoord.prodMk ((hX.comp hcoord).prodMk (hY.comp hcoord))
  have hg : Continuous g := by
    apply hfY.comp_continuous hmap
    intro t
    have htR : (u, clip v₀ v₁ t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      ⟨huI, clip_mem_Icc hv t⟩
    exact ⟨htR, hball _ htR⟩
  have hline : ∀ t ∈ Icc v₀ v₁, Y (u, t) = y₀ u + ∫ s in v₀..t, g s := by
    intro t ht
    rw [heq (u, t) ⟨huI, ht⟩]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_refl v₀, hv⟩ ht hs
    simp only [g, clip_eq_self hsI]
  have h := hasDerivAt_of_eq_integral_on_Icc hvI
    (fun t => Y (u, t)) g (y₀ u) hg hline
  simpa only [g, clip_eq_self (Set.mem_Icc_of_Ioo hvI)] using h

end Goursat

end
