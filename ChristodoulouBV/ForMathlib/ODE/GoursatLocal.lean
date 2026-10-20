module

public import Mathlib
public import ChristodoulouBV.ForMathlib.ODE.GoursatGlobal
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Goursat equations with a Lipschitz bound on a ball

The Picard map preserves a closed ball of continuous functions when the edge data
and the characteristic integrals have enough room inside the ball. The resulting
contraction only uses the Lipschitz bound inside that ball.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def radialClip {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : G) (ρ : ℝ) (z : G) : G :=
  c + (ρ / max ρ ‖z - c‖) • (z - c)

private theorem continuous_radialClip {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : G) (ρ : ℝ) (hρ : 0 < ρ) : Continuous (radialClip c ρ) := by
  have hden : ∀ z : G, max ρ ‖z - c‖ ≠ 0 := by
    intro z
    exact ne_of_gt (hρ.trans_le (le_max_left _ _))
  have hscalar : Continuous (fun z : G => ρ / max ρ ‖z - c‖) :=
    continuous_const.div
      (continuous_const.max ((continuous_id.sub continuous_const).norm)) hden
  exact continuous_const.add (hscalar.smul (continuous_id.sub continuous_const))

private theorem radialClip_mem {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : G) (ρ : ℝ) (hρ : 0 < ρ) (z : G) :
    dist (radialClip c ρ z) c ≤ ρ := by
  have hd : 0 < max ρ ‖z - c‖ := hρ.trans_le (le_max_left _ _)
  have hn : ‖z - c‖ ≤ max ρ ‖z - c‖ := le_max_right _ _
  rw [dist_eq_norm, radialClip]
  have hsub : c + (ρ / max ρ ‖z - c‖) • (z - c) - c =
      (ρ / max ρ ‖z - c‖) • (z - c) := by abel
  rw [hsub]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ hd)]
  calc
    (ρ / max ρ ‖z - c‖) * ‖z - c‖ =
        (ρ * ‖z - c‖) / max ρ ‖z - c‖ := by ring
    _ ≤ ρ := (div_le_iff₀ hd).2 (mul_le_mul_of_nonneg_left hn hρ.le)

private theorem radialClip_eq_self {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : G) (ρ : ℝ) (hρ : 0 < ρ) (z : G)
    (hz : dist z c ≤ ρ) : radialClip c ρ z = z := by
  have hn : ‖z - c‖ ≤ ρ := by simpa only [dist_eq_norm] using hz
  simp only [radialClip, max_eq_left hn, div_self hρ.ne', one_smul]
  abel

private theorem continuous_uncurry_clipped_ball_nonlinearity {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (c : G) (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ × ℝ → G → H)
    (hf : ContinuousOn f.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {a | dist a c ≤ ρ})) :
    Continuous (Function.uncurry (fun q a =>
      f (clippedPoint hu hv q).1 (radialClip c ρ a))) := by
  have hm : Continuous (fun z : (ℝ × ℝ) × G =>
      ((clippedPoint hu hv z.1).1, radialClip c ρ z.2)) :=
    (((continuous_clippedPoint hu hv).subtype_val.comp continuous_fst).prodMk
      ((continuous_radialClip c ρ hρ).comp continuous_snd))
  exact hf.comp_continuous hm (fun z =>
    ⟨(clippedPoint hu hv z.1).2, radialClip_mem c ρ hρ z.2⟩)

private theorem norm_integral_le_of_norm_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b M : ℝ} (hab : a ≤ b) (f : ℝ → G)
    (hf : ∀ s ∈ Icc a b, ‖f s‖ ≤ M) :
    ‖∫ s in a..b, f s‖ ≤ M * (b - a) := by
  have h : ∀ s ∈ Set.uIoc a b, ‖f s‖ ≤ M := by
    intro s hs
    exact hf s (by simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs)
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := M) (f := f) h)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem isClosed_bounded_maps (u₀ u₁ v₀ v₁ : ℝ)
    (c : E × F) (ρ : ℝ) :
    IsClosed {w : C(rectangle u₀ u₁ v₀ v₁, E × F) | ∀ p, dist (w p) c ≤ ρ} := by
  have h : IsClosed (⋂ p : rectangle u₀ u₁ v₀ v₁,
      {w : C(rectangle u₀ u₁ v₀ v₁, E × F) | dist (w p) c ≤ ρ}) :=
    isClosed_iInter fun p => isClosed_le
      ((continuous_eval_const p).dist continuous_const) continuous_const
  convert h using 1
  ext w
  simp only [mem_ofPred_eq, mem_iInter]

private theorem picard_mem_bounded_maps
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ r M : ℝ) (hM : 0 ≤ M)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fX q a‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fY q a‖ ≤ M)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : ∀ p, dist (w p) c ≤ ρ) :
    ∀ p, dist (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w p) c ≤ ρ := by
  intro p
  have hX : ‖∫ s in u₀..p.1.1,
      fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))‖ ≤
      M * (p.1.1 - u₀) := by
    apply norm_integral_le_of_norm_le p.2.1.1
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ := ⟨hs.1, hs.2.trans p.2.1.2⟩
    exact hMX (s, p.1.2) ⟨hsI, p.2.2⟩ _ (hw _)
  have hY : ‖∫ t in v₀..p.1.2,
      fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))‖ ≤
      M * (p.1.2 - v₀) := by
    apply norm_integral_le_of_norm_le p.2.2.1
    intro t ht
    have htI : t ∈ Icc v₀ v₁ := ⟨ht.1, ht.2.trans p.2.2.2⟩
    exact hMY (p.1.1, t) ⟨p.2.1, htI⟩ _ (hw _)
  have hInt : dist
      (∫ s in u₀..p.1.1, fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
       ∫ t in v₀..p.1.2, fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t))))
      (0, 0) ≤ M * max (u₁ - u₀) (v₁ - v₀) := by
    rw [Prod.dist_eq]
    apply max_le
    · simpa only [dist_zero_right] using hX.trans
        (mul_le_mul_of_nonneg_left (le_max_of_le_left
          (sub_le_sub_right p.2.1.2 _)) hM)
    · simpa only [dist_zero_right] using hY.trans
        (mul_le_mul_of_nonneg_left (le_max_of_le_right
          (sub_le_sub_right p.2.2.2 _)) hM)
  rw [picard_apply]
  have hpair :
      (x₀ p.1.2 + ∫ s in u₀..p.1.1,
          fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
       y₀ p.1.1 + ∫ t in v₀..p.1.2,
          fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) =
      (x₀ p.1.2, y₀ p.1.1) +
      (∫ s in u₀..p.1.1, fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
       ∫ t in v₀..p.1.2, fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) := rfl
  rw [hpair]
  calc
    dist _ c ≤ dist _ (x₀ p.1.2, y₀ p.1.1) +
        dist (x₀ p.1.2, y₀ p.1.1) c := dist_triangle _ _ _
    _ = dist
        (∫ s in u₀..p.1.1, fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
         ∫ t in v₀..p.1.2, fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t))))
        (0, 0) + dist (x₀ p.1.2, y₀ p.1.1) c := by
      simp [dist_eq_norm, add_sub_cancel_left]
    _ ≤ M * max (u₁ - u₀) (v₁ - v₀) + r := add_le_add hInt (hdata p.1 p.2)
    _ = r + M * max (u₁ - u₀) (v₁ - v₀) := add_comm _ _
    _ ≤ ρ := hsize

private theorem dist_picard_le_of_bounded
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ : ℝ) (κ : NNReal)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : ∀ p, dist (w p) c ≤ ρ) (hz : ∀ p, dist (z p) c ≤ ρ) :
    dist (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY z) ≤
      ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * dist w z := by
  apply (ContinuousMap.dist_le (mul_nonneg
    (mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu))) dist_nonneg)).2
  intro p
  rw [Prod.dist_eq]
  apply max_le
  · have hfw : Continuous (fun s : ℝ =>
        fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))) :=
      continuous_comp_clippedPoint hu hv fX hfX w
        (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
    have hfz : Continuous (fun s : ℝ =>
        fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2)))) :=
      continuous_comp_clippedPoint hu hv fX hfX z
        (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
    have hbound : ∀ s ∈ Icc u₀ p.1.1,
        ‖fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))) -
          fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2)))‖ ≤
          (κ : ℝ) * dist w z := by
      intro s hs
      rw [← dist_eq_norm]
      have hsI : s ∈ Icc u₀ u₁ := ⟨hs.1, hs.2.trans p.2.1.2⟩
      exact (hLX (s, p.1.2) ⟨hsI, p.2.2⟩ _ _ (hw _) (hz _)).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousMap.dist_apply_le_dist (clippedPoint hu hv (s, p.1.2)))
          κ.coe_nonneg)
    have h := norm_integral_sub_le_of_norm_sub_le p.2.1.1 _ _
      (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _) hbound
    simp only [picard_apply, dist_eq_norm, add_sub_add_left_eq_sub] at ⊢
    simp only [dist_eq_norm] at h
    calc
      _ ≤ ((κ : ℝ) * ‖w - z‖) * (p.1.1 - u₀) := h
      _ ≤ ((κ : ℝ) * ‖w - z‖) * max (u₁ - u₀) (v₁ - v₀) := by
        gcongr
        exact le_max_of_le_left (sub_le_sub_right p.2.1.2 _)
      _ = ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * ‖w - z‖ := by ring
  · have hfw : Continuous (fun t : ℝ =>
        fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) :=
      continuous_comp_clippedPoint hu hv fY hfY w
        (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
    have hfz : Continuous (fun t : ℝ =>
        fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t)))) :=
      continuous_comp_clippedPoint hu hv fY hfY z
        (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
    have hbound : ∀ t ∈ Icc v₀ p.1.2,
        ‖fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t))) -
          fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t)))‖ ≤
          (κ : ℝ) * dist w z := by
      intro t ht
      rw [← dist_eq_norm]
      have htI : t ∈ Icc v₀ v₁ := ⟨ht.1, ht.2.trans p.2.2.2⟩
      exact (hLY (p.1.1, t) ⟨p.2.1, htI⟩ _ _ (hw _) (hz _)).trans
        (mul_le_mul_of_nonneg_left
          (ContinuousMap.dist_apply_le_dist (clippedPoint hu hv (p.1.1, t)))
          κ.coe_nonneg)
    have h := norm_integral_sub_le_of_norm_sub_le p.2.2.1 _ _
      (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _) hbound
    simp only [picard_apply, dist_eq_norm, add_sub_add_left_eq_sub] at ⊢
    simp only [dist_eq_norm] at h
    calc
      _ ≤ ((κ : ℝ) * ‖w - z‖) * (p.1.2 - v₀) := h
      _ ≤ ((κ : ℝ) * ‖w - z‖) * max (u₁ - u₀) (v₁ - v₀) := by
        gcongr
        exact le_max_of_le_right (sub_le_sub_right p.2.2.2 _)
      _ = ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * ‖w - z‖ := by ring

/-- A Goursat solution exists when the edge values and the integrals remain in
a closed ball on which the nonlinearities are Lipschitz. The size condition is
`r + M * max (u₁-u₀) (v₁-v₀) ≤ ρ`. -/
private theorem exists_continuous_solution_of_lipschitzOn_ball
    [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ r M : ℝ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (κ : NNReal)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fX q a‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fY q a‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ w : C(rectangle u₀ u₁ v₀ v₁, E × F),
      (∀ p, dist (w p) c ≤ ρ) ∧
      ∀ p, w p =
        (x₀ p.1.2 + ∫ s in u₀..p.1.1,
            fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
         y₀ p.1.1 + ∫ t in v₀..p.1.2,
            fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) := by
  let S : Set (C(rectangle u₀ u₁ v₀ v₁, E × F)) :=
    {w | ∀ p, dist (w p) c ≤ ρ}
  have hS : IsClosed S := isClosed_bounded_maps u₀ u₁ v₀ v₁ c ρ
  let : CompleteSpace S := hS.completeSpace_coe
  let T : S → S := fun w =>
    ⟨picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w.1,
      picard_mem_bounded_maps u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
        c ρ r M hM hdata hMX hMY hsize w.1 w.2⟩
  have hT : ContractingWith
      (⟨(κ : ℝ) * max (u₁ - u₀) (v₁ - v₀),
        mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu))⟩ : NNReal) T := by
    constructor
    · exact hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro w z
      exact dist_picard_le_of_bounded u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
        hx₀ hy₀ hfX hfY c ρ κ hLX hLY w.1 z.1 w.2 z.2
  let w₀ : S := ⟨ContinuousMap.const _ c, by
    intro p
    simpa using hρ⟩
  obtain ⟨w, hw, _, _⟩ := hT.exists_fixedPoint w₀ (by simp)
  refine ⟨w.1, w.2, fun p => ?_⟩
  have h := congrArg (fun z : S => z.1 p) hw.symm
  exact h.trans (picard_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w.1 p)

/-- Local Goursat existence with continuity and Lipschitz bounds required only
on the rectangle times a closed ball. -/
private theorem exists_continuous_solution_of_continuousOn_lipschitzOn_ball
    [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ r M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (κ : NNReal)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {a | dist a c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {a | dist a c ≤ ρ}))
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fX q a‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fY q a‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ w : C(rectangle u₀ u₁ v₀ v₁, E × F),
      (∀ p, dist (w p) c ≤ ρ) ∧
      ∀ p, w p =
        (x₀ p.1.2 + ∫ s in u₀..p.1.1,
            fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
         y₀ p.1.1 + ∫ t in v₀..p.1.2,
            fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) := by
  let fXc : ℝ × ℝ → E × F → E := fun q a =>
    fX (clippedPoint hu hv q).1 (radialClip c ρ a)
  let fYc : ℝ × ℝ → E × F → F := fun q a =>
    fY (clippedPoint hu hv q).1 (radialClip c ρ a)
  have hfXc : Continuous fXc.uncurry :=
    continuous_uncurry_clipped_ball_nonlinearity hu hv c ρ hρ fX hfX
  have hfYc : Continuous fYc.uncurry :=
    continuous_uncurry_clipped_ball_nonlinearity hu hv c ρ hρ fY hfY
  have hXeq (q : ℝ × ℝ) (hq : q ∈ rectangle u₀ u₁ v₀ v₁)
      (a : E × F) (ha : dist a c ≤ ρ) : fXc q a = fX q a := by
    have hc : (clippedPoint hu hv q).1 = q :=
      congrArg Subtype.val (clippedPoint_eq_self hu hv ⟨q, hq⟩)
    simp only [fXc, hc, radialClip_eq_self c ρ hρ a ha]
  have hYeq (q : ℝ × ℝ) (hq : q ∈ rectangle u₀ u₁ v₀ v₁)
      (a : E × F) (ha : dist a c ≤ ρ) : fYc q a = fY q a := by
    have hc : (clippedPoint hu hv q).1 = q :=
      congrArg Subtype.val (clippedPoint_eq_self hu hv ⟨q, hq⟩)
    simp only [fYc, hc, radialClip_eq_self c ρ hρ a ha]
  have hMXc : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a,
      dist a c ≤ ρ → ‖fXc q a‖ ≤ M := by
    intro q hq a ha
    rw [hXeq q hq a ha]
    exact hMX q hq a ha
  have hMYc : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a,
      dist a c ≤ ρ → ‖fYc q a‖ ≤ M := by
    intro q hq a ha
    rw [hYeq q hq a ha]
    exact hMY q hq a ha
  have hLXc : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fXc q a) (fXc q b) ≤ (κ : ℝ) * dist a b := by
    intro q hq a b ha hb
    rw [hXeq q hq a ha, hXeq q hq b hb]
    exact hLX q hq a b ha hb
  have hLYc : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fYc q a) (fYc q b) ≤ (κ : ℝ) * dist a b := by
    intro q hq a b ha hb
    rw [hYeq q hq a ha, hYeq q hq b hb]
    exact hLY q hq a b ha hb
  obtain ⟨w, hw, heq⟩ := exists_continuous_solution_of_lipschitzOn_ball
    u₀ u₁ v₀ v₁ hu hv x₀ y₀ fXc fYc hx₀ hy₀ hfXc hfYc
    c ρ r M hρ.le hM κ hdata hMXc hMYc hLXc hLYc hsize hsmall
  refine ⟨w, hw, fun p => ?_⟩
  rw [heq p]
  apply Prod.ext
  · dsimp
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_refl u₀, hu⟩ p.2.1 hs
    exact hXeq (s, p.1.2) ⟨hsI, p.2.2⟩ _ (hw _)
  · dsimp
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_refl v₀, hv⟩ p.2.2 ht
    exact hYeq (p.1.1, t) ⟨p.2.1, htI⟩ _ (hw _)

/-- A solution with ordinary two-component integral equations exists on a
rectangle satisfying the explicit ball and contraction size bounds. -/
theorem exists_continuous_solution_on_rectangle_of_lipschitzOn_ball
    [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (c : E × F) (ρ r M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (κ : NNReal)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {a | dist a c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {a | dist a c ≤ ρ}))
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fX q a‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a, dist a c ≤ ρ → ‖fY q a‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist a c ≤ ρ → dist b c ≤ ρ →
      dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
      Continuous X ∧ Continuous Y ∧
      (∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ) ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)) := by
  obtain ⟨w, hw, heq⟩ := exists_continuous_solution_of_continuousOn_lipschitzOn_ball
    u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ c ρ r M hρ hM κ
    hfX hfY hdata hMX hMY hLX hLY hsize hsmall
  let X : ℝ × ℝ → E := fun p => (w (clippedPoint hu hv p)).1
  let Y : ℝ × ℝ → F := fun p => (w (clippedPoint hu hv p)).2
  refine ⟨X, Y, (w.continuous.comp (continuous_clippedPoint hu hv)).fst,
    (w.continuous.comp (continuous_clippedPoint hu hv)).snd, ?_, ?_⟩
  · intro p hp
    have hclip : clippedPoint hu hv p = (⟨p, hp⟩ : rectangle u₀ u₁ v₀ v₁) :=
      clippedPoint_eq_self hu hv ⟨p, hp⟩
    simpa only [X, Y, hclip] using hw ⟨p, hp⟩
  · intro p hp
    let q : rectangle u₀ u₁ v₀ v₁ := ⟨p, hp⟩
    have hclip : clippedPoint hu hv p = q := clippedPoint_eq_self hu hv q
    have h := heq q
    dsimp [X, Y] at ⊢
    rw [hclip]
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem fixedPoint_unique_of_solution_lipschitz
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hLX : ∀ q : rectangle u₀ u₁ v₀ v₁,
      dist (fX q.1 (w q)) (fX q.1 (z q)) ≤ (κ : ℝ) * dist (w q) (z q))
    (hLY : ∀ q : rectangle u₀ u₁ v₀ v₁,
      dist (fY q.1 (w q)) (fY q.1 (z q)) ≤ (κ : ℝ) * dist (w q) (z q))
    (hw : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w)
    (hz : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) z) :
    w = z := by
  let K : ℝ := (κ : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hκK : (κ : ℝ) < K := by dsimp [K]; linarith
  let d : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => Real.exp (-(K * (p.1.1 + p.1.2))) • (w p - z p),
      (by fun_prop : Continuous (fun p : rectangle u₀ u₁ v₀ v₁ =>
        Real.exp (-(K * (p.1.1 + p.1.2))) • (w p - z p)))⟩
  have hpoint (p : rectangle u₀ u₁ v₀ v₁) :
      dist (w p) (z p) ≤ Real.exp (K * (p.1.1 + p.1.2)) * ‖d‖ := by
    have hdecomp : w p - z p =
        Real.exp (K * (p.1.1 + p.1.2)) • d p := by
      change w p - z p = Real.exp (K * (p.1.1 + p.1.2)) •
        (Real.exp (-(K * (p.1.1 + p.1.2))) • (w p - z p))
      rw [smul_smul, ← Real.exp_add]
      simp
    rw [dist_eq_norm, hdecomp, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm d p)
      (Real.exp_pos _).le
  have hboundX (p : rectangle u₀ u₁ v₀ v₁) :
      ‖(∫ s in u₀..p.1.1,
          fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))) -
        ∫ s in u₀..p.1.1,
          fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2)))‖ ≤
        ((κ : ℝ) * ‖d‖) / K * Real.exp (K * (p.1.1 + p.1.2)) := by
    have hfw : Continuous (fun s : ℝ =>
        fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))) :=
      continuous_comp_clippedPoint hu hv fX hfX w
        (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
    have hfz : Continuous (fun s : ℝ =>
        fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2)))) :=
      continuous_comp_clippedPoint hu hv fX hfX z
        (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
    apply norm_integral_sub_le_exp p.2.1.1 hK
      (mul_nonneg κ.coe_nonneg (norm_nonneg d)) _ _
      (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _)
    intro s hs
    rw [← dist_eq_norm]
    have hsI : s ∈ Icc u₀ u₁ := ⟨hs.1, hs.2.trans p.2.1.2⟩
    let q : rectangle u₀ u₁ v₀ v₁ := ⟨(s, p.1.2), ⟨hsI, p.2.2⟩⟩
    have hclip : clippedPoint hu hv (s, p.1.2) = q :=
      clippedPoint_eq_self hu hv q
    rw [hclip]
    calc
      dist (fX q.1 (w q)) (fX q.1 (z q)) ≤
          (κ : ℝ) * dist (w q) (z q) := hLX q
      _ ≤ (κ : ℝ) * (Real.exp (K * (s + p.1.2)) * ‖d‖) :=
        mul_le_mul_of_nonneg_left (hpoint q) κ.coe_nonneg
      _ = ((κ : ℝ) * ‖d‖) * Real.exp (K * (s + p.1.2)) := by ring
  have hboundY (p : rectangle u₀ u₁ v₀ v₁) :
      ‖(∫ t in v₀..p.1.2,
          fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) -
        ∫ t in v₀..p.1.2,
          fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t)))‖ ≤
        ((κ : ℝ) * ‖d‖) / K * Real.exp (K * (p.1.1 + p.1.2)) := by
    have hfw : Continuous (fun t : ℝ =>
        fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) :=
      continuous_comp_clippedPoint hu hv fY hfY w
        (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
    have hfz : Continuous (fun t : ℝ =>
        fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t)))) :=
      continuous_comp_clippedPoint hu hv fY hfY z
        (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
    rw [add_comm p.1.1 p.1.2]
    apply norm_integral_sub_le_exp p.2.2.1 hK
      (mul_nonneg κ.coe_nonneg (norm_nonneg d)) _ _
      (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _)
    intro t ht
    rw [← dist_eq_norm]
    have htI : t ∈ Icc v₀ v₁ := ⟨ht.1, ht.2.trans p.2.2.2⟩
    let q : rectangle u₀ u₁ v₀ v₁ := ⟨(p.1.1, t), ⟨p.2.1, htI⟩⟩
    have hclip : clippedPoint hu hv (p.1.1, t) = q :=
      clippedPoint_eq_self hu hv q
    rw [hclip]
    calc
      dist (fY q.1 (w q)) (fY q.1 (z q)) ≤
          (κ : ℝ) * dist (w q) (z q) := hLY q
      _ ≤ (κ : ℝ) * (Real.exp (K * (p.1.1 + t)) * ‖d‖) :=
        mul_le_mul_of_nonneg_left (hpoint q) κ.coe_nonneg
      _ = ((κ : ℝ) * ‖d‖) * Real.exp (K * (t + p.1.1)) := by
        rw [add_comm p.1.1 t]
        ac_rfl
  have hdist (p : rectangle u₀ u₁ v₀ v₁) :
      dist (w p) (z p) ≤
        ((κ : ℝ) * ‖d‖) / K * Real.exp (K * (p.1.1 + p.1.2)) := by
    have hwp := congrArg (fun f : C(rectangle u₀ u₁ v₀ v₁, E × F) => f p) hw.symm
    have hzp := congrArg (fun f : C(rectangle u₀ u₁ v₀ v₁, E × F) => f p) hz.symm
    rw [hwp, hzp, picard_apply, picard_apply, Prod.dist_eq]
    apply max_le
    · simpa only [dist_eq_norm, add_sub_add_left_eq_sub] using hboundX p
    · simpa only [dist_eq_norm, add_sub_add_left_eq_sub] using hboundY p
  have hdle (p : rectangle u₀ u₁ v₀ v₁) : ‖d p‖ ≤ (κ : ℝ) / K * ‖d‖ := by
    change ‖Real.exp (-(K * (p.1.1 + p.1.2))) • (w p - z p)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ← dist_eq_norm]
    calc
      _ ≤ Real.exp (-(K * (p.1.1 + p.1.2))) *
          (((κ : ℝ) * ‖d‖) / K * Real.exp (K * (p.1.1 + p.1.2))) :=
        mul_le_mul_of_nonneg_left (hdist p) (Real.exp_pos _).le
      _ = (κ : ℝ) / K * ‖d‖ := by
        rw [mul_comm ((κ : ℝ) * ‖d‖ / K), ← mul_assoc,
          ← Real.exp_add]
        simp only [neg_add_cancel, Real.exp_zero, one_mul]
        ring
  have hD : ‖d‖ ≤ (κ : ℝ) / K * ‖d‖ := by
    exact (ContinuousMap.norm_le d
      (mul_nonneg (div_nonneg κ.coe_nonneg hK.le) (norm_nonneg d))).2 hdle
  have hq : (κ : ℝ) / K < 1 := (div_lt_one hK).2 hκK
  have hzero : ‖d‖ = 0 := by
    have hn := norm_nonneg d
    nlinarith
  apply ContinuousMap.ext
  intro p
  have hp : d p = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm ((hdle p).trans (by rw [hzero]; simp)) (norm_nonneg _)
  have hE : Real.exp (-(K * (p.1.1 + p.1.2))) ≠ 0 :=
    (Real.exp_pos _).ne'
  change Real.exp (-(K * (p.1.1 + p.1.2))) • (w p - z p) = 0 at hp
  exact sub_eq_zero.mp ((smul_eq_zero.mp hp).resolve_left hE)

/-- Two continuous Goursat solutions agree on any rectangle when the
nonlinearities are jointly locally Lipschitz. Compactness of the two solution
ranges supplies the Lipschitz constant used by the weighted integral estimate. -/
theorem eq_on_rectangle_of_integral_equations_of_locallyLipschitz
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : ContinuousOn X (rectangle u₀ u₁ v₀ v₁))
    (hY : ContinuousOn Y (rectangle u₀ u₁ v₀ v₁))
    (hX' : ContinuousOn X' (rectangle u₀ u₁ v₀ v₁))
    (hY' : ContinuousOn Y' (rectangle u₀ u₁ v₀ v₁))
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : LocallyLipschitz fX.uncurry)
    (hfY : LocallyLipschitz fY.uncurry)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p := by
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX).prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY)⟩
  let z : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X' p.1, Y' p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX').prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY')⟩
  let S : Set (E × F) := Set.range w ∪ Set.range z
  have hS : IsCompact S :=
    (isCompact_range w.continuous).union (isCompact_range z.continuous)
  have hR : IsCompact (rectangle u₀ u₁ v₀ v₁) :=
    isCompact_Icc.prod isCompact_Icc
  have hT : IsCompact (rectangle u₀ u₁ v₀ v₁ ×ˢ S) := hR.prod hS
  obtain ⟨κX, hκX⟩ :=
    (hfX.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hT)
  obtain ⟨κY, hκY⟩ :=
    (hfY.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hT)
  let κ : NNReal := max κX κY
  have hLX (q : rectangle u₀ u₁ v₀ v₁) :
      dist (fX q.1 (w q)) (fX q.1 (z q)) ≤ (κ : ℝ) * dist (w q) (z q) := by
    have h := hκX.dist_le_mul (q.1, w q) ⟨q.2, Or.inl ⟨q, rfl⟩⟩
      (q.1, z q) ⟨q.2, Or.inr ⟨q, rfl⟩⟩
    have hd : dist (q.1, w q) (q.1, z q) = dist (w q) (z q) := by
      simp [Prod.dist_eq]
    rw [hd] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left κX κY) dist_nonneg)
  have hLY (q : rectangle u₀ u₁ v₀ v₁) :
      dist (fY q.1 (w q)) (fY q.1 (z q)) ≤ (κ : ℝ) * dist (w q) (z q) := by
    have h := hκY.dist_le_mul (q.1, w q) ⟨q.2, Or.inl ⟨q, rfl⟩⟩
      (q.1, z q) ⟨q.2, Or.inr ⟨q, rfl⟩⟩
    have hd : dist (q.1, w q) (q.1, z q) = dist (w q) (z q) := by
      simp [Prod.dist_eq]
    rw [hd] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right κX κY) dist_nonneg)
  have hw : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX.continuous hfY.continuous) w :=
    isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv
      X Y x₀ y₀ fX fY hX hY hx₀ hy₀ hfX.continuous hfY.continuous heq
  have hz : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX.continuous hfY.continuous) z :=
    isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv
      X' Y' x₀ y₀ fX fY hX' hY' hx₀ hy₀ hfX.continuous hfY.continuous heq'
  have hwz := fixedPoint_unique_of_solution_lipschitz u₀ u₁ v₀ v₁ hu hv
    x₀ y₀ fX fY hx₀ hy₀ hfX.continuous hfY.continuous κ w z hLX hLY hw hz
  intro p hp
  exact Prod.mk.inj (congrArg
    (fun a : C(rectangle u₀ u₁ v₀ v₁, E × F) => a ⟨p, hp⟩) hwz)
end Goursat

end
