module

public import Mathlib

/-!
# Goursat integral equations on a rectangle

This file develops the continuous-function fixed-point formulation of a first-order
semilinear characteristic initial-value problem.  The two unknowns may take values
in different real Banach spaces.
-/

public section

open Set intervalIntegral

namespace Goursat

/-- The closed rectangle with lower corner `(u₀, v₀)` and upper corner `(u₁, v₁)`. -/
def rectangle (u₀ u₁ v₀ v₁ : ℝ) : Set (ℝ × ℝ) :=
  Icc u₀ u₁ ×ˢ Icc v₀ v₁

/-- A closed rectangle is compact, including when it is empty. -/
instance compactSpace_rectangle (u₀ u₁ v₀ v₁ : ℝ) :
    CompactSpace (rectangle u₀ u₁ v₀ v₁) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

/-- Clamp a real number to an interval. -/
def clip (a b x : ℝ) : ℝ := max a (min x b)

/-- Clamping takes values in the interval when it is nonempty. -/
theorem clip_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clip a b x ∈ Icc a b := by
  simp only [clip, mem_Icc]
  constructor
  · exact le_max_left _ _
  · exact max_le hab (min_le_right _ _)

/-- Clamping fixes points of the interval. -/
theorem clip_eq_self {a b x : ℝ} (hx : x ∈ Icc a b) : clip a b x = x := by
  simp only [clip, mem_Icc] at *
  simp [max_eq_right hx.1, min_eq_left hx.2]

/-- Clamping is continuous. -/
theorem continuous_clip (a b : ℝ) : Continuous (clip a b) := by
  change Continuous (fun x : ℝ => max a (min x b))
  exact continuous_const.max (continuous_id.min continuous_const)

/-- Clamping both coordinates maps the plane into a nonempty closed rectangle. -/
def clippedPoint {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) :
    ℝ × ℝ → rectangle u₀ u₁ v₀ v₁ :=
  fun p => ⟨(clip u₀ u₁ p.1, clip v₀ v₁ p.2),
    ⟨clip_mem_Icc hu p.1, clip_mem_Icc hv p.2⟩⟩

/-- The clipped-point map is continuous. -/
theorem continuous_clippedPoint {u₀ u₁ v₀ v₁ : ℝ}
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) :
    Continuous (clippedPoint hu hv) := by
  exact Continuous.subtype_mk
    (((continuous_clip u₀ u₁).comp continuous_fst).prodMk
      ((continuous_clip v₀ v₁).comp continuous_snd))
    (fun p => ⟨clip_mem_Icc hu p.1, clip_mem_Icc hv p.2⟩)

/-- On the rectangle, clipping changes no point. -/
theorem clippedPoint_eq_self {u₀ u₁ v₀ v₁ : ℝ}
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (p : rectangle u₀ u₁ v₀ v₁) : clippedPoint hu hv p.1 = p := by
  apply Subtype.ext
  exact Prod.ext (clip_eq_self p.2.1) (clip_eq_self p.2.2)

/-- A bound for the difference of two interval integrals on an ordered interval. -/
theorem norm_integral_sub_le_of_norm_sub_le {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b C : ℝ} (hab : a ≤ b) (f g : ℝ → G)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hfg : ∀ s ∈ Icc a b, ‖f s - g s‖ ≤ C) :
    ‖(∫ s in a..b, f s) - ∫ s in a..b, g s‖ ≤ C * (b - a) := by
  have hsub : (∫ s in a..b, f s) - (∫ s in a..b, g s) =
      ∫ s in a..b, f s - g s := (intervalIntegral.integral_sub hf hg).symm
  rw [hsub]
  have h : ∀ s ∈ Set.uIoc a b, ‖f s - g s‖ ≤ C := by
    intro s hs
    exact hfg s (by simpa [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc hs)
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := C) (f := fun s => f s - g s) h)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The characteristic Picard operator on continuous functions over a rectangle. -/
@[expose] noncomputable def picard (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    C(rectangle u₀ u₁ v₀ v₁, E × F) := by
  let wc : ℝ × ℝ → E × F := fun p => w (clippedPoint hu hv p)
  have hwc : Continuous wc := w.continuous.comp (continuous_clippedPoint hu hv)
  have hX : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      fX (q.2, q.1.2) (wc (q.2, q.1.2))) := by
    have hp : Continuous (fun q : (ℝ × ℝ) × ℝ => (q.2, q.1.2)) :=
      continuous_snd.prodMk (continuous_snd.comp continuous_fst)
    exact hfX.comp (hp.prodMk (hwc.comp hp))
  have hY : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      fY (q.1.1, q.2) (wc (q.1.1, q.2))) := by
    have hp : Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) :=
      (continuous_fst.comp continuous_fst).prodMk continuous_snd
    exact hfY.comp (hp.prodMk (hwc.comp hp))
  have hIX : Continuous (fun p : ℝ × ℝ =>
      ∫ s in u₀..p.1, fX (s, p.2) (wc (s, p.2))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hX continuous_fst
  have hIY : Continuous (fun p : ℝ × ℝ =>
      ∫ t in v₀..p.2, fY (p.1, t) (wc (p.1, t))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hY continuous_snd
  refine ⟨fun p =>
    (x₀ p.1.2 + ∫ s in u₀..p.1.1, fX (s, p.1.2) (wc (s, p.1.2)),
     y₀ p.1.1 + ∫ t in v₀..p.1.2, fY (p.1.1, t) (wc (p.1.1, t))), ?_⟩
  have h : Continuous (fun p : ℝ × ℝ =>
      (x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (wc (s, p.2)),
       y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (wc (p.1, t)))) :=
    ((hx₀.comp continuous_snd).add hIX).prodMk
      ((hy₀.comp continuous_fst).add hIY)
  exact h.comp continuous_subtype_val

/-- Evaluation of the characteristic Picard operator. -/
theorem picard_apply (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (p : rectangle u₀ u₁ v₀ v₁) :
    picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w p =
      (x₀ p.1.2 + ∫ s in u₀..p.1.1,
          fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
       y₀ p.1.1 + ∫ t in v₀..p.1.2,
          fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) := by
  rfl

/-- A continuous section of a nonlinearity evaluated at a clamped continuous function. -/
theorem continuous_comp_clippedPoint {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (f : ℝ × ℝ → G → H) (hf : Continuous f.uncurry)
    (w : C(rectangle u₀ u₁ v₀ v₁, G))
    (p : ℝ → ℝ × ℝ) (hp : Continuous p) :
    Continuous (fun s => f (p s) (w (clippedPoint hu hv (p s)))) := by
  exact hf.comp (hp.prodMk
    (w.continuous.comp ((continuous_clippedPoint hu hv).comp hp)))

/-- The characteristic Picard operator is Lipschitz in the sup metric. -/
theorem dist_picard_le (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    dist (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY z) ≤
      ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * dist w z := by
  apply (ContinuousMap.dist_le (mul_nonneg
    (mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu))) (dist_nonneg))).2
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
      intro s _
      rw [← dist_eq_norm]
      exact (hLX _ _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousMap.dist_apply_le_dist (clippedPoint hu hv (s, p.1.2))) κ.coe_nonneg)
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
      intro t _
      rw [← dist_eq_norm]
      exact (hLY _ _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousMap.dist_apply_le_dist (clippedPoint hu hv (p.1.1, t))) κ.coe_nonneg)
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

/-- On a sufficiently small rectangle the Picard operator is a contraction. -/
theorem contractingWith_picard (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ContractingWith
      (⟨(κ : ℝ) * max (u₁ - u₀) (v₁ - v₀),
        mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu))⟩ : NNReal)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) := by
  constructor
  · exact hsmall
  · apply LipschitzWith.of_dist_le_mul
    intro w z
    exact dist_picard_le u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
      κ hLX hLY w z

/-- A continuous Goursat solution exists on a small closed rectangle. -/
theorem exists_continuous_solution [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ w : C(rectangle u₀ u₁ v₀ v₁, E × F),
      ∀ p : rectangle u₀ u₁ v₀ v₁,
        w p =
          (x₀ p.1.2 + ∫ s in u₀..p.1.1,
              fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
           y₀ p.1.1 + ∫ t in v₀..p.1.2,
              fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) := by
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  have hT := contractingWith_picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
    κ hLX hLY hsmall
  obtain ⟨w, hw, _, _⟩ := hT.exists_fixedPoint (ContinuousMap.const _ (0, 0)) (by simp)
  refine ⟨w, fun p => ?_⟩
  calc
    w p = T w p := congrArg (fun q : C(rectangle u₀ u₁ v₀ v₁, E × F) => q p) hw.symm
    _ = _ := picard_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w p

/-- Small-rectangle existence in the ordinary two-component integral formulation. -/
theorem exists_continuous_solution_on_rectangle [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
      Continuous X ∧ Continuous Y ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)) := by
  obtain ⟨w, hw⟩ := exists_continuous_solution u₀ u₁ v₀ v₁ hu hv
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY κ hLX hLY hsmall
  let X : ℝ × ℝ → E := fun p => (w (clippedPoint hu hv p)).1
  let Y : ℝ × ℝ → F := fun p => (w (clippedPoint hu hv p)).2
  refine ⟨X, Y, (w.continuous.comp (continuous_clippedPoint hu hv)).fst,
    (w.continuous.comp (continuous_clippedPoint hu hv)).snd, ?_⟩
  intro p hp
  let q : rectangle u₀ u₁ v₀ v₁ := ⟨p, hp⟩
  have hq : clippedPoint hu hv p = q := clippedPoint_eq_self hu hv q
  have h := hw q
  dsimp [X, Y] at ⊢
  rw [hq]
  constructor
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The continuous solution of the characteristic integral equations is unique
on a small rectangle. -/
theorem unique_continuous_solution (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : ∀ p : rectangle u₀ u₁ v₀ v₁,
      w p =
        (x₀ p.1.2 + ∫ s in u₀..p.1.1,
            fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
         y₀ p.1.1 + ∫ t in v₀..p.1.2,
            fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))))
    (hz : ∀ p : rectangle u₀ u₁ v₀ v₁,
      z p =
        (x₀ p.1.2 + ∫ s in u₀..p.1.1,
            fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2))),
         y₀ p.1.1 + ∫ t in v₀..p.1.2,
            fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t))))) :
    w = z := by
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  have hT := contractingWith_picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
    κ hLX hLY hsmall
  have hwfix : Function.IsFixedPt T w := by
    apply ContinuousMap.ext
    intro p
    exact (picard_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w p).trans
      (hw p).symm
  have hzfix : Function.IsFixedPt T z := by
    apply ContinuousMap.ext
    intro p
    exact (picard_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY z p).trans
      (hz p).symm
  exact hT.fixedPoint_unique' hwfix hzfix

/-- Continuous dependence on characteristic data for the same nonlinearities
on a small rectangle. -/
theorem dist_solutions_le (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ x₀' : ℝ → E) (y₀ y₀' : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hx₀' : Continuous x₀') (hy₀' : Continuous y₀')
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (A B : ℝ) (hA : 0 ≤ A)
    (hdataX : ∀ v ∈ Icc v₀ v₁, dist (x₀ v) (x₀' v) ≤ A)
    (hdataY : ∀ u ∈ Icc u₀ u₁, dist (y₀ u) (y₀' u) ≤ B)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w)
    (hz : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀' y₀' fX fY hx₀' hy₀' hfX hfY) z) :
    dist w z ≤ max A B /
      (1 - (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) := by
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  let T' := picard u₀ u₁ v₀ v₁ hu hv x₀' y₀' fX fY hx₀' hy₀' hfX hfY
  have hT := contractingWith_picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
    κ hLX hLY hsmall
  apply hT.dist_fixedPoint_fixedPoint_of_dist_le' T' hw hz
  intro q
  apply (ContinuousMap.dist_le (le_trans hA (le_max_left A B))).2
  intro p
  rw [Prod.dist_eq]
  apply max_le
  · rw [picard_apply, picard_apply]
    simp only [dist_eq_norm, add_sub_add_right_eq_sub]
    simpa only [dist_eq_norm] using (hdataX p.1.2 p.2.2).trans (le_max_left A B)
  · rw [picard_apply, picard_apply]
    simp only [dist_eq_norm, add_sub_add_right_eq_sub]
    simpa only [dist_eq_norm] using (hdataY p.1.1 p.2.1).trans (le_max_right A B)

/-- An integral equation has the expected derivative at every interior point. -/
theorem hasDerivAt_of_eq_integral_on_Icc {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {a b c : ℝ} (hc : c ∈ Ioo a b) (g f : ℝ → G) (d : G)
    (hf : Continuous f)
    (heq : ∀ t ∈ Icc a b, g t = d + ∫ s in a..t, f s) :
    HasDerivAt g (f c) c := by
  have hprim : HasDerivAt (fun t => d + ∫ s in a..t, f s) (f c) c :=
    (intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable a c)
      (hf.aestronglyMeasurable.stronglyMeasurableAtFilter) hf.continuousAt).const_add d
  apply hprim.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hc.1 hc.2] with t ht
  exact heq t ht

/-- The first Goursat equation gives the `u` derivative in the rectangle's interior. -/
theorem hasDerivAt_first_of_integral_equations
    [CompleteSpace E]
    (u₀ u₁ v₀ v₁ : ℝ) (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hfX : Continuous fX.uncurry)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    {u v : ℝ} (hu : u ∈ Ioo u₀ u₁) (hv : v ∈ Icc v₀ v₁) :
    HasDerivAt (fun s => X (s, v)) (fX (u, v) (X (u, v), Y (u, v))) u := by
  have hp : Continuous (fun s : ℝ => (s, v)) := continuous_id.prodMk continuous_const
  have hf : Continuous (fun s : ℝ => fX (s, v) (X (s, v), Y (s, v))) :=
    hfX.comp (hp.prodMk ((hX.prodMk hY).comp hp))
  exact hasDerivAt_of_eq_integral_on_Icc hu _ _ (x₀ v) hf
    (fun s hs => (heq (s, v) ⟨hs, hv⟩).1)

/-- The second Goursat equation gives the `v` derivative in the rectangle's interior. -/
theorem hasDerivAt_second_of_integral_equations
    [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hfY : Continuous fY.uncurry)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    {u v : ℝ} (hu : u ∈ Icc u₀ u₁) (hv : v ∈ Ioo v₀ v₁) :
    HasDerivAt (fun t => Y (u, t)) (fY (u, v) (X (u, v), Y (u, v))) v := by
  have hp : Continuous (fun t : ℝ => (u, t)) := continuous_const.prodMk continuous_id
  have hf : Continuous (fun t : ℝ => fY (u, t) (X (u, t), Y (u, t))) :=
    hfY.comp (hp.prodMk ((hX.prodMk hY).comp hp))
  exact hasDerivAt_of_eq_integral_on_Icc hv _ _ (y₀ u) hf
    (fun t ht => (heq (u, t) ⟨hu, ht⟩).2)

/-- Restrict an ordinary continuous integral solution to the rectangle as a Picard fixed point. -/
theorem isFixedPt_picard_of_integral_equations
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : ContinuousOn X (rectangle u₀ u₁ v₀ v₁))
    (hY : ContinuousOn Y (rectangle u₀ u₁ v₀ v₁))
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t))) :
    Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY)
      ⟨fun p : rectangle u₀ u₁ v₀ v₁ => (X p.1, Y p.1),
        (continuousOn_iff_continuous_domRestrict.mp hX).prodMk
          (continuousOn_iff_continuous_domRestrict.mp hY)⟩ := by
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX).prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY)⟩
  apply ContinuousMap.ext
  intro p
  have hIX : (∫ s in u₀..p.1.1,
      fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))) =
      ∫ s in u₀..p.1.1, fX (s, p.1.2) (X (s, p.1.2), Y (s, p.1.2)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_refl u₀, hu⟩ p.2.1 hs
    simp [w, clippedPoint, clip_eq_self hsI, clip_eq_self p.2.2]
    rfl
  have hIY : (∫ t in v₀..p.1.2,
      fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) =
      ∫ t in v₀..p.1.2, fY (p.1.1, t) (X (p.1.1, t), Y (p.1.1, t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_refl v₀, hv⟩ p.2.2 ht
    simp [w, clippedPoint, clip_eq_self p.2.1, clip_eq_self htI]
    rfl
  rw [picard_apply, hIX, hIY]
  exact Prod.ext (heq p.1 p.2).1.symm (heq p.1 p.2).2.symm

/-- Uniqueness among functions continuous on a small rectangle and satisfying
the integral equations. -/
theorem eq_on_rectangle_of_integral_equations
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : ContinuousOn X (rectangle u₀ u₁ v₀ v₁))
    (hY : ContinuousOn Y (rectangle u₀ u₁ v₀ v₁))
    (hX' : ContinuousOn X' (rectangle u₀ u₁ v₀ v₁))
    (hY' : ContinuousOn Y' (rectangle u₀ u₁ v₀ v₁))
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p := by
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX).prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY)⟩
  let z : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X' p.1, Y' p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX').prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY')⟩
  have hw : Function.IsFixedPt T w :=
    isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv X Y x₀ y₀ fX fY
      hX hY hx₀ hy₀ hfX hfY heq
  have hz : Function.IsFixedPt T z :=
    isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv X' Y' x₀ y₀ fX fY
      hX' hY' hx₀ hy₀ hfX hfY heq'
  have hT := contractingWith_picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
    κ hLX hLY hsmall
  have hweq : w = z := hT.fixedPoint_unique' hw hz
  intro p hp
  have h := congrArg (fun q : C(rectangle u₀ u₁ v₀ v₁, E × F) => q ⟨p, hp⟩) hweq
  exact Prod.mk.inj h

/-- Coordinate clipping extends a nonlinearity continuous on a rectangle to a
continuous function on the whole plane, without changing it on the rectangle. -/
theorem continuous_uncurry_clipped_nonlinearity {G H : Type*}
    [TopologicalSpace G] [TopologicalSpace H]
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (f : ℝ × ℝ → G → H)
    (hf : ContinuousOn f.uncurry (rectangle u₀ u₁ v₀ v₁ ×ˢ Set.univ)) :
    Continuous (Function.uncurry
      (fun q a => f (clippedPoint hu hv q).1 a)) := by
  let c : ((ℝ × ℝ) × G) → ((ℝ × ℝ) × G) :=
    fun z => ((clippedPoint hu hv z.1).1, z.2)
  have hc : Continuous c :=
    ((continuous_clippedPoint hu hv).subtype_val.comp continuous_fst).prodMk continuous_snd
  have hcmem : ∀ z, c z ∈ rectangle u₀ u₁ v₀ v₁ ×ˢ Set.univ := by
    intro z
    exact ⟨(clippedPoint hu hv z.1).2, Set.mem_univ _⟩
  exact hf.comp_continuous hc hcmem

/-- Local Goursat existence requires continuity and a uniform Lipschitz bound
only on the rectangle, with no condition outside it. -/
theorem exists_continuous_solution_on_rectangle_of_continuousOn
    [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : ContinuousOn fX.uncurry (rectangle u₀ u₁ v₀ v₁ ×ˢ Set.univ))
    (hfY : ContinuousOn fY.uncurry (rectangle u₀ u₁ v₀ v₁ ×ˢ Set.univ))
    (κ : NNReal)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
      Continuous X ∧ Continuous Y ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)) := by
  let fXc : ℝ × ℝ → E × F → E := fun q a => fX (clippedPoint hu hv q).1 a
  let fYc : ℝ × ℝ → E × F → F := fun q a => fY (clippedPoint hu hv q).1 a
  have hfXc : Continuous fXc.uncurry :=
    continuous_uncurry_clipped_nonlinearity hu hv fX hfX
  have hfYc : Continuous fYc.uncurry :=
    continuous_uncurry_clipped_nonlinearity hu hv fY hfY
  have hLXc : ∀ q a b, dist (fXc q a) (fXc q b) ≤ (κ : ℝ) * dist a b := by
    intro q a b
    exact hLX _ (clippedPoint hu hv q).2 a b
  have hLYc : ∀ q a b, dist (fYc q a) (fYc q b) ≤ (κ : ℝ) * dist a b := by
    intro q a b
    exact hLY _ (clippedPoint hu hv q).2 a b
  obtain ⟨X, Y, hX, hY, heq⟩ :=
    exists_continuous_solution_on_rectangle u₀ u₁ v₀ v₁ hu hv
      x₀ y₀ fXc fYc hx₀ hy₀ hfXc hfYc κ hLXc hLYc hsmall
  refine ⟨X, Y, hX, hY, ?_⟩
  intro p hp
  have h := heq p hp
  constructor
  · rw [h.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_refl u₀, hu⟩ hp.1 hs
    simp [fXc, clippedPoint, clip_eq_self hsI, clip_eq_self hp.2]
  · rw [h.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_refl v₀, hv⟩ hp.2 ht
    simp [fYc, clippedPoint, clip_eq_self hp.1, clip_eq_self htI]

/-- Local uniqueness also needs the nonlinearity assumptions only on the rectangle. -/
theorem eq_on_rectangle_of_integral_equations_of_continuousOn
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : ContinuousOn X (rectangle u₀ u₁ v₀ v₁))
    (hY : ContinuousOn Y (rectangle u₀ u₁ v₀ v₁))
    (hX' : ContinuousOn X' (rectangle u₀ u₁ v₀ v₁))
    (hY' : ContinuousOn Y' (rectangle u₀ u₁ v₀ v₁))
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : ContinuousOn fX.uncurry (rectangle u₀ u₁ v₀ v₁ ×ˢ Set.univ))
    (hfY : ContinuousOn fY.uncurry (rectangle u₀ u₁ v₀ v₁ ×ˢ Set.univ))
    (κ : NNReal)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ a b,
      dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p := by
  let fXc : ℝ × ℝ → E × F → E := fun q a => fX (clippedPoint hu hv q).1 a
  let fYc : ℝ × ℝ → E × F → F := fun q a => fY (clippedPoint hu hv q).1 a
  have hfXc : Continuous fXc.uncurry :=
    continuous_uncurry_clipped_nonlinearity hu hv fX hfX
  have hfYc : Continuous fYc.uncurry :=
    continuous_uncurry_clipped_nonlinearity hu hv fY hfY
  have hLXc : ∀ q a b, dist (fXc q a) (fXc q b) ≤ (κ : ℝ) * dist a b := by
    intro q a b
    exact hLX _ (clippedPoint hu hv q).2 a b
  have hLYc : ∀ q a b, dist (fYc q a) (fYc q b) ≤ (κ : ℝ) * dist a b := by
    intro q a b
    exact hLY _ (clippedPoint hu hv q).2 a b
  have translate (U : ℝ × ℝ → E) (V : ℝ × ℝ → F)
      (h : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        U p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (U (s, p.2), V (s, p.2)) ∧
        V p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (U (p.1, t), V (p.1, t))) :
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        U p = x₀ p.2 + ∫ s in u₀..p.1, fXc (s, p.2) (U (s, p.2), V (s, p.2)) ∧
        V p = y₀ p.1 + ∫ t in v₀..p.2, fYc (p.1, t) (U (p.1, t), V (p.1, t)) := by
    intro p hp
    constructor
    · rw [(h p hp).1]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Icc u₀ u₁ :=
        Set.uIcc_subset_Icc ⟨le_refl u₀, hu⟩ hp.1 hs
      simp [fXc, clippedPoint, clip_eq_self hsI, clip_eq_self hp.2]
    · rw [(h p hp).2]
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Icc v₀ v₁ :=
        Set.uIcc_subset_Icc ⟨le_refl v₀, hv⟩ hp.2 ht
      simp [fYc, clippedPoint, clip_eq_self hp.1, clip_eq_self htI]
  exact eq_on_rectangle_of_integral_equations u₀ u₁ v₀ v₁ hu hv
    X X' Y Y' x₀ y₀ fXc fYc hX hY hX' hY' hx₀ hy₀ hfXc hfYc
    κ hLXc hLYc hsmall (translate X Y heq) (translate X' Y' heq')

/-- A sup-norm dependence estimate for the two components of continuous solutions. -/
theorem iSup_norm_sub_add_norm_sub_le
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ x₀' : ℝ → E) (y₀ y₀' : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : ContinuousOn X (rectangle u₀ u₁ v₀ v₁))
    (hY : ContinuousOn Y (rectangle u₀ u₁ v₀ v₁))
    (hX' : ContinuousOn X' (rectangle u₀ u₁ v₀ v₁))
    (hY' : ContinuousOn Y' (rectangle u₀ u₁ v₀ v₁))
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hx₀' : Continuous x₀') (hy₀' : Continuous y₀')
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (A B : ℝ) (hA : 0 ≤ A)
    (hdataX : ∀ v ∈ Icc v₀ v₁, dist (x₀ v) (x₀' v) ≤ A)
    (hdataY : ∀ u ∈ Icc u₀ u₁, dist (y₀ u) (y₀' u) ≤ B)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀' p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀' p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    (⨆ p : rectangle u₀ u₁ v₀ v₁,
      ‖X p.1 - X' p.1‖ + ‖Y p.1 - Y' p.1‖) ≤
      2 * max A B / (1 - (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) := by
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX).prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY)⟩
  let z : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X' p.1, Y' p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX').prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY')⟩
  have hw : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w :=
    isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv X Y x₀ y₀ fX fY
      hX hY hx₀ hy₀ hfX hfY heq
  have hz : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀' y₀' fX fY hx₀' hy₀' hfX hfY) z :=
    isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv X' Y' x₀' y₀' fX fY
      hX' hY' hx₀' hy₀' hfX hfY heq'
  have hdist := dist_solutions_le u₀ u₁ v₀ v₁ hu hv x₀ x₀' y₀ y₀'
    fX fY hx₀ hy₀ hx₀' hy₀' hfX hfY κ hLX hLY hsmall
    A B hA hdataX hdataY w z hw hz
  let _ : Nonempty (rectangle u₀ u₁ v₀ v₁) :=
    ⟨⟨(u₀, v₀), ⟨⟨le_rfl, hu⟩, ⟨le_rfl, hv⟩⟩⟩⟩
  apply ciSup_le
  intro p
  have hp := (ContinuousMap.dist_apply_le_dist p).trans hdist
  change dist (X p.1, Y p.1) (X' p.1, Y' p.1) ≤
    max A B / (1 - (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) at hp
  rw [Prod.dist_eq] at hp
  have h₁ : ‖X p.1 - X' p.1‖ ≤
      max A B / (1 - (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) := by
    simpa only [dist_eq_norm] using (le_max_left _ _).trans hp
  have h₂ : ‖Y p.1 - Y' p.1‖ ≤
      max A B / (1 - (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) := by
    simpa only [dist_eq_norm] using (le_max_right _ _).trans hp
  have hsum := add_le_add h₁ h₂
  convert hsum using 1; ring

end Goursat

end
