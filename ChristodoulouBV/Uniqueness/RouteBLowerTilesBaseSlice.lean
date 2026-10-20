module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverJetClosure
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
# Horizontal slices of the terminal base jets

The canonical closed-rectangle full jets supply the incoming-edge
derivatives used by the characteristic rectangle theorem, including at the
two endpoints of the compact base.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Restrict a canonical full scalar jet to the terminal horizontal edge. -/
theorem hasDerivWithinAt_terminal_horizontal_slice
    {a vBar vStar : ℝ} (hBarStar : vBar ≤ vStar)
    {f du dv : ℝ × ℝ → ℝ}
    (hjet : ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
      HasFDerivWithinAt f (rectangleScalarJet (du p) (dv p))
        (Icc 0 a ×ˢ Icc vBar vStar) p)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    HasDerivWithinAt (fun t => f (t, vStar)) (du (u, vStar))
      (Icc 0 a) u := by
  have hp : (u, vStar) ∈ Icc 0 a ×ˢ Icc vBar vStar :=
    ⟨hu, ⟨hBarStar, le_rfl⟩⟩
  have hpath : HasDerivWithinAt (fun t : ℝ => (t, vStar))
      (1, 0) (Icc 0 a) u :=
    ((hasDerivAt_id u).hasDerivWithinAt).prodMk
      ((hasDerivAt_const u vStar).hasDerivWithinAt)
  have hmap : MapsTo (fun t : ℝ => (t, vStar)) (Icc 0 a)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    fun t ht => ⟨ht, ⟨hBarStar, le_rfl⟩⟩
  simpa only [Function.comp_def, rectangleScalarJet_apply_first] using
    (hjet (u, vStar) hp).comp_hasDerivWithinAt u hpath hmap

/-- Restrict a full scalar jet to any horizontal slice of the closed base. -/
theorem hasDerivWithinAt_base_horizontal_slice
    {a vBar vStar : ℝ} {f du dv : ℝ × ℝ → ℝ}
    (hjet : ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
      HasFDerivWithinAt f (rectangleScalarJet (du p) (dv p))
        (Icc 0 a ×ˢ Icc vBar vStar) p)
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    HasDerivWithinAt (fun t => f (t, v)) (du (u, v))
      (Icc 0 a) u := by
  have hpath : HasDerivWithinAt (fun t : ℝ => (t, v))
      (1, 0) (Icc 0 a) u :=
    ((hasDerivAt_id u).hasDerivWithinAt).prodMk
      ((hasDerivAt_const u v).hasDerivWithinAt)
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 a)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    fun t ht => ⟨ht, hv⟩
  simpa only [Function.comp_def, rectangleScalarJet_apply_first] using
    (hjet (u, v) ⟨hu, hv⟩).comp_hasDerivWithinAt u hpath hmap

/-- Restrict a full scalar jet to any vertical slice of the closed base. -/
theorem hasDerivWithinAt_base_vertical_slice
    {a vBar vStar : ℝ} {f du dv : ℝ × ℝ → ℝ}
    (hjet : ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
      HasFDerivWithinAt f (rectangleScalarJet (du p) (dv p))
        (Icc 0 a ×ˢ Icc vBar vStar) p)
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    HasDerivWithinAt (fun t => f (u, t)) (dv (u, v))
      (Icc vBar vStar) v := by
  have hpath : HasDerivWithinAt (fun t : ℝ => (u, t))
      (0, 1) (Icc vBar vStar) v :=
    ((hasDerivAt_const v u).hasDerivWithinAt).prodMk
      ((hasDerivAt_id v).hasDerivWithinAt)
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc vBar vStar)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    fun t ht => ⟨hu, ht⟩
  simpa only [Function.comp_def, rectangleScalarJet_apply_second] using
    (hjet (u, v) ⟨hu, hv⟩).comp_hasDerivWithinAt v hpath hmap

/-- A continuous terminal rectangle trace has a continuous incoming-edge
slice on the full closed interval. -/
theorem continuousOn_terminal_horizontal_slice
    {a vBar vStar : ℝ} (hBarStar : vBar ≤ vStar)
    {f : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn f (Icc 0 a ×ˢ Icc vBar vStar)) :
    ContinuousOn (fun u => f (u, vStar)) (Icc 0 a) :=
  hcont.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hu => ⟨hu, ⟨hBarStar, le_rfl⟩⟩)

/-- Restrict a relative C¹ field to the terminal horizontal edge. -/
theorem contDiffOn_terminal_horizontal_slice
    {a vBar vStar : ℝ} (hBarStar : vBar ≤ vStar)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F}
    (hf : ContDiffOn ℝ 1 f (Icc 0 a ×ˢ Icc vBar vStar)) :
    ContDiffOn ℝ 1 (fun u => f (u, vStar)) (Icc 0 a) := by
  have hpath : ContDiffOn ℝ 1
      (fun u : ℝ => (u, vStar)) (Icc 0 a) :=
    contDiffOn_id.prodMk contDiffOn_const
  exact hf.comp hpath (fun u hu => ⟨hu, ⟨hBarStar, le_rfl⟩⟩)

/-- The derivative of a C¹ terminal slice varies continuously along the
entire compact incoming edge. -/
theorem continuousOn_terminal_horizontal_derivWithin
    {a vBar vStar : ℝ} (ha : 0 < a) (hBarStar : vBar ≤ vStar)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F}
    (hf : ContDiffOn ℝ 1 f (Icc 0 a ×ˢ Icc vBar vStar)) :
    ContinuousOn
      (derivWithin (fun u => f (u, vStar)) (Icc 0 a)) (Icc 0 a) :=
  (contDiffOn_terminal_horizontal_slice hBarStar hf).continuousOn_derivWithin
    (uniqueDiffOn_Icc ha) (by norm_num)

end ChristodoulouBV.Uniqueness

end
