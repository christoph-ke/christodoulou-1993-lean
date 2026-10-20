module

public import ChristodoulouBV.C1Solution.UniquenessHorizontalJetIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Absolute differences along incoming rays

The horizontal fundamental theorem converts equality of the initial
values and outgoing jets into integrals of the two source differences.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- The difference of two horizontally driven fields is bounded by the
integral of their source difference when the initial traces agree. -/
theorem horizontal_value_difference_le_integral
    {B : ℝ} (hB : 0 < B) {F₁ F₂ G₁ G₂ : ℝ × ℝ → ℝ}
    (hF₁ : ContDiffOn ℝ 1 F₁ (closedCoordTriangle 0 B))
    (hF₂ : ContDiffOn ℝ 1 F₂ (closedCoordTriangle 0 B))
    (hG₁ : ContDiffOn ℝ 1 G₁ (closedCoordTriangle 0 B))
    (hG₂ : ContDiffOn ℝ 1 G₂ (closedCoordTriangle 0 B))
    (hFu₁ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F₁ (closedCoordTriangle 0 B) p) (1, 0) = G₁ p)
    (hFu₂ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) p) (1, 0) = G₂ p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B)
    (hinit : F₁ (0, v) = F₂ (0, v)) :
    |F₁ (u, v) - F₂ (u, v)| ≤
      ∫ s in (0 : ℝ)..u, |G₁ (s, v) - G₂ (s, v)| := by
  have hI₁ := integral_horizontal_source_eq_sub hB hF₁ hG₁ hFu₁ hu huv hv
  have hI₂ := integral_horizontal_source_eq_sub hB hF₂ hG₂ hFu₂ hu huv hv
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u)
      (closedCoordTriangle 0 B) := by
    intro s hs
    exact ⟨hs.1, hs.2.trans huv, hv⟩
  have hG₁c : ContinuousOn (fun s => G₁ (s, v)) (Icc 0 u) :=
    hG₁.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hG₂c : ContinuousOn (fun s => G₂ (s, v)) (Icc 0 u) :=
    hG₂.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hGI₁ : IntervalIntegrable (fun s => G₁ (s, v)) volume 0 u :=
    hG₁c.intervalIntegrable_of_Icc hu
  have hGI₂ : IntervalIntegrable (fun s => G₂ (s, v)) volume 0 u :=
    hG₂c.intervalIntegrable_of_Icc hu
  have heq : F₁ (u, v) - F₂ (u, v) =
      ∫ s in (0 : ℝ)..u, G₁ (s, v) - G₂ (s, v) := by
    rw [intervalIntegral.integral_sub hGI₁ hGI₂, hI₁, hI₂, hinit]
    ring
  rw [heq]
  exact intervalIntegral.abs_integral_le_integral_abs hu

/-- The outgoing-jet difference has the same incoming-ray integral
estimate, with the outgoing jet of the source as density. -/
theorem horizontal_vertical_jet_difference_le_integral
    {B : ℝ} (hB : 0 < B) {F₁ F₂ G₁ G₂ : ℝ × ℝ → ℝ}
    (hF₁ : ContDiffOn ℝ 1 F₁ (closedCoordTriangle 0 B))
    (hF₂ : ContDiffOn ℝ 1 F₂ (closedCoordTriangle 0 B))
    (hG₁ : ContDiffOn ℝ 1 G₁ (closedCoordTriangle 0 B))
    (hG₂ : ContDiffOn ℝ 1 G₂ (closedCoordTriangle 0 B))
    (hFu₁ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F₁ (closedCoordTriangle 0 B) p) (1, 0) = G₁ p)
    (hFu₂ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) p) (1, 0) = G₂ p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B)
    (hinit :
      (fderivWithin ℝ F₁ (closedCoordTriangle 0 B) (0, v)) (0, 1) =
      (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) (0, v)) (0, 1)) :
    |(fderivWithin ℝ F₁ (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
      ∫ s in (0 : ℝ)..u,
        |(fderivWithin ℝ G₁ (closedCoordTriangle 0 B) (s, v)) (0, 1) -
          (fderivWithin ℝ G₂ (closedCoordTriangle 0 B) (s, v)) (0, 1)| := by
  let K := closedCoordTriangle 0 B
  let j₁ : ℝ → ℝ := fun s => (fderivWithin ℝ G₁ K (s, v)) (0, 1)
  let j₂ : ℝ → ℝ := fun s => (fderivWithin ℝ G₂ K (s, v)) (0, 1)
  have hI₁ := integral_horizontal_source_vertical_jet_eq_sub
    hB hF₁ hG₁ hFu₁ hu huv hv
  have hI₂ := integral_horizontal_source_vertical_jet_eq_sub
    hB hF₂ hG₂ hFu₂ hu huv hv
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) K := by
    intro s hs
    exact ⟨hs.1, hs.2.trans huv, hv⟩
  have hcont₁ : ContinuousOn j₁ (Icc 0 u) :=
    ((hG₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hcont₂ : ContinuousOn j₂ (Icc 0 u) :=
    ((hG₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hGI₁ : IntervalIntegrable j₁ volume 0 u :=
    hcont₁.intervalIntegrable_of_Icc hu
  have hGI₂ : IntervalIntegrable j₂ volume 0 u :=
    hcont₂.intervalIntegrable_of_Icc hu
  have heq :
      (fderivWithin ℝ F₁ K (u, v)) (0, 1) -
        (fderivWithin ℝ F₂ K (u, v)) (0, 1) =
      ∫ s in (0 : ℝ)..u, j₁ s - j₂ s := by
    rw [intervalIntegral.integral_sub hGI₁ hGI₂]
    change (∫ s in (0 : ℝ)..u, j₁ s) = _ at hI₁
    change (∫ s in (0 : ℝ)..u, j₂ s) = _ at hI₂
    rw [hI₁, hI₂, hinit]
    ring
  rw [heq]
  exact intervalIntegral.abs_integral_le_integral_abs hu

end ChristodoulouBV.C1Solution

end
