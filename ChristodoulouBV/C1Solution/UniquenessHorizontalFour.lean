module

public import ChristodoulouBV.C1Solution.UniquenessHorizontalDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Four-component horizontal difference estimate

The values and outgoing jets of two horizontally driven fields have one
combined integral estimate with no loss in the coefficient.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- The four source differences for two horizontally driven C¹ fields. -/
@[expose] noncomputable def horizontalFourSourceSummand (B : ℝ)
    (G₁ G₂ Q₁ Q₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  |G₁ p - G₂ p| + |Q₁ p - Q₂ p| +
  |(fderivWithin ℝ G₁ (closedCoordTriangle 0 B) p) (0, 1) -
    (fderivWithin ℝ G₂ (closedCoordTriangle 0 B) p) (0, 1)| +
  |(fderivWithin ℝ Q₁ (closedCoordTriangle 0 B) p) (0, 1) -
    (fderivWithin ℝ Q₂ (closedCoordTriangle 0 B) p) (0, 1)|

/-- The four-source summand is continuous on the compact triangle. -/
theorem horizontalFourSourceSummand_continuousOn {B : ℝ} (hB : 0 < B)
    {G₁ G₂ Q₁ Q₂ : ℝ × ℝ → ℝ}
    (hG₁ : ContDiffOn ℝ 1 G₁ (closedCoordTriangle 0 B))
    (hG₂ : ContDiffOn ℝ 1 G₂ (closedCoordTriangle 0 B))
    (hQ₁ : ContDiffOn ℝ 1 Q₁ (closedCoordTriangle 0 B))
    (hQ₂ : ContDiffOn ℝ 1 Q₂ (closedCoordTriangle 0 B)) :
    ContinuousOn (horizontalFourSourceSummand B G₁ G₂ Q₁ Q₂)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hjet (F : ℝ × ℝ → ℝ) (hF : ContDiffOn ℝ 1 F K) :
      ContinuousOn (fun p => (fderivWithin ℝ F K p) (0, 1)) K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  change ContinuousOn (fun p =>
    |G₁ p - G₂ p| + |Q₁ p - Q₂ p| +
    |(fderivWithin ℝ G₁ K p) (0, 1) -
      (fderivWithin ℝ G₂ K p) (0, 1)| +
    |(fderivWithin ℝ Q₁ K p) (0, 1) -
      (fderivWithin ℝ Q₂ K p) (0, 1)|) K
  exact (((hG₁.continuousOn.sub hG₂.continuousOn).abs.add
    (hQ₁.continuousOn.sub hQ₂.continuousOn).abs).add
    ((hjet G₁ hG₁).sub (hjet G₂ hG₂)).abs).add
    ((hjet Q₁ hQ₁).sub (hjet Q₂ hQ₂)).abs

/-- Initial agreement of both values and outgoing jets bounds their
four-component difference by one integral of the four source differences. -/
theorem horizontal_four_difference_le_integral
    {B : ℝ} (hB : 0 < B)
    {F₁ F₂ H₁ H₂ G₁ G₂ Q₁ Q₂ : ℝ × ℝ → ℝ}
    (hF₁ : ContDiffOn ℝ 1 F₁ (closedCoordTriangle 0 B))
    (hF₂ : ContDiffOn ℝ 1 F₂ (closedCoordTriangle 0 B))
    (hH₁ : ContDiffOn ℝ 1 H₁ (closedCoordTriangle 0 B))
    (hH₂ : ContDiffOn ℝ 1 H₂ (closedCoordTriangle 0 B))
    (hG₁ : ContDiffOn ℝ 1 G₁ (closedCoordTriangle 0 B))
    (hG₂ : ContDiffOn ℝ 1 G₂ (closedCoordTriangle 0 B))
    (hQ₁ : ContDiffOn ℝ 1 Q₁ (closedCoordTriangle 0 B))
    (hQ₂ : ContDiffOn ℝ 1 Q₂ (closedCoordTriangle 0 B))
    (hFu₁ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F₁ (closedCoordTriangle 0 B) p) (1, 0) = G₁ p)
    (hFu₂ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) p) (1, 0) = G₂ p)
    (hHu₁ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ H₁ (closedCoordTriangle 0 B) p) (1, 0) = Q₁ p)
    (hHu₂ : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ H₂ (closedCoordTriangle 0 B) p) (1, 0) = Q₂ p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B)
    (hFinit : F₁ (0, v) = F₂ (0, v))
    (hHinit : H₁ (0, v) = H₂ (0, v))
    (hFjinit :
      (fderivWithin ℝ F₁ (closedCoordTriangle 0 B) (0, v)) (0, 1) =
      (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) (0, v)) (0, 1))
    (hHjinit :
      (fderivWithin ℝ H₁ (closedCoordTriangle 0 B) (0, v)) (0, 1) =
      (fderivWithin ℝ H₂ (closedCoordTriangle 0 B) (0, v)) (0, 1)) :
    |F₁ (u, v) - F₂ (u, v)| + |H₁ (u, v) - H₂ (u, v)| +
      |(fderivWithin ℝ F₁ (closedCoordTriangle 0 B) (u, v)) (0, 1) -
        (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) (u, v)) (0, 1)| +
      |(fderivWithin ℝ H₁ (closedCoordTriangle 0 B) (u, v)) (0, 1) -
        (fderivWithin ℝ H₂ (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
    ∫ s in (0 : ℝ)..u,
      horizontalFourSourceSummand B G₁ G₂ Q₁ Q₂ (s, v) := by
  let K := closedCoordTriangle 0 B
  let a : ℝ → ℝ := fun s => |G₁ (s, v) - G₂ (s, v)|
  let b : ℝ → ℝ := fun s => |Q₁ (s, v) - Q₂ (s, v)|
  let c : ℝ → ℝ := fun s =>
    |(fderivWithin ℝ G₁ K (s, v)) (0, 1) -
      (fderivWithin ℝ G₂ K (s, v)) (0, 1)|
  let d : ℝ → ℝ := fun s =>
    |(fderivWithin ℝ Q₁ K (s, v)) (0, 1) -
      (fderivWithin ℝ Q₂ K (s, v)) (0, 1)|
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) K := by
    intro s hs
    exact ⟨hs.1, hs.2.trans huv, hv⟩
  have hpath : ContinuousOn (fun s : ℝ => (s, v)) (Icc 0 u) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hcont (J : ℝ × ℝ → ℝ) (hJ : ContinuousOn J K) :
      ContinuousOn (fun s => J (s, v)) (Icc 0 u) :=
    hJ.comp hpath hmap
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hjet (J : ℝ × ℝ → ℝ) (hJ : ContDiffOn ℝ 1 J K) :
      ContinuousOn (fun p => (fderivWithin ℝ J K p) (0, 1)) K :=
    (hJ.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have ha : IntervalIntegrable a volume 0 u :=
    ((hcont G₁ hG₁.continuousOn).sub
      (hcont G₂ hG₂.continuousOn)).abs.intervalIntegrable_of_Icc hu
  have hb : IntervalIntegrable b volume 0 u :=
    ((hcont Q₁ hQ₁.continuousOn).sub
      (hcont Q₂ hQ₂.continuousOn)).abs.intervalIntegrable_of_Icc hu
  have hc : IntervalIntegrable c volume 0 u :=
    ((hcont _ (hjet G₁ hG₁)).sub
      (hcont _ (hjet G₂ hG₂))).abs.intervalIntegrable_of_Icc hu
  have hd : IntervalIntegrable d volume 0 u :=
    ((hcont _ (hjet Q₁ hQ₁)).sub
      (hcont _ (hjet Q₂ hQ₂))).abs.intervalIntegrable_of_Icc hu
  have hfirst := horizontal_value_difference_le_integral
    hB hF₁ hF₂ hG₁ hG₂ hFu₁ hFu₂ hu huv hv hFinit
  have hsecond := horizontal_value_difference_le_integral
    hB hH₁ hH₂ hQ₁ hQ₂ hHu₁ hHu₂ hu huv hv hHinit
  have hthird := horizontal_vertical_jet_difference_le_integral
    hB hF₁ hF₂ hG₁ hG₂ hFu₁ hFu₂ hu huv hv hFjinit
  have hfourth := horizontal_vertical_jet_difference_le_integral
    hB hH₁ hH₂ hQ₁ hQ₂ hHu₁ hHu₂ hu huv hv hHjinit
  have hsum : (∫ s in (0 : ℝ)..u,
      horizontalFourSourceSummand B G₁ G₂ Q₁ Q₂ (s, v)) =
      (∫ s in (0 : ℝ)..u, a s) +
      (∫ s in (0 : ℝ)..u, b s) +
      (∫ s in (0 : ℝ)..u, c s) +
      (∫ s in (0 : ℝ)..u, d s) := by
    change (∫ s in (0 : ℝ)..u, a s + b s + c s + d s) = _
    rw [intervalIntegral.integral_add (ha.add hb |>.add hc) hd]
    rw [intervalIntegral.integral_add (ha.add hb) hc]
    rw [intervalIntegral.integral_add ha hb]
  rw [hsum]
  dsimp [a, b, c, d] at *
  linarith only [hfirst, hsecond, hthird, hfourth]

end ChristodoulouBV.C1Solution

end
