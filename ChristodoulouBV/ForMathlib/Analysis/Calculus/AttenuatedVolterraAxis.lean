module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraHorizontalDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Uniform diagonal estimates for attenuated Volterra integrals

Compactness gives a single modulus for the entire diagonal, including its
vertices. The source amplitude and its horizontal-jet amplitude may vary
along the diagonal.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- A continuous function on a compact closed coordinate triangle has one
modulus of continuity along the whole diagonal. -/
theorem uniform_diagonal_continuity
    {a b : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (closedCoordTriangle a b)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |F (u, v) - F (u, u)| < ε := by
  intro ε hε
  have huc := (isCompact_closedCoordTriangle a b)
    |>.uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u v hu huv hv hgap
  have hp : (u, v) ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
  have hdiag : (u, u) ∈ closedCoordTriangle a b := ⟨hu, le_rfl, huv.trans hv⟩
  have hdist : dist (u, v) (u, u) = v - u := by
    rw [dist_prod_same_left, Real.dist_eq]
    simp only [abs_of_nonneg (sub_nonneg.mpr huv)]
  have h := hmod (u, v) hp (u, u) hdiag (by simpa only [hdist] using hgap)
  simpa only [Real.dist_eq] using h

/-- A nonnegative linearly growing attenuation kernel has a quadratic
Volterra potential on every subinterval of a triangle ray. -/
theorem attenuation_integral_nonneg_le_half_sq
    {a b u s v K₀ : ℝ} {k : ℝ × ℝ → ℝ}
    (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b)
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hK₀ : 0 ≤ K₀)
    (hbound : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1)) :
    0 ≤ (∫ t in s..v, k (u, t)) ∧
      (∫ t in s..v, k (u, t)) ≤ K₀ * (v - u) ^ 2 / 2 := by
  have hseg : ∀ t ∈ Icc s v, (u, t) ∈ closedCoordTriangle a b := by
    intro t ht
    exact ⟨hu, hus.trans ht.1, ht.2.trans hv⟩
  have hi : IntervalIntegrable (fun t => k (u, t)) volume s v :=
    (hk.comp (continuous_const.prodMk continuous_id).continuousOn hseg)
      |>.intervalIntegrable_of_Icc hsv
  have hnonneg : 0 ≤ (∫ t in s..v, k (u, t)) :=
    intervalIntegral.integral_nonneg hsv (fun t ht => (hbound _ (hseg t ht)).1)
  have habs := abs_integral_le_half_sq_of_abs_le_linear hsv hK₀ hi (by
    intro t ht
    have h := hbound _ (hseg t ht)
    simpa only [abs_of_nonneg h.1] using h.2)
  exact ⟨hnonneg, by simpa only [abs_of_nonneg hnonneg] using habs⟩

/-- On the nonnegative half-line, the deviation of the decaying
exponential from one is bounded by its argument. -/
theorem abs_exp_neg_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x) - 1| ≤ x := by
  have hle : Real.exp (-x) ≤ 1 := (Real.exp_le_one_iff).2 (neg_nonpos.mpr hx)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith only [Real.one_sub_le_exp_neg x]

end intervalIntegral

end
