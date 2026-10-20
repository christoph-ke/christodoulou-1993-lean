module

public import ChristodoulouBV.Existence.ScalarLimitCompact
public import ChristodoulouBV.Existence.ScalarLimitRightTV
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Scalar limits for the BV existence construction

The scalar limit uses the single shared selection for all seven fields. The scalar
radius converges uniformly on closed finite triangles and has zero axis
trace. The quotient scalar converges locally uniformly off the axis and
is absolutely continuous on every closed null segment.

`alpha_beta_limit` and `data_trace_limit` retain the raw Helly values,
including every prescribed value of arbitrary BV data. The separate
right-v α and right-u β representatives have sectionwise a.e. convergence
and preserve both scalar-radius primitives. For right-continuous data,
`data_trace_limit_of_right_continuous` retains the literal initial values
of the same canonical field record used by the quantitative existence construction.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Scalar compactness and regularity on the shared existence carrier. The raw
amplitude bound retains the smooth approximants' common offset. All numeric coefficients are
universal and no further subsequence is extracted. -/
theorem scalar_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    StrictMono d.subsequence ∧ Continuous d.scalarRadius ∧
    TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => (T (d.subsequence n)).r p.1 p.2 *
        (T (d.subsequence n)).phi p.1 p.2) d.scalarRadius atTop globalDomain ∧
    (∀ b : ℝ, TendstoUniformlyOn (fun n => scalarRadiusWithAxis (T (d.subsequence n)))
      d.scalarRadius atTop (closedCoordTriangle 0 b)) ∧
    (∀ x : ℝ, 0 ≤ x → d.scalarRadius (x, x) = 0) ∧
    ContinuousOn (fun p => d.rawFields.phi p.1 p.2) globalDomain ∧
    TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => (T (d.subsequence n)).phi p.1 p.2)
      (fun p => d.rawFields.phi p.1 p.2) atTop globalDomain ∧
    (∀ p ∈ globalDomain, |d.rawFields.phi p.1 p.2| ≤ 6 * D.toReal + C) ∧
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (d.rawFields.phi u) a b) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (fun u => d.rawFields.phi u v) a b) := by
  obtain ⟨hout, hin⟩ := scalar_limit_absolute_continuity h hD d
  exact ⟨d.strictMono, d.scalarRadius_continuous, d.scalarRadius_limit,
    d.scalarRadius_uniform_on_closed_triangle h, fun _ hx => d.scalarRadius_axis h hx,
    d.scalar_continuousOn h, d.scalar_locally_uniform h,
    fun _ hp => d.scalar_amplitude h hp, hout, hin⟩

end ChristodoulouBV

end
