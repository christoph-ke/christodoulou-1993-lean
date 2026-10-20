module

public import ChristodoulouBV.Existence.AreaLimitBoundsExhaustion
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Finite BV area on shrinking tails

Global finiteness is supplied by the uniform smooth estimates. The
continuity results here therefore need no additional finite-area premise.
The literal triangles in (6.13)--(6.17) shrink monotonically to the empty
set. More general moving wedges can use nested containing tails.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Every subset of the global domain has finite carrier area, with the
same quantitative bound as the whole domain. -/
theorem bv_analytic_area_subset_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {E : Set (ℝ × ℝ)}
    (hE : E ⊆ globalDomain) :
    bvAnalyticArea h hD d k E ≤ areaPairBound D k ∧
      bvAnalyticArea h hD d k E ≠ ∞ := by
  have hb := (measure_mono hE).trans (bv_analytic_area_global_bound h hD d k)
  exact ⟨hb, ne_top_of_le_ne_top (area_pair_bound_ne_top hD k) hb⟩

/-- Continuity on nested measurable tails in the global domain. The
finite initial area is a consequence, rather than an extra premise. -/
theorem bv_analytic_area_shrinking
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (E : ℕ → Set (ℝ × ℝ))
    (hE : ∀ n, MeasurableSet (E n)) (hm : Antitone E)
    (hsub : E 0 ⊆ globalDomain) (he : (⋂ n, E n) = ∅) :
    Tendsto (fun n => bvAnalyticArea h hD d k (E n)) atTop (𝓝 0) :=
  bv_analytic_area_continuity h hD d k E hE hm
    (bv_analytic_area_subset_finite h hD d k hsub).2 he

/-- The continuous-parameter shrinking-tail rule. It is enough that one
positive tail is contained in the global domain; this handles incoming
triangles whose lower corner is nonnegative only for small parameters. -/
theorem bv_analytic_area_shrinking_right
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (E : ℝ → Set (ℝ × ℝ))
    (hE : ∀ ε, 0 < ε → MeasurableSet (E ε))
    (hm : ∀ ε η, 0 < ε → ε ≤ η → E ε ⊆ E η)
    (hsub : ∃ ε, 0 < ε ∧ E ε ⊆ globalDomain)
    (he : (⋂ ε > 0, E ε) = ∅) :
    Tendsto (fun ε => bvAnalyticArea h hD d k (E ε)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ε, hε, hsub⟩ := hsub
  have ht := tendsto_measure_biInter_gt (μ := bvAnalyticArea h hD d k)
    (s := E) (fun r hr => (hE r hr).nullMeasurableSet) hm
    ⟨ε, hε, (bv_analytic_area_subset_finite h hD d k hsub).2⟩
  simpa only [he, measure_empty, Function.comp_def] using ht

/-- The outgoing triangles in (6.13)--(6.15) have area tending to zero
for each of the four pairs, including at the initial vertex. -/
theorem bv_analytic_area_outgoing_triangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε => bvAnalyticArea h hD d k (openCoordTriangle a (a + ε)))
      (𝓝[>] 0) (𝓝 0) := by
  apply bv_analytic_area_shrinking_right h hD d k
  · intro ε _
    change MeasurableSet {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2 ∧ p.2 < a + ε}
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  · intro ε η _ hεη p hp
    exact ⟨hp.1, hp.2.1, by linarith only [hp.2.2, hεη]⟩
  · exact ⟨1, zero_lt_one, fun _ hp => ⟨ha.trans hp.1.le, hp.2.1⟩⟩
  · apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp1 := mem_iInter.mp (mem_iInter.mp hp 1) zero_lt_one
    have hg : 0 < p.2 - a := sub_pos.mpr (hp1.1.trans hp1.2.1)
    have hp2 := mem_iInter.mp (mem_iInter.mp hp ((p.2 - a) / 2))
      (by linarith only [hg])
    change a < p.1 ∧ p.1 < p.2 ∧ p.2 < a + (p.2 - a) / 2 at hp2
    linarith only [hp2.2.2, hg]

/-- The incoming triangles in (6.16)--(6.17) have area tending to zero.
Finiteness is obtained from the tail at `ε=a/2`, inside the global domain. -/
theorem bv_analytic_area_incoming_triangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => bvAnalyticArea h hD d k (openCoordTriangle (a - ε) a))
      (𝓝[>] 0) (𝓝 0) := by
  apply bv_analytic_area_shrinking_right h hD d k
  · intro ε _
    change MeasurableSet {p : ℝ × ℝ | a - ε < p.1 ∧ p.1 < p.2 ∧ p.2 < a}
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  · intro ε η _ hεη p hp
    exact ⟨(sub_le_sub_left hεη a).trans_lt hp.1, hp.2.1, hp.2.2⟩
  · refine ⟨a / 2, by linarith only [ha], fun p hp => ⟨?_, hp.2.1⟩⟩
    change a - a / 2 < p.1 ∧ p.1 < p.2 ∧ p.2 < a at hp
    linarith only [ha, hp.1]
  · apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp1 := mem_iInter.mp (mem_iInter.mp hp 1) zero_lt_one
    have hg : 0 < a - p.1 := sub_pos.mpr (hp1.2.1.trans hp1.2.2)
    have hp2 := mem_iInter.mp (mem_iInter.mp hp ((a - p.1) / 2))
      (by linarith only [hg])
    change a - (a - p.1) / 2 < p.1 ∧ p.1 < p.2 ∧ p.2 < a at hp2
    linarith only [hp2.1, hg]

end ChristodoulouBV

end
