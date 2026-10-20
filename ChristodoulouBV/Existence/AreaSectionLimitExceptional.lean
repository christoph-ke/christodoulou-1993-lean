module

public import ChristodoulouBV.Existence.AreaSectionLimitCore
import Mathlib.Tactic

/-!
# A common exceptional set from transverse control

Separate BV sections do not by themselves give a common countable
exceptional set. Uniform Lipschitz control in the other coordinate
allows the exceptional sets on a countable dense set of sections to
control every section.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- A family of real BV functions which is uniformly Lipschitz in a
separable transverse parameter has one countable set containing the
discontinuities of every section. -/
theorem exists_common_exceptional_set_of_uniform_lipschitz
    {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    {F : X → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hBV : ∀ x, BoundedVariationOn (F x) univ)
    (hLip : ∀ x z t, dist (F x t) (F z t) ≤ K * dist x z) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ t ∉ S, ∀ x, ContinuousAt (F x) t := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  let S := ⋃ x ∈ D, {t | ¬ContinuousAt (F x) t}
  have hSc : S.Countable := hDc.biUnion fun x _ => (hBV x).countable_not_continuousAt
  refine ⟨S, hSc, ?_⟩
  intro t ht x
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hη : 0 < ε / (4 * (K + 1)) := div_pos hε (by linarith only [hK])
  obtain ⟨z, hzD, hxz⟩ := hDd.exists_dist_lt x hη
  have hzt : ContinuousAt (F z) t := by
    by_contra hn
    exact ht (mem_iUnion₂.mpr ⟨z, hzD, hn⟩)
  obtain ⟨δ, hδ, hδcont⟩ := Metric.continuousAt_iff.mp hzt (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hsmall : K * dist x z < ε / 4 := by
    have hdist := dist_nonneg (x := x) (y := z)
    have hmul := (lt_div_iff₀ (by linarith only [hK] : 0 < 4 * (K + 1))).mp hxz
    nlinarith only [hmul, hdist, hK]
  calc
    dist (F x y) (F x t) ≤ dist (F x y) (F z y) + dist (F z y) (F x t) :=
      dist_triangle _ _ _
    _ ≤ dist (F x y) (F z y) + (dist (F z y) (F z t) + dist (F z t) (F x t)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ ≤ K * dist x z + (dist (F z y) (F z t) + K * dist x z) := by
      rw [dist_comm (F z t) (F x t)]
      exact add_le_add (hLip x z y) (add_le_add le_rfl (hLip x z t))
    _ < ε := by linarith only [hδcont hy, hsmall]

/-- The same common-set argument on a compact section interval. Constant
extension is used only to invoke the global BV discontinuity theorem. -/
theorem exists_common_exceptional_set_on_interval
    {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    {F : X → ℝ → ℝ} {K a b : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hBV : ∀ x, BoundedVariationOn (F x) (Icc a b))
    (hLip : ∀ x z t, t ∈ Icc a b → dist (F x t) (F z t) ≤ K * dist x z) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ t ∈ Ioo a b, t ∉ S → ∀ x, ContinuousAt (F x) t := by
  let G := fun x => Function.extendIcc (F x) hab
  obtain ⟨S, hSc, hS⟩ := exists_common_exceptional_set_of_uniform_lipschitz hK
    (fun x => BoundedVariationOn.extendIcc_boundedVariationOn hab (hBV x))
    (F := G) (fun x z t => hLip x z (Set.projIcc a b hab t) (Set.projIcc a b hab t).property)
  refine ⟨S, hSc, fun t ht hts x => (hS t hts x).congr_of_eventuallyEq ?_⟩
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
  exact (BoundedVariationOn.extendIcc_of_mem hab ⟨hv.1.le, hv.2.le⟩).symm

end ChristodoulouBV

end
