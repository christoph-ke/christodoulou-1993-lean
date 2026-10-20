module

public import ChristodoulouBV.Existence.ScalarLimitCore
public import ChristodoulouBV.BVSolution.PrimitiveCalculus
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Scalar primitives and absolute continuity of the limit

The scalar-radius primitive equations pass by dominated convergence on
every closed null segment. Division by the strictly positive radius then
gives the exact sectionwise absolute continuity required by `IsBVSolution`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Both scalar-radius primitives survive on the common subsequence.
They retain the raw Helly point values of α and β. -/
theorem scalar_radius_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (fun v => d.scalarRadius (u, v)) (d.alpha u) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.scalarRadius (u, v)) (fun u => d.beta u v) a b := by
  obtain ⟨_, hα, hβ, _⟩ := alpha_beta_limit h d
  have hV := lt_top_iff_ne_top.mpr (scalarVariationBound_ne_top hD C)
  constructor
  · intro u a b hab hs
    have haU : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    have hBV : BoundedVariationOn (d.alpha u) (Ioi u) :=
      ne_of_lt ((hα u haU.1).trans_lt hV)
    apply interval_primitive_limit hab
      (fun n => (h (d.subsequence n)).solution.solution.scalar_radius_out u a b hab hs)
      (M := 2 * D.toReal + C / 2)
    · intro n t ht
      exact (h (d.subsequence n)).amplitudes.alpha (u, t) (hs ⟨rfl, ht⟩)
    · exact d.scalarRadius_limit.tendsto_at haU
    · exact d.scalarRadius_limit.tendsto_at (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)
    · intro t ht
      exact d.alpha_limit (u, t) (hs ⟨rfl, ht⟩)
    · apply hBV.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)).2
  · intro v a b hab hs
    have haU : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
    have hBV : BoundedVariationOn (fun u => d.beta u v) (Ico 0 v) :=
      ne_of_lt ((hβ v (haU.1.trans_lt haU.2)).trans_lt hV)
    apply interval_primitive_limit hab
      (fun n => (h (d.subsequence n)).solution.solution.scalar_radius_in v a b hab hs)
      (M := 4 * D.toReal + 2 * C / 3)
    · intro n t ht
      exact (h (d.subsequence n)).amplitudes.beta (t, v) (hs ⟨ht, rfl⟩)
    · exact d.scalarRadius_limit.tendsto_at haU
    · exact d.scalarRadius_limit.tendsto_at (hs ⟨⟨hab, le_rfl⟩, rfl⟩)
    · intro t ht
      exact d.beta_limit (t, v) (hs ⟨ht, rfl⟩)
    · apply hBV.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (show (t, v) ∈ globalDomain from hs ⟨ht, rfl⟩)

/-- The scalar primitives have exactly the frozen `r * φ` shape on
every outgoing and incoming closed null segment. -/
theorem s6_scalar_primitive
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (fun v => d.rawFields.r u v * d.rawFields.phi u v)
        (d.rawFields.alpha u) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.rawFields.r u v * d.rawFields.phi u v)
        (fun u => d.rawFields.beta u v) a b := by
  obtain ⟨hout, hin⟩ := scalar_radius_primitive_limit h hD d
  constructor
  · intro u a b hab hs
    obtain ⟨hi, he⟩ := hout u a b hab hs
    refine ⟨hi, ?_⟩
    change d.rawFields.r u b * d.rawFields.phi u b -
      d.rawFields.r u a * d.rawFields.phi u a = _
    rw [show d.rawFields.r u b * d.rawFields.phi u b = d.scalarRadius (u, b) from
      d.radius_mul_scalar h (hs ⟨rfl, ⟨hab, le_rfl⟩⟩),
      show d.rawFields.r u a * d.rawFields.phi u a = d.scalarRadius (u, a) from
      d.radius_mul_scalar h (hs ⟨rfl, ⟨le_rfl, hab⟩⟩)]
    exact he
  · intro v a b hab hs
    obtain ⟨hi, he⟩ := hin v a b hab hs
    refine ⟨hi, ?_⟩
    change d.rawFields.r b v * d.rawFields.phi b v -
      d.rawFields.r a v * d.rawFields.phi a v = _
    rw [show d.rawFields.r b v * d.rawFields.phi b v = d.scalarRadius (b, v) from
      d.radius_mul_scalar h (hs ⟨⟨hab, le_rfl⟩, rfl⟩),
      show d.rawFields.r a v * d.rawFields.phi a v = d.scalarRadius (a, v) from
      d.radius_mul_scalar h (hs ⟨⟨le_rfl, hab⟩, rfl⟩)]
    exact he

/-- The quotient scalar is absolutely continuous on every closed null
segment, including segments starting on the initial edge. -/
theorem scalar_limit_absolute_continuity
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (d.rawFields.phi u) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (fun u => d.rawFields.phi u v) a b := by
  obtain ⟨hψout, hψin⟩ := scalar_radius_primitive_limit h hD d
  obtain ⟨hrout, hrin⟩ := radius_primitive_limit h hD d
  constructor
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    have hψ := (IntervalPrimitive.ac_ae_of_subsegments hab
      (fun x y hax hxy hyb => hψout u x y hxy
        ((outSeg_subsegment hax hxy hyb).trans hs))).1
    have hr := (IntervalPrimitive.ac_ae_of_subsegments hab
      (fun x y hax hxy hyb => hrout u x y hxy
        ((outSeg_subsegment hax hxy hyb).trans hs))).1
    apply (hψ.div_and_ae_deriv hr (c := (a - u) / 3)
      (div_pos (sub_pos.mpr hp.2) (by norm_num)) ?_).1
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htU := hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)
    exact (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 u) (by norm_num)).trans
      ((d.radius_lower h htU).trans (le_abs_self _))
  · intro v a b hab hs
    have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
    have hψ := (IntervalPrimitive.ac_ae_of_subsegments hab
      (fun x y hax hxy hyb => hψin v x y hxy
        ((inSeg_subsegment hax hxy hyb).trans hs))).1
    have hr := (IntervalPrimitive.ac_ae_of_subsegments hab
      (fun x y hax hxy hyb => hrin v x y hxy
        ((inSeg_subsegment hax hxy hyb).trans hs))).1
    apply (hψ.div_and_ae_deriv hr (c := (v - b) / 3)
      (div_pos (sub_pos.mpr hp.2) (by norm_num)) ?_).1
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htU := hs (show (t, v) ∈ inSeg v a b from ⟨ht, rfl⟩)
    exact (div_le_div_of_nonneg_right (sub_le_sub_left ht.2 v) (by norm_num)).trans
      ((d.radius_lower h htU).trans (le_abs_self _))

end ChristodoulouBV

end
