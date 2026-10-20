module

public import ChristodoulouBV.C1Solution.ExtractionAxisJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Derivatives of the regular-axis traces

The diagonal derivative is the sum of the two continuous coordinate jets.
The mixed transport jets vanish on the axis, yielding the derivative traces
used after (4.5a).
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

private theorem hasDerivAt_diagonal_of_contDiffOn {B : ℝ} (_hB : 0 < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) B) :
    HasDerivAt (fun t => f (t, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 B) (u, u)) (1, 0) +
        (fderivWithin ℝ f (closedCoordTriangle 0 B) (u, u)) (0, 1)) u := by
  let K := closedCoordTriangle 0 B
  have huK : (u, u) ∈ K := ⟨hu.1.le, le_rfl, hu.2.le⟩
  have hdiff : DifferentiableWithinAt ℝ f K (u, u) :=
    hf.differentiableOn (by norm_num) (u, u) huK
  have hpair : HasDerivAt (fun t : ℝ => (t, t)) (1, 1) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_id' u)
  have hnear : ∀ᶠ t in 𝓝 u, (t, t) ∈ K := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
    exact ⟨ht.1.le, le_rfl, ht.2.le⟩
  have hcomp := hdiff.hasFDerivWithinAt.comp_hasDerivAt
    (f := fun t : ℝ => (t, t)) u hpair hnear
  have hvec : ((1 : ℝ), (1 : ℝ)) =
      ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
    ext <;> norm_num
  rw [hvec, map_add] at hcomp
  simpa only [Function.comp_def] using hcomp

/-- The incoming expansion and scalar-radius derivative have the derivative
traces printed after (4.5a), with the corrected negative axis sign. -/
theorem axis_trace_derivatives {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) B) :
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (1, 0) =
      -deriv (fun t => S.lam t t) a ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (1, 0) =
      -deriv (fun t => S.alpha t t) a := by
  have haK : a ∈ Icc 0 B := ⟨ha.1.le, ha.2.le⟩
  obtain ⟨hlamU, _, halphaU, _⟩ :=
    C1Solution.four_mixed_axis_jets hB hBb H haK
  obtain ⟨hnuU, hbetaU⟩ :=
    C1Solution.incoming_axis_coordinate_jets hB hBb H haK
  have hLamTrace := (hasDerivAt_diagonal_of_contDiffOn hB
    (C1Solution.five_fields_contDiffOn hB hBb H).1 ha).deriv
  have hAlphaTrace := (hasDerivAt_diagonal_of_contDiffOn hB
    (C1Solution.alpha_contDiffOn hB hBb H) ha).deriv
  rw [hlamU, zero_add] at hLamTrace
  rw [halphaU, zero_add] at hAlphaTrace
  change deriv (fun t => S.lam t t) a = _ at hLamTrace
  change deriv (fun t => S.alpha t t) a = _ at hAlphaTrace
  rw [hLamTrace, hAlphaTrace]
  exact ⟨hnuU, hbetaU⟩

end ChristodoulouBV

end
