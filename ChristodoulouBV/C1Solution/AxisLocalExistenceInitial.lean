module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceClassical
public import ChristodoulouBV.C1Solution.AxisLocalExistenceEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Local frozen C¹ solution from regular initial data

The half-line datum is extended to a global edge representative and bounded
on a fixed compact segment. Picard existence, reconstruction, and the
classical-to-frozen bridge then give the initial local solution.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Regular initial scalar data give the bounded global edge data required by
the axis Picard box on a fixed unit segment. -/
theorem exists_initial_edge_data {alpha₀ : ℝ → ℝ}
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0)) :
    ∃ M : ℝ, 1 ≤ M ∧
      EdgeData 0 1 M (fun _ => 1 / 2)
        (fun v => 2 * initialEdgeExtension alpha₀ v) := by
  let hEdge : ℝ → ℝ := fun v => 2 * initialEdgeExtension alpha₀ v
  have hhC1 : ContDiff ℝ 1 hEdge :=
    contDiff_const.mul (initialEdgeExtension_c1 hα)
  obtain ⟨C₀, hC₀⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hhC1.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hhC1.continuous_deriv_one.continuousOn
  let M := max 1 (max C₀ C₁)
  have hM : 1 ≤ M := le_max_left _ _
  refine ⟨M, hM, ?_⟩
  refine {
    g_c1 := contDiff_const
    h_c1 := hhC1
    g_lower := ?_
    g_upper := ?_
    g_deriv_bound := ?_
    h_bound := ?_
    h_deriv_bound := ?_ }
  · intro v _
    norm_num
  · intro v _
    norm_num
  · intro v _
    have hM0 : 0 ≤ M := le_trans (by norm_num) hM
    simpa using hM0
  · intro v hv
    have h : |hEdge v| ≤ C₀ := by simpa only [Real.norm_eq_abs] using hC₀ v hv
    exact h.trans ((le_max_left C₀ C₁).trans (le_max_right 1 (max C₀ C₁)))
  · intro v hv
    have h : |deriv hEdge v| ≤ C₁ := by
      simpa only [Real.norm_eq_abs] using hC₁ v hv
    exact h.trans ((le_max_right C₀ C₁).trans (le_max_right 1 (max C₀ C₁)))

end ChristodoulouBV.AxisPicard

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.AxisPicard

/-- Every regular initial scalar datum has a short axis triangle carrying a
frozen C¹ solution with the exact radius and scalar initial traces. -/
theorem exists_local_c1_solution (alpha₀ : ℝ → ℝ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0)) :
    ∃ v₁ : ℝ, 0 < v₁ ∧ ∃ T : Fields,
      IsC1Solution (developmentWithInitialEdge v₁) T ∧
      ∀ v ∈ Ioo (0 : ℝ) v₁,
        T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v := by
  let hEdge : ℝ → ℝ := fun v => 2 * initialEdgeExtension alpha₀ v
  obtain ⟨M, hM, D⟩ := exists_initial_edge_data hα
  let b := min 1 ((numericalLedger M).lifetime M)
  have hb : 0 < b := lt_min (by norm_num) (numerical_lifetime_pos hM)
  have hbunit : b ≤ 1 := min_le_left _ _
  have hsmall : b ≤ (numericalLedger M).lifetime M := min_le_right _ _
  have D' : EdgeData 0 b M (fun _ => 1 / 2) hEdge := {
    g_c1 := D.g_c1
    h_c1 := D.h_c1
    g_lower := fun v hv => D.g_lower v ⟨hv.1, hv.2.trans hbunit⟩
    g_upper := fun v hv => D.g_upper v ⟨hv.1, hv.2.trans hbunit⟩
    g_deriv_bound := fun v hv => D.g_deriv_bound v ⟨hv.1, hv.2.trans hbunit⟩
    h_bound := fun v hv => D.h_bound v ⟨hv.1, hv.2.trans hbunit⟩
    h_deriv_bound := fun v hv => D.h_deriv_bound v ⟨hv.1, hv.2.trans hbunit⟩ }
  obtain ⟨x, hfixed, _⟩ :=
    exists_reconstructed_fields D' hb hM (by simpa using hsmall)
  let S := x.1.toTriple.toFields
  let T := clipFieldsToClosedTriangle S b
  have hsol : IsC1Solution (developmentWithInitialEdge b) S :=
    (x.isSolution_and_isC1Solution_initial hb hM hsmall D'.g_lower hfixed).2
  have hT : IsC1Solution (developmentWithInitialEdge b) T :=
    ((clipped_isSolution_and_isC1Solution_iff hb S).2).mp hsol
  refine ⟨b, hb, T, hT, ?_⟩
  intro v hv
  have hvcc : v ∈ Icc 0 b := ⟨hv.1.le, hv.2.le⟩
  have hpK : ((0 : ℝ), v) ∈ closedCoordTriangle 0 b :=
    by
      change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ v ∧ v ≤ b
      exact ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hclipr : T.r 0 v = S.r 0 v := by
    simp [T, clipFieldsToClosedTriangle, clipToClosedTriangle_eq_self hpK]
  have hclipα : T.alpha 0 v = S.alpha 0 v := by
    simp [T, clipFieldsToClosedTriangle, clipToClosedTriangle_eq_self hpK]
  constructor
  · rw [hclipr]
    exact x.radius_initial_gauge hvcc
  · rw [hclipα]
    have htrace := (x.reconstructed_edge_trace hvcc).2.2
    change S.alpha 0 v = (1 / 2 : ℝ) * hEdge v at htrace
    rw [htrace]
    change (1 / 2 : ℝ) * (2 * initialEdgeExtension alpha₀ v) = alpha₀ v
    rw [initialEdgeExtension_eq hv.1.le]
    ring

end ChristodoulouBV.C1Solution

end
