module

public import ChristodoulouBV.AreaEstimates.SmallDataLemma
public import ChristodoulouBV.AreaEstimates.LogTransportCore
public import ChristodoulouBV.AreaEstimates.LogTransportSliceCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Three-term variation on each unit null slice

The quotient, scalar, and logarithmic terms have one numerical coefficient
fixed before the solution.  The initial outgoing characteristic is included.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The real coefficient used for both three-term slice bounds. -/
noncomputable def s4SliceTVK : ℝ := 10 ^ 62

/-- The explicit value of the universal slice coefficient. -/
theorem s4SliceTVK_eq : s4SliceTVK = 10 ^ 62 := rfl

/-- The universal slice coefficient is positive. -/
theorem s4SliceTVK_pos : 0 < s4SliceTVK := by
  norm_num [s4SliceTVK]

private theorem initial_phi_variation_ne_top_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (S.phi 0) (Ioo (0 : ℝ) 1) ≠ ⊤ := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hφ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hφedge : ContDiffOn ℝ 1 (S.phi 0) (Icc 0 1) :=
    hφ.comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.phi 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        using hφedge).absolutelyContinuousOnInterval
  rw [AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
    (by norm_num : (0 : ℝ) ≤ 1) hAC]
  exact ENNReal.ofReal_ne_top

/-- The scalar variation on the initial outgoing characteristic is at most
twice the centered initial variation. -/
theorem s4_initial_phi_variation_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    eVariationOn (S.phi 0) (Ioo (0 : ℝ) 1) ≤ 2 * sourceD S := by
  have hvar := initial_phi_variation_le_sourceD H hr
  have hfinite := initial_phi_variation_ne_top_unit H
  have hDfinite := sourceD_ne_top_unit H
  have hreal : (eVariationOn (S.phi 0) (Ioo (0 : ℝ) 1)).toReal ≤
      (2 * sourceD S).toReal := by
    simpa [ENNReal.toReal_mul] using hvar
  exact (ENNReal.toReal_le_toReal hfinite
    (ENNReal.mul_ne_top (by norm_num) hDfinite)).mp hreal

/-- The normalized initial field has variation at most twice the initial
field variation, since the initial lapse is one half. -/
theorem s4_initial_quotient_variation_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    eVariationOn (fun v => S.alpha 0 v / S.lam 0 v) (Ioo (0 : ℝ) 1) ≤
      2 * sourceD S := by
  have hEq : EqOn (fun v => S.alpha 0 v / S.lam 0 v)
      (fun v => 2 * S.alpha 0 v) (Ioo (0 : ℝ) 1) := by
    intro v hv
    change S.alpha 0 v / S.lam 0 v = 2 * S.alpha 0 v
    rw [initial_lam_eq_of_gauge H hr hv]
    ring
  rw [eVariationOn.congr hEq]
  have hLip : LipschitzOnWith 2 (fun x : ℝ => 2 * x) Set.univ := by
    apply LipschitzWith.lipschitzOnWith
    exact LipschitzWith.of_dist_le_mul (by
      intro x y
      simp only [Real.dist_eq]
      rw [← mul_sub, abs_mul]
      norm_num)
  have h := hLip.comp_eVariationOn_le
    (fun v (_ : v ∈ Ioo (0 : ℝ) 1) => Set.mem_univ (S.alpha 0 v))
  convert h using 1 <;> norm_num [Function.comp_def, sourceD]

end ChristodoulouBV

end
