module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointGeneric
import ChristodoulouBV.Uniqueness.ExtensionFamily
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Joint off-axis terminal radius

The canonical radius is C¹ on every finite closed triangle and equals the
frozen radius off the axis. Its outgoing derivative is the expansion `λ`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The old radii have one jointly continuous terminal trace on every closed
off-axis rectangle. -/
theorem exists_radius_terminal_trace_on_rectangle
    {alpha₀ : ℝ → ℝ} {vStar a vBar : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ rTrace : ℝ × ℝ → ℝ,
      ContinuousOn rTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          rTrace (u, v) = (S b).r u v := by
  have hEq (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) vStar)
      (u : ℝ) (hu : u ∈ Icc 0 a)
      (v : ℝ) (hv : v ∈ Ico vBar b) :
      C1Solution.canonicalRadius (S b) (u, v) = (S b).r u v := by
    let T : ℝ := (v + b) / 2
    have hT : 0 < T := by dsimp [T]; linarith only [ha, haBar, hv.1, hv.2]
    have hTb : T < b := by dsimp [T]; linarith only [hv.2]
    have hvT : v ≤ T := by dsimp [T]; linarith only [hv.2]
    exact C1Solution.canonicalRadius_eq_radius hT hTb
      (hfamily b hb).1 hu.1 (hu.2.trans_lt (haBar.trans_le hv.1)) hvT
  obtain ⟨R, hR, hRmatch⟩ :=
    exists_joint_terminal_trace_of_compatible_c1_family
      (F := fun b p => C1Solution.canonicalRadius (S b) p)
      ha haBar hBarStar (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by
        intro b₁ hb₁ b₂ hb₂ u hu v hv
        have hv₁ : v ∈ Ico vBar b₁ := ⟨hv.1, hv.2.trans_le (min_le_left _ _)⟩
        have hv₂ : v ∈ Ico vBar b₂ := ⟨hv.1, hv.2.trans_le (min_le_right _ _)⟩
        rw [hEq b₁ hb₁ u hu v hv₁, hEq b₂ hb₂ u hu v hv₂]
        have hp₁ : (u, v) ∈ developmentWithInitialEdge b₁ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv₁.2⟩
        have hp₂ : (u, v) ∈ developmentWithInitialEdge b₂ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv₂.2⟩
        exact (family_fields_eq_on_common_development hfamily hb₁ hb₂
          ⟨hp₁, hp₂⟩).1)
      (by
        intro b hb T hT hTb
        exact C1Solution.canonicalRadius_contDiffOn hT hTb (hfamily b hb).1)
      (by
        intro b hb u hu v hv
        let T : ℝ := (v + b) / 2
        have hT : 0 < T := by dsimp [T]; linarith only [ha, haBar, hv.1, hv.2]
        have hTb : T < b := by dsimp [T]; linarith only [hv.2]
        have hvT : v < T := by dsimp [T]; linarith only [hv.2]
        have huv : u < v := hu.2.trans_lt (haBar.trans hv.1)
        have hpK : (u, v) ∈ closedCoordTriangle 0 T :=
          ⟨hu.1.le, huv.le, hvT.le⟩
        have hder := vertical_hasDerivAt_of_closed_jet
          (C1Solution.canonicalRadius_contDiffOn hT hTb (hfamily b hb).1)
          hu.1.le huv hvT
          (C1Solution.canonicalRadius_vertical_jet hT hTb (hfamily b hb).1 hpK)
        rw [hder.deriv, abs_of_pos]
        · exact lam_le_half_of_initial_gauge (hfamily b hb).1
            (fun w hw => ((hfamily b hb).2 w hw).1) hu.1.le huv hv.2
        · exact (hfamily b hb).1.solution.lam_pos (u, v)
            ⟨hu.1.le, huv, hv.2⟩)
  refine ⟨R, hR, ?_⟩
  intro b hb u hu v hv
  exact (hRmatch b hb u hu v hv).trans (hEq b hb u hu v hv)

end ChristodoulouBV.Uniqueness

end
