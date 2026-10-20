module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointGeneric
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceNuDerivative
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalarDerivative
import ChristodoulouBV.Uniqueness.ExtensionFamily
import ChristodoulouBV.Uniqueness.ExtensionLocalRadius
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Joint terminal traces of the incoming and scalar fields

The generic terminal rectangle argument applies to `ν`, `φ`, and `ζ` using
the cutoff-independent outgoing derivative estimates.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The compatible old family has jointly continuous terminal traces of
`ν`, `φ`, and `ζ` on every closed off-axis rectangle. -/
theorem exists_nu_phi_zeta_terminal_traces_on_rectangle
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ nuTrace phiTrace zetaTrace : ℝ × ℝ → ℝ,
      ContinuousOn nuTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn phiTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn zetaTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          nuTrace (u, v) = (S b).nu u v ∧
          phiTrace (u, v) = (S b).phi u v ∧
          zetaTrace (u, v) = (S b).zeta u v) := by
  obtain ⟨Cν, hCν, hν⟩ :=
    exists_uniform_nu_outgoing_derivative_bound_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨B, N, hB, hN, hscalar⟩ :=
    exists_uniform_scalar_outgoing_derivative_bounds_before_star
      hu₀ hα hfamily hε1 htail
  have hφM : 0 ≤ B / 4 := div_nonneg hB (by norm_num)
  have hζM : 0 ≤ N * B / 4 :=
    div_nonneg (mul_nonneg hN hB) (by norm_num)
  obtain ⟨nuTrace, hνcont, hνmatch⟩ :=
    exists_joint_terminal_trace_of_compatible_c1_family
      (F := fun b p => (S b).nu p.1 p.2)
      ha haBar hBarStar hCν
      (by
        intro b₁ hb₁ b₂ hb₂ u hu v hv
        have hp₁ : (u, v) ∈ developmentWithInitialEdge b₁ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
            hv.2.trans_le (min_le_left _ _)⟩
        have hp₂ : (u, v) ∈ developmentWithInitialEdge b₂ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
            hv.2.trans_le (min_le_right _ _)⟩
        exact (family_fields_eq_on_common_development hfamily hb₁ hb₂
          ⟨hp₁, hp₂⟩).2.2.2.2.1)
      (by
        intro b hb T hT hTb
        exact (C1Solution.five_fields_contDiffOn hT hTb (hfamily b hb).1).2.1)
      (by
        intro b hb u hu v hv
        exact hν b hb u v hu.1 (hu.2.trans_lt (haBar.trans hv.1)) hv.2)
  obtain ⟨phiTrace, hφcont, hφmatch⟩ :=
    exists_joint_terminal_trace_of_compatible_c1_family
      (F := fun b p => (S b).phi p.1 p.2)
      ha haBar hBarStar hφM
      (by
        intro b₁ hb₁ b₂ hb₂ u hu v hv
        have hp₁ : (u, v) ∈ developmentWithInitialEdge b₁ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
            hv.2.trans_le (min_le_left _ _)⟩
        have hp₂ : (u, v) ∈ developmentWithInitialEdge b₂ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
            hv.2.trans_le (min_le_right _ _)⟩
        exact (family_fields_eq_on_common_development hfamily hb₁ hb₂
          ⟨hp₁, hp₂⟩).2.1)
      (by
        intro b hb T hT hTb
        exact (C1Solution.five_fields_contDiffOn hT hTb (hfamily b hb).1).2.2.1)
      (by
        intro b hb u hu v hv
        have hOpen : IsOpen (openCoordTriangle 0 b) := by
          rw [← interior_closedCoordTriangle]
          exact isOpen_interior
        have hSubset : openCoordTriangle 0 b ⊆
            developmentWithInitialEdge b := by
          intro p hp
          exact ⟨hp.1.le, hp.2.1, hp.2.2⟩
        have hp : (u, v) ∈ interior (developmentWithInitialEdge b) :=
          (hOpen.subset_interior_iff.mpr hSubset)
            ⟨hu.1, hu.2.trans_lt (haBar.trans hv.1), hv.2⟩
        rw [(phi_hasDerivAt_v_of_c1_interior (hfamily b hb).1 hp).deriv]
        exact (hscalar b hb u v hu.1
          (hu.2.trans_lt (haBar.trans hv.1)) hv.2).1)
  obtain ⟨zetaTrace, hζcont, hζmatch⟩ :=
    exists_joint_terminal_trace_of_compatible_c1_family
      (F := fun b p => (S b).zeta p.1 p.2)
      ha haBar hBarStar hζM
      (by
        intro b₁ hb₁ b₂ hb₂ u hu v hv
        have hp₁ : (u, v) ∈ developmentWithInitialEdge b₁ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
            hv.2.trans_le (min_le_left _ _)⟩
        have hp₂ : (u, v) ∈ developmentWithInitialEdge b₂ :=
          ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
            hv.2.trans_le (min_le_right _ _)⟩
        have hfields := family_fields_eq_on_common_development
          hfamily hb₁ hb₂ ⟨hp₁, hp₂⟩
        simp only [Fields.zeta, hfields.2.2.2.2.2.2,
          hfields.2.2.2.2.1, hfields.2.1])
      (by
        intro b hb T hT hTb
        exact (C1Solution.five_fields_contDiffOn hT hTb (hfamily b hb).1).2.2.2.2)
      (by
        intro b hb u hu v hv
        exact (hscalar b hb u v hu.1
          (hu.2.trans_lt (haBar.trans hv.1)) hv.2).2)
  refine ⟨nuTrace, phiTrace, zetaTrace,
    hνcont, hφcont, hζcont, ?_⟩
  intro b hb u hu v hv
  exact ⟨hνmatch b hb u hu v hv,
    hφmatch b hb u hu v hv, hζmatch b hb u hu v hv⟩

end ChristodoulouBV.Uniqueness

end
