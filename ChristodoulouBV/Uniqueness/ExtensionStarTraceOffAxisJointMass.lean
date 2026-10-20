module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointGeneric
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointRadiusFloor
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalarDerivative
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import ChristodoulouBV.C1Solution.ExtractionMass
import ChristodoulouBV.Uniqueness.ExtensionFamily
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionLocalRadius
import ChristodoulouBV.Uniqueness.ExtensionLocalMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

/-!
# Joint terminal mass trace

The outgoing mass density is uniformly bounded on the old family. The common
terminal rectangle lemma then applies to the canonical mass.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Uniform outgoing mass derivative bound on the strict old union. -/
theorem exists_uniform_mass_outgoing_derivative_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |deriv ((S b).m u) v| ≤ M := by
  obtain ⟨B, _, hB, _, hscalar⟩ :=
    exists_uniform_scalar_outgoing_derivative_bounds_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε1 htail
  let T : ℝ := B / 4 * (vStar / 2)
  let M : ℝ := T ^ 2 / (2 * c)
  have hM : 0 ≤ M := div_nonneg (sq_nonneg _) (by positivity)
  refine ⟨M, hM, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  have hpU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, huv, hvb⟩
  have hp : (u, v) ∈ interior (developmentWithInitialEdge b) := by
    have hOpen : IsOpen (openCoordTriangle 0 b) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior
    have hSubset : openCoordTriangle 0 b ⊆
        developmentWithInitialEdge b := by
      intro p hp
      exact ⟨hp.1.le, hp.2.1, hp.2.2⟩
    exact (hOpen.subset_interior_iff.mpr hSubset) ⟨hu, huv, hvb⟩
  have hr : 0 < (S b).r u v := H.solution.radius_pos (u, v) hpU
  have hlam : 0 < (S b).lam u v := H.solution.lam_pos (u, v) hpU
  have hlamFloor : c ≤ (S b).lam u v := hfloor b hb u v hu.le huv hvb
  have hq : 0 ≤ 1 - 2 * (S b).m u v / (S b).r u v ∧
      1 - 2 * (S b).m u v / (S b).r u v ≤ 1 := by
    have hs := H.reduced_signs_of_c1 hpU
    constructor <;> linarith [hs.2.2.1, hs.2.2.2]
  have hrad : (S b).r u v ≤ vStar / 2 := by
    have hrad' := radius_antitone_on_incoming_of_c1 H
      (le_refl 0) hu.le huv hvb
    have hinit := ((hfamily b hb).2 v ⟨hu.trans huv, hvb⟩).1
    rw [hinit] at hrad'
    linarith only [hrad', hvb, hb.2]
  have hθ : |(S b).theta u v| ≤ T := by
    have hquot := (hscalar b hb u v hu huv hvb).1
    have hident : |(S b).theta u v| =
        |(S b).theta u v / (S b).r u v| * (S b).r u v := by
      rw [abs_div, abs_of_pos hr]
      field_simp [ne_of_gt hr]
    rw [hident]
    calc
      |(S b).theta u v / (S b).r u v| * (S b).r u v ≤
          (B / 4) * (S b).r u v :=
        mul_le_mul_of_nonneg_right hquot hr.le
      _ ≤ T := mul_le_mul_of_nonneg_left hrad (div_nonneg hB (by norm_num))
  have hθsq : ((S b).theta u v) ^ 2 ≤ T ^ 2 := by
    have hT0 : 0 ≤ T := by
      dsimp [T]
      exact mul_nonneg (div_nonneg hB (by norm_num))
        (div_nonneg (hu₀.1.le.trans hu₀.2.le) (by norm_num))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT0).2 hθ
  let q : ℝ := 1 - 2 * (S b).m u v / (S b).r u v
  have hnum : q * ((S b).theta u v) ^ 2 ≤ T ^ 2 := by
    calc
      q * ((S b).theta u v) ^ 2 ≤ ((S b).theta u v) ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) hq.2
      _ ≤ T ^ 2 := hθsq
  have hnum0 : 0 ≤ q * ((S b).theta u v) ^ 2 :=
    mul_nonneg hq.1 (sq_nonneg _)
  have hden : 0 < 2 * (S b).lam u v := by positivity
  have hdenC : 0 < 2 * c := by positivity
  have hMbound : q * ((S b).theta u v) ^ 2 /
      (2 * (S b).lam u v) ≤ M := by
    apply (div_le_div_iff₀ hden hdenC).2
    calc
      (q * ((S b).theta u v) ^ 2) * (2 * c) ≤ T ^ 2 * (2 * c) :=
        mul_le_mul_of_nonneg_right hnum hdenC.le
      _ ≤ T ^ 2 * (2 * (S b).lam u v) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlamFloor (by norm_num))
          (sq_nonneg T)
  rw [(mass_hasDerivAt_v_of_c1_interior H hp).deriv]
  change |q * ((S b).theta u v) ^ 2 /
    (2 * (S b).lam u v)| ≤ M
  rw [abs_of_nonneg (div_nonneg hnum0 hden.le)]
  exact hMbound

/-- The compatible masses have a jointly continuous terminal value on every
closed off-axis rectangle. -/
theorem exists_mass_terminal_trace_on_rectangle
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
    ∃ mTrace : ℝ × ℝ → ℝ,
      ContinuousOn mTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          mTrace (u, v) = (S b).m u v := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_mass_outgoing_derivative_bound_before_star
      hu₀ hα hfamily hε1 htail
  have hEq (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) vStar)
      (u : ℝ) (hu : u ∈ Icc 0 a)
      (v : ℝ) (hv : v ∈ Ico vBar b) :
      C1Solution.canonicalMass b (S b) (u, v) = (S b).m u v :=
    C1Solution.canonicalMass_eq_mass
      ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv.2⟩
  obtain ⟨G, hG, hGmatch⟩ :=
    exists_joint_terminal_trace_of_compatible_c1_family
      (F := fun b p => C1Solution.canonicalMass b (S b) p)
      ha haBar hBarStar hM
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
          ⟨hp₁, hp₂⟩).2.2.1)
      (by
        intro b hb T hT hTb
        exact C1Solution.canonicalMass_contDiffOn hT hTb (hfamily b hb).1)
      (by
        intro b hb u hu v hv
        let T : ℝ := (v + b) / 2
        have hT : 0 < T := by dsimp [T]; linarith only [ha, haBar, hv.1, hv.2]
        have hTb : T < b := by dsimp [T]; linarith only [hv.2]
        have hvT : v < T := by dsimp [T]; linarith only [hv.2]
        have huv : u < v := hu.2.trans_lt (haBar.trans hv.1)
        have hp : (u, v) ∈ openCoordTriangle 0 T :=
          ⟨hu.1, huv, hvT⟩
        have hder := C1Solution.canonicalMass_vertical_hasDerivAt
          hT hTb (hfamily b hb).1 hp
        rw [hder.deriv]
        have hmem : (u, v) ∈ developmentWithInitialEdge b :=
          ⟨hu.1.le, huv, hv.2⟩
        change |(1 - C1Solution.canonicalMassRatio b (S b) (u, v)) *
          ((S b).theta u v) ^ 2 / (2 * (S b).lam u v)| ≤ M
        rw [C1Solution.canonicalMassRatio_eq_mass_ratio (hfamily b hb).1 hmem]
        have hactual := hbound b hb u v hu.1 huv hv.2
        rw [(mass_hasDerivAt_v_of_c1_interior (hfamily b hb).1 (by
          have hOpen : IsOpen (openCoordTriangle 0 b) := by
            rw [← interior_closedCoordTriangle]; exact isOpen_interior
          have hSubset : openCoordTriangle 0 b ⊆
              developmentWithInitialEdge b := by
            intro p hp; exact ⟨hp.1.le, hp.2.1, hp.2.2⟩
          exact (hOpen.subset_interior_iff.mpr hSubset)
            ⟨hu.1, huv, hv.2⟩)).deriv] at hactual
        exact hactual)
  refine ⟨G, hG, ?_⟩
  intro b hb u hu v hv
  exact (hGmatch b hb u hu v hv).trans (hEq b hb u hu v hv)

end ChristodoulouBV.Uniqueness

end
