module

public import ChristodoulouBV.AreaEstimates.SourceInputs
public import ChristodoulouBV.BVSolution.C1InitialCompatibility
public import ChristodoulouBV.C1Solution.ExtractionAxisJets
public import ChristodoulouBV.C1Solution.ExtractionMass
public import ChristodoulouBV.AreaEstimates.GaugeAxisShift
public import ChristodoulouBV.AreaEstimates.GaugeAxisRegularity
public import ChristodoulouBV.AreaEstimates.GaugeAxisScalarTransport
public import ChristodoulouBV.AreaEstimates.GaugeAxisI
public import ChristodoulouBV.AreaEstimates.GaugeAxisDiagonal
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The Section 4 gauge and regular axis

The quantities below use extended nonnegative values, so their definitions
also cover a C¹ solution whose variation or null integrals diverge at the
excluded upper vertex. On a finite estimate they have the paper's real values.
Axis field values refer to the five C¹ fields and to `α` and `β`, which are
determined by them. Radius and mass at the excluded diagonal are represented
by their canonical extensions in the extraction library.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The initial variation `D` of Section 4, allowing the value `∞`. -/
noncomputable def sourceD (S : Fields) : ℝ≥0∞ :=
  eVariationOn (S.alpha 0) (Ioo (0 : ℝ) 1)

/-- The outgoing null integral supremum `X` of Section 4. -/
noncomputable def sourceX (S : Fields) : ℝ≥0∞ :=
  ⨆ u ∈ Ioo (0 : ℝ) 1,
    ∫⁻ v in Ioo u 1, ENNReal.ofReal (|S.theta u v| / S.r u v)

/-- The incoming null integral supremum `Y` of Section 4. -/
noncomputable def sourceY (S : Fields) : ℝ≥0∞ :=
  ⨆ v ∈ Ioo (0 : ℝ) 1,
    ∫⁻ u in Ioo 0 v, ENNReal.ofReal (|S.zeta u v| / S.r u v)

/-- The combined null integral size `Z = max X Y`. -/
noncomputable def sourceZ (S : Fields) : ℝ≥0∞ :=
  max (sourceX S) (sourceY S)

/-- The three conditional bootstrap bounds used in Section 4. -/
def s4_bootstrap (S : Fields) : Prop :=
  (∀ p ∈ developmentWithInitialEdge 1, (1 / 3 : ℝ) ≤ S.lam p.1 p.2) ∧
  (∀ p ∈ developmentWithInitialEdge 1, -(2 / 3 : ℝ) ≤ S.nu p.1 p.2) ∧
  (∀ p ∈ developmentWithInitialEdge 1,
    2 * S.m p.1 p.2 / S.r p.1 p.2 ≤ (1 / 3 : ℝ))

/-- In the prescribed radius gauge the initial outgoing expansion is `1/2`.
The data size and null sizes are the definitions immediately above. -/
theorem source_gauge_data {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2) :
    ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.lam 0 v = 1 / 2 := by
  intro v hv
  exact ⟨hr v hv, initial_lam_eq_of_gauge H hr hv⟩

/-- The initial variation is invariant under a scalar shift in the radius
gauge: the initial `α` changes by the constant `c/2`. -/
theorem sourceD_scalarShift {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (c : ℝ) (hunit : (1 : ℝ) ≤ b) :
    sourceD (scalarShift S c) = sourceD S := by
  have heq : EqOn (fun v => (scalarShift S c).alpha 0 v)
      (fun v => S.alpha 0 v + c / 2) (Ioo (0 : ℝ) 1) := by
    intro v hv
    change S.alpha 0 v + c * S.lam 0 v = S.alpha 0 v + c / 2
    rw [initial_lam_eq_of_gauge H hr (by
      exact ⟨hv.1, hv.2.trans_le hunit⟩)]
    ring
  calc
    sourceD (scalarShift S c) =
        eVariationOn (fun v => S.alpha 0 v + c / 2) (Ioo (0 : ℝ) 1) :=
      eVariationOn.congr heq
    _ = sourceD S := eVariationOn_add_const_real _ _ _

/-- The outgoing null integral size is invariant under a scalar shift. -/
theorem sourceX_scalarShift (S : Fields) (c : ℝ) :
    sourceX (scalarShift S c) = sourceX S := by
  simp only [sourceX, scalarShift_theta, scalarShift_r]

/-- The incoming null integral size is invariant under a scalar shift. -/
theorem sourceY_scalarShift (S : Fields) (c : ℝ) :
    sourceY (scalarShift S c) = sourceY S := by
  simp only [sourceY, scalarShift_zeta, scalarShift_r]

/-- Center the origin scalar value and retain the exact inverse shift needed
to restore the prescribed initial data. The shift may depend on the datum. -/
theorem scalar_shift {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hunit : (1 : ℝ) ≤ b) :
    ∃ T : Fields,
      IsC1Solution (developmentWithInitialEdge b) T ∧
      T.phi 0 0 = 0 ∧
      sourceD T = sourceD S ∧ sourceX T = sourceX S ∧
      sourceY T = sourceY S ∧ sourceZ T = sourceZ S ∧
      scalarShift T (S.phi 0 0) = S ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        T.alpha 0 v = S.alpha 0 v - S.phi 0 0 / 2 := by
  let c : ℝ := -S.phi 0 0
  refine ⟨scalarShift S c, H.scalarShift c, ?_,
    sourceD_scalarShift H hr c hunit,
    sourceX_scalarShift S c, sourceY_scalarShift S c, ?_, ?_, ?_⟩
  · change S.phi 0 0 + c = 0
    dsimp [c]
    ring
  · simp only [sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  · simpa only [c, neg_neg] using scalarShift_neg S c
  · intro v hv
    change S.alpha 0 v + c * S.lam 0 v =
      S.alpha 0 v - S.phi 0 0 / 2
    rw [initial_lam_eq_of_gauge H hr hv]
    dsimp [c]
    ring

/-- Centering at the origin makes the initial scalar-radius derivative zero.
The variation bound is extended-real and therefore also covers infinite
variation; for finite data it is exactly the paper's `|α| ≤ D`. -/
theorem s4_initial_alpha_zero {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hunit : (1 : ℝ) ≤ b) (hcenter : S.phi 0 0 = 0) :
    S.alpha 0 0 = 0 ∧
    ∀ v ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal |S.alpha 0 v| ≤ sourceD S := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfb : (1 / 2 : ℝ) < b := by linarith
  have hzero := C1Solution.alpha_eq_lam_mul_phi_axis
    hhalf hhalfb H (show (0 : ℝ) ∈ Icc 0 (1 / 2 : ℝ) by
      constructor <;> norm_num)
  rw [hcenter, mul_zero] at hzero
  refine ⟨hzero, ?_⟩
  intro v hv
  let w : ℝ := (v + 1) / 2
  let B : ℝ := (w + 1) / 2
  have hvw : v < w := by dsimp [w]; linarith [hv.2]
  have hwB : w < B := by dsimp [B, w]; linarith [hv.2]
  have hB : 0 < B := by dsimp [B, w]; linarith [hv.1]
  have hBb : B < b := by dsimp [B, w]; linarith [hv.2, hunit]
  have hw1 : w < 1 := by dsimp [w]; linarith [hv.2]
  have hcont : ContinuousOn (S.alpha 0) (Icc 0 w) :=
    (C1Solution.alpha_contDiffOn hB hBb H).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨le_rfl, ht.1, ht.2.trans hwB.le⟩)
  have hvar : eVariationOn (S.alpha 0) (Icc 0 w) ≤ sourceD S := by
    rw [← eVariationOn.Ioo_eq_Icc_of_continuousOn (le_of_lt (lt_trans hv.1 hvw))
      hcont]
    exact eVariationOn.mono _ (fun t ht => ⟨ht.1, ht.2.trans hw1⟩)
  have hpoint := eVariationOn.edist_le (S.alpha 0)
    (show (0 : ℝ) ∈ Icc 0 w by exact ⟨le_rfl, (lt_trans hv.1 hvw).le⟩)
    (show v ∈ Icc 0 w by exact ⟨hv.1.le, hvw.le⟩)
  rw [hzero] at hpoint
  simpa only [sourceD, edist_dist, Real.dist_eq, zero_sub, abs_neg] using hpoint.trans hvar

/-- The centered initial amplitude is bounded by the real variation when
the initial datum has finite variation. -/
theorem s4_initial_alpha_abs_le {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hunit : (1 : ℝ) ≤ b) (hcenter : S.phi 0 0 = 0)
    (hD : sourceD S ≠ ∞)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    |S.alpha 0 v| ≤ (sourceD S).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hD).mp
    ((s4_initial_alpha_zero H hunit hcenter).2 v hv)

/-- Literal regular-axis identities for the C¹ fields and their relative
coordinate jets on every smaller closed development. The last four clauses
give the zero conjugate jets and the differentiated diagonal identities. -/
theorem axis_traces {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {a : ℝ} (ha : a ∈ Icc 0 B) :
    S.theta a a = 0 ∧ S.zeta a a = 0 ∧
    S.nu a a = -S.lam a a ∧
    S.alpha a a = S.lam a a * S.phi a a ∧
    S.beta a a = -S.alpha a a ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (1, 0) = 0 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (0, 1) = 0 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (1, 0) = 0 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (0, 1) = 0 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (1, 0) =
      -(fderivWithin ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2)
        (closedCoordTriangle 0 B) (a, a)) (0, 1) ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2)
      (closedCoordTriangle 0 B) (a, a)) (1, 0) =
      -(fderivWithin ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2)
        (closedCoordTriangle 0 B) (a, a)) (0, 1) := by
  obtain ⟨hlu, hnv, hau, hbv⟩ :=
    C1Solution.four_mixed_axis_jets hB hBb H ha
  obtain ⟨hnu, hbeta⟩ :=
    C1Solution.incoming_axis_coordinate_jets hB hBb H ha
  exact ⟨C1Solution.theta_axis_eq_zero hB hBb H ha,
    C1Solution.zeta_axis_eq_zero hB hBb H ha,
    C1Solution.nu_eq_neg_lam_axis hB hBb H ha,
    C1Solution.alpha_eq_lam_mul_phi_axis hB hBb H ha,
    C1Solution.beta_eq_neg_alpha_axis hB hBb H ha,
    hlu, hnv, hau, hbv, hnu, hbeta⟩

end ChristodoulouBV

end
