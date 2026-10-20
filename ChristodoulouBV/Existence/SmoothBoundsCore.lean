module

public import ChristodoulouBV.Existence.GlobalC1
public import ChristodoulouBV.Existence.SmoothData
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude
import Mathlib.Tactic

/-!+# Centered smooth solutions on all finite charts

The scalar normalization is performed separately for each solution. All
constants in this file depend only on total variation, including at zero
variation. No estimate of the unnormalized scalar is used.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- The scalar field centered at the initial vertex, with the induced
changes of both derivatives of `r φ`. -/
@[expose] def smoothCenteredFields (S : Fields) : Fields :=
  scalarShift S (-S.phi 0 0)

/-- Centering really sets the scalar at the initial vertex to zero. -/
theorem smoothCenteredFields_center (S : Fields) :
    (smoothCenteredFields S).phi 0 0 = 0 := by
  simp only [smoothCenteredFields, scalarShift, add_neg_cancel]

/-- The original solution is recovered by its own scalar offset. -/
theorem smoothCenteredFields_restore (S : Fields) :
    scalarShift (smoothCenteredFields S) (S.phi 0 0) = S := by
  simpa only [smoothCenteredFields, neg_neg] using
    scalarShift_neg S (-S.phi 0 0)

/-- Every centered unit chart has the hypotheses of Lemma 4.3, with its
initial variation bounded by the full original datum variation. -/
theorem smooth_centered_chart_bounds
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) :
    let Q := Uniqueness.rescaledFields (smoothCenteredFields S) 0 a
    IsC1Solution (developmentWithInitialEdge 1) Q ∧
      (∀ v ∈ Ioo (0 : ℝ) 1, Q.r 0 v = v / 2) ∧
      Q.phi 0 0 = 0 ∧ s4_bootstrap Q ∧
      sourceD Q ≤ eVariationOn alpha₀ (Ioi (0 : ℝ)) ∧
      sourceD Q ≤ s4Epsilon0 ∧ sourceZ Q ≤ s4Epsilon0 := by
  let T := Uniqueness.rescaledFields S 0 a
  let Q := Uniqueness.rescaledFields (smoothCenteredFields S) 0 a
  have hscale := s6_scale ha (by linarith : a < a + 1)
    (hfinite (a + 1) (by linarith)) (fun v hv => hdata v hv.1)
  have hQ : Q = scalarShift T (-S.phi 0 0) := by
    rfl
  have HQ : IsC1Solution (developmentWithInitialEdge 1) Q :=
    hQ ▸ hscale.1.scalarShift (-S.phi 0 0)
  have hr : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 :=
    fun v hv => (hscale.2.1 v hv).1
  have hDQ : sourceD Q = sourceD T := by
    rw [hQ]
    exact sourceD_scalarShift hscale.1 hr _ le_rfl
  have hno := global_c1_no_first_exit hfinite hdata hD ha
  have hb : s4_bootstrap Q := by
    refine ⟨?_, ?_, ?_⟩ <;> intro p hp
    · exact le_trans (by norm_num) (hno.2.2.1 p hp).1
    · exact le_trans (by norm_num) (hno.2.2.1 p hp).2.1
    · have hm := (hno.2.2.1 p hp).2.2
      change 2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ (1 / 3 : ℝ)
      linarith only [hm]
  have hZQ : sourceZ Q = sourceZ T := by
    simp only [hQ, sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  refine ⟨HQ, hr, ?_, hb, hDQ ▸ hscale.2.2, ?_, ?_⟩
  · simpa only [Q, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      mul_zero, zero_add] using smoothCenteredFields_center S
  · rw [hDQ]
    exact hscale.2.2.trans (hD.le.trans epsilonChosen_le_s4)
  · rw [hZQ]
    exact hno.2.1.le

private theorem amplitude_le_sup {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 1))
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    |f p| ≤ sSup {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1, x = |f q|} := by
  have hc := continuous_abs.comp_continuousOn hf
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hc).bddAbove
  apply le_csSup (show BddAbove {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1,
    x = |f q|} from ?_) ⟨p, hp, rfl⟩
  refine ⟨M, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  exact hM ⟨q, ⟨hq.1, hq.2.1.le, hq.2.2.le⟩, rfl⟩

/-- Universal centered amplitudes on the entire smooth development.
The outgoing initial ray is included. The invariant amplitudes `θ,ζ` need
no datum-dependent offset. -/
theorem smooth_centered_amplitude_bounds
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∀ p ∈ globalDomain,
      |(smoothCenteredFields S).alpha p.1 p.2| ≤
          2 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal ∧
      |(smoothCenteredFields S).beta p.1 p.2| ≤
          4 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal ∧
      |(smoothCenteredFields S).phi p.1 p.2| ≤
          6 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal ∧
      |S.theta p.1 p.2| ≤ 5 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal ∧
      |S.zeta p.1 p.2| ≤ 8 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal := by
  intro p hp
  let a := p.2 + 1
  have ha : 0 < a := by dsimp [a]; linarith only [hp.1, hp.2]
  let Q := Uniqueness.rescaledFields (smoothCenteredFields S) 0 a
  obtain ⟨HQ, hr, hc, hb, hDQ, _, _⟩ :=
    smooth_centered_chart_bounds hfinite hdata hD ha
  have hpQ : (p.1 / a, p.2 / a) ∈ developmentWithInitialEdge 1 :=
    ⟨div_nonneg hp.1 ha.le, div_lt_div_of_pos_right hp.2 ha,
      (div_lt_one ha).mpr (lt_add_one p.2)⟩
  have hreal := ENNReal.toReal_mono (ne_of_lt (hD.trans_le le_top)) hDQ
  obtain ⟨hl, hn, hφ, hα, hβ⟩ := unit_field_contDiffOn HQ
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hθ := hK ▸ HQ.theta_c1
  have hζ := hK ▸ HQ.zeta_c1
  obtain ⟨hA, hB, hP⟩ := lemma4_2 HQ hr hc hb
  obtain ⟨hT, hZ⟩ := eq4_3 HQ hr hc hb
  simp only [sourceA] at hA
  simp only [sourceB] at hB
  simp only [sourceP] at hP
  simp only [sourceThetaAmp] at hT
  simp only [sourceZetaAmp] at hZ
  have hvals :
      |Q.alpha (p.1 / a) (p.2 / a)| ≤ 2 * (eVariationOn alpha₀ (Ioi 0)).toReal ∧
      |Q.beta (p.1 / a) (p.2 / a)| ≤ 4 * (eVariationOn alpha₀ (Ioi 0)).toReal ∧
      |Q.phi (p.1 / a) (p.2 / a)| ≤ 6 * (eVariationOn alpha₀ (Ioi 0)).toReal ∧
      |Q.theta (p.1 / a) (p.2 / a)| ≤ 5 * (eVariationOn alpha₀ (Ioi 0)).toReal ∧
      |Q.zeta (p.1 / a) (p.2 / a)| ≤ 8 * (eVariationOn alpha₀ (Ioi 0)).toReal := by
    refine ⟨(amplitude_le_sup hα.continuousOn hpQ).trans (hA.trans ?_),
      (amplitude_le_sup hβ.continuousOn hpQ).trans (hB.trans ?_),
      (amplitude_le_sup hφ.continuousOn hpQ).trans (hP.trans ?_),
      (amplitude_le_sup hθ.continuousOn hpQ).trans (hT.trans ?_),
      (amplitude_le_sup hζ.continuousOn hpQ).trans (hZ.trans ?_)⟩ <;>
      exact mul_le_mul_of_nonneg_left hreal (by norm_num)
  have heqθ : Q.theta (p.1 / a) (p.2 / a) = S.theta p.1 p.2 := by
    simp only [Q, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_div_cancel₀ _ ha.ne', Fields.theta, smoothCenteredFields, scalarShift]
    ring
  have heqζ : Q.zeta (p.1 / a) (p.2 / a) = S.zeta p.1 p.2 := by
    simp only [Q, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_div_cancel₀ _ ha.ne', Fields.zeta, smoothCenteredFields, scalarShift]
    ring
  rw [heqθ, heqζ] at hvals
  simpa only [Q, Uniqueness.rescaledFields,
    Uniqueness.affineCoordinate, zero_add, mul_div_cancel₀ _ ha.ne'] using hvals

end ChristodoulouBV

end
