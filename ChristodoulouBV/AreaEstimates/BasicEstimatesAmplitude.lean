module

public import ChristodoulouBV.AreaEstimates.GaugeAxis
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# First Section 4 amplitude estimate

The source amplitudes are suprema over the augmented open development. The
closed-triangle C¹ regularity gives finite bounds and transfers inequalities
to the regular axis.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV

/-- The supremum `A` of the outgoing scalar-radius derivative on the unit development. -/
noncomputable def sourceA (S : Fields) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |S.alpha p.1 p.2|}

/-- The supremum `P` of the scalar field on the unit development. -/
noncomputable def sourceP (S : Fields) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |S.phi p.1 p.2|}

/-- The supremum `B` of the incoming scalar-radius derivative on the unit development. -/
noncomputable def sourceB (S : Fields) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |S.beta p.1 p.2|}

/-- The supremum of the outgoing scalar amplitude on the unit development. -/
noncomputable def sourceThetaAmp (S : Fields) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |S.theta p.1 p.2|}

/-- The supremum of the incoming scalar amplitude on the unit development. -/
noncomputable def sourceZetaAmp (S : Fields) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |S.zeta p.1 p.2|}

/-- The initial variation is finite for a C¹ solution on a triangle whose
closure contains the unit initial segment. -/
theorem sourceD_ne_top {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    sourceD S ≠ ⊤ := by
  let K := closedCoordTriangle 0 1
  have hmap : MapsTo (fun t : ℝ => (0, t)) (Icc 0 1) K := by
    intro t ht
    exact ⟨le_refl (0 : ℝ), ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hα : ContDiffOn ℝ 1 (S.alpha 0) (Icc 0 1) :=
    (C1Solution.alpha_contDiffOn (by norm_num) hb H).comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.alpha 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.alpha 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα).absolutelyContinuousOnInterval
  rw [sourceD, AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
    (by norm_num : (0 : ℝ) ≤ 1) hAC]
  exact ENNReal.ofReal_ne_top

private theorem source_amplitude_bddAbove
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 1)) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |f p|} := by
  have hcont : ContinuousOn (fun p => |f p|) (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn hf
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hcont).bddAbove
  refine ⟨M, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  apply hM
  exact ⟨p, ⟨hp.1, hp.2.1.le, hp.2.2.le⟩, rfl⟩

private theorem sourceA_bddAbove {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1,
      x = |S.alpha p.1 p.2|} :=
  source_amplitude_bddAbove
    (C1Solution.alpha_contDiffOn (by norm_num) hb H).continuousOn

private theorem sourceP_bddAbove {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1,
      x = |S.phi p.1 p.2|} :=
  source_amplitude_bddAbove
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1.continuousOn

private theorem sourceB_bddAbove {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1,
      x = |S.beta p.1 p.2|} :=
  source_amplitude_bddAbove
    (C1Solution.beta_contDiffOn (by norm_num) hb H).continuousOn

private theorem sourceA_nonneg {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    0 ≤ sourceA S := by
  have hp : (0, (1 / 2 : ℝ)) ∈ developmentWithInitialEdge 1 := by
    change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
    norm_num
  exact (abs_nonneg _).trans (le_csSup (sourceA_bddAbove hb H)
    ⟨(0, (1 / 2 : ℝ)), hp, rfl⟩)

private theorem abs_alpha_le_sourceA_closed {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 1) :
    |S.alpha p.1 p.2| ≤ sourceA S := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => |S.alpha q.1 q.2|)
      (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn
      (C1Solution.alpha_contDiffOn (by norm_num) hb H).continuousOn
  have hmaps : MapsTo (fun q : ℝ × ℝ => |S.alpha q.1 q.2|)
      (developmentWithInitialEdge 1) (Iic (sourceA S)) := by
    intro q hq
    exact le_csSup (sourceA_bddAbove hb H) ⟨q, hq, rfl⟩
  have hcl : closure (developmentWithInitialEdge 1) =
      closedCoordTriangle 0 1 := by
    simpa only [developmentWithInitialEdge] using
      (closure_initialEdgeTriangle (show (0 : ℝ) < 1 by norm_num))
  have h := hmaps.closure_of_continuousOn (hcl ▸ hcont) (hcl.symm ▸ hp)
  simpa only [isClosed_Iic.closure_eq, mem_Iic] using h

private theorem sourceP_nonneg {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    0 ≤ sourceP S := by
  have hp : (0, (1 / 2 : ℝ)) ∈ developmentWithInitialEdge 1 := by
    change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
    norm_num
  exact (abs_nonneg _).trans (le_csSup (sourceP_bddAbove hb H)
    ⟨(0, (1 / 2 : ℝ)), hp, rfl⟩)

private theorem abs_phi_le_sourceP {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    |S.phi p.1 p.2| ≤ sourceP S :=
  le_csSup (sourceP_bddAbove hb H) ⟨p, hp, rfl⟩

private theorem abs_phi_le_sourceP_closed {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 1) :
    |S.phi p.1 p.2| ≤ sourceP S := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => |S.phi q.1 q.2|)
      (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn
      (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1.continuousOn
  have hmaps : MapsTo (fun q : ℝ × ℝ => |S.phi q.1 q.2|)
      (developmentWithInitialEdge 1) (Iic (sourceP S)) := by
    intro q hq
    exact le_csSup (sourceP_bddAbove hb H) ⟨q, hq, rfl⟩
  have hcl : closure (developmentWithInitialEdge 1) =
      closedCoordTriangle 0 1 := by
    simpa only [developmentWithInitialEdge] using
      (closure_initialEdgeTriangle (show (0 : ℝ) < 1 by norm_num))
  have h := hmaps.closure_of_continuousOn (hcl ▸ hcont) (hcl.symm ▸ hp)
  simpa only [isClosed_Iic.closure_eq, mem_Iic] using h

private theorem bootstrap_lam_closed {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hboot : s4_bootstrap S) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle 0 1) :
    (1 / 3 : ℝ) ≤ S.lam p.1 p.2 := by
  have hcl : closure (developmentWithInitialEdge 1) =
      closedCoordTriangle 0 1 := by
    simpa only [developmentWithInitialEdge] using
      (closure_initialEdgeTriangle (show (0 : ℝ) < 1 by norm_num))
  have hcont :=
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).1.continuousOn
  have hmap : MapsTo (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (developmentWithInitialEdge 1) (Ici (1 / 3 : ℝ)) :=
    fun p hp => hboot.1 p hp
  have h := hmap.closure_of_continuousOn (hcl ▸ hcont) (hcl.symm ▸ hp)
  simpa only [isClosed_Ici.closure_eq, mem_Ici] using h

private theorem amplitude_transport_of_nonpos_coefficient
    {f g c phi : ℝ → ℝ} {a b P : ℝ} (hab : a ≤ b)
    (hf : IntervalPrimitive f (fun x => c x * phi x) a b)
    (hg : IntervalPrimitive g c a b)
    (hc : ∀ x ∈ Icc a b, c x ≤ 0)
    (hphi : ∀ x ∈ Icc a b, |phi x| ≤ P) :
    |f b| ≤ |f a| + P * (g a - g b) := by
  have hci : IntervalIntegrable c volume a b := hg.1
  have hfci : IntervalIntegrable (fun x => c x * phi x) volume a b := hf.1
  have hmaj : IntervalIntegrable (fun x => P * -c x) volume a b :=
    hci.neg.const_mul P
  have hpoint : ∀ x ∈ Icc a b, |c x * phi x| ≤ P * -c x := by
    intro x hx
    have hcx : 0 ≤ -c x := neg_nonneg.mpr (hc x hx)
    rw [abs_mul, abs_of_nonpos (hc x hx)]
    nlinarith only [hphi x hx, hcx]
  have hnorm : |∫ x in a..b, c x * phi x| ≤
      ∫ x in a..b, P * -c x := by
    calc
      |∫ x in a..b, c x * phi x| ≤
          ∫ x in a..b, |c x * phi x| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (μ := volume) (f := fun x : ℝ => c x * phi x) hab)
      _ ≤ ∫ x in a..b, P * -c x :=
        intervalIntegral.integral_mono_on hab hfci.abs hmaj hpoint
  have hgid : ∫ x in a..b, P * -c x = P * (g a - g b) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, ← hg.2]
    ring
  rw [hgid, ← hf.2] at hnorm
  calc
    |f b| = |f a + (f b - f a)| := by congr 1; ring
    _ ≤ |f a| + |f b - f a| := abs_add_le _ _
    _ ≤ |f a| + P * (g a - g b) := add_le_add_right hnorm _

/-- Equation (4.1): under the Section 4 bootstrap, `P ≤ 3A`. The C¹
premise extends across the closed unit triangle, as required by the source. -/
theorem eq4_1_larger {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceP S ≤ 3 * sourceA S := by
  have hA : 0 ≤ sourceA S := sourceA_nonneg hb H
  have hlamClosed : ∀ p ∈ closedCoordTriangle 0 1,
      (1 / 3 : ℝ) ≤ S.lam p.1 p.2 :=
    fun p hp => bootstrap_lam_closed hb H hboot hp
  apply csSup_le (by
    exact ⟨|S.phi 0 (1 / 2)|,
      ⟨(0, (1 / 2 : ℝ)), by
        change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
        norm_num, rfl⟩⟩)
  rintro x ⟨⟨u, v⟩, hp, rfl⟩
  have huv : u < v := hp.2.1
  have hpK : (u, v) ∈ closedCoordTriangle 0 1 :=
    ⟨hp.1, huv.le, hp.2.2.le⟩
  have hseg : ∀ t ∈ Icc u v, (u, t) ∈ closedCoordTriangle 0 1 := by
    intro t ht
    exact ⟨hp.1, ht.1, ht.2.trans hp.2.2.le⟩
  have hα : ContinuousOn (S.alpha u) (Icc u v) :=
    (C1Solution.alpha_contDiffOn (by norm_num) hb H).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hseg
  have hint : |∫ t in u..v, S.alpha u t| ≤ sourceA S * (v - u) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (C := sourceA S) (f := S.alpha u) (by
        intro t ht
        rw [uIoc_of_le huv.le] at ht
        have htK : (u, t) ∈ closedCoordTriangle 0 1 :=
          hseg t ⟨ht.1.le, ht.2⟩
        simpa only [Real.norm_eq_abs] using abs_alpha_le_sourceA_closed hb H htK)
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr huv)] using h
  have hrad := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H hp.1 huv hp.2.2.le
  have hψ := C1Solution.canonicalScalarRadius_eq_radius_mul_phi
    (by norm_num) hb H hp.1 huv hp.2.2.le
  change (∫ t in u..v, S.lam u t) = S.r u v at hrad
  change (∫ t in u..v, S.alpha u t) = S.r u v * S.phi u v at hψ
  have hlam : (v - u) / 3 ≤ S.r u v := by
    rw [← hrad]
    have hlamCont : ContinuousOn (S.lam u) (Icc u v) :=
      (C1Solution.five_fields_contDiffOn (by norm_num) hb H).1.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hseg
    have hmono := intervalIntegral.integral_mono_on huv.le
      (show IntervalIntegrable (fun _ : ℝ => (1 / 3 : ℝ)) volume u v from
        continuous_const.intervalIntegrable u v)
      (hlamCont.intervalIntegrable_of_Icc huv.le)
      (fun t ht => hlamClosed (u, t) (hseg t ht))
    simpa [div_eq_mul_inv, mul_comm] using hmono
  have hrpos : 0 < S.r u v :=
    H.solution.radius_pos (u, v) ⟨hp.1, hp.2.1, hp.2.2.trans hb⟩
  rw [hψ] at hint
  have hmul : |S.phi u v| * S.r u v ≤ sourceA S * (v - u) := by
    simpa [abs_mul, abs_of_pos hrpos, mul_comm] using hint
  have hgap : v - u ≤ 3 * S.r u v := by linarith only [hlam]
  have hprod := mul_le_mul_of_nonneg_left hgap hA
  nlinarith only [hmul, hprod, hrpos]

private theorem alpha_abs_le_initial_add {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ}
    (hp : (u, v) ∈ developmentWithInitialEdge 1) :
    |S.alpha u v| ≤ |S.alpha 0 v| +
      sourceP S * (S.lam 0 v - S.lam u v) := by
  have hu : 0 ≤ u := hp.1
  have huv : u < v := hp.2.1
  have hseg : inSeg v 0 u ⊆ developmentWithInitialEdge b := by
    intro q hq
    rcases q with ⟨s, t⟩
    have hst : s ∈ Icc 0 u ∧ t = v := by simpa [inSeg] using hq
    rcases hst with ⟨hs, rfl⟩
    exact ⟨hs.1, hs.2.trans_lt huv, hp.2.2.trans hb⟩
  let c : ℝ → ℝ := fun s =>
    (2 * S.m s v / S.r s v) * S.lam s v * S.nu s v /
      ((1 - 2 * S.m s v / S.r s v) * S.r s v)
  have hα : IntervalPrimitive (fun s => S.alpha s v)
      (fun s => c s * S.phi s v) 0 u :=
    H.solution.alpha_in v 0 u hu hseg
  have hlamPrim : IntervalPrimitive (fun s => S.lam s v) c 0 u :=
    H.solution.lam_in v 0 u hu hseg
  have hc : ∀ s ∈ Icc 0 u, c s ≤ 0 := by
    intro s hs
    have hpK : (s, v) ∈ closedCoordTriangle 0 1 :=
      ⟨hs.1, (hs.2.trans_lt huv).le, hp.2.2.le⟩
    have hjet := (C1Solution.four_mixed_coordinate_jets
      (by norm_num) hb H hpK).1
    have hsign := (c1_causal_signs (by norm_num) hb H hpK
      (hs.2.trans_lt huv)).2.2.2.2.1
    have heq := C1Solution.canonicalMixedCoefficient_eq_frozen
      (by norm_num) hb H hs.1 (hs.2.trans_lt huv) hp.2.2.le
    change C1Solution.canonicalMixedCoefficient b S (s, v) = c s at heq
    exact heq ▸ (hjet ▸ hsign)
  have hφ : ∀ s ∈ Icc 0 u, |S.phi s v| ≤ sourceP S := by
    intro s hs
    exact abs_phi_le_sourceP hb H (p := (s, v))
      ⟨hs.1, hs.2.trans_lt huv, hp.2.2⟩
  exact amplitude_transport_of_nonpos_coefficient hu hα hlamPrim hc hφ

private theorem eq4_2a_finite {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≠ ⊤) :
    sourceA S ≤ 2 * (sourceD S).toReal := by
  have hPA : sourceP S ≤ 3 * sourceA S := eq4_1_larger hb H hr hcenter hboot
  have hA : 0 ≤ sourceA S := sourceA_nonneg hb H
  have hbound : sourceA S ≤ (sourceD S).toReal + sourceP S / 6 := by
    apply csSup_le (by
      exact ⟨|S.alpha 0 (1 / 2)|,
        ⟨(0, (1 / 2 : ℝ)), by
          change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
          norm_num, rfl⟩⟩)
    rintro x ⟨⟨u, v⟩, hp, rfl⟩
    have htrans := alpha_abs_le_initial_add hb H hp
    have hv : v ∈ Ioo (0 : ℝ) 1 :=
      ⟨hp.1.trans_lt hp.2.1, hp.2.2⟩
    have hα0 := s4_initial_alpha_abs_le H (le_of_lt hb) hcenter hD hv
    have hvb : v ∈ Ioo (0 : ℝ) b := ⟨hv.1, hv.2.trans hb⟩
    have hlam0 := (source_gauge_data H hr v hvb).2
    have hlamLo := hboot.1 (u, v) hp
    have hP : 0 ≤ sourceP S := sourceP_nonneg hb H
    rw [hlam0] at htrans
    nlinarith only [htrans, hα0, hlamLo, hP]
  linarith only [hbound, hPA]

/-- Equation (4.2a), with the source variation as an extended nonnegative
quantity. For C¹ data it is finite; the extended formulation is also valid
without that separate finiteness lemma. -/
theorem eq4_2a_larger {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    ENNReal.ofReal (sourceA S) ≤ 2 * sourceD S := by
  by_cases hD : sourceD S = ⊤
  · simp [hD]
  · have h := eq4_2a_finite hb H hr hcenter hboot hD
    have hDpos : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
    have hA : 0 ≤ sourceA S := sourceA_nonneg hb H
    rw [← ENNReal.ofReal_toReal hD]
    calc
      ENNReal.ofReal (sourceA S) ≤
          ENNReal.ofReal (2 * (sourceD S).toReal) := ENNReal.ofReal_le_ofReal h
      _ = 2 * ENNReal.ofReal (sourceD S).toReal := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num

private theorem beta_abs_le_axis_add {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) :
    |S.beta u v| ≤ |S.alpha u u| +
      sourceP S * (-S.lam u u - S.nu u v) := by
  let K := closedCoordTriangle 0 1
  let c : ℝ → ℝ := fun t => C1Solution.canonicalMixedCoefficient b S (u, t)
  have hu : 0 ≤ u := hp.1
  have huv : u ≤ v := hp.2.1.le
  have hv : v ≤ 1 := hp.2.2.le
  have huK : u ∈ Icc 0 1 := ⟨hu, huv.trans hv⟩
  have hseg : ∀ t ∈ Icc u v, (u, t) ∈ K := by
    intro t ht
    exact ⟨hu, ht.1, ht.2.trans hv⟩
  have hcCont : ContinuousOn c (Icc u v) :=
    (C1Solution.canonicalMixedCoefficient_continuousOn
      (by norm_num) hb H).comp
      (continuous_const.prodMk continuous_id).continuousOn hseg
  have hphiCont : ContinuousOn (fun t => S.phi u t) (Icc u v) :=
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hseg
  have hci : IntervalIntegrable c volume u v :=
    hcCont.intervalIntegrable_of_Icc huv
  have hfc : IntervalIntegrable (fun t => c t * S.phi u t) volume u v :=
    (hcCont.mul hphiCont).intervalIntegrable_of_Icc huv
  have hnuFTC := C1Solution.integral_vertical_jet_eq_sub (by norm_num)
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.1 hu huv hv
  have hbetaFTC := C1Solution.integral_vertical_jet_eq_sub (by norm_num)
    (C1Solution.beta_contDiffOn (by norm_num) hb H) hu huv hv
  have hnuInt : (∫ t in u..v, c t) = S.nu u v - S.nu u u := by
    have heq : (∫ t in u..v, c t) =
        ∫ t in u..v,
          (fderivWithin ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) K (u, t)) (0, 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      exact ((C1Solution.four_mixed_coordinate_jets
        (by norm_num) hb H (hseg t ht)).2.1).symm
    exact heq.trans hnuFTC
  have hbetaInt : (∫ t in u..v, c t * S.phi u t) =
      S.beta u v - S.beta u u := by
    have heq : (∫ t in u..v, c t * S.phi u t) =
        ∫ t in u..v,
          (fderivWithin ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) K (u, t)) (0, 1) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv] at ht
      exact ((C1Solution.four_mixed_coordinate_jets
        (by norm_num) hb H (hseg t ht)).2.2.2).symm
    exact heq.trans hbetaFTC
  have hcNonpos : ∀ t ∈ Icc u v, c t ≤ 0 := by
    intro t ht
    by_cases htu : t = u
    · subst t
      rw [show c u = 0 from C1Solution.canonicalMixedCoefficient_axis b S u]
    · have hut : u < t := lt_of_le_of_ne ht.1 (Ne.symm htu)
      have hpK : (u, t) ∈ K := hseg t ht
      have hsign := (c1_causal_signs (by norm_num) hb H hpK hut).2.2.2.2.2
      have hjet := (C1Solution.four_mixed_coordinate_jets
        (by norm_num) hb H hpK).2.1
      change C1Solution.canonicalMixedCoefficient b S (u, t) ≤ 0
      exact hjet ▸ hsign
  have hphiBound : ∀ t ∈ Icc u v, |S.phi u t| ≤ sourceP S := by
    intro t ht
    exact abs_phi_le_sourceP_closed hb H (hseg t ht)
  have hpoint : ∀ t ∈ Icc u v,
      |c t * S.phi u t| ≤ sourceP S * -c t := by
    intro t ht
    rw [abs_mul, abs_of_nonpos (hcNonpos t ht)]
    convert mul_le_mul_of_nonneg_left (hphiBound t ht)
      (neg_nonneg.mpr (hcNonpos t ht)) using 1
    ring
  have hmaj : IntervalIntegrable (fun t => sourceP S * -c t) volume u v :=
    hci.neg.const_mul _
  have hnorm : |∫ t in u..v, c t * S.phi u t| ≤
      ∫ t in u..v, sourceP S * -c t := by
    calc
      |∫ t in u..v, c t * S.phi u t| ≤
          ∫ t in u..v, |c t * S.phi u t| := by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (μ := volume) (f := fun t : ℝ => c t * S.phi u t) huv)
      _ ≤ ∫ t in u..v, sourceP S * -c t :=
        intervalIntegral.integral_mono_on huv hfc.abs hmaj hpoint
  have hnuAxis := C1Solution.nu_eq_neg_lam_axis
    (by norm_num) hb H huK
  have hbetaAxis := C1Solution.beta_eq_neg_alpha_axis
    (by norm_num) hb H huK
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_neg, hnuInt, hnuAxis,
    hbetaInt, hbetaAxis] at hnorm
  calc
    |S.beta u v| = |-S.alpha u u + (S.beta u v - -S.alpha u u)| := by
      congr 1
      ring
    _ ≤ |-S.alpha u u| + |S.beta u v - -S.alpha u u| := abs_add_le _ _
    _ ≤ |S.alpha u u| + sourceP S * (-S.lam u u - S.nu u v) := by
      rw [abs_neg]
      convert add_le_add_right hnorm _ using 1
      ring

private theorem sourceB_le_two_sourceA {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0)
    (hboot : s4_bootstrap S) :
    sourceB S ≤ 2 * sourceA S := by
  have hPA : sourceP S ≤ 3 * sourceA S := eq4_1_larger hb H hr hcenter hboot
  have hP : 0 ≤ sourceP S := sourceP_nonneg hb H
  apply csSup_le (by
    exact ⟨|S.beta 0 (1 / 2)|,
      ⟨(0, (1 / 2 : ℝ)), by
        change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
        norm_num, rfl⟩⟩)
  rintro x ⟨⟨u, v⟩, hp, rfl⟩
  have hbeta := beta_abs_le_axis_add hb H hp
  have haxis : (u, u) ∈ closedCoordTriangle 0 1 :=
    ⟨hp.1, le_rfl, hp.2.1.le.trans hp.2.2.le⟩
  have hAaxis := abs_alpha_le_sourceA_closed hb H haxis
  have hlamAxis := bootstrap_lam_closed hb H hboot haxis
  have hnu := hboot.2.1 (u, v) hp
  have hfactor : -S.lam u u - S.nu u v ≤ (1 / 3 : ℝ) := by
    linarith only [hlamAxis, hnu]
  have hprod := mul_le_mul_of_nonneg_left hfactor hP
  nlinarith only [hbeta, hAaxis, hprod, hPA]

/-- Equation (4.2b): `B ≤ 2A ≤ 4D`. -/
theorem eq4_2b_larger {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceB S ≤ 2 * sourceA S ∧
      ENNReal.ofReal (sourceB S) ≤ 4 * sourceD S := by
  have hBA := sourceB_le_two_sourceA hb H hr hcenter hboot
  have hAD := eq4_2a_larger hb H hr hcenter hboot
  refine ⟨hBA, ?_⟩
  calc
    ENNReal.ofReal (sourceB S) ≤ ENNReal.ofReal (2 * sourceA S) :=
      ENNReal.ofReal_le_ofReal hBA
    _ = 2 * ENNReal.ofReal (sourceA S) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ ≤ 2 * (2 * sourceD S) :=
      mul_le_mul_of_nonneg_left hAD (by norm_num)
    _ = 4 * sourceD S := by ring

/-- Lemma 4.2: the three amplitudes under the conditional Section 4
bootstrap. No smallness threshold is needed. -/
theorem lemma4_2_larger {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    ENNReal.ofReal (sourceA S) ≤ 2 * sourceD S ∧
      ENNReal.ofReal (sourceB S) ≤ 4 * sourceD S ∧
        ENNReal.ofReal (sourceP S) ≤ 6 * sourceD S := by
  have hA := eq4_2a_larger hb H hr hcenter hboot
  have hB := (eq4_2b_larger hb H hr hcenter hboot).2
  have hPA := eq4_1_larger hb H hr hcenter hboot
  refine ⟨hA, hB, ?_⟩
  calc
    ENNReal.ofReal (sourceP S) ≤ ENNReal.ofReal (3 * sourceA S) :=
      ENNReal.ofReal_le_ofReal hPA
    _ = 3 * ENNReal.ofReal (sourceA S) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    _ ≤ 3 * (2 * sourceD S) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    _ = 6 * sourceD S := by ring

private theorem eq4_3_finite {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≠ ⊤) :
    sourceThetaAmp S ≤ 5 * (sourceD S).toReal ∧
      sourceZetaAmp S ≤ 8 * (sourceD S).toReal := by
  have hAD := eq4_2a_finite hb H hr hcenter hboot hD
  have hBA := sourceB_le_two_sourceA hb H hr hcenter hboot
  have hPA := eq4_1_larger hb H hr hcenter hboot
  have hA : 0 ≤ sourceA S := sourceA_nonneg hb H
  have hP : 0 ≤ sourceP S := sourceP_nonneg hb H
  have hB : sourceB S ≤ 4 * (sourceD S).toReal := by
    linarith only [hBA, hAD]
  have hPbound : sourceP S ≤ 6 * (sourceD S).toReal := by
    linarith only [hPA, hAD]
  have htheta : ∀ p ∈ developmentWithInitialEdge 1,
      |S.theta p.1 p.2| ≤ 5 * (sourceD S).toReal := by
    rintro ⟨u, v⟩ hp
    have hα : |S.alpha u v| ≤ sourceA S :=
      le_csSup (sourceA_bddAbove hb H) ⟨(u, v), hp, rfl⟩
    have hφ : |S.phi u v| ≤ sourceP S := abs_phi_le_sourceP hb H hp
    have hlamLo := hboot.1 (u, v) hp
    have hlamHi := Uniqueness.lam_le_half_of_initial_gauge H hr
      hp.1 hp.2.1 (hp.2.2.trans hb)
    have hprod : S.lam u v * |S.phi u v| ≤ (1 / 2 : ℝ) * sourceP S :=
      calc
        S.lam u v * |S.phi u v| ≤ S.lam u v * sourceP S :=
          mul_le_mul_of_nonneg_left hφ (by linarith only [hlamLo])
        _ ≤ (1 / 2 : ℝ) * sourceP S :=
          mul_le_mul_of_nonneg_right hlamHi hP
    have htriangle : |S.theta u v| ≤ |S.alpha u v| +
        S.lam u v * |S.phi u v| := by
      change |S.alpha u v - S.lam u v * S.phi u v| ≤ _
      have h := abs_sub_le (S.alpha u v) 0 (S.lam u v * S.phi u v)
      have hlamNonneg : 0 ≤ S.lam u v := by linarith only [hlamLo]
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg hlamNonneg] using h
    linarith only [htriangle, hα, hprod, hAD, hPbound]
  have hzeta : ∀ p ∈ developmentWithInitialEdge 1,
      |S.zeta p.1 p.2| ≤ 8 * (sourceD S).toReal := by
    rintro ⟨u, v⟩ hp
    have hβ : |S.beta u v| ≤ sourceB S :=
      le_csSup (sourceB_bddAbove hb H) ⟨(u, v), hp, rfl⟩
    have hφ : |S.phi u v| ≤ sourceP S := abs_phi_le_sourceP hb H hp
    have hpK : (u, v) ∈ closedCoordTriangle 0 1 :=
      ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
    have hnuNeg := (c1_causal_signs (by norm_num) hb H hpK hp.2.1).1
    have hnuLo := hboot.2.1 (u, v) hp
    have hprod : -S.nu u v * |S.phi u v| ≤ (2 / 3 : ℝ) * sourceP S :=
      calc
        -S.nu u v * |S.phi u v| ≤ -S.nu u v * sourceP S :=
          mul_le_mul_of_nonneg_left hφ (by linarith only [hnuNeg])
        _ ≤ (2 / 3 : ℝ) * sourceP S :=
          mul_le_mul_of_nonneg_right (by linarith only [hnuLo]) hP
    have htriangle : |S.zeta u v| ≤ |S.beta u v| +
        -S.nu u v * |S.phi u v| := by
      change |S.beta u v - S.nu u v * S.phi u v| ≤ _
      have h := abs_sub_le (S.beta u v) 0 (S.nu u v * S.phi u v)
      simpa [abs_mul, abs_of_neg hnuNeg] using h
    linarith only [htriangle, hβ, hprod, hB, hPbound]
  constructor
  · apply csSup_le (by
      exact ⟨|S.theta 0 (1 / 2)|,
        ⟨(0, (1 / 2 : ℝ)), by
          change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
          norm_num, rfl⟩⟩)
    rintro x ⟨p, hp, rfl⟩
    exact htheta p hp
  · apply csSup_le (by
      exact ⟨|S.zeta 0 (1 / 2)|,
        ⟨(0, (1 / 2 : ℝ)), by
          change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
          norm_num, rfl⟩⟩)
    rintro x ⟨p, hp, rfl⟩
    exact hzeta p hp

/-- Equation (4.3): the universal `5D` and `8D` bounds for the scalar
amplitudes, under the same bootstrap and gauges as Lemma 4.2. -/
theorem eq4_3_larger {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    ENNReal.ofReal (sourceThetaAmp S) ≤ 5 * sourceD S ∧
      ENNReal.ofReal (sourceZetaAmp S) ≤ 8 * sourceD S := by
  by_cases hD : sourceD S = ⊤
  · simp [hD]
  · obtain ⟨htheta, hzeta⟩ := eq4_3_finite hb H hr hcenter hboot hD
    rw [← ENNReal.ofReal_toReal hD]
    constructor
    · calc
        ENNReal.ofReal (sourceThetaAmp S) ≤
            ENNReal.ofReal (5 * (sourceD S).toReal) := ENNReal.ofReal_le_ofReal htheta
        _ = 5 * ENNReal.ofReal (sourceD S).toReal := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
          norm_num
    · calc
        ENNReal.ofReal (sourceZetaAmp S) ≤
            ENNReal.ofReal (8 * (sourceD S).toReal) := ENNReal.ofReal_le_ofReal hzeta
        _ = 8 * ENNReal.ofReal (sourceD S).toReal := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
          norm_num

/-- The real form of (4.2a), using finiteness of `D` for a C¹ solution. -/
theorem eq4_2a_real {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA S ≤ 2 * (sourceD S).toReal :=
  eq4_2a_finite hb H hr hcenter hboot (sourceD_ne_top hb H)

/-- The real form of (4.2b), including `B ≤ 2A ≤ 4D`. -/
theorem eq4_2b_real {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceB S ≤ 2 * sourceA S ∧
      2 * sourceA S ≤ 4 * (sourceD S).toReal := by
  have hBA := sourceB_le_two_sourceA hb H hr hcenter hboot
  have hAD := eq4_2a_real hb H hr hcenter hboot
  exact ⟨hBA, by linarith only [hAD]⟩

/-- Lemma 4.2 in the paper's real-valued notation. -/
theorem lemma4_2_real {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA S ≤ 2 * (sourceD S).toReal ∧
      sourceB S ≤ 4 * (sourceD S).toReal ∧
        sourceP S ≤ 6 * (sourceD S).toReal := by
  have hA := eq4_2a_real hb H hr hcenter hboot
  have hB := eq4_2b_real hb H hr hcenter hboot
  have hP := eq4_1_larger hb H hr hcenter hboot
  constructor
  · exact hA
  constructor
  · linarith only [hB.1, hB.2]
  · linarith only [hP, hA]

/-- Equation (4.3) in the paper's real-valued notation. -/
theorem eq4_3_real {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceThetaAmp S ≤ 5 * (sourceD S).toReal ∧
      sourceZetaAmp S ≤ 8 * (sourceD S).toReal :=
  eq4_3_finite hb H hr hcenter hboot (sourceD_ne_top hb H)

end ChristodoulouBV

end
