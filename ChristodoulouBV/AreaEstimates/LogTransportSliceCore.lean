module

public import ChristodoulouBV.AreaEstimates.LogTransportIncoming
import ChristodoulouBV.AreaEstimates.FieldTransportAxis
import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationCore
import ChristodoulouBV.AreaEstimates.SourceInputs
import ChristodoulouBV.AreaEstimates.ScalarAreaWeights
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Core logarithmic variation estimates on null slices

The three estimates (4.12c), sign-corrected (4.13c), and (4.14) convert
the integrated logarithmic residuals into total variation bounds.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

private theorem slice_vertical_deriv {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1))
    {u t B : ℝ} (hu : 0 < u) (hut : u < t) (htB : t < B) (hB : B < 1) :
    deriv (fun s => F (u, s)) t =
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, t)) (0, 1) := by
  have hp : (u, t) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, hut, htB⟩
  have hpBig : (u, t) ∈ interior (closedCoordTriangle 0 1) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, hut, htB.trans hB⟩
  have hdiff : DifferentiableAt ℝ F (u, t) :=
    (hF.differentiableOn (by norm_num) (u, t) (interior_subset hpBig))
      |>.differentiableAt (mem_of_superset
        (isOpen_interior.mem_nhds hpBig) interior_subset)
  have hpath : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) t :=
    (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpath
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty (lt_trans hu hut |>.trans htB))
  rw [fderivWithin_eq_fderiv (hunique (u, t) (interior_subset hp)) hdiff]
  simpa only [Function.comp_def] using hcomp.deriv

private theorem slice_horizontal_deriv {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1))
    {t v B : ℝ} (ht : 0 < t) (htv : t < v) (hvB : v < B) (hB : B < 1) :
    deriv (fun s => F (s, v)) t =
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (t, v)) (1, 0) := by
  have hp : (t, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨ht, htv, hvB⟩
  have hpBig : (t, v) ∈ interior (closedCoordTriangle 0 1) := by
    rw [interior_closedCoordTriangle]
    exact ⟨ht, htv, hvB.trans hB⟩
  have hdiff : DifferentiableAt ℝ F (t, v) :=
    (hF.differentiableOn (by norm_num) (t, v) (interior_subset hpBig))
      |>.differentiableAt (mem_of_superset
        (isOpen_interior.mem_nhds hpBig) interior_subset)
  have hpath : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t v)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpath
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty (lt_trans ht htv |>.trans hvB))
  rw [fderivWithin_eq_fderiv (hunique (t, v) (interior_subset hp)) hdiff]
  simpa only [Function.comp_def] using hcomp.deriv

private theorem outgoing_phi_weight_eq_abs_deriv {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u t : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo u 1) :
    |S.theta u t| / S.r u t = |deriv (S.phi u) t| := by
  let B := (t + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, ht.1]
  have htB : t < B := by dsimp [B]; linarith only [ht.2]
  have hB1 : B < 1 := by dsimp [B]; linarith only [ht.2]
  have hpB : (u, t) ∈ closedCoordTriangle 0 B :=
    ⟨hu.1.le, ht.1.le, htB.le⟩
  have hderiv := slice_vertical_deriv (unit_field_contDiffOn H).2.2.1
    hu.1 ht.1 htB hB1
  have htheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hB1 H hpB
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    hu.1.le ht.1 htB.le
  have hrpos : 0 < S.r u t :=
    H.solution.radius_pos (u, t) ⟨hu.1.le, ht.1, ht.2⟩
  rw [hr, ← hderiv] at htheta
  rw [htheta, abs_mul, abs_of_pos hrpos]
  field_simp [hrpos.ne']

private theorem incoming_phi_weight_eq_abs_deriv {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {t v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo 0 v) :
    |S.zeta t v| / S.r t v =
      |deriv (fun s => S.phi s v) t| := by
  let B := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hpB : (t, v) ∈ closedCoordTriangle 0 B :=
    ⟨ht.1.le, ht.2.le, hvB.le⟩
  have hderiv := slice_horizontal_deriv (unit_field_contDiffOn H).2.2.1
    ht.1 ht.2 hvB hB1
  have hzeta := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    hB hB1 H hpB
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    ht.1.le ht.2 hvB.le
  have hrpos : 0 < S.r t v :=
    H.solution.radius_pos (t, v) ⟨ht.1.le, ht.2, hv.2⟩
  rw [hr, ← hderiv] at hzeta
  rw [hzeta, abs_mul, abs_of_pos hrpos]
  field_simp [hrpos.ne']

/-- The outgoing scalar variation is exactly its null weight integral. -/
theorem source_outgoing_phi_variation_eq_weight {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (S.phi u) (Ioo u 1) =
      ∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t) := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2⟩
  have hpath : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (S.phi u) (Icc u 1) :=
    (unit_field_contDiffOn H).2.2.1.comp hpath hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi u) u 1 :=
    (show ContDiffOn ℝ 1 (S.phi u) (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hphi).absolutelyContinuousOnInterval
  exact (null_lintegral_eq_scalar_variation hu.2.le hAC
    (fun t ht => outgoing_phi_weight_eq_abs_deriv H hu ht)).symm

/-- The incoming scalar variation is exactly its null weight integral. -/
theorem source_incoming_phi_variation_eq_weight {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (fun t => S.phi t v) (Ioo 0 v) =
      ∫⁻ t in Ioo 0 v, ENNReal.ofReal (|S.zeta t v| / S.r t v) := by
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨ht.1, ht.2, hv.2.le⟩
  have hpath : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (fun t => S.phi t v) (Icc 0 v) :=
    (unit_field_contDiffOn H).2.2.1.comp hpath hmap
  have hAC : AbsolutelyContinuousOnInterval (fun t => S.phi t v) 0 v :=
    (show ContDiffOn ℝ 1 (fun t => S.phi t v) (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hphi).absolutelyContinuousOnInterval
  exact (null_lintegral_eq_scalar_variation hv.1.le hAC
    (fun t ht => incoming_phi_weight_eq_abs_deriv H hv ht)).symm

/-- Pass a nonnegative integral bound from compact cutoffs to the open unit endpoint. -/
theorem lintegral_Ioo_unit_le_of_cutoffs {a : ℝ} (ha : a < 1)
    (F : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hcut : ∀ b ∈ Ioo a 1, (∫⁻ t in Ioo a b, F t) ≤ C) :
    (∫⁻ t in Ioo a 1, F t) ≤ C := by
  let b : ℕ → ℝ := fun n => max a (1 - 1 / (n + 1 : ℝ))
  let E : ℕ → Set ℝ := fun n => Ioo a (b n)
  have hb1 (n : ℕ) : b n < 1 := by
    apply max_lt ha
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hbmono : Monotone b := by
    intro n m hnm
    dsimp [b]
    apply max_le_max_left
    have hden : (n + 1 : ℝ) ≤ (m + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have hfrac := one_div_le_one_div_of_le hpos hden
    linarith only [hfrac]
  have hEmono : Monotone E := by
    intro n m hnm x hx
    exact ⟨hx.1, hx.2.trans_le (hbmono hnm)⟩
  have hcover : (⋃ n, E n) = Ioo a 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      exact ⟨hxn.1, hxn.2.trans (hb1 n)⟩
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx.2)
      apply mem_iUnion.mpr
      refine ⟨n, hx.1, ?_⟩
      have hlt : x < 1 - 1 / (n + 1 : ℝ) := by linarith only [hn]
      exact hlt.trans_le (le_max_right _ _)
  have hdir : Directed (· ⊆ ·) E := by
    intro n m
    exact ⟨max n m, hEmono (le_max_left n m), hEmono (le_max_right n m)⟩
  calc
    (∫⁻ t in Ioo a 1, F t) = ∫⁻ t in ⋃ n, E n, F t := by rw [hcover]
    _ = ⨆ n, ∫⁻ t in E n, F t := setLIntegral_iUnion_of_directed F hdir
    _ ≤ C := by
      apply iSup_le
      intro n
      by_cases hab : a < b n
      · exact hcut (b n) ⟨hab, hb1 n⟩
      · have hEmpty : E n = ∅ := by
          ext x
          constructor
          · intro hx
            exact False.elim
              ((not_lt_of_ge (le_of_not_gt hab)) (hx.1.trans hx.2))
          · intro hx
            exact hx.elim
        simp [hEmpty]

private theorem aemeasurable_Ioo_unit_of_cutoffs {a : ℝ} (ha : a < 1)
    {F : ℝ → ℝ≥0∞}
    (hcut : ∀ b ∈ Ioo a 1,
      AEMeasurable F (volume.restrict (Ioo a b))) :
    AEMeasurable F (volume.restrict (Ioo a 1)) := by
  let b : ℕ → ℝ := fun n => max a (1 - 1 / (n + 1 : ℝ))
  let E : ℕ → Set ℝ := fun n => Ioo a (b n)
  have hb1 (n : ℕ) : b n < 1 := by
    apply max_lt ha
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hcover : (⋃ n, E n) = Ioo a 1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      exact ⟨hxn.1, hxn.2.trans (hb1 n)⟩
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx.2)
      apply mem_iUnion.mpr
      refine ⟨n, hx.1, ?_⟩
      have hlt : x < 1 - 1 / (n + 1 : ℝ) := by linarith only [hn]
      exact hlt.trans_le (le_max_right _ _)
  rw [← hcover, aemeasurable_iUnion_iff]
  intro n
  by_cases hab : a < b n
  · exact hcut (b n) ⟨hab, hb1 n⟩
  · have hEmpty : E n = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim
          ((not_lt_of_ge (le_of_not_gt hab)) (hx.1.trans hx.2))
      · intro hx
        exact hx.elim
    rw [hEmpty, Measure.restrict_empty]
    exact aemeasurable_zero_measure

private theorem log_corrections_continuousOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hboot : s4_bootstrap S) :
    ContinuousOn (fun p : ℝ × ℝ => sourceLogCorrection S p.1 p.2)
      (openCoordTriangle 0 1) ∧
    ContinuousOn (fun p : ℝ × ℝ => sourceLogCorrectionStar S p.1 p.2)
      (openCoordTriangle 0 1) := by
  let T := openCoordTriangle (0 : ℝ) 1
  have hsub : T ⊆ closedCoordTriangle 0 1 :=
    fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hθ : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2) T := by
    have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1)
    exact (hK ▸ H.theta_c1).continuousOn.mono hsub
  have hζ : ContinuousOn (fun p : ℝ × ℝ => S.zeta p.1 p.2) T := by
    have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1)
    exact (hK ▸ H.zeta_c1).continuousOn.mono hsub
  have hLam : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2) T :=
    (unit_field_contDiffOn H).1.continuousOn.mono hsub
  have hNu : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2) T :=
    (unit_field_contDiffOn H).2.1.continuousOn.mono hsub
  have hR : ContinuousOn (C1Solution.canonicalRadius S) T :=
    (sourceCanonicalRadius_contDiffOn H).continuousOn.mono hsub
  have hLamNe : ∀ p ∈ T, S.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (by
      have hpU : p ∈ developmentWithInitialEdge 1 :=
        ⟨hp.1.le, hp.2.1, hp.2.2⟩
      linarith only [hboot.1 p hpU])
  have hNuNe : ∀ p ∈ T, S.nu p.1 p.2 ≠ 0 := by
    intro p hp
    have hpU : p ∈ developmentWithInitialEdge 1 :=
      ⟨hp.1.le, hp.2.1, hp.2.2⟩
    have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
      IsC1Solution.isBVSolution_development (by norm_num) H
    exact ne_of_lt ((hBV.nu_le_neg_lower (by norm_num) hboot.1 hpU).trans_lt
      (by norm_num))
  have hRne : ∀ p ∈ T, C1Solution.canonicalRadius S p ≠ 0 := by
    intro p hp
    rw [sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]
    exact ne_of_gt (H.solution.radius_pos p ⟨hp.1.le, hp.2.1, hp.2.2⟩)
  have hQ : ContinuousOn (fun p : ℝ × ℝ =>
      S.theta p.1 p.2 / S.lam p.1 p.2 -
        S.zeta p.1 p.2 / S.nu p.1 p.2) T :=
    (hθ.div hLam hLamNe).sub (hζ.div hNu hNuNe)
  have hOut : ContinuousOn (fun p : ℝ × ℝ =>
      S.theta p.1 p.2 / C1Solution.canonicalRadius S p *
        (S.theta p.1 p.2 / S.lam p.1 p.2 -
          S.zeta p.1 p.2 / S.nu p.1 p.2)) T :=
    (hθ.div hR hRne).mul hQ
  have hIn : ContinuousOn (fun p : ℝ × ℝ =>
      S.zeta p.1 p.2 / C1Solution.canonicalRadius S p *
        (S.theta p.1 p.2 / S.lam p.1 p.2 -
          S.zeta p.1 p.2 / S.nu p.1 p.2)) T :=
    (hζ.div hR hRne).mul hQ
  constructor
  · apply hOut.congr
    intro p hp
    simp only [sourceLogCorrection,
      sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]
  · apply hIn.congr
    intro p hp
    simp only [sourceLogCorrectionStar,
      sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]

private theorem outgoing_correction_aemeasurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    AEMeasurable (fun v => ENNReal.ofReal |sourceLogCorrection S u v|)
      (volume.restrict (Ioo u 1)) := by
  have hpath : ContinuousOn (fun v : ℝ => (u, v)) (Ioo u 1) := by fun_prop
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Ioo u 1)
      (openCoordTriangle 0 1) :=
    fun v hv => ⟨hu.1, hv.1, hv.2⟩
  have hcont := (log_corrections_continuousOn H hboot).1.comp hpath hmap
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont.abs).aemeasurable
    measurableSet_Ioo

private theorem incoming_correction_aemeasurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    AEMeasurable (fun u => ENNReal.ofReal |sourceLogCorrectionStar S u v|)
      (volume.restrict (Ioo 0 v)) := by
  have hpath : ContinuousOn (fun u : ℝ => (u, v)) (Ioo 0 v) := by fun_prop
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Ioo 0 v)
      (openCoordTriangle 0 1) :=
    fun u hu => ⟨hu.1, hu.2, hv.2⟩
  have hcont := (log_corrections_continuousOn H hboot).2.comp hpath hmap
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont.abs).aemeasurable
    measurableSet_Ioo

private theorem outgoing_mass_aemeasurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    AEMeasurable (fun v => ENNReal.ofReal (IsBVSolution.nuCoeff S u v))
      (volume.restrict (Ioo u 1)) := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  apply aemeasurable_Ioo_unit_of_cutoffs hu.2
  intro b hb
  have hU : (u, b) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.1.le, hb.1, hb.2⟩
  have hbound : ∀ v ∈ Ioc u b,
      |S.theta u v / S.lam u v| ≤ 15 * (sourceD S).toReal := by
    intro v hv
    exact source_theta_div_lam_le_sourceD H hr hcenter hboot
      (hBV.solution.development.outgoing_mem hU hv.1 hv.2)
  have hInt : IntegrableOn (IsBVSolution.nuCoeff S u) (Ioo u b) :=
    (hBV.nu_coeff_integrable_axis hU hbound).mono_set Ioo_subset_Ioc_self
  exact hInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal

private theorem incoming_mass_aemeasurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    AEMeasurable (fun u =>
      ENNReal.ofReal (-IsBVSolution.incomingCoeff S u v))
      (volume.restrict (Ioo 0 v)) := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have haccess : ∀ u ∈ Ico 0 v, (u, v) ∈ developmentWithInitialEdge 1 :=
    fun u hu => ⟨hu.1, hu.2, hv.2⟩
  have hbound : ∀ u ∈ Ico 0 v,
      |S.zeta u v / S.nu u v| ≤ 24 * (sourceD S).toReal := by
    intro u hu
    have hp := haccess u hu
    have hz := (eq4_3_pointwise H hr hcenter hboot hp).2
    have hnu := hBV.nu_le_neg_lower (by norm_num) hboot.1 hp
    have hnupos : (1 / 3 : ℝ) ≤ |S.nu u v| := by
      rw [abs_of_neg (by linarith only [hnu])]
      linarith only [hnu]
    have hd : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
    rw [abs_div]
    apply (div_le_iff₀ (by linarith only [hnupos])).2
    have hm := mul_le_mul_of_nonneg_left hnupos hd
    nlinarith only [hz, hm]
  have hInt : IntegrableOn (fun u => -IsBVSolution.incomingCoeff S u v)
      (Ioo 0 v) :=
    (hBV.incomingCoeff_integrable_axis hv.1 haccess hbound).neg.mono_set
      Ioo_subset_Ioc_self
  exact hInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal

private theorem outgoing_mass_expression_eq_nuCoeff {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) :
    (2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v) * (S.lam u v / S.r u v) =
      IsBVSolution.nuCoeff S u v := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hp).2
    linarith only [hratio]
  rw [hBV.nuCoeff_eq_mass_ratio_coefficient_out hp]
  field_simp [hrne, hgapne]

private theorem incoming_mass_expression_eq_incomingCoeff {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) :
    (2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v) * (S.nu u v / S.r u v) =
      IsBVSolution.incomingCoeff S u v := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hp).2
    linarith only [hratio]
  rw [IsBVSolution.incomingCoeff]
  field_simp [hrne, hgapne]

/-- Variation on an open unit interval is the supremum over compact upper
cutoffs. -/
theorem variation_Ioo_unit_eq_iSup_cutoff (f : ℝ → ℝ)
    {a : ℝ} (_ha : a < 1) :
    eVariationOn f (Ioo a 1) =
      ⨆ b ∈ Ioo a 1, eVariationOn f (Ioo a b) := by
  apply le_antisymm
  · rw [eVariationOn.eq_biSup_inter_Icc]
    apply iSup_le
    intro p
    apply iSup_le
    intro hp
    let b := (p.2 + 1) / 2
    have hb : b ∈ Ioo a 1 := by
      dsimp [b]
      constructor <;> linarith only [hp.2.1.1, hp.2.1.2]
    apply le_trans (eVariationOn.mono f (s := Ioo a b)
      (t := Ioo a 1 ∩ Icc p.1 p.2) ?_)
      (le_biSup (fun b => eVariationOn f (Ioo a b)) hb)
    intro x hx
    exact ⟨hx.1.1, by dsimp [b]; linarith only [hx.2.2, hp.2.1.2]⟩
  · apply iSup_le
    intro b
    apply iSup_le
    intro hb
    exact eVariationOn.mono f
      (fun x hx => ⟨hx.1, hx.2.trans hb.2⟩)

private theorem variation_le_three_lintegrals {a b : ℝ} (hab : a ≤ b)
    {f R M C : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpoint : ∀ t ∈ Ioo a b,
      |deriv f t| ≤ |R t| + M t + |C t|)
    (hMnonneg : ∀ t ∈ Ioo a b, 0 ≤ M t)
    (hM : AEMeasurable (fun t => ENNReal.ofReal (M t))
      (volume.restrict (Ioo a b)))
    (hC : AEMeasurable (fun t => ENNReal.ofReal |C t|)
      (volume.restrict (Ioo a b))) :
    eVariationOn f (Ioo a b) ≤
      (∫⁻ t in Ioo a b, ENNReal.ofReal |R t|) +
        (∫⁻ t in Ioo a b, ENNReal.ofReal (M t)) +
          (∫⁻ t in Ioo a b, ENNReal.ofReal |C t|) := by
  have hpointE (t : ℝ) (ht : t ∈ Ioo a b) :
      ENNReal.ofReal |deriv f t| ≤
        ENNReal.ofReal |R t| + ENNReal.ofReal (M t) +
          ENNReal.ofReal |C t| := by
    have h := ENNReal.ofReal_le_ofReal (hpoint t ht)
    rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (hMnonneg t ht))
      (abs_nonneg _), ENNReal.ofReal_add (abs_nonneg _) (hMnonneg t ht)] at h
    exact h
  calc
    eVariationOn f (Ioo a b) =
        ∫⁻ t in Ioo a b, ENNReal.ofReal |deriv f t| :=
      (null_lintegral_eq_scalar_variation hab hf (fun _ _ => rfl)).symm
    _ ≤ ∫⁻ t in Ioo a b,
          ENNReal.ofReal |R t| + ENNReal.ofReal (M t) +
            ENNReal.ofReal |C t| := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hpointE t ht
    _ = _ := by
      rw [lintegral_add_right' _ hC, lintegral_add_right' _ hM]

/-- Outgoing logarithmic variation bounded by residual, mass, and correction integrals. -/
theorem outgoing_log_variation_le_components {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
      (∫⁻ v in Ioo u 1,
        ENNReal.ofReal |sourceOutgoingLogResidual S u v|) +
        (∫⁻ v in Ioo u 1,
          ENNReal.ofReal (IsBVSolution.nuCoeff S u v)) +
          (∫⁻ v in Ioo u 1,
            ENNReal.ofReal |sourceLogCorrection S u v|) := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hMfull := outgoing_mass_aemeasurable H hr hcenter hboot hu
  have hCfull := outgoing_correction_aemeasurable H hboot hu
  rw [variation_Ioo_unit_eq_iSup_cutoff _ hu.2]
  apply iSup_le
  intro b
  apply iSup_le
  intro hb
  let B : ℝ := (b + 1) / 2
  let K := closedCoordTriangle (0 : ℝ) B
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, hb.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hb.2]
  have hbB : b < B := by dsimp [B]; linarith only [hb.2]
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u b) K := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2.trans hbB.le⟩
  have hpath : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u b) := by
    fun_prop
  have hlam := (C1Solution.five_fields_contDiffOn hB hB1 H).1
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) K :=
    hlam.log (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))
  have hslice : ContDiffOn ℝ 1 (fun t => Real.log (S.lam u t))
      (Icc u b) := hlog.comp hpath hmap
  have hAC : AbsolutelyContinuousOnInterval
      (fun t => Real.log (S.lam u t)) u b :=
    (show ContDiffOn ℝ 1 (fun t => Real.log (S.lam u t))
      (uIcc u b) by
        simpa only [uIcc_of_le hb.1.le] using hslice).absolutelyContinuousOnInterval
  have hsub : Ioo u b ⊆ Ioo u 1 :=
    fun t ht => ⟨ht.1, ht.2.trans hb.2⟩
  have hMmeas := hMfull.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hCmeas := hCfull.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hMnonneg (t : ℝ) (ht : t ∈ Ioo u b) :
      0 ≤ IsBVSolution.nuCoeff S u t :=
    IsBVSolution.nu_coeff_nonneg hBV.solution.development hBV
      ⟨hu.1.le, ht.1, ht.2.trans hb.2⟩
  have hpoint (t : ℝ) (ht : t ∈ Ioo u b) :
      |deriv (fun v => Real.log (S.lam u v)) t| ≤
        |sourceOutgoingLogResidual S u t| +
          IsBVSolution.nuCoeff S u t + |sourceLogCorrection S u t| := by
    have hp : (u, t) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, ht.1, ht.2.trans hb.2⟩
    have hEq : deriv (fun v => Real.log (S.lam u v)) t =
        sourceOutgoingLogResidual S u t +
          IsBVSolution.nuCoeff S u t - sourceLogCorrection S u t := by
      rw [sourceOutgoingLogResidual.eq_1,
        ← outgoing_mass_expression_eq_nuCoeff H hp]
      ring
    rw [hEq]
    calc
      |sourceOutgoingLogResidual S u t +
          IsBVSolution.nuCoeff S u t - sourceLogCorrection S u t| ≤
          |sourceOutgoingLogResidual S u t +
            IsBVSolution.nuCoeff S u t| +
            |sourceLogCorrection S u t| := abs_sub _ _
      _ ≤ (|sourceOutgoingLogResidual S u t| +
          |IsBVSolution.nuCoeff S u t|) +
            |sourceLogCorrection S u t| :=
        add_le_add_left (abs_add_le _ _) _
      _ = _ := by rw [abs_of_nonneg (hMnonneg t ht)]
  have hVar := variation_le_three_lintegrals hb.1.le hAC hpoint
    hMnonneg hMmeas hCmeas
  exact hVar.trans (by
    apply add_le_add
    · apply add_le_add <;> exact lintegral_mono_set hsub
    · exact lintegral_mono_set hsub)

/-- Incoming logarithmic variation bounded by the corrected residual,
mass, and correction integrals. -/
theorem incoming_log_variation_le_components {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤
      (∫⁻ u in Ioo 0 v,
        ENNReal.ofReal |sourceIncomingLogResidual S u v|) +
        (∫⁻ u in Ioo 0 v,
          ENNReal.ofReal (-IsBVSolution.incomingCoeff S u v)) +
          (∫⁻ u in Ioo 0 v,
            ENNReal.ofReal |sourceLogCorrectionStar S u v|) := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle (0 : ℝ) B
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 v) K := by
    intro u hu
    exact ⟨hu.1, hu.2, hvB.le⟩
  have hpath : ContDiffOn ℝ 1 (fun u : ℝ => (u, v)) (Icc 0 v) := by
    fun_prop
  have hnu := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) K :=
    hnu.neg.log (fun p hp => neg_ne_zero.mpr
      (C1Solution.nu_neg_closed_triangle hB hB1 H hp).ne)
  have hslice : ContDiffOn ℝ 1 (fun u => Real.log (-S.nu u v))
      (Icc 0 v) := hlog.comp hpath hmap
  have hAC : AbsolutelyContinuousOnInterval
      (fun u => Real.log (-S.nu u v)) 0 v :=
    (show ContDiffOn ℝ 1 (fun u => Real.log (-S.nu u v))
      (uIcc 0 v) by
        simpa only [uIcc_of_le hv.1.le] using hslice).absolutelyContinuousOnInterval
  have hMnonneg (u : ℝ) (hu : u ∈ Ioo 0 v) :
      0 ≤ -IsBVSolution.incomingCoeff S u v :=
    neg_nonneg.mpr (hBV.incomingCoeff_nonpos
      ⟨hu.1.le, hu.2, hv.2⟩)
  have hpoint (u : ℝ) (hu : u ∈ Ioo 0 v) :
      |deriv (fun t => Real.log (-S.nu t v)) u| ≤
        |sourceIncomingLogResidual S u v| -
          IsBVSolution.incomingCoeff S u v +
            |sourceLogCorrectionStar S u v| := by
    have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hu.2, hv.2⟩
    have hEq : deriv (fun t => Real.log (-S.nu t v)) u =
        sourceIncomingLogResidual S u v +
          IsBVSolution.incomingCoeff S u v +
            sourceLogCorrectionStar S u v := by
      rw [sourceIncomingLogResidual.eq_1,
        ← incoming_mass_expression_eq_incomingCoeff H hp]
      ring
    rw [hEq]
    calc
      |sourceIncomingLogResidual S u v +
          IsBVSolution.incomingCoeff S u v +
            sourceLogCorrectionStar S u v| ≤
          |sourceIncomingLogResidual S u v +
            IsBVSolution.incomingCoeff S u v| +
            |sourceLogCorrectionStar S u v| := abs_add_le _ _
      _ ≤ (|sourceIncomingLogResidual S u v| +
          |IsBVSolution.incomingCoeff S u v|) +
            |sourceLogCorrectionStar S u v| :=
        add_le_add_left (abs_add_le _ _) _
      _ = _ := by
        rw [abs_of_nonpos (neg_nonneg.mp (hMnonneg u hu))]
        ring
  exact variation_le_three_lintegrals hv.1.le hAC hpoint hMnonneg
    (incoming_mass_aemeasurable H hr hcenter hboot hv)
    (incoming_correction_aemeasurable H hboot hv)


/-- The incoming quadratic correction has the same quotient bound as the
outgoing correction, with the incoming null weight. -/
theorem source_log_correction_star_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) :
    |sourceLogCorrectionStar S u v| ≤
      39 * (sourceD S).toReal * (|S.zeta u v| / S.r u v) := by
  have hrad : 0 < S.r u v := H.solution.radius_pos (u, v) hp
  have hζdiv : 0 ≤ |S.zeta u v| / S.r u v :=
    div_nonneg (abs_nonneg _) hrad.le
  have hdiff := source_log_quotient_difference_bound H hr hcenter hboot hp
  rw [sourceLogCorrectionStar, abs_mul, abs_div, abs_of_pos hrad]
  calc
    |S.zeta u v| / S.r u v *
        |S.theta u v / S.lam u v - S.zeta u v / S.nu u v| ≤
        |S.zeta u v| / S.r u v * (39 * (sourceD S).toReal) :=
      mul_le_mul_of_nonneg_left hdiff hζdiv
    _ = 39 * (sourceD S).toReal * (|S.zeta u v| / S.r u v) := by ring

end ChristodoulouBV

end
