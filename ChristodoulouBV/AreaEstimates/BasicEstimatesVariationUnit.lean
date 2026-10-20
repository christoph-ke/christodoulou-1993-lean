module

public import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationOutgoing
public import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationIncoming
public import ChristodoulouBV.C1Solution.Rescaling
public import ChristodoulouBV.C1Solution.FrozenBridge
import all ChristodoulouBV.Uniqueness.RescalingBasic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Unit-triangle scope of Lemma 4.1

Positive dilation applies the compact proof to every interior cutoff of the
source's closed C¹ triangle. Variation on the open outgoing characteristic is
the supremum of these cutoff variations.
-/

public section

open Set MeasureTheory
open scoped Topology Interval ENNReal

namespace ChristodoulouBV

open Uniqueness

private theorem variation_Ioo_unit_eq_iSup_cutoff (f : ℝ → ℝ)
    {a : ℝ} (_ha : a < 1) :
    eVariationOn f (Ioo a 1) =
      ⨆ h ∈ Ioo a 1, eVariationOn f (Ioo a h) := by
  apply le_antisymm
  · rw [eVariationOn.eq_biSup_inter_Icc]
    apply iSup_le
    intro p
    apply iSup_le
    intro hp
    let h := (p.2 + 1) / 2
    have hh : h ∈ Ioo a 1 := by
      dsimp [h]
      constructor <;> linarith only [hp.2.1.1, hp.2.1.2]
    apply le_trans (eVariationOn.mono f (s := Ioo a h) (t := Ioo a 1 ∩ Icc p.1 p.2) ?_)
      (le_biSup (fun h => eVariationOn f (Ioo a h)) hh)
    intro x hx
    exact ⟨hx.1.1, by dsimp [h]; linarith only [hx.2.2, hp.2.1.2]⟩
  · apply iSup_le
    intro h
    apply iSup_le
    intro hh
    exact eVariationOn.mono f (fun x hx => ⟨hx.1, hx.2.trans hh.2⟩)

private theorem variation_scale_Ioo (f : ℝ → ℝ)
    {a b h : ℝ} (hh : 0 < h) :
    eVariationOn (fun t => f (h * t)) (Ioo (a / h) (b / h)) =
      eVariationOn f (Ioo a b) := by
  have himage : (fun t : ℝ => h * t) '' Ioo (a / h) (b / h) = Ioo a b := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor
      · have := (div_lt_iff₀ hh).mp ht.1
        simpa only [mul_comm] using this
      · have := (lt_div_iff₀ hh).mp ht.2
        simpa only [mul_comm] using this
    · intro hx
      refine ⟨x / h, ?_, by field_simp [hh.ne']⟩
      constructor
      · exact (div_lt_div_iff_of_pos_right hh).mpr hx.1
      · exact (div_lt_div_iff_of_pos_right hh).mpr hx.2
  rw [← himage]
  exact eVariationOn.comp_eq_of_monotoneOn f (fun t => h * t)
    ((show Monotone (fun t : ℝ => h * t) from
      fun _ _ hxy => mul_le_mul_of_nonneg_left hxy hh.le).monotoneOn _)

private theorem unit_phi_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := by
  simpa only [C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)] using H.phi_c1

private theorem unit_vertical_deriv {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1))
    {u t B : ℝ} (hu : 0 < u) (hut : u < t) (htB : t < B) (hB : B < 1) :
    deriv (fun s => F (u, s)) t =
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, t)) (0, 1) := by
  have hp : (u, t) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, hut, htB⟩
  have hpK : (u, t) ∈ closedCoordTriangle 0 1 :=
    ⟨hu.le, hut.le, (htB.trans hB).le⟩
  have hdiff : DifferentiableAt ℝ F (u, t) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, t)
      (show (u, t) ∈ interior (closedCoordTriangle 0 1) by
        rw [interior_closedCoordTriangle]
        exact ⟨hu, hut, htB.trans hB⟩))
      |>.differentiableAt (isOpen_interior.mem_nhds (by
        rw [interior_closedCoordTriangle]
        exact ⟨hu, hut, htB.trans hB⟩))
  have hpair : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) t :=
    (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpair
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty (lt_trans hu hut |>.trans htB))
  rw [fderivWithin_eq_fderiv (hunique (u, t) (interior_subset hp)) hdiff]
  simpa only [Function.comp_def] using hcomp.deriv

private theorem unit_horizontal_deriv {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1))
    {t v B : ℝ} (ht : 0 < t) (htv : t < v) (hvB : v < B) (hB : B < 1) :
    deriv (fun s => F (s, v)) t =
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (t, v)) (1, 0) := by
  have hp : (t, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨ht, htv, hvB⟩
  have hdiff : DifferentiableAt ℝ F (t, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (t, v)
      (show (t, v) ∈ interior (closedCoordTriangle 0 1) by
        rw [interior_closedCoordTriangle]
        exact ⟨ht, htv, hvB.trans hB⟩))
      |>.differentiableAt (isOpen_interior.mem_nhds (by
        rw [interior_closedCoordTriangle]
        exact ⟨ht, htv, hvB.trans hB⟩))
  have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t v)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpair
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle 0 B) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty (lt_trans ht htv |>.trans hvB))
  rw [fderivWithin_eq_fderiv (hunique (t, v) (interior_subset hp)) hdiff]
  simpa only [Function.comp_def] using hcomp.deriv

private theorem unit_outgoing_pointwise {u t : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo u 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    |S.theta u t| / S.r u t = |deriv (S.phi u) t| := by
  let B := (t + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, ht.1]
  have htB : t < B := by dsimp [B]; linarith only [ht.2]
  have hB1 : B < 1 := by dsimp [B]; linarith only [ht.2]
  have hpB : (u, t) ∈ closedCoordTriangle 0 B :=
    ⟨hu.1.le, ht.1.le, htB.le⟩
  have hderiv := unit_vertical_deriv (unit_phi_contDiffOn H)
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

private theorem unit_incoming_pointwise {t v : ℝ}
    (hv : v ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo 0 v)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    |S.zeta t v| / S.r t v =
      |deriv (fun s => S.phi s v) t| := by
  let B := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hpB : (t, v) ∈ closedCoordTriangle 0 B :=
    ⟨ht.1.le, ht.2.le, hvB.le⟩
  have hderiv := unit_horizontal_deriv (unit_phi_contDiffOn H)
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

private theorem outgoing_variation_contract {b u : ℝ}
    (hb : 1 < b) (hu : u ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    eVariationOn (S.phi u) (Ioo u 1) ≤
      eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u 1) := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (S.phi u) (Icc u 1) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).comp
      hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi u) u 1 :=
    (show ContDiffOn ℝ 1 (S.phi u) (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hphi).absolutelyContinuousOnInterval
  rw [← null_lintegral_eq_scalar_variation hu.2.le hAC
    (fun t ht => outgoing_theta_over_r_eq_abs_phi_deriv hb hu ht H)]
  exact outgoing_scalar_variation_bound hb hu H

private theorem incoming_variation_contract {b v : ℝ}
    (hb : 1 < b) (hv : v ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    eVariationOn (fun t => S.phi t v) (Ioo 0 v) ≤
      eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo 0 v) := by
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨ht.1, ht.2, hv.2.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (fun t => S.phi t v) (Icc 0 v) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).comp
      hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (fun t => S.phi t v) 0 v :=
    (show ContDiffOn ℝ 1 (fun t => S.phi t v) (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hphi).absolutelyContinuousOnInterval
  rw [← null_lintegral_eq_scalar_variation hv.1.le hAC
    (fun t ht => incoming_zeta_over_r_eq_abs_phi_deriv hb hv ht H)]
  exact incoming_scalar_variation_bound hb hv H

private theorem unit_outgoing_variation_contract {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (S.phi u) (Ioo u 1) ≤
      eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u 1) := by
  rw [variation_Ioo_unit_eq_iSup_cutoff (S.phi u) hu.2]
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  have hh0 : 0 < h := hu.1.trans hh.1
  have hscaled : u / h ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨div_pos hu.1 hh0,
      (div_lt_one hh0).mpr hh.1⟩
  have hb : 1 < 1 / h := by
    apply (lt_div_iff₀ hh0).mpr
    simpa only [one_mul] using hh.2
  let T := rescaledFields S 0 h
  have Hh : IsC1Solution (developmentWithInitialEdge (1 / h)) T :=
    C1Solution.rescaled_development_isC1Solution H hh0
  have hphi := variation_scale_Ioo (S.phi u) (a := u) (b := h) hh0
  have hF := variation_scale_Ioo (fun t => S.alpha u t / S.lam u t)
    (a := u) (b := h) hh0
  have hFmono : eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u h) ≤
      eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u 1) :=
    eVariationOn.mono _ (fun t ht => ⟨ht.1, ht.2.trans hh.2⟩)
  calc
    eVariationOn (S.phi u) (Ioo u h) =
        eVariationOn (T.phi (u / h)) (Ioo (u / h) 1) := by
      simpa only [T, rescaledFields, affineCoordinate, zero_add,
        mul_div_cancel₀ u hh0.ne', div_self hh0.ne'] using hphi.symm
    _ ≤ eVariationOn (fun t => T.alpha (u / h) t / T.lam (u / h) t)
          (Ioo (u / h) 1) := outgoing_variation_contract hb hscaled Hh
    _ = eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u h) := by
      simpa only [T, rescaledFields, affineCoordinate, zero_add,
        mul_div_cancel₀ u hh0.ne', div_self hh0.ne'] using hF
    _ ≤ _ := hFmono

private theorem unit_incoming_variation_contract {v : ℝ}
    (hv : v ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (fun t => S.phi t v) (Ioo 0 v) ≤
      eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo 0 v) := by
  let h := (v + 1) / 2
  have hh0 : 0 < h := by dsimp [h]; linarith only [hv.1]
  have hvh : v < h := by dsimp [h]; linarith only [hv.2]
  have hh1 : h < 1 := by dsimp [h]; linarith only [hv.2]
  have hscaled : v / h ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hv.1 hh0, (div_lt_one hh0).mpr hvh⟩
  have hb : 1 < 1 / h := by
    apply (lt_div_iff₀ hh0).mpr
    simpa only [one_mul] using hh1
  let T := rescaledFields S 0 h
  have Hh : IsC1Solution (developmentWithInitialEdge (1 / h)) T :=
    C1Solution.rescaled_development_isC1Solution H hh0
  have hphi := variation_scale_Ioo (fun t => S.phi t v)
    (a := 0) (b := v) hh0
  have hF := variation_scale_Ioo (fun t => S.beta t v / S.nu t v)
    (a := 0) (b := v) hh0
  calc
    eVariationOn (fun t => S.phi t v) (Ioo 0 v) =
        eVariationOn (fun t => T.phi t (v / h)) (Ioo 0 (v / h)) := by
      simpa only [T, rescaledFields, affineCoordinate, zero_add,
        mul_div_cancel₀ v hh0.ne', zero_div] using hphi.symm
    _ ≤ eVariationOn (fun t => T.beta t (v / h) / T.nu t (v / h))
          (Ioo 0 (v / h)) := incoming_variation_contract hb hscaled Hh
    _ = eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo 0 v) := by
      simpa only [T, rescaledFields, affineCoordinate, zero_add,
        mul_div_cancel₀ v hh0.ne', zero_div] using hF

/-- Lemma 4.1's outgoing null integral under the exact C¹ hypothesis on
the closed unit triangle. -/
theorem outgoing_scalar_variation_bound_unit {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t)) ≤
      eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u 1) := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (S.phi u) (Icc u 1) :=
    (unit_phi_contDiffOn H).comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi u) u 1 :=
    (show ContDiffOn ℝ 1 (S.phi u) (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hphi).absolutelyContinuousOnInterval
  calc
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t)) =
        eVariationOn (S.phi u) (Ioo u 1) :=
      null_lintegral_eq_scalar_variation hu.2.le hAC
        (fun t ht => unit_outgoing_pointwise hu ht H)
    _ ≤ _ := unit_outgoing_variation_contract hu H

/-- Lemma 4.1's incoming null integral under the exact C¹ hypothesis on
the closed unit triangle. -/
theorem incoming_scalar_variation_bound_unit {v : ℝ}
    (hv : v ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    (∫⁻ t in Ioo 0 v, ENNReal.ofReal (|S.zeta t v| / S.r t v)) ≤
      eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo 0 v) := by
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨ht.1, ht.2, hv.2.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (fun t => S.phi t v) (Icc 0 v) :=
    (unit_phi_contDiffOn H).comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (fun t => S.phi t v) 0 v :=
    (show ContDiffOn ℝ 1 (fun t => S.phi t v) (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hphi).absolutelyContinuousOnInterval
  calc
    (∫⁻ t in Ioo 0 v, ENNReal.ofReal (|S.zeta t v| / S.r t v)) =
        eVariationOn (fun t => S.phi t v) (Ioo 0 v) :=
      null_lintegral_eq_scalar_variation hv.1.le hAC
        (fun t ht => unit_incoming_pointwise hv ht H)
    _ ≤ _ := unit_incoming_variation_contract hv H

end ChristodoulouBV

end
