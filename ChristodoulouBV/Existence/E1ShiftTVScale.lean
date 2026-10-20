module

public import ChristodoulouBV.Existence.E1ShiftTV
public import ChristodoulouBV.C1Solution.Rescaling
import Mathlib.Tactic

/-!
# Finite null segments and physical rescaling

The physical chart `(u,v) ↦ (b*u,b*v)` sends `(0,1)` to `(0,b)`.
Each term of the three-term variation is exactly preserved, including the
open endpoints, and initial datum variation has the same property.
-/

@[expose] public section

open Set
open ChristodoulouBV.Uniqueness
open scoped ENNReal

namespace ChristodoulouBV

/-- Outgoing three-term TV on the open finite segment `(u,b)`. -/
noncomputable def e1OutgoingTVFinite (S : Fields) (u b : ℝ) : ℝ≥0∞ :=
  eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u b) +
  eVariationOn (S.phi u) (Ioo u b) +
  eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u b)

/-- Incoming three-term TV on the open finite segment `(a,v)`. -/
noncomputable def e1IncomingTVFinite (S : Fields) (a v : ℝ) : ℝ≥0∞ :=
  eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo a v) +
  eVariationOn (fun u => S.phi u v) (Ioo a v) +
  eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo a v)

/-- Shifting the scalar leaves the complete outgoing TV on a finite open
segment unchanged. -/
theorem e1OutgoingTVFinite_scalarShift (S : Fields) (c u b : ℝ)
    (hLam : ∀ v ∈ Ioo u b, S.lam u v ≠ 0) :
    e1OutgoingTVFinite (scalarShift S c) u b = e1OutgoingTVFinite S u b := by
  have hq : EqOn (fun v => (scalarShift S c).alpha u v /
      (scalarShift S c).lam u v)
      (fun v => S.alpha u v / S.lam u v + c) (Ioo u b) := by
    intro v hv
    exact scalarShift_alpha_div_lam S c u v (hLam v hv)
  unfold e1OutgoingTVFinite
  rw [eVariationOn.congr hq, eVariationOn_add_const_real,
    scalarShift_phi_variation_out]
  change _ + _ + eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u b) = _
  rfl

/-- Shifting the scalar leaves the complete incoming TV on a finite open
segment unchanged. -/
theorem e1IncomingTVFinite_scalarShift (S : Fields) (c a v : ℝ)
    (hν : ∀ u ∈ Ioo a v, S.nu u v ≠ 0) :
    e1IncomingTVFinite (scalarShift S c) a v = e1IncomingTVFinite S a v := by
  have hq : EqOn (fun u => (scalarShift S c).beta u v /
      (scalarShift S c).nu u v)
      (fun u => S.beta u v / S.nu u v + c) (Ioo a v) := by
    intro u hu
    exact scalarShift_beta_div_nu S c u v (hν u hu)
  unfold e1IncomingTVFinite
  rw [eVariationOn.congr hq, eVariationOn_add_const_real,
    scalarShift_phi_variation_in]
  change _ + _ + eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo a v) = _
  rfl

/-- Positive multiplication exactly preserves variation on open intervals. -/
theorem e1_variation_scale_Ioo (f : ℝ → ℝ) {a b h : ℝ} (hh : 0 < h) :
    eVariationOn (fun t => f (h * t)) (Ioo a b) =
      eVariationOn f (Ioo (h * a) (h * b)) := by
  have hc : Continuous (fun t : ℝ => h * t) := continuous_const.mul continuous_id
  have hm : StrictMono (fun t : ℝ => h * t) :=
    fun _ _ hxy => mul_lt_mul_of_pos_left hxy hh
  change eVariationOn (f ∘ fun t : ℝ => h * t) (Ioo a b) = _
  rw [eVariationOn.comp_eq_of_monotoneOn f (fun t : ℝ => h * t)
      (hm.monotone.monotoneOn _), hc.image_Ioo_of_strictMono hm]

/-- Every outgoing term has weight zero under the physical chart. -/
theorem e1OutgoingTVFinite_rescaled (S : Fields) {h : ℝ} (hh : 0 < h)
    (u b : ℝ) :
    e1OutgoingTVFinite (rescaledFields S 0 h) u b =
      e1OutgoingTVFinite S (h * u) (h * b) := by
  have hq := e1_variation_scale_Ioo
    (fun v => S.alpha (h * u) v / S.lam (h * u) v)
    (a := u) (b := b) hh
  have hp := e1_variation_scale_Ioo (S.phi (h * u))
    (a := u) (b := b) hh
  have hl := e1_variation_scale_Ioo
    (fun v => Real.log (S.lam (h * u) v)) (a := u) (b := b) hh
  simpa only [e1OutgoingTVFinite, rescaledFields, affineCoordinate,
    zero_add, mul_zero] using congrArg₂ (fun x y : ℝ≥0∞ => x + y)
      (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hq hp) hl

/-- Every incoming term has weight zero under the physical chart. -/
theorem e1IncomingTVFinite_rescaled (S : Fields) {h : ℝ} (hh : 0 < h)
    (a v : ℝ) :
    e1IncomingTVFinite (rescaledFields S 0 h) a v =
      e1IncomingTVFinite S (h * a) (h * v) := by
  have hq := e1_variation_scale_Ioo
    (fun u => S.beta u (h * v) / S.nu u (h * v))
    (a := a) (b := v) hh
  have hp := e1_variation_scale_Ioo
    (fun u => S.phi u (h * v)) (a := a) (b := v) hh
  have hl := e1_variation_scale_Ioo
    (fun u => Real.log (-S.nu u (h * v))) (a := a) (b := v) hh
  simpa only [e1IncomingTVFinite, rescaledFields, affineCoordinate,
    zero_add, mul_zero] using congrArg₂ (fun x y : ℝ≥0∞ => x + y)
      (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hq hp) hl

/-- A unit chart sees exactly the datum TV on the physical cutoff. -/
theorem sourceD_rescaled_eq_cutoff (S : Fields) {h : ℝ} (hh : 0 < h) :
    sourceD (rescaledFields S 0 h) =
      eVariationOn (S.alpha 0) (Ioo 0 h) := by
  simpa only [sourceD, rescaledFields, affineCoordinate,
    zero_add, mul_zero, mul_one] using
    e1_variation_scale_Ioo (S.alpha 0)
      (a := 0) (b := 1) hh

/-- The complete smooth small-data bound, with its exact six premises, in the
finite TV notation used by the quantitative existence construction. The outgoing estimate includes `u=0`. -/
theorem e1_centered_three_term_tv_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    (∀ u ∈ Ico (0 : ℝ) 1,
      e1OutgoingTVFinite S u 1 ≤
        ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      e1IncomingTVFinite S 0 v ≤
        ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) := by
  simpa only [e1OutgoingTVFinite, e1IncomingTVFinite] using
    s4_three_term_slice_tv_unit H hr hcenter hboot hD hZ

/-- Scalar centering is removed without an amplitude premise. The six
assumptions are exactly the smooth small-data premises apart from the normalization
`S.phi 0 0 = 0`, which is now performed inside the proof. -/
theorem e1_three_term_tv_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    (∀ u ∈ Ico (0 : ℝ) 1,
      e1OutgoingTVFinite S u 1 ≤
        ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      e1IncomingTVFinite S 0 v ≤
        ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) := by
  let T := scalarShift S (-S.phi 0 0)
  have HT : IsC1Solution (developmentWithInitialEdge 1) T :=
    H.scalarShift _
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := hr
  have hcT : T.phi 0 0 = 0 := by
    dsimp [T, scalarShift]
    ring
  have hbT : s4_bootstrap T := by
    simpa only [T, s4_bootstrap, scalarShift] using hboot
  have hDT : sourceD T = sourceD S :=
    sourceD_scalarShift H hr _ (by norm_num)
  have hZT : sourceZ T = sourceZ S := by
    simp only [T, sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  have hbase := e1_centered_three_term_tv_unit HT hrT hcT hbT
    (by simpa only [hDT] using hD) (by simpa only [hZT] using hZ)
  have hrestore : scalarShift T (S.phi 0 0) = S := by
    simpa only [T, neg_neg] using scalarShift_neg S (-S.phi 0 0)
  constructor
  · intro u hu
    have hLam : ∀ v ∈ Ioo u 1, T.lam u v ≠ 0 := by
      intro v hv
      exact (HT.solution.lam_pos (u, v) ⟨hu.1, hv.1, hv.2⟩).ne'
    have heq := e1OutgoingTVFinite_scalarShift T (S.phi 0 0) u 1 hLam
    rw [hrestore] at heq
    calc
      e1OutgoingTVFinite S u 1 = e1OutgoingTVFinite T u 1 := heq
      _ ≤ _ := by simpa only [hDT] using hbase.1 u hu
  · intro v hv
    have hBV : IsBVSolution (developmentWithInitialEdge 1) T :=
      HT.isBVSolution_development (by norm_num)
    obtain ⟨c, hc, hLam⟩ := hBV.lam_bounded_below
    have hν : ∀ u ∈ Ioo 0 v, T.nu u v ≠ 0 := by
      intro u hu
      have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
        ⟨hu.1.le, hu.2, hv.2⟩
      exact ne_of_lt ((hBV.nu_le_neg_lower hc hLam hp).trans_lt
        (neg_lt_zero.mpr hc))
    have heq := e1IncomingTVFinite_scalarShift T (S.phi 0 0) 0 v hν
    rw [hrestore] at heq
    calc
      e1IncomingTVFinite S 0 v = e1IncomingTVFinite T 0 v := heq
      _ ≤ _ := by simpa only [hDT] using hbase.2 v hv

/-- The uncentered smooth small-data estimate on any physical finite cutoff. Its
bootstrap and smallness hypotheses are precisely the smooth small-data hypotheses in the
unit chart; no scalar amplitude is assumed. -/
theorem e1_three_term_tv_cutoff {S : Fields} {b : ℝ} (hb : 0 < b)
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hboot : s4_bootstrap (rescaledFields S 0 b))
    (hD : sourceD (rescaledFields S 0 b) ≤ s4Epsilon0)
    (hZ : sourceZ (rescaledFields S 0 b) ≤ s4Epsilon0) :
    (∀ u ∈ Ico (0 : ℝ) b,
      e1OutgoingTVFinite S u b ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn (S.alpha 0) (Ioo 0 b)).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) b,
      e1IncomingTVFinite S 0 v ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn (S.alpha 0) (Ioo 0 b)).toReal)) := by
  let T := rescaledFields S 0 b
  have HT : IsC1Solution (developmentWithInitialEdge 1) T := by
    simpa only [T, div_self hb.ne'] using
      C1Solution.rescaled_development_isC1Solution H hb
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := by
    intro v hv
    have hvb : b * v ∈ Ioo (0 : ℝ) b := by
      exact ⟨mul_pos hb hv.1, (mul_lt_mul_of_pos_left hv.2 hb).trans_eq
        (mul_one b)⟩
    have hval : S.r 0 (b * v) / b = v / 2 := by
      rw [hr _ hvb]
      field_simp [hb.ne']
    simpa only [T, rescaledFields, affineCoordinate, mul_zero, zero_add]
      using hval
  have hunit := e1_three_term_tv_unit HT hrT hboot hD hZ
  have hsrc : sourceD T = eVariationOn (S.alpha 0) (Ioo 0 b) :=
    sourceD_rescaled_eq_cutoff S hb
  constructor
  · intro u hu
    have hu' : u / b ∈ Ico (0 : ℝ) 1 := by
      refine ⟨div_nonneg hu.1 hb.le, ?_⟩
      apply (div_lt_iff₀ hb).mpr
      simpa only [one_mul] using hu.2
    have hscale : e1OutgoingTVFinite T (u / b) 1 =
        e1OutgoingTVFinite S u b := by
      have hbu : b * (u / b) = u := by field_simp [hb.ne']
      simpa only [T, hbu, mul_one] using
        e1OutgoingTVFinite_rescaled S hb (u / b) 1
    simpa only [hscale, hsrc] using hunit.1 (u / b) hu'
  · intro v hv
    have hv' : v / b ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨div_pos hv.1 hb, ?_⟩
      apply (div_lt_iff₀ hb).mpr
      simpa only [one_mul] using hv.2
    have hscale : e1IncomingTVFinite T 0 (v / b) =
        e1IncomingTVFinite S 0 v := by
      have hbv : b * (v / b) = v := by field_simp [hb.ne']
      simpa only [T, hbv, mul_zero] using
        e1IncomingTVFinite_rescaled S hb 0 (v / b)
    simpa only [hscale, hsrc] using hunit.2 (v / b) hv'

/-- The initial variation on every finite cutoff is bounded by the same
global datum variation on `(0,∞)`. -/
theorem e1_source_variation_cutoff_le_global (S : Fields) (b : ℝ) :
    eVariationOn (S.alpha 0) (Ioo 0 b) ≤
      eVariationOn (S.alpha 0) (Ioi 0) := by
  exact eVariationOn.mono _ (fun _ hx => hx.1)

/-- The physical cutoff estimate uses one datum TV and one universal
coefficient for all positive cutoffs. Finiteness of the global TV is exactly
the consequence of the strict small-data hypothesis needed for `toReal`.
The smooth small-data hypotheses remain those on the scaled unit chart. -/
theorem e1_three_term_tv_cutoff_globalD {S : Fields} {b : ℝ} (hb : 0 < b)
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    (hboot : s4_bootstrap (rescaledFields S 0 b))
    (hD : sourceD (rescaledFields S 0 b) ≤ s4Epsilon0)
    (hZ : sourceZ (rescaledFields S 0 b) ≤ s4Epsilon0)
    (hfinite : eVariationOn (S.alpha 0) (Ioi 0) ≠ ⊤) :
    (∀ u ∈ Ico (0 : ℝ) b,
      e1OutgoingTVFinite S u b ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn (S.alpha 0) (Ioi 0)).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) b,
      e1IncomingTVFinite S 0 v ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn (S.alpha 0) (Ioi 0)).toReal)) := by
  have hcut := e1_three_term_tv_cutoff hb H hr hboot hD hZ
  have hreal : (eVariationOn (S.alpha 0) (Ioo 0 b)).toReal ≤
      (eVariationOn (S.alpha 0) (Ioi 0)).toReal :=
    ENNReal.toReal_mono hfinite (e1_source_variation_cutoff_le_global S b)
  have hK : ENNReal.ofReal (s4SliceTVK *
      (eVariationOn (S.alpha 0) (Ioo 0 b)).toReal) ≤
      ENNReal.ofReal (s4SliceTVK *
        (eVariationOn (S.alpha 0) (Ioi 0)).toReal) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hreal s4SliceTVK_pos.le
  exact ⟨fun u hu => (hcut.1 u hu).trans hK,
    fun v hv => (hcut.2 v hv).trans hK⟩

end ChristodoulouBV

end
