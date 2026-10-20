module

public import ChristodoulouBV.Existence.GlobalC1Exhaustion
public import ChristodoulouBV.Existence.C1Endpoint
import all ChristodoulouBV.Existence.C1EndpointTV
import Mathlib.Tactic

/-!
# Uniform bounds for the global C¹ witness

All estimates concern one total field with finite C¹ charts and the given
initial data. Constants are the fixed Section 4, bootstrap, and endpoint constants.
The outgoing variation exhaustion includes the initial ray.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The endpoint coefficient is the same universal coefficient used
after the global outgoing exhaustion. -/
theorem s6EndpointTVK_eq : s6EndpointTVK = 3 * s4SliceTVK := by
  rw [s6EndpointTVK]

/-- The universal coefficient controlling both complete ray variations is
strictly positive. -/
theorem s6EndpointTVK_pos : 0 < s6EndpointTVK := by
  rw [s6EndpointTVK_eq]
  exact mul_pos (by norm_num) s4SliceTVK_pos

/-- The no-first-exit and complete slice estimates hold in every unit
rescaling of the same global field. -/
theorem global_c1_no_first_exit
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) :
    let T := Uniqueness.rescaledFields S 0 a
    IsC1Solution (developmentWithInitialEdge 1) T ∧
      sourceZ T < s4Epsilon0 ∧
      (∀ p ∈ developmentWithInitialEdge 1,
        (1 / 3 : ℝ) + 1 / 36 ≤ T.lam p.1 p.2 ∧
        -(2 / 3 : ℝ) + 1 / 36 ≤ T.nu p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 + 1 / 36 ≤ (1 / 3 : ℝ)) ∧
      (∀ u ∈ Ico (0 : ℝ) 1,
        e1OutgoingTVFinite T u 1 ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD T).toReal)) ∧
      (∀ v ∈ Ioo (0 : ℝ) 1,
        e1IncomingTVFinite T 0 v ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD T).toReal)) := by
  have hB : 0 < a + 1 := ha.trans (lt_add_one a)
  have Hb := hfinite (a + 2) (by linarith)
  have hdataB : ∀ v ∈ Ioo (0 : ℝ) (a + 2),
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v := fun v hv => hdata v hv.1
  obtain ⟨HT, hZ, hgeometry⟩ :=
    no_first_exit hB (by linarith) Hb hdataB hD a ha (lt_add_one a)
  obtain ⟨hOut, hIn⟩ :=
    no_first_exit_slice_tv hB (by linarith) Hb hdataB hD a ha (lt_add_one a)
  exact ⟨HT, hZ, hgeometry, hOut, hIn⟩

/-- The universal strict bootstrap margins hold at every global point,
including `u=0`. -/
theorem global_c1_bootstrap_margins
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) + 1 / 36 ≤ S.lam p.1 p.2 ∧
      -(2 / 3 : ℝ) + 1 / 36 ≤ S.nu p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 + 1 / 36 ≤ (1 / 3 : ℝ) := by
  intro p hp
  let a := p.2 + 1
  have ha : 0 < a := by dsimp [a]; linarith [hp.1, hp.2]
  have hpa : (p.1 / a, p.2 / a) ∈ developmentWithInitialEdge 1 :=
    ⟨div_nonneg hp.1 ha.le, div_lt_div_of_pos_right hp.2 ha,
      (div_lt_one ha).mpr (lt_add_one p.2)⟩
  have h := (global_c1_no_first_exit hfinite hdata hD ha).2.2.1 _ hpa
  rw [Uniqueness.rescaled_mass_ratio S (a := 0) ha (p.1 / a) (p.2 / a)] at h
  simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
    mul_div_cancel₀ _ ha.ne', zero_add] using h

/-- The outgoing expansion never exceeds its initial gauge value. This
uses the signed mixed primitive and the BV mass and expansion signs. -/
theorem s6_lam_le_half_of_initial_gauge {b : ℝ} (hb : 0 < b) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2) :
    ∀ p ∈ developmentWithInitialEdge b, S.lam p.1 p.2 ≤ (1 / 2 : ℝ) := by
  have hBV := H.isBVSolution_development hb
  obtain ⟨c, hc, hLam⟩ := hBV.lam_bounded_below
  intro p hp
  have hseg : inSeg p.2 0 p.1 ⊆ developmentWithInitialEdge b := by
    intro q hq
    exact ⟨hq.1.1, by rw [hq.2]; exact hq.1.2.trans_lt hp.2.1,
      by rw [hq.2]; exact hp.2.2⟩
  let F : ℝ → ℝ := fun u =>
    (2 * S.m u p.2 / S.r u p.2) * S.lam u p.2 * S.nu u p.2 /
      ((1 - 2 * S.m u p.2 / S.r u p.2) * S.r u p.2)
  have hF (t : ℝ) (ht : t ∈ Icc 0 p.1) : F t ≤ 0 := by
    have htp : (t, p.2) ∈ developmentWithInitialEdge b := hseg ⟨ht, rfl⟩
    have hmu := hBV.mass_ratio_bounds htp
    have hnu : S.nu t p.2 ≤ 0 :=
      (hBV.nu_le_neg_lower hc hLam htp).trans (neg_nonpos.mpr hc.le)
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hmu.1 (H.solution.lam_pos _ htp).le) hnu)
      (mul_nonneg (sub_nonneg.mpr hmu.2.le) (H.solution.radius_pos _ htp).le)
  have hInt : 0 ≤ ∫ t in (0 : ℝ)..p.1, -F t :=
    intervalIntegral.integral_nonneg hp.1 (fun t ht => neg_nonneg.mpr (hF t ht))
  rw [intervalIntegral.integral_neg] at hInt
  have hprim := (H.solution.lam_in p.2 0 p.1 hp.1 hseg).2
  have hInit := initial_lam_eq_of_gauge H hr ⟨hp.1.trans_lt hp.2.1, hp.2.2⟩
  change S.lam p.1 p.2 - S.lam 0 p.2 = ∫ t in (0 : ℝ)..p.1, F t at hprim
  linarith only [hInt, hprim, hInit]

/-- The six geometry inequalities hold pointwise for the same field
that carries the finite C¹ charts and no-first-exit bounds. -/
theorem global_c1_geometry
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ 2 / 3 ∧
      (2 / 3 : ℝ) ≤ 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≤ 1 := by
  have hmargin := global_c1_bootstrap_margins hfinite hdata hD
  intro p hp
  have hb : 0 < p.2 + 1 := by linarith [hp.1, hp.2]
  have H := hfinite (p.2 + 1) hb
  have hpb : p ∈ developmentWithInitialEdge (p.2 + 1) :=
    ⟨hp.1, hp.2, lt_add_one p.2⟩
  have hBV := H.isBVSolution_development hb
  have hLam : ∀ q ∈ developmentWithInitialEdge (p.2 + 1),
      (1 / 3 : ℝ) ≤ S.lam q.1 q.2 := by
    intro q hq
    linarith only [(hmargin q ⟨hq.1, hq.2.1⟩).1]
  have hnu := hBV.nu_le_neg_lower (by norm_num : (0 : ℝ) < 1 / 3) hLam hpb
  have hmu := (hBV.mass_ratio_bounds hpb).1
  have hupper := s6_lam_le_half_of_initial_gauge hb H
    (fun v hv => (hdata v hv.1).1) p hpb
  obtain ⟨hl, hn, hm⟩ := hmargin p hp
  exact ⟨by linarith only [hl], hupper, by linarith only [hnu],
    by linarith only [hn], by linarith only [hm], by linarith only [hmu]⟩

private theorem variation_Ioi_le_of_finite (f : ℝ → ℝ) (u : ℝ) {C : ℝ≥0∞}
    (hcut : ∀ a : ℝ, u < a → eVariationOn f (Ioo u a) ≤ C) :
    eVariationOn f (Ioi u) ≤ C := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  obtain ⟨hp₁, hp₂, _⟩ := hp
  have hua : u < p.2 + 1 := hp₂.trans (lt_add_one p.2)
  have hsub : Ioi u ∩ Icc p.1 p.2 ⊆ Ioo u (p.2 + 1) :=
    fun _ hx => ⟨hx.1, hx.2.2.trans_lt (lt_add_one p.2)⟩
  exact (eVariationOn.mono f hsub).trans (hcut _ hua)

/-- Both complete three-term ray variations have the universal endpoint
coefficient, independent of the datum, its scalar offset, and the ray.
The outgoing bound includes the initial ray `u=0`. -/
theorem global_c1_universal_tv_bound
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    (∀ u : ℝ, 0 ≤ u → e1OutgoingTV S u ≤
      ENNReal.ofReal (s6EndpointTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) ∧
    (∀ v : ℝ, 0 < v → e1IncomingTV S v ≤
      ENNReal.ofReal (s6EndpointTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) := by
  let C := ENNReal.ofReal (s4SliceTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)
  have hconst : C + C + C =
      ENNReal.ofReal (s6EndpointTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) := by
    rw [s6EndpointTVK_eq, mul_assoc,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    dsimp only [C]
    ring
  constructor
  · intro u hu
    have hcut (a : ℝ) (hua : u < a) : e1OutgoingTVFinite S u a ≤ C := by
      have ha : 0 < a := hu.trans_lt hua
      exact (s6_finite_cutoff_three_term_tv (by linarith : 0 < a + 1)
        (by linarith : a + 1 < a + 2) (hfinite (a + 2) (by linarith))
        (fun v hv => hdata v hv.1) hD ha (lt_add_one a)).1 u ⟨hu, hua⟩
    have hq : eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioi u) ≤ C := by
      apply variation_Ioi_le_of_finite
      intro a hua
      exact (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤
        eVariationOn (S.phi u) (Ioo u a) from bot_le)).trans
        ((le_add_of_nonneg_right bot_le).trans (hcut a hua))
    have hp : eVariationOn (S.phi u) (Ioi u) ≤ C := by
      apply variation_Ioi_le_of_finite
      intro a hua
      exact (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤
        eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u a)
          from bot_le)).trans
        ((le_add_of_nonneg_right bot_le).trans (hcut a hua))
    have hl : eVariationOn (fun v => Real.log (S.lam u v)) (Ioi u) ≤ C := by
      apply variation_Ioi_le_of_finite
      intro a hua
      exact (le_add_of_nonneg_left bot_le).trans (hcut a hua)
    exact (add_le_add (add_le_add hq hp) hl).trans_eq hconst
  · intro v hv
    have hfamily : ∀ b ∈ Ioo (0 : ℝ) (v + 1),
        IsC1Solution (developmentWithInitialEdge b) S ∧
        ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2 ∧ S.alpha 0 w = alpha₀ w :=
      fun b hb => ⟨hfinite b hb.1, fun w hw => hdata w hw.1⟩
    exact (endpointPatch_universal_tv_bound (by linarith : 0 < v + 1)
      hD hfamily).2 v ⟨hv, lt_add_one v⟩

end ChristodoulouBV

end
