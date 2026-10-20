module

public import ChristodoulouBV.Existence.C1Family
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The universal small-data threshold for the C¹ bootstrap

The threshold is fixed before the characteristic datum.  It uses the
numerical constants of Section 4 and the common slice variation constant.
-/

@[expose] public section

open Set Filter
open scoped ENNReal Topology

namespace ChristodoulouBV

private theorem variation_left_endpoint_bound {f : ℝ → ℝ}
    {a b y L : ℝ} (hy : y ∈ Ioo a b)
    (hlim : Filter.Tendsto f (𝓝[>] a) (𝓝 L)) :
    ENNReal.ofReal |f y - L| ≤ eVariationOn f (Ioo a b) := by
  have hevent : ∀ᶠ x in 𝓝[>] a,
      ENNReal.ofReal |f y - f x| ≤ eVariationOn f (Ioo a b) := by
    filter_upwards [Ioo_mem_nhdsGT hy.1] with x hx
    have hx' : x ∈ Ioo a b := ⟨hx.1, hx.2.trans hy.2⟩
    simpa only [edist_dist, Real.dist_eq] using
      eVariationOn.edist_le f hy hx'
  have ht : Filter.Tendsto
      (fun x => ENNReal.ofReal |f y - f x|) (𝓝[>] a)
      (𝓝 (ENNReal.ofReal |f y - L|)) := by
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.sub hlim).abs))
  exact le_of_tendsto_of_tendsto ht tendsto_const_nhds hevent

private theorem variation_right_endpoint_bound {f : ℝ → ℝ}
    {a b x L : ℝ} (hx : x ∈ Ioo a b)
    (hlim : Filter.Tendsto f (𝓝[<] b) (𝓝 L)) :
    ENNReal.ofReal |f x - L| ≤ eVariationOn f (Ioo a b) := by
  have hevent : ∀ᶠ y in 𝓝[<] b,
      ENNReal.ofReal |f x - f y| ≤ eVariationOn f (Ioo a b) := by
    filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy
    have hy' : y ∈ Ioo a b := ⟨hx.1.trans hy.1, hy.2⟩
    simpa only [edist_dist, Real.dist_eq] using
      eVariationOn.edist_le f hx hy'
  have ht : Filter.Tendsto
      (fun y => ENNReal.ofReal |f x - f y|) (𝓝[<] b)
      (𝓝 (ENNReal.ofReal |f x - L|)) := by
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.sub hlim).abs))
  exact le_of_tendsto_of_tendsto ht tendsto_const_nhds hevent

private theorem continuousOn_Icc_tendsto_right {f : ℝ → ℝ}
    {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto f (𝓝[>] a) (𝓝 (f a)) := by
  have hid : Filter.Tendsto (fun x : ℝ => x) (𝓝[>] a)
      (𝓝[Icc a b] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsGT hab)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)⟩
  exact (hf.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.comp hid

private theorem continuousOn_Icc_tendsto_left {f : ℝ → ℝ}
    {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto f (𝓝[<] b) (𝓝 (f b)) := by
  have hid : Filter.Tendsto (fun x : ℝ => x) (𝓝[<] b)
      (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT hab)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)⟩
  exact (hf.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.comp hid

/-- One explicit threshold, fixed independently of either C¹ or BV data. -/
noncomputable def epsilonChosen : ℝ := 1 / 10 ^ (80 : ℕ)

/-- The numerical value of the chosen universal threshold. -/
theorem epsilonChosen_eq : epsilonChosen = 1 / 10 ^ (80 : ℕ) := rfl

/-- The threshold is positive. -/
theorem epsilonChosen_pos : 0 < epsilonChosen := by
  norm_num [epsilonChosen]

/-- The fixed threshold lies below the Section 4 absorption threshold. -/
theorem epsilonChosen_le_s4 :
    ENNReal.ofReal epsilonChosen ≤ s4Epsilon0 := by
  norm_num [epsilonChosen, s4Epsilon0, ENNReal.ofReal_div_of_pos]

/-- The linear `Z` estimate is strictly below the Section 4 threshold at
the chosen size. -/
theorem epsilonChosen_z_small :
    s4UniversalC * ENNReal.ofReal epsilonChosen < s4Epsilon0 := by
  have hC : s4UniversalC = ENNReal.ofReal (10 ^ (60 : ℕ) : ℝ) := by
    norm_num [s4UniversalC]
  have hε : s4Epsilon0 = ENNReal.ofReal (1 / 10 ^ (12 : ℕ) : ℝ) := by
    norm_num [s4Epsilon0, ENNReal.ofReal_div_of_pos]
  rw [hC, hε, ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
    (by norm_num [epsilonChosen])

/-- The quadratic mass bound is strictly below the first-exit threshold. -/
theorem epsilonChosen_mass_small :
    s4UniversalC * ENNReal.ofReal epsilonChosen ^ 2 < 1 / 3 := by
  have hC : s4UniversalC = ENNReal.ofReal (10 ^ (60 : ℕ) : ℝ) := by
    norm_num [s4UniversalC]
  have hThird : (1 / 3 : ℝ≥0∞) = ENNReal.ofReal (1 / 3 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hC, hThird, ← ENNReal.ofReal_pow epsilonChosen_pos.le,
    ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
    (by norm_num [epsilonChosen])

/-- The same universal size controls the exponential estimates for both
null expansions. -/
theorem epsilonChosen_exponent_small :
    (10 ^ (60 : ℕ) : ℝ) * epsilonChosen ^ 2 < 1 / 10 := by
  norm_num [epsilonChosen]

/-- Every datum below the fixed threshold has a universal quadratic margin. -/
theorem epsilonChosen_quadratic_margin {D : ℝ≥0∞}
    (hD : D < ENNReal.ofReal epsilonChosen) :
    (10 ^ (60 : ℕ) : ℝ) * D.toReal ^ 2 < 1 / 10 := by
  have hDreal : D.toReal < epsilonChosen :=
    ENNReal.toReal_lt_of_lt_ofReal hD
  have hsq : D.toReal ^ 2 < epsilonChosen ^ 2 :=
    (sq_lt_sq₀ ENNReal.toReal_nonneg epsilonChosen_pos.le).mpr hDreal
  have hmul := mul_lt_mul_of_pos_left hsq
    (by positivity : (0 : ℝ) < 10 ^ (60 : ℕ))
  exact hmul.trans epsilonChosen_exponent_small

/-- The coefficient for the complete outgoing and incoming three-term
slice variation sums is positive and fixed before the data. -/
theorem epsilonChosen_slice_constant :
    0 < s4SliceTVK ∧ s4SliceTVK = 10 ^ (62 : ℕ) :=
  ⟨s4SliceTVK_pos, s4SliceTVK_eq⟩

/-- Section 6's universal choice of `εStar`: the linear and quadratic
improvements and one slice TV coefficient hold simultaneously. -/
theorem epsilon_star_choice :
    ∃ εStar : ℝ, 0 < εStar ∧
      ENNReal.ofReal εStar ≤ s4Epsilon0 ∧
      s4UniversalC * ENNReal.ofReal εStar < s4Epsilon0 ∧
      s4UniversalC * ENNReal.ofReal εStar ^ 2 < 1 / 3 ∧
      (10 ^ (60 : ℕ) : ℝ) * εStar ^ 2 < 1 / 10 ∧
      0 < s4SliceTVK := by
  exact ⟨epsilonChosen, epsilonChosen_pos, epsilonChosen_le_s4,
    epsilonChosen_z_small, epsilonChosen_mass_small,
    epsilonChosen_exponent_small, s4SliceTVK_pos⟩

/-- The incoming mass primitive and the amplitude estimate (4.3) give a
quadratic mass-ratio estimate throughout a centered unit development. -/
theorem s6_improve_mu_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    ∀ p ∈ developmentWithInitialEdge 1,
      2 * S.m p.1 p.2 / S.r p.1 p.2 ≤
        576 * (sourceD S).toReal ^ 2 := by
  let D : ℝ := (sourceD S).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  intro p hp
  have haccess : ∀ s ∈ Ico p.1 p.2,
      (s, p.2) ∈ developmentWithInitialEdge 1 := by
    intro s hs
    exact ⟨hp.1.trans hs.1, hs.2, hp.2.2⟩
  have hsmall : ∀ s ∈ Ioo p.1 p.2,
      S.zeta s p.2 ^ 2 ≤ (576 * D ^ 2) * (1 / 3 : ℝ) ^ 2 := by
    intro s hs
    have hsU : (s, p.2) ∈ developmentWithInitialEdge 1 :=
      ⟨hp.1.trans hs.1.le, hs.2, hp.2.2⟩
    have hz := (eq4_3_pointwise H hr hcenter hboot hsU).2
    have hsq : S.zeta s p.2 ^ 2 ≤ (8 * D) ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (S.zeta s p.2))
        (by positivity : 0 ≤ 8 * D)).mpr (by simpa only [D] using hz)
      simpa only [sq_abs] using h
    nlinarith only [hsq]
  exact hBV.mass_ratio_le_of_zeta_sq_le_on_incoming_ray
    (by norm_num : (0 : ℝ) < 1 / 3)
    (by intro q hq; exact hboot.1 q hq)
    hp.2.1 (by positivity : 0 ≤ 576 * D ^ 2)
    haccess hsmall

/-- Lemma 4.3 improves the null size strictly below the Section 4
threshold. The scalar is centered internally, so the statement does not
restrict the constant part of the initial datum. -/
theorem s6_improve_z {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S)
    (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen) :
    sourceZ S ≤ s4UniversalC * sourceD S ∧
      sourceZ S < s4Epsilon0 := by
  let T := scalarShift S (-S.phi 0 0)
  have HT : IsC1Solution (developmentWithInitialEdge 1) T :=
    H.scalarShift _
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := by
    simpa only [T, scalarShift] using hr
  have hcenter : T.phi 0 0 = 0 := by
    change S.phi 0 0 + -S.phi 0 0 = 0
    ring
  have hbootT : s4_bootstrap T := by
    simpa only [T, s4_bootstrap, scalarShift] using hboot
  have hDT : sourceD T = sourceD S :=
    sourceD_scalarShift H hr _ (by norm_num)
  have hZT : sourceZ T = sourceZ S := by
    simp only [T, sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  have hDsmall : sourceD T ≤ s4Epsilon0 := by
    rw [hDT]
    exact hD.le.trans epsilonChosen_le_s4
  have hZsmall : sourceZ T ≤ s4Epsilon0 := by
    rw [hZT]
    exact hZ
  have hmain := (lemma4_3 HT hrT hcenter hbootT hDsmall hZsmall).1
  rw [hDT, hZT] at hmain
  refine ⟨hmain, hmain.trans_lt ?_⟩
  exact (mul_le_mul_of_nonneg_left hD.le bot_le).trans_lt
    epsilonChosen_z_small

/-- The mass ratio has a strict uniform margin at the first-exit scale.
The coefficient is the universal `10^60`, independent of the scalar
constant and of the datum. -/
theorem s6_improve_mu {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen) :
    ∀ p ∈ developmentWithInitialEdge 1,
      2 * S.m p.1 p.2 / S.r p.1 p.2 ≤
        (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1 / 3 := by
  let T := scalarShift S (-S.phi 0 0)
  have HT : IsC1Solution (developmentWithInitialEdge 1) T := H.scalarShift _
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := by
    simpa only [T, scalarShift] using hr
  have hcenter : T.phi 0 0 = 0 := by
    change S.phi 0 0 + -S.phi 0 0 = 0
    ring
  have hbootT : s4_bootstrap T := by
    simpa only [T, s4_bootstrap, scalarShift] using hboot
  have hDT : sourceD T = sourceD S :=
    sourceD_scalarShift H hr _ (by norm_num)
  have hDreal : (sourceD S).toReal < epsilonChosen :=
    ENNReal.toReal_lt_of_lt_ofReal hD
  have hDnonneg : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
  have hquad : (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2 < 1 / 3 := by
    have hsq : (sourceD S).toReal ^ 2 < epsilonChosen ^ 2 :=
      (sq_lt_sq₀ hDnonneg epsilonChosen_pos.le).mpr hDreal
    have hmul := mul_lt_mul_of_pos_left hsq
      (by positivity : (0 : ℝ) < 10 ^ (60 : ℕ))
    linarith only [hmul, epsilonChosen_exponent_small]
  intro p hp
  have hmass := s6_improve_mu_unit HT hrT hcenter hbootT p hp
  rw [hDT] at hmass
  have hmassS : 2 * S.m p.1 p.2 / S.r p.1 p.2 ≤
      576 * (sourceD S).toReal ^ 2 := by
    simpa only [T, scalarShift] using hmass
  have hK : 576 * (sourceD S).toReal ^ 2 ≤
      (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    norm_num
  exact ⟨hmassS.trans hK, (hmassS.trans hK).trans_lt hquad⟩

private theorem s6_log_variation_real {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen) :
    (eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) ≠ ⊤ ∧
      (eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1)).toReal ≤
        (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2) ∧
      (∀ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≠ ⊤ ∧
        (eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)).toReal ≤
          (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2) ∧
      (∀ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≠ ⊤ ∧
        (eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)).toReal ≤
          (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2) := by
  let Q : ℝ≥0∞ := s4UniversalC * sourceD S ^ 2
  have hQsmall : Q < 1 / 3 := by
    calc
      Q ≤ s4UniversalC * ENNReal.ofReal epsilonChosen ^ 2 := by
        dsimp [Q]
        gcongr
      _ < 1 / 3 := epsilonChosen_mass_small
  have hQfinite : Q ≠ ⊤ := (hQsmall.trans_le le_top).ne
  have hQreal : Q.toReal =
      (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2 := by
    simp only [Q, ENNReal.toReal_mul, ENNReal.toReal_pow]
    norm_num [s4UniversalC]
  obtain ⟨_, _, hlog, _, _⟩ := lemma4_3 H hr hcenter hboot
    (hD.le.trans epsilonChosen_le_s4) hZ
  obtain ⟨hAxis, hOut, hIn⟩ := hlog
  rw [← hQreal]
  refine ⟨⟨(hAxis.trans_lt hQsmall |>.trans_le le_top).ne,
    ENNReal.toReal_mono hQfinite hAxis⟩, ?_, ?_⟩
  · intro u hu
    have hpoint : eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
        ⨆ w ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun v => Real.log (S.lam w v)) (Ioo w 1) := by
      exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    have hbound := hpoint.trans hOut
    exact ⟨(hbound.trans_lt hQsmall |>.trans_le le_top).ne,
      ENNReal.toReal_mono hQfinite hbound⟩
  · intro v hv
    have hpoint : eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤
        ⨆ w ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun u => Real.log (-S.nu u w)) (Ioo 0 w) := by
      exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
    have hbound := hpoint.trans hIn
    exact ⟨(hbound.trans_lt hQsmall |>.trans_le le_top).ne,
      ENNReal.toReal_mono hQfinite hbound⟩

private theorem s6_axis_log_tendsto_initial {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    Filter.Tendsto (fun t => Real.log (S.lam t t))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (1 / 2 : ℝ))) := by
  have hB : (0 : ℝ) < 1 / 2 := by norm_num
  have hB1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hcontLam : ContinuousOn (fun t : ℝ => S.lam t t)
      (Icc 0 (1 / 2 : ℝ)) := by
    have h := (C1Solution.five_fields_contDiffOn hB hB1 H).1.continuousOn
    apply h.comp (continuous_id.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨ht.1, le_rfl, ht.2⟩
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
  have hpos : ∀ t ∈ Icc (0 : ℝ) (1 / 2), 0 < S.lam t t := by
    intro t ht
    exact hc.trans_le (hcl (t, t) ⟨ht.1, le_rfl, ht.2⟩)
  have hcontLog : ContinuousOn (fun t : ℝ => Real.log (S.lam t t))
      (Icc 0 (1 / 2 : ℝ)) :=
    hcontLam.log (fun t ht => (hpos t ht).ne')
  have hlim := continuousOn_Icc_tendsto_right hB hcontLog
  simpa only [s6_initial_lam_vertex (by norm_num : (0 : ℝ) < 1) H hr]
    using hlim

private theorem s6_outgoing_log_tendsto_axis {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv1 : v < 1) :
    Filter.Tendsto (fun t => Real.log (S.lam u t))
      (𝓝[>] u) (𝓝 (Real.log (S.lam u u))) := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hu, huv]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv1]
  have hvB : v < B := by dsimp [B]; linarith only [hv1]
  have huB : u < B := huv.trans hvB
  have hcontLam : ContinuousOn (S.lam u) (Icc u B) := by
    have h := (C1Solution.five_fields_contDiffOn hB hB1 H).1.continuousOn
    apply h.comp (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨hu.le, ht.1, ht.2⟩
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
  have hpos : ∀ t ∈ Icc u B, 0 < S.lam u t := by
    intro t ht
    exact hc.trans_le (hcl (u, t) ⟨hu.le, ht.1, ht.2⟩)
  have hcontLog : ContinuousOn (fun t => Real.log (S.lam u t))
      (Icc u B) := hcontLam.log (fun t ht => (hpos t ht).ne')
  exact continuousOn_Icc_tendsto_right huB hcontLog

private theorem s6_incoming_log_tendsto_axis {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Filter.Tendsto (fun t => Real.log (-S.nu t v))
      (𝓝[<] v) (𝓝 (Real.log (-S.nu v v))) := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hcontNu : ContinuousOn (fun t : ℝ => -S.nu t v) (Icc 0 v) := by
    have h := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1.continuousOn.neg
    apply h.comp (continuous_id.prodMk continuous_const).continuousOn
    intro t ht
    exact ⟨ht.1, ht.2, hvB.le⟩
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_neg_nu_lower_bound hB hB1 H
  have hpos : ∀ t ∈ Icc (0 : ℝ) v, 0 < -S.nu t v := by
    intro t ht
    exact hc.trans_le (hcl (t, v) ⟨ht.1, ht.2, hvB.le⟩)
  have hcontLog : ContinuousOn (fun t => Real.log (-S.nu t v))
      (Icc 0 v) := hcontNu.log (fun t ht => (hpos t ht).ne')
  exact continuousOn_Icc_tendsto_left hv.1 hcontLog

private theorem s6_log_expansion_bounds_interior {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) 1, S.r 0 w = w / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv1 : v < 1) :
    Real.log (1 / 2 : ℝ) -
        2 * (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2 ≤
          Real.log (S.lam u v) ∧
      Real.log (-S.nu u v) ≤ Real.log (1 / 2 : ℝ) +
        2 * (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2 := by
  let q : ℝ := (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2
  obtain ⟨hAxis, hOut, hIn⟩ :=
    s6_log_variation_real H hr hcenter hboot hZ hD
  have hAxisU : |Real.log (S.lam u u) - Real.log (1 / 2 : ℝ)| ≤ q := by
    have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hu, huv.trans hv1⟩
    have h := variation_left_endpoint_bound huI
      (s6_axis_log_tendsto_initial H hr)
    have hreal := ENNReal.toReal_mono hAxis.1 h
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
    exact hreal.trans hAxis.2
  have hAxisV : |Real.log (S.lam v v) - Real.log (1 / 2 : ℝ)| ≤ q := by
    have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hu.trans huv, hv1⟩
    have h := variation_left_endpoint_bound hvI
      (s6_axis_log_tendsto_initial H hr)
    have hreal := ENNReal.toReal_mono hAxis.1 h
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
    exact hreal.trans hAxis.2
  have hOutUV : |Real.log (S.lam u v) - Real.log (S.lam u u)| ≤ q := by
    have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hu, huv.trans hv1⟩
    have hvI : v ∈ Ioo u 1 := ⟨huv, hv1⟩
    have h := variation_left_endpoint_bound hvI
      (s6_outgoing_log_tendsto_axis H hu huv hv1)
    have hreal := ENNReal.toReal_mono (hOut u huI).1 h
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
    exact hreal.trans (hOut u huI).2
  have hInUV : |Real.log (-S.nu u v) - Real.log (-S.nu v v)| ≤ q := by
    have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hu.trans huv, hv1⟩
    have huI : u ∈ Ioo (0 : ℝ) v := ⟨hu, huv⟩
    have h := variation_right_endpoint_bound huI
      (s6_incoming_log_tendsto_axis H hvI)
    have hreal := ENNReal.toReal_mono (hIn v hvI).1 h
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
    exact hreal.trans (hIn v hvI).2
  have hNuAxis : S.nu v v = -S.lam v v := by
    let B : ℝ := (v + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [hu, huv]
    have hB1 : B < 1 := by dsimp [B]; linarith only [hv1]
    have hvB : v < B := by dsimp [B]; linarith only [hv1]
    exact C1Solution.nu_eq_neg_lam_axis hB hB1 H
      ⟨(hu.trans huv).le, hvB.le⟩
  rw [hNuAxis, neg_neg] at hInUV
  constructor
  · have h1 := (abs_le.mp hAxisU).1
    have h2 := (abs_le.mp hOutUV).1
    dsimp [q] at h1 h2 ⊢
    linarith only [h1, h2]
  · have h1 := (abs_le.mp hAxisV).2
    have h2 := (abs_le.mp hInUV).2
    dsimp [q] at h1 h2 ⊢
    linarith only [h1, h2]

private theorem s6_numerical_null_margin {x : ℝ}
    (hx : x < 1 / 5) :
    (1 / 3 : ℝ) + 1 / 36 < (1 / 2) * Real.exp (-x) ∧
      -(2 / 3 : ℝ) + 1 / 36 < -(1 / 2) * Real.exp x := by
  have hExpOneFifth : Real.exp (1 / 5 : ℝ) < 11 / 9 := by
    have h := Real.exp_lt_two_add_div_two_sub
      (by norm_num : (0 : ℝ) < 1 / 5)
      (by norm_num : (1 / 5 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hExpX : Real.exp x < 11 / 9 :=
    (Real.exp_lt_exp.mpr hx).trans hExpOneFifth
  have hExpNeg : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith only [h]
  constructor
  · nlinarith only [hx, hExpNeg]
  · linarith only [hExpX]

private theorem s6_null_margin_interior {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) 1, S.r 0 w = w / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv1 : v < 1) :
    (1 / 3 : ℝ) + 1 / 36 < S.lam u v ∧
      -(2 / 3 : ℝ) + 1 / 36 < S.nu u v := by
  let x : ℝ := 2 * (10 ^ (60 : ℕ) : ℝ) * (sourceD S).toReal ^ 2
  have hDreal : (sourceD S).toReal < epsilonChosen :=
    ENNReal.toReal_lt_of_lt_ofReal hD
  have hDnonneg : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
  have hx : x < 1 / 5 := by
    have hsq : (sourceD S).toReal ^ 2 < epsilonChosen ^ 2 :=
      (sq_lt_sq₀ hDnonneg epsilonChosen_pos.le).mpr hDreal
    have hmul := mul_lt_mul_of_pos_left hsq
      (by positivity : (0 : ℝ) < 10 ^ (60 : ℕ))
    dsimp [x]
    linarith only [hmul, epsilonChosen_exponent_small]
  have hnum := s6_numerical_null_margin hx
  have hlog := s6_log_expansion_bounds_interior H hr hcenter hboot
    hZ hD hu huv hv1
  have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.le, huv, hv1⟩
  have hLamPos : 0 < S.lam u v := by
    have h := hboot.1 (u, v) hp
    linarith only [h]
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hNuPos : 0 < -S.nu u v := by
    have h := hBV.nu_le_neg_lower (by norm_num) hboot.1 hp
    linarith only [h]
  have hExpL : (1 / 2 : ℝ) * Real.exp (-x) ≤ S.lam u v := by
    have h := Real.exp_le_exp.mpr hlog.1
    rw [sub_eq_add_neg, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_log hLamPos] at h
    simpa only [x] using h
  have hExpN : -S.nu u v ≤ (1 / 2 : ℝ) * Real.exp x := by
    have h := Real.exp_le_exp.mpr hlog.2
    rw [Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2),
      Real.exp_log hNuPos] at h
    simpa only [x] using h
  exact ⟨hnum.1.trans_le hExpL, by linarith only [hnum.2, hExpN]⟩

private theorem s6_improve_null_centered {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) 1, S.r 0 w = w / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen) :
    ∀ p ∈ developmentWithInitialEdge 1,
      (1 / 3 : ℝ) + 1 / 36 ≤ S.lam p.1 p.2 ∧
        -(2 / 3 : ℝ) + 1 / 36 ≤ S.nu p.1 p.2 := by
  intro p hp
  rcases p with ⟨u, v⟩
  rcases eq_or_lt_of_le hp.1 with hzero | hu
  · change (0 : ℝ) = u at hzero
    subst u
    have hv : v ∈ Ioo (0 : ℝ) 1 := ⟨hp.2.1, hp.2.2⟩
    have hLam : S.lam 0 v = 1 / 2 :=
      initial_lam_eq_of_gauge H hr hv
    let B : ℝ := (v + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
    have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    have hcontNu : ContinuousOn (fun u : ℝ => S.nu u v)
        (Icc 0 v) := by
      have h := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1.continuousOn
      apply h.comp (continuous_id.prodMk continuous_const).continuousOn
      intro t ht
      exact ⟨ht.1, ht.2, hvB.le⟩
    have hlim := continuousOn_Icc_tendsto_right hv.1 hcontNu
    have hevent : ∀ᶠ u in 𝓝[>] (0 : ℝ),
        -(2 / 3 : ℝ) + 1 / 36 ≤ S.nu u v := by
      filter_upwards [Ioo_mem_nhdsGT hv.1] with u hu'
      exact (s6_null_margin_interior H hr hcenter hboot hZ hD
        hu'.1 hu'.2 hv.2).2.le
    have hNu : -(2 / 3 : ℝ) + 1 / 36 ≤ S.nu 0 v :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim hevent
    exact ⟨by rw [hLam]; norm_num, hNu⟩
  · exact ⟨(s6_null_margin_interior H hr hcenter hboot hZ hD
      hu hp.2.1 hp.2.2).1.le,
      (s6_null_margin_interior H hr hcenter hboot hZ hD
      hu hp.2.1 hp.2.2).2.le⟩

/-- Both null expansions retain one fixed positive margin beyond their
first-exit thresholds on the entire unit development, including its
initial edge. -/
theorem s6_improve_null {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S)
    (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen) :
    ∀ p ∈ developmentWithInitialEdge 1,
      (1 / 3 : ℝ) + 1 / 36 ≤ S.lam p.1 p.2 ∧
        -(2 / 3 : ℝ) + 1 / 36 ≤ S.nu p.1 p.2 := by
  let T := scalarShift S (-S.phi 0 0)
  have HT : IsC1Solution (developmentWithInitialEdge 1) T := H.scalarShift _
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := by
    simpa only [T, scalarShift] using hr
  have hcenter : T.phi 0 0 = 0 := by
    change S.phi 0 0 + -S.phi 0 0 = 0
    ring
  have hbootT : s4_bootstrap T := by
    simpa only [T, s4_bootstrap, scalarShift] using hboot
  have hDT : sourceD T = sourceD S :=
    sourceD_scalarShift H hr _ (by norm_num)
  have hZT : sourceZ T = sourceZ S := by
    simp only [T, sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  have hsmallD : sourceD T < ENNReal.ofReal epsilonChosen := by
    rw [hDT]
    exact hD
  have hsmallZ : sourceZ T ≤ s4Epsilon0 := by
    rw [hZT]
    exact hZ
  intro p hp
  have h := s6_improve_null_centered HT hrT hcenter hbootT
    hsmallZ hsmallD p hp
  simpa only [T, scalarShift] using h

/-- The complete three-term slice variation estimate has the same universal
coefficient after an arbitrary constant scalar shift. The outgoing bound
includes the initial ray `u = 0`. -/
theorem s6_three_term_slice_tv_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S) (hZ : sourceZ S ≤ s4Epsilon0)
    (hD : sourceD S < ENNReal.ofReal epsilonChosen) :
    (∀ u ∈ Ico (0 : ℝ) 1,
      eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) +
        eVariationOn (S.phi u) (Ioo u 1) +
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) +
        eVariationOn (fun u => S.phi u v) (Ioo 0 v) +
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) := by
  let T := scalarShift S (-S.phi 0 0)
  have HT : IsC1Solution (developmentWithInitialEdge 1) T := H.scalarShift _
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := by
    simpa only [T, scalarShift] using hr
  have hcenter : T.phi 0 0 = 0 := by
    change S.phi 0 0 + -S.phi 0 0 = 0
    ring
  have hbootT : s4_bootstrap T := by
    simpa only [T, s4_bootstrap, scalarShift] using hboot
  have hDT : sourceD T = sourceD S :=
    sourceD_scalarShift H hr _ (by norm_num)
  have hZT : sourceZ T = sourceZ S := by
    simp only [T, sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  have hsmallD : sourceD T ≤ s4Epsilon0 := by
    rw [hDT]
    exact hD.le.trans epsilonChosen_le_s4
  have hsmallZ : sourceZ T ≤ s4Epsilon0 := by
    rw [hZT]
    exact hZ
  obtain ⟨hOut, hIn⟩ :=
    s4_three_term_slice_tv_unit HT hrT hcenter hbootT hsmallD hsmallZ
  constructor
  · intro u hu
    have hα : eVariationOn (fun v => T.alpha u v / T.lam u v) (Ioo u 1) =
        eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) := by
      calc
        _ = eVariationOn
            (fun v => S.alpha u v / S.lam u v + -S.phi 0 0) (Ioo u 1) := by
          apply eVariationOn.congr
          intro v hv
          have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
            ⟨hu.1, hv.1, hv.2⟩
          have hne : S.lam u v ≠ 0 :=
            ne_of_gt (by linarith [hboot.1 (u, v) hp])
          dsimp [T, scalarShift]
          field_simp [hne]
        _ = _ := eVariationOn_add_const_real _ _ _
    have hφ : eVariationOn (T.phi u) (Ioo u 1) =
        eVariationOn (S.phi u) (Ioo u 1) := by
      simpa only [T, scalarShift] using
        (eVariationOn_add_const_real (S.phi u) (-S.phi 0 0) (Ioo u 1))
    have hlog : eVariationOn (fun v => Real.log (T.lam u v)) (Ioo u 1) =
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) := rfl
    simpa only [hα, hφ, hlog, hDT] using hOut u hu
  · intro v hv
    have hβ : eVariationOn (fun u => T.beta u v / T.nu u v) (Ioo 0 v) =
        eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) := by
      calc
        _ = eVariationOn
            (fun u => S.beta u v / S.nu u v + -S.phi 0 0) (Ioo 0 v) := by
          apply eVariationOn.congr
          intro u hu
          have hB : 0 < (v + 1) / 2 := by linarith [hv.1]
          have hB1 : (v + 1) / 2 < 1 := by linarith [hv.2]
          have hvB : v ≤ (v + 1) / 2 := by linarith [hv.2]
          have hne : S.nu u v ≠ 0 := ne_of_lt
            (C1Solution.nu_neg hB hB1 H hu.1.le hu.2 hvB)
          dsimp [T, scalarShift]
          field_simp [hne]
        _ = _ := eVariationOn_add_const_real _ _ _
    have hφ : eVariationOn (fun u => T.phi u v) (Ioo 0 v) =
        eVariationOn (fun u => S.phi u v) (Ioo 0 v) := by
      simpa only [T, scalarShift] using
        (eVariationOn_add_const_real (fun u => S.phi u v)
          (-S.phi 0 0) (Ioo 0 v))
    have hlog : eVariationOn (fun u => Real.log (-T.nu u v)) (Ioo 0 v) =
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) := rfl
    simpa only [hβ, hφ, hlog, hDT] using hIn v hv

end ChristodoulouBV

end
