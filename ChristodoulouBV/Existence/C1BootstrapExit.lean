module

public import ChristodoulouBV.Existence.C1Bootstrap
public import ChristodoulouBV.Uniqueness.Rescaling
import Mathlib.Tactic

/-!
# The first-exit argument for finite C¹ developments

The unit bootstrap is inherited by smaller cutoffs.  This file assembles
that order structure with the C¹ endpoint continuity theorem.
-/

public section

open Set Filter
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- On a unit C¹ development, the source null size is the maximum of the
two scalar variation suprema used by the rescaling library. -/
theorem s6_sourceZ_eq_local {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    sourceZ S = max (Uniqueness.localX S 0 1)
      (Uniqueness.localY S 0 1) := by
  have hX : sourceX S = Uniqueness.localX S 0 1 := by
    unfold sourceX Uniqueness.localX
    congr 1
    funext u
    congr 1
    funext hu
    exact (source_outgoing_phi_variation_eq_weight H hu).symm
  have hY : sourceY S = Uniqueness.localY S 0 1 := by
    unfold sourceY Uniqueness.localY
    congr 1
    funext v
    congr 1
    funext hv
    exact (source_incoming_phi_variation_eq_weight H hv).symm
  simp only [sourceZ, hX, hY]

/-- Restricting the terminal cutoff cannot increase the outgoing scalar
variation supremum. -/
theorem s6_localX_mono (S : Fields) {a c : ℝ}
    (hca : c ≤ a) :
    Uniqueness.localX S 0 c ≤ Uniqueness.localX S 0 a := by
  unfold Uniqueness.localX
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have hua : u ∈ Ioo (0 : ℝ) a := ⟨hu.1, hu.2.trans_le hca⟩
  calc
    eVariationOn (S.phi u) (Ioo u c) ≤
        eVariationOn (S.phi u) (Ioo u a) :=
      eVariationOn.mono _ (fun v hv => ⟨hv.1, hv.2.trans_le hca⟩)
    _ ≤ _ := by
      apply le_iSup_of_le u
      exact le_iSup_of_le hua le_rfl

/-- Restricting the terminal cutoff cannot increase the incoming scalar
variation supremum. -/
theorem s6_localY_mono (S : Fields) {a c : ℝ}
    (hca : c ≤ a) :
    Uniqueness.localY S 0 c ≤ Uniqueness.localY S 0 a := by
  unfold Uniqueness.localY
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hva : v ∈ Ioo (0 : ℝ) a := ⟨hv.1, hv.2.trans_le hca⟩
  exact le_iSup_of_le v (le_iSup_of_le hva le_rfl)

/-- The null size on a smaller positive rescaled cone is bounded by that
on a larger cone of the same C¹ solution. -/
theorem s6_sourceZ_rescaled_mono {S : Fields} {a c : ℝ}
    (hc : 0 < c) (hca : c ≤ a)
    (Hc : IsC1Solution (developmentWithInitialEdge 1)
      (Uniqueness.rescaledFields S 0 c))
    (Ha : IsC1Solution (developmentWithInitialEdge 1)
      (Uniqueness.rescaledFields S 0 a)) :
    sourceZ (Uniqueness.rescaledFields S 0 c) ≤
      sourceZ (Uniqueness.rescaledFields S 0 a) := by
  have ha : 0 < a := hc.trans_le hca
  rw [s6_sourceZ_eq_local Hc, s6_sourceZ_eq_local Ha,
    Uniqueness.rescaled_localX S hc,
    Uniqueness.rescaled_localY S hc,
    Uniqueness.rescaled_localX S ha,
    Uniqueness.rescaled_localY S ha]
  simpa only [zero_add] using
    max_le_max (s6_localX_mono S hca) (s6_localY_mono S hca)

/-- The geometric bootstrap on a unit rescaling persists under a smaller
positive cutoff of the same underlying fields. -/
theorem s6_bootstrap_rescaled_mono (S : Fields) {a c : ℝ}
    (hc : 0 < c) (hca : c ≤ a)
    (hboot : s4_bootstrap (Uniqueness.rescaledFields S 0 a)) :
    s4_bootstrap (Uniqueness.rescaledFields S 0 c) := by
  have ha : 0 < a := hc.trans_le hca
  let t : ℝ := c / a
  have ht : 0 < t := div_pos hc ha
  have ht1 : t ≤ 1 := (div_le_one ha).mpr hca
  have hat : a * t = c := by
    dsimp [t]
    field_simp [ha.ne']
  have hmap : ∀ p ∈ developmentWithInitialEdge 1,
      (t * p.1, t * p.2) ∈ developmentWithInitialEdge 1 := by
    intro p hp
    have hvpos : 0 < p.2 := hp.1.trans_lt hp.2.1
    exact ⟨mul_nonneg ht.le hp.1,
      mul_lt_mul_of_pos_left hp.2.1 ht,
      (mul_le_of_le_one_left hvpos.le ht1).trans_lt hp.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h := hboot.1 (t * p.1, t * p.2) (hmap p hp)
    simpa only [Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate, zero_add, mul_zero,
      ← mul_assoc, hat] using h
  · intro p hp
    have h := hboot.2.1 (t * p.1, t * p.2) (hmap p hp)
    simpa only [Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate, zero_add, mul_zero,
      ← mul_assoc, hat] using h
  · intro p hp
    have h := hboot.2.2 (t * p.1, t * p.2) (hmap p hp)
    rw [Uniqueness.rescaled_mass_ratio S (a := 0) ha] at h
    rw [Uniqueness.rescaled_mass_ratio S (a := 0) hc]
    simpa only [Uniqueness.affineCoordinate, zero_add,
      ← mul_assoc, hat] using h

/-- A finite C¹ development can be normalized to the unit triangle while
retaining the exact characteristic trace and no larger initial variation. -/
theorem s6_scale {alpha₀ : ℝ → ℝ} {b a : ℝ}
    (ha : 0 < a) (hab : a < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) :
    let T := Uniqueness.rescaledFields S 0 a
    IsC1Solution (developmentWithInitialEdge 1) T ∧
      (∀ v ∈ Ioo (0 : ℝ) 1,
        T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ (a * v)) ∧
      sourceD T ≤ eVariationOn alpha₀ (Ioi (0 : ℝ)) := by
  let T := Uniqueness.rescaledFields S 0 a
  have hunit : 1 ≤ b / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [one_mul] using hab.le
  have HT : IsC1Solution (developmentWithInitialEdge 1) T :=
    C1Solution.isC1Solution_restrict_initialEdge
      (C1Solution.rescaled_development_isC1Solution H ha) hunit
  have htrace : ∀ v ∈ Ioo (0 : ℝ) 1,
      T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ (a * v) := by
    intro v hv
    have hav : a * v ∈ Ioo (0 : ℝ) b := by
      constructor
      · exact mul_pos ha hv.1
      · calc
          a * v < a * 1 := mul_lt_mul_of_pos_left hv.2 ha
          _ = a := by ring
          _ < b := hab
    obtain ⟨hrv, hαv⟩ := hdata (a * v) hav
    constructor
    · dsimp [T, Uniqueness.rescaledFields,
        Uniqueness.affineCoordinate]
      simp only [mul_zero, zero_add]
      rw [hrv]
      field_simp [ha.ne']
    · simpa only [T, Uniqueness.rescaledFields,
        Uniqueness.affineCoordinate, mul_zero, zero_add] using hαv
  have hEq : EqOn (T.alpha 0) (fun v => alpha₀ (a * v))
      (Ioo (0 : ℝ) 1) := fun v hv => (htrace v hv).2
  have hVar : eVariationOn (fun v => alpha₀ (a * v))
      (Ioo (0 : ℝ) 1) ≤ eVariationOn alpha₀ (Ioi (0 : ℝ)) := by
    have h := Uniqueness.eVariationOn_affine_le (f := alpha₀)
      (s := Ioi (0 : ℝ)) (t := Ioo (0 : ℝ) 1)
      (a := 0) (h := a) ha (by
        intro v hv
        simpa only [Set.mem_Ioi, Uniqueness.affineCoordinate, zero_add]
          using (mul_pos ha hv.1))
    simpa only [Uniqueness.affineCoordinate, zero_add] using h
  refine ⟨HT, htrace, ?_⟩
  rw [sourceD, eVariationOn.congr hEq]
  exact hVar

/-- On each finite C¹ member, every smaller cutoff satisfies the three
geometric bootstrap bounds and the null-size bound. This is the
open-closed first-exit step before passage to the maximal family. -/
theorem s6_no_first_exit_finite {alpha₀ : ℝ → ℝ} {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen) :
    ∀ a : ℝ, 0 < a → a < B →
      s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0 := by
  let A : Set ℝ := {a | 0 < a ∧ a < B ∧
    s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
    sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0}
  have hHrestrict : IsC1Solution (developmentWithInitialEdge B) S :=
    C1Solution.isC1Solution_restrict_initialEdge H hBb.le
  have hdataB : ∀ v ∈ Ioo (0 : ℝ) B,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v := by
    intro v hv
    exact hdata v ⟨hv.1, hv.2.trans hBb⟩
  obtain ⟨aStart, haStart, haStartB, _, hbootStart, hZStart, _⟩ :=
    bootstrap_start hB hHrestrict hdataB
  have hstart : aStart ∈ A :=
    ⟨haStart, haStartB, hbootStart, hZStart⟩
  have hAne : A.Nonempty := ⟨aStart, hstart⟩
  have hAbdd : BddAbove A := ⟨B, fun a ha => ha.2.1.le⟩
  have hmono : ∀ a ∈ A, ∀ c : ℝ, 0 < c → c ≤ a → c ∈ A := by
    intro a ha c hc hca
    have hcB : c < B := hca.trans_lt ha.2.1
    have Ha := (s6_scale ha.1 (ha.2.1.trans hBb) H hdata).1
    have Hc := (s6_scale hc (hcB.trans hBb) H hdata).1
    exact ⟨hc, hcB,
      s6_bootstrap_rescaled_mono S hc hca ha.2.2.1,
      (s6_sourceZ_rescaled_mono hc hca Hc Ha).trans ha.2.2.2⟩
  let s : ℝ := sSup A
  have hs : 0 < s :=
    haStart.trans_le (le_csSup hAbdd hstart)
  have hsB : s ≤ B := csSup_le hAne (fun a ha => ha.2.1.le)
  have hprev : ∀ a : ℝ, 0 < a → a < s →
      s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0 := by
    intro a ha has
    obtain ⟨x, hx, hax⟩ := exists_lt_of_lt_csSup hAne has
    exact ((hmono x hx a ha hax.le).2.2)
  have hsEqB : s = B := by
    by_contra hne
    have hsBlt : s < B := lt_of_le_of_ne hsB hne
    have hcont := first_exit_continuity hB hBb hs hsBlt H hprev
    let T := Uniqueness.rescaledFields S 0 s
    obtain ⟨HT, htrace, hDscale⟩ :=
      s6_scale hs (hsBlt.trans hBb) H hdata
    have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 :=
      fun v hv => (htrace v hv).1
    have hDT : sourceD T < ENNReal.ofReal epsilonChosen :=
      hDscale.trans_lt hD
    have hZstrict := (s6_improve_z HT hrT hcont.1 hcont.2.1 hDT).2
    have hnull := s6_improve_null HT hrT hcont.1 hcont.2.1 hDT
    have hmass := s6_improve_mu HT hrT hcont.1 hDT
    have hquad := epsilonChosen_quadratic_margin hDT
    have hmargin : ∃ ηG : ℝ, 0 < ηG ∧
        ∀ p ∈ developmentWithInitialEdge 1,
          (1 / 3 : ℝ) + ηG ≤ S.lam (s * p.1) (s * p.2) ∧
          -(2 / 3 : ℝ) + ηG ≤ S.nu (s * p.1) (s * p.2) ∧
          C1Solution.canonicalMassRatio b S (s • p) + ηG ≤
            (1 / 3 : ℝ) := by
      refine ⟨1 / 36, by norm_num, ?_⟩
      intro p hp
      have hnullp := hnull p hp
      have hmassp := (hmass p hp).1
      have hpS : (s • p) ∈ developmentWithInitialEdge b := by
        have hsv : s * p.2 < s := by
          simpa only [mul_one] using mul_lt_mul_of_pos_left hp.2.2 hs
        refine ⟨?_, ?_, ?_⟩
        · simpa only [Prod.smul_fst, smul_eq_mul] using
            (mul_nonneg hs.le hp.1)
        · simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using
            (mul_lt_mul_of_pos_left hp.2.1 hs)
        · simpa only [Prod.smul_snd, smul_eq_mul] using
            hsv.trans (hsBlt.trans hBb)
      have hratio : C1Solution.canonicalMassRatio b S (s • p) =
          2 * T.m p.1 p.2 / T.r p.1 p.2 := by
        rw [C1Solution.canonicalMassRatio_eq_mass_ratio H hpS]
        simpa only [T, Uniqueness.affineCoordinate, zero_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using
            (Uniqueness.rescaled_mass_ratio S (a := 0) hs p.1 p.2).symm
      refine ⟨?_, ?_, ?_⟩
      · simpa only [T, Uniqueness.rescaledFields,
          Uniqueness.affineCoordinate, zero_add] using hnullp.1
      · simpa only [T, Uniqueness.rescaledFields,
          Uniqueness.affineCoordinate, zero_add] using hnullp.2
      · rw [hratio]
        linarith only [hmassp, hquad]
    obtain ⟨a, hsa, haB, hadm⟩ :=
      hcont.2.2 ⟨hmargin, hZstrict⟩
    have haA : a ∈ A := ⟨hs.trans hsa, haB, hadm.1, hadm.2⟩
    exact (not_lt_of_ge (le_csSup hAbdd haA)) hsa
  intro a ha haB
  have has : a < s := by rwa [hsEqB]
  exact hprev a ha has

/-- No first exit occurs in a finite C¹ development: each smaller unit
rescaling has strict margins for `Z`, both expansions, and the mass ratio.
The margins and the initial variation threshold are universal. -/
theorem no_first_exit {alpha₀ : ℝ → ℝ} {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen) :
    ∀ a : ℝ, 0 < a → a < B →
      let T := Uniqueness.rescaledFields S 0 a
      IsC1Solution (developmentWithInitialEdge 1) T ∧
      sourceZ T < s4Epsilon0 ∧
      ∀ p ∈ developmentWithInitialEdge 1,
        (1 / 3 : ℝ) + 1 / 36 ≤ T.lam p.1 p.2 ∧
        -(2 / 3 : ℝ) + 1 / 36 ≤ T.nu p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 + 1 / 36 ≤
          (1 / 3 : ℝ) := by
  intro a ha haB
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨HT, htrace, hDscale⟩ :=
    s6_scale ha (haB.trans hBb) H hdata
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 :=
    fun v hv => (htrace v hv).1
  have hDT : sourceD T < ENNReal.ofReal epsilonChosen :=
    hDscale.trans_lt hD
  have hweak := s6_no_first_exit_finite hB hBb H hdata hD a ha haB
  have hZ := (s6_improve_z HT hrT hweak.1 hweak.2 hDT).2
  have hnull := s6_improve_null HT hrT hweak.1 hweak.2 hDT
  have hmass := s6_improve_mu HT hrT hweak.1 hDT
  have hquad := epsilonChosen_quadratic_margin hDT
  refine ⟨HT, hZ, ?_⟩
  intro p hp
  obtain ⟨hlam, hnu⟩ := hnull p hp
  have hmu := (hmass p hp).1
  exact ⟨hlam, hnu, by linarith only [hmu, hquad]⟩

/-- The same rescaled member of the no-first-exit family has the complete
outgoing and incoming slice variation bounds with the one universal
coefficient `s4SliceTVK`, including the initial outgoing ray. -/
theorem no_first_exit_slice_tv {alpha₀ : ℝ → ℝ} {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen) :
    ∀ a : ℝ, 0 < a → a < B →
      let T := Uniqueness.rescaledFields S 0 a
      (∀ u ∈ Ico (0 : ℝ) 1,
        eVariationOn (fun v => T.alpha u v / T.lam u v) (Ioo u 1) +
          eVariationOn (T.phi u) (Ioo u 1) +
          eVariationOn (fun v => Real.log (T.lam u v)) (Ioo u 1) ≤
            ENNReal.ofReal (s4SliceTVK * (sourceD T).toReal)) ∧
      (∀ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => T.beta u v / T.nu u v) (Ioo 0 v) +
          eVariationOn (fun u => T.phi u v) (Ioo 0 v) +
          eVariationOn (fun u => Real.log (-T.nu u v)) (Ioo 0 v) ≤
            ENNReal.ofReal (s4SliceTVK * (sourceD T).toReal)) := by
  intro a ha haB
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨HT, htrace, hDscale⟩ :=
    s6_scale ha (haB.trans hBb) H hdata
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 :=
    fun v hv => (htrace v hv).1
  have hweak := s6_no_first_exit_finite hB hBb H hdata hD a ha haB
  exact s6_three_term_slice_tv_unit HT hrT hweak.1 hweak.2
    (hDscale.trans_lt hD)

/-- The maximal C¹ parameter is the supremum of finite developments.
Every strictly smaller positive cutoff has a development with the universal
strict bootstrap margins, and no development lies beyond the supremum.
This statement exposes the parameter through an existential witness rather
than selecting one from a nonunique existence proof. -/
theorem exists_c1_maximal_parameter_with_bootstrap
    (alpha₀ : ℝ → ℝ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen) :
    ∃ vStar : ℝ≥0∞,
      0 < vStar ∧
      vStar = sSup ((fun b : ℝ => ENNReal.ofReal b) ''
        {b : ℝ | C1InitialDevelopment alpha₀ b}) ∧
      (∀ a : ℝ, 0 < a → ENNReal.ofReal a < vStar →
        ∃ b : ℝ, a < b ∧
          ∃ S : Fields,
            IsC1Solution (developmentWithInitialEdge b) S ∧
            (∀ v ∈ Ioo (0 : ℝ) b,
              S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) ∧
            (let T := Uniqueness.rescaledFields S 0 a;
              IsC1Solution (developmentWithInitialEdge 1) T ∧
              sourceZ T < s4Epsilon0 ∧
              (∀ p ∈ developmentWithInitialEdge 1,
                (1 / 3 : ℝ) + 1 / 36 ≤ T.lam p.1 p.2 ∧
                -(2 / 3 : ℝ) + 1 / 36 ≤ T.nu p.1 p.2 ∧
                2 * T.m p.1 p.2 / T.r p.1 p.2 + 1 / 36 ≤
                  (1 / 3 : ℝ)) ∧
              (∀ u ∈ Ico (0 : ℝ) 1,
                eVariationOn (fun v => T.alpha u v / T.lam u v) (Ioo u 1) +
                  eVariationOn (T.phi u) (Ioo u 1) +
                  eVariationOn (fun v => Real.log (T.lam u v)) (Ioo u 1) ≤
                    ENNReal.ofReal (s4SliceTVK * (sourceD T).toReal)) ∧
              (∀ v ∈ Ioo (0 : ℝ) 1,
                eVariationOn (fun u => T.beta u v / T.nu u v) (Ioo 0 v) +
                  eVariationOn (fun u => T.phi u v) (Ioo 0 v) +
                  eVariationOn (fun u => Real.log (-T.nu u v)) (Ioo 0 v) ≤
                    ENNReal.ofReal (s4SliceTVK * (sourceD T).toReal)))) ∧
      (∀ b : ℝ, 0 < b → vStar < ENNReal.ofReal b →
        ¬ C1InitialDevelopment alpha₀ b) := by
  refine ⟨c1MaximalParameter alpha₀, c1MaximalParameter_pos alpha₀ hα,
    rfl, ?_, ?_⟩
  · intro a ha hmax
    obtain ⟨x, hx, hax⟩ := lt_sSup_iff.mp hmax
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨hbpos, S, HS, hdata⟩ := hb
    have hab : a < b :=
      (ENNReal.ofReal_lt_ofReal_iff hbpos).mp hax
    let B : ℝ := (a + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith
    have haB : a < B := by dsimp [B]; linarith
    have hBb : B < b := by dsimp [B]; linarith
    obtain ⟨hT, hZ, hgeo⟩ :=
      no_first_exit hB hBb HS hdata hD a ha haB
    obtain ⟨hOut, hIn⟩ :=
      no_first_exit_slice_tv hB hBb HS hdata hD a ha haB
    exact ⟨b, hab, S, HS, hdata, hT, hZ, hgeo, hOut, hIn⟩
  · intro b hb hmax H
    have hmem : ENNReal.ofReal b ∈
        (fun c : ℝ => ENNReal.ofReal c) ''
          {c : ℝ | C1InitialDevelopment alpha₀ c} :=
      ⟨b, H, rfl⟩
    exact (not_lt_of_ge (le_sSup hmem)) hmax

end ChristodoulouBV

end
