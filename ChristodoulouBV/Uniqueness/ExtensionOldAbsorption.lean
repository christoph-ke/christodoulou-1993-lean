module

public import ChristodoulouBV.Uniqueness.ExtensionOldAbsorptionFinite
public import ChristodoulouBV.Uniqueness.ExtensionOldAbsorptionAlgebra
import ChristodoulouBV.Uniqueness.ExtensionTransport
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge

/-!
# Absorption on finite cutoffs of the old extension domain

This is Christodoulou's equation (5.10) with both suprema taken below a
finite compatible outgoing cutoff. The full-domain passage uses the separate
incoming boundedness argument.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- On an incoming segment of a C¹ development the radius decreases, since
the incoming expansion `ν` is negative. -/
theorem radius_le_on_incoming_segment {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v : ℝ} (hu₀ : 0 < u₀) (hu₀u : u₀ ≤ u)
    (huv : u < v) (hvb : v < b) :
    S.r u v ≤ S.r u₀ v := by
  have hseg : inSeg v u₀ u ⊆ developmentWithInitialEdge b := by
    rintro ⟨s, w⟩ ⟨hs, hw⟩
    have hwv : w = v := hw
    subst w
    exact ⟨hu₀.le.trans hs.1, hs.2.trans_lt huv, hvb⟩
  have hprim := H.solution.radius_in v u₀ u hu₀u hseg
  have hν : ∀ s ∈ Icc u₀ u, 0 ≤ -S.nu s v := by
    intro s hs
    have hp : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hu₀.le.trans hs.1, hs.2.trans_lt huv, hvb⟩
    exact neg_nonneg.mpr (H.reduced_signs_of_c1 hp).1.le
  have hI : 0 ≤ ∫ s in u₀..u, -S.nu s v :=
    intervalIntegral.integral_nonneg hu₀u hν
  dsimp [IntervalPrimitive] at hprim
  rw [intervalIntegral.integral_neg] at hI
  linarith only [hprim.2, hI]

private theorem weighted_alphaPrime_pointwise_bound
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v δ ε A D : ℝ}
    (hu₀ : 0 < u₀) (hu₀u : u₀ < u)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : ε < 1)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b)
    (hμ : ∀ s ∈ Ioc u₀ u, ∀ w ∈ Ioc s v,
      2 * S.m s w / S.r s w ≤ ε)
    (hA : ∀ s ∈ Ioc u₀ u, ∀ w ∈ Ioc s v,
      (S.r s w) ^ δ *
        |deriv (fun t => S.alpha s t / S.lam s t) w / S.lam s w| ≤ A)
    (hD : (S.r u₀ v) ^ δ *
      |deriv (fun t => S.alpha u₀ t / S.lam u₀ t) v / S.lam u₀ v| ≤ D) :
    (S.r u v) ^ δ *
      |deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v| ≤
        D + oldAbsorptionCoefficient δ ε * A := by
  have hpu := hseg u (right_mem_Icc.mpr hu₀u.le)
  have hp₀ := hseg u₀ (left_mem_Icc.mpr hu₀u.le)
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v)
    ⟨hpu.1.1.le, hpu.2.1, hpu.2.2⟩
  have hr₀ : 0 < S.r u₀ v := H.solution.radius_pos (u₀, v)
    ⟨hp₀.1.1.le, hp₀.2.1, hp₀.2.2⟩
  have hrr₀ : S.r u v ≤ S.r u₀ v :=
    radius_le_on_incoming_segment H hu₀ hu₀u.le hpu.2.1 hpu.2.2
  have hpowle : (S.r u v) ^ δ ≤ (S.r u₀ v) ^ δ :=
    Real.rpow_le_rpow hr.le hrr₀ hδ.le
  have hpow : (S.r u v) ^ δ * (S.r u v)^(-δ) = 1 := by
    rw [← Real.rpow_add hr]
    simp
  have hP := alphaPrime_le_initial_add_integrals_pointwise H hu₀u hseg
  have hI₁ := integralI₁_le_weightedSup H hu₀u hδ hε hseg
    (fun s hs => hμ s hs v (right_mem_Ioc.mpr (hseg s ⟨hs.1.le, hs.2⟩).2.1))
    (fun s hs => hA s hs v (right_mem_Ioc.mpr (hseg s ⟨hs.1.le, hs.2⟩).2.1))
  have hI₂ := integralI₂_le_weightedSup H hu₀u hδ hδ1 hε hseg
    (fun s hs => hμ s hs v (right_mem_Ioc.mpr (hseg s ⟨hs.1.le, hs.2⟩).2.1))
    hA
  have hI₃ := integralI₃_le_weightedSup H hu₀u hδ hδ1 hε hseg hμ hA
  have hpow0 : 0 ≤ (S.r u v) ^ δ := Real.rpow_nonneg hr.le _
  have hinitial : (S.r u v) ^ δ *
      |deriv (fun t => S.alpha u₀ t / S.lam u₀ t) v / S.lam u₀ v| ≤ D :=
    (mul_le_mul_of_nonneg_right hpowle (abs_nonneg _)).trans hD
  have h₁ : (S.r u v) ^ δ * |integralI₁ b S u₀ u v hseg| ≤
      (ε / (1 - ε)) * A / δ := by
    calc
      _ ≤ (S.r u v) ^ δ *
          ((ε / (1 - ε)) * A / δ * (S.r u v)^(-δ)) :=
        mul_le_mul_of_nonneg_left hI₁ hpow0
      _ = (ε / (1 - ε)) * A / δ := by
        calc
          _ = ((ε / (1 - ε)) * A / δ) *
              ((S.r u v) ^ δ * (S.r u v)^(-δ)) := by ring
          _ = _ := by rw [hpow]; ring
  have h₂ : (S.r u v) ^ δ * |integralI₂ b S u₀ u v hseg| ≤
      (ε / (1 - ε)) * A / (δ * (2 - δ)) := by
    calc
      _ ≤ (S.r u v) ^ δ *
          ((ε / (1 - ε)) * A / (δ * (2 - δ)) * (S.r u v)^(-δ)) :=
        mul_le_mul_of_nonneg_left hI₂ hpow0
      _ = (ε / (1 - ε)) * A / (δ * (2 - δ)) := by
        calc
          _ = ((ε / (1 - ε)) * A / (δ * (2 - δ))) *
              ((S.r u v) ^ δ * (S.r u v)^(-δ)) := by ring
          _ = _ := by rw [hpow]; ring
  have h₃ : (S.r u v) ^ δ * |integralI₃ b S u₀ u v hseg| ≤
      (3 * ε / (1 - ε)^2) *
        ((3 - δ) / (δ * (1 - δ) * (2 - δ))) * A := by
    calc
      _ ≤ (S.r u v) ^ δ *
          ((3 * ε / (1 - ε)^2) *
            ((3 - δ) / (δ * (1 - δ) * (2 - δ))) *
              A * (S.r u v)^(-δ)) :=
        mul_le_mul_of_nonneg_left hI₃ hpow0
      _ = (3 * ε / (1 - ε)^2) *
            ((3 - δ) / (δ * (1 - δ) * (2 - δ))) * A := by
        calc
          _ = ((3 * ε / (1 - ε)^2) *
                ((3 - δ) / (δ * (1 - δ) * (2 - δ))) * A) *
                ((S.r u v) ^ δ * (S.r u v)^(-δ)) := by ring
          _ = _ := by rw [hpow]; ring
  have hweighted : (S.r u v) ^ δ *
      |deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v| ≤
      D + 2 * ((ε / (1 - ε)) * A / δ) +
        3 * ((ε / (1 - ε)) * A / (δ * (2 - δ))) +
        (3 * ε / (1 - ε)^2) *
          ((3 - δ) / (δ * (1 - δ) * (2 - δ))) * A := by
    have hm := mul_le_mul_of_nonneg_left hP hpow0
    nlinarith only [hm, hinitial, h₁, h₂, h₃]
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have h1δ : 1 - δ ≠ 0 := ne_of_gt (by linarith : 0 < 1 - δ)
  have h2δ : 2 - δ ≠ 0 := ne_of_gt (by linarith : 0 < 2 - δ)
  have h1ε : 1 - ε ≠ 0 := ne_of_gt (by linarith : 0 < 1 - ε)
  have hcoeff :
      2 * ((ε / (1 - ε)) * A / δ) +
        3 * ((ε / (1 - ε)) * A / (δ * (2 - δ))) +
        (3 * ε / (1 - ε)^2) *
          ((3 - δ) / (δ * (1 - δ) * (2 - δ))) * A =
      oldAbsorptionCoefficient δ ε * A := by
    unfold oldAbsorptionCoefficient oldAbsorptionA oldAbsorptionB
    field_simp [hδne, h1δ, h2δ, h1ε]
    ring
  rw [← hcoeff]
  simpa only [add_assoc] using hweighted

/-- Equation (5.10) on a finite compatible cutoff. `A′_t` and `D′_t` are
genuine finite suprema; the source coefficient is unchanged. -/
theorem weightedSup_self_bound
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ t δ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁t : u₁ < t)
    (htStar : t < vStar) (hδ : 0 < δ) (hδ1 : δ < 1)
    (_hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    finiteWeightedAlphaPrimeSup u₀ u₁ vStar δ t S ≤
      finiteIncomingWeightedAlphaPrimeSup u₀ vStar δ t S +
        oldAbsorptionCoefficient δ ε *
          finiteWeightedAlphaPrimeSup u₀ u₁ vStar δ t S := by
  have ht : 0 < t := hu₀.trans (hu₀u₁.trans hu₁t)
  have hu₁Star : u₁ < vStar := hu₁t.trans htStar
  let A := finiteWeightedAlphaPrimeSup u₀ u₁ vStar δ t S
  let D := finiteIncomingWeightedAlphaPrimeSup u₀ vStar δ t S
  change A ≤ D + oldAbsorptionCoefficient δ ε * A
  apply csSup_le (weightedAlphaPrimeValuesBelow_nonempty
    hu₀ hu₀u₁ hu₁t htStar hfamily)
  rintro x ⟨b, hb, p, htrunc, hp, hpt, rfl⟩
  obtain ⟨hu₀u, huu₁, huv, hvStar⟩ :=
    (mem_truncatedDevelopment_iff hu₁Star).1 htrunc
  let H := (hfamily b hb).1
  have hseg : ∀ s ∈ Icc u₀ p.1.1,
      (s, p.1.2) ∈ openDevelopment 0 b := by
    intro s hs
    have hsv : s < p.1.2 := hs.2.trans_lt huv
    exact ⟨⟨hu₀.trans_le hs.1, hsv.trans hp.2.2⟩,
      ⟨hsv, hp.2.2⟩⟩
  have hμ : ∀ s ∈ Ioc u₀ p.1.1, ∀ w ∈ Ioc s p.1.2,
      2 * (S b).m s w / (S b).r s w ≤ ε := by
    intro s hs w hw
    have hsw : (s, w) ∈ openDevelopment u₀ vStar :=
      ⟨⟨hs.1, hw.1.trans (hw.2.trans_lt hvStar)⟩,
        ⟨hw.1, hw.2.trans_lt hvStar⟩⟩
    have hsb : (s, w) ∈ developmentWithInitialEdge b :=
      ⟨(hu₀.trans hs.1).le, hw.1, hw.2.trans_lt hp.2.2⟩
    exact htail b hb (s, w) ⟨hsw, hsb⟩
  have hA : ∀ s ∈ Ioc u₀ p.1.1, ∀ w ∈ Ioc s p.1.2,
      (S b).r s w ^ δ *
        |deriv (fun z => (S b).alpha s z / (S b).lam s z) w /
          (S b).lam s w| ≤ A := by
    intro s hs w hw
    have hsw : (s, w) ∈ openDevelopment 0 b :=
      ⟨⟨hu₀.trans hs.1, hw.1.trans (hw.2.trans_lt hp.2.2)⟩,
        ⟨hw.1, hw.2.trans_lt hp.2.2⟩⟩
    have htrSW : (s, w) ∈ truncatedDevelopment u₀ u₁ vStar :=
      (mem_truncatedDevelopment_iff hu₁Star).2
        ⟨hs.1, hs.2.trans_lt huu₁, hw.1, hw.2.trans_lt hvStar⟩
    let q : AlphaPrimeDomain (S b) :=
      ⟨(s, w), alphaPrimeDomain_of_open H hsw⟩
    have hbound := weighted_alphaPrime_le_finite_cutoff_sup
      ht htStar hδ.le hfamily hb q htrSW hsw (hw.2.trans hpt)
    simpa only [A, alphaPrime_eq_deriv] using hbound
  have hp₀ : (u₀, p.1.2) ∈ openDevelopment 0 b :=
    hseg u₀ (left_mem_Icc.mpr hu₀u.le)
  let q₀ : AlphaPrimeDomain (S b) :=
    ⟨(u₀, p.1.2), alphaPrimeDomain_of_open H hp₀⟩
  have hD : (S b).r u₀ p.1.2 ^ δ *
      |deriv (fun z => (S b).alpha u₀ z / (S b).lam u₀ z) p.1.2 /
        (S b).lam u₀ p.1.2| ≤ D := by
    have hbound := incoming_weighted_alphaPrime_le_finite_sup
      ht htStar hδ.le hfamily hb q₀ rfl ⟨hu₀u.trans huv, hvStar⟩
        hp₀ hpt
    simpa only [D, alphaPrime_eq_deriv] using hbound
  have hpoint := weighted_alphaPrime_pointwise_bound H hu₀ hu₀u
    hδ hδ1 hε1 hseg hμ hA hD
  simpa only [A, D, alphaPrime_eq_deriv] using hpoint

/-- The finite-cutoff uniform bound following (5.11), with the source's
displayed denominator. Neither bound depends on a C¹ member at `vStar`. -/
theorem finiteWeightedAlphaPrimeSup_le_finiteIncoming_div
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ t ε : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁t : u₁ < t)
    (htStar : t < vStar)
    (hε0 : 0 ≤ ε) (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    finiteWeightedAlphaPrimeSup u₀ u₁ vStar ((1 : ℝ) / 2) t S ≤
      finiteIncomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) t S /
        (1 - ε / ((5 - 2 * Real.sqrt 6) / 3)) := by
  obtain ⟨ε₁, hε₁eq, _, hε₁lt1, _, _, _, hcompare⟩ :=
    universal_epsilon_choice
  have hεlt : ε < ε₁ := by simpa only [hε₁eq] using hε1
  have hεlt1 : ε < 1 := hεlt.trans hε₁lt1
  have hcoeff := hcompare ε hε0 hεlt
  let A := finiteWeightedAlphaPrimeSup u₀ u₁ vStar ((1 : ℝ) / 2) t S
  let D := finiteIncomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) t S
  have hA0 : 0 ≤ A := finiteWeightedAlphaPrimeSup_nonneg
    hu₀ hu₀u₁ hu₁t htStar (by norm_num) hfamily
  have hself : A ≤ D +
      oldAbsorptionCoefficient ((1 : ℝ) / 2) ε * A :=
    weightedSup_self_bound hu₀ hu₀u₁ hu₁t htStar
      (by norm_num) (by norm_num) hε0 hεlt1 hfamily htail
  have hcoeffA : oldAbsorptionCoefficient ((1 : ℝ) / 2) ε * A ≤
      (ε / ε₁) * A := mul_le_mul_of_nonneg_right hcoeff.1 hA0
  have hbound : A ≤ D + (ε / ε₁) * A := by
    linarith only [hself, hcoeffA]
  have hden : 0 < 1 - ε / ε₁ := by linarith [hcoeff.2]
  have hfinal : A ≤ D / (1 - ε / ε₁) := by
    apply (le_div_iff₀ hden).2
    nlinarith only [hbound]
  simpa only [A, D, hε₁eq] using hfinal

/-- Weighted `α′` samples on the entire compatible old domain below
`vStar`. No member at `vStar` occurs in this definition. -/
def weightedAlphaPrimeValuesBeforeStar (u₀ vStar δ : ℝ)
    (S : ℝ → Fields) : Set ℝ :=
  {x | ∃ b ∈ Ioo (0 : ℝ) vStar,
    ∃ p : AlphaPrimeDomain (S b),
      (p : ℝ × ℝ) ∈ openDevelopment u₀ vStar ∧
      (p : ℝ × ℝ) ∈ openDevelopment 0 b ∧
      x = (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p|}

/-- The compatible full-domain supremum `A′_*` in (5.12). Its finiteness
is established only after the incoming bound is available. -/
noncomputable def weightedAlphaPrimeSupBeforeStar (u₀ vStar δ : ℝ)
    (S : ℝ → Fields) : ℝ :=
  sSup (weightedAlphaPrimeValuesBeforeStar u₀ vStar δ S)

/-- The old domain contains an actual off-axis weighted sample. -/
theorem weightedAlphaPrimeValuesBeforeStar_nonempty
    {alpha₀ : ℝ → ℝ} {vStar u₀ δ : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    (weightedAlphaPrimeValuesBeforeStar u₀ vStar δ S).Nonempty := by
  let u := (u₀ + vStar) / 2
  let v := (u + vStar) / 2
  let b := (v + vStar) / 2
  have hu₀u : u₀ < u := by dsimp [u]; linarith [hu₀.2]
  have huStar : u < vStar := by dsimp [u]; linarith [hu₀.2]
  have huv : u < v := by dsimp [v]; linarith [huStar]
  have hvStar : v < vStar := by dsimp [u, v]; linarith [hu₀.2]
  have hvb : v < b := by dsimp [b]; linarith [hvStar]
  have hbStar : b < vStar := by dsimp [b]; linarith [hvStar]
  have hb : b ∈ Ioo (0 : ℝ) vStar :=
    ⟨hu₀.1.trans (hu₀u.trans (huv.trans hvb)), hbStar⟩
  have hdev : (u, v) ∈ openDevelopment u₀ vStar :=
    ⟨⟨hu₀u, huv.trans hvStar⟩, ⟨huv, hvStar⟩⟩
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu₀.1.trans hu₀u, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
  let p : AlphaPrimeDomain (S b) :=
    ⟨(u, v), alphaPrimeDomain_of_open (hfamily b hb).1 hp⟩
  exact ⟨(S b).r u v ^ δ * |alphaPrime (S b) p|,
    b, hb, p, hdev, hp, rfl⟩

/-- Conditional passage from finite cutoffs to equation (5.12). The only
extra hypothesis is the uniform incoming boundedness statement; the
compatible C¹ family and mass bound are the frozen premises. -/
theorem weightedAlphaPrime_bound_before_star_of_incoming_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (_hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε0 : 0 ≤ ε)
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε)
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    BddAbove (weightedAlphaPrimeValuesBeforeStar u₀ vStar ((1 : ℝ) / 2) S) ∧
      weightedAlphaPrimeSupBeforeStar u₀ vStar ((1 : ℝ) / 2) S ≤
        incomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) S /
          (1 - ε / ((5 - 2 * Real.sqrt 6) / 3)) := by
  obtain ⟨ε₁, hε₁eq, _, _, _, _, _, hcompare⟩ :=
    universal_epsilon_choice
  have hεlt : ε < ε₁ := by simpa only [hε₁eq] using hε1
  have hcoeff := hcompare ε hε0 hεlt
  let D := incomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) S
  let C : ℝ := D / (1 - ε / ε₁)
  have hpoint : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p : AlphaPrimeDomain (S b),
        (p : ℝ × ℝ) ∈ openDevelopment u₀ vStar →
        (p : ℝ × ℝ) ∈ openDevelopment 0 b →
        (S b).r p.1.1 p.1.2 ^ ((1 : ℝ) / 2) *
          |alphaPrime (S b) p| ≤ C := by
    intro b hb p hdev hp
    let u₁ : ℝ := (p.1.2 + vStar) / 2
    let t : ℝ := (u₁ + vStar) / 2
    have hpuu₁ : p.1.1 < u₁ := by
      dsimp [u₁]
      linarith [hdev.2.1, hdev.2.2]
    have hu₀u₁ : u₀ < u₁ := hdev.1.1.trans hpuu₁
    have hu₁Star : u₁ < vStar := by dsimp [u₁]; linarith [hdev.2.2]
    have hu₁t : u₁ < t := by dsimp [t]; linarith [hu₁Star]
    have htStar : t < vStar := by dsimp [t]; linarith [hu₁Star]
    have hpvt : p.1.2 ≤ t := by dsimp [t, u₁]; linarith [hdev.2.2]
    have htrunc : (p : ℝ × ℝ) ∈ truncatedDevelopment u₀ u₁ vStar :=
      (mem_truncatedDevelopment_iff hu₁Star).2
        ⟨hdev.1.1, hpuu₁, hdev.2.1, hdev.2.2⟩
    let A := finiteWeightedAlphaPrimeSup u₀ u₁ vStar ((1 : ℝ) / 2) t S
    let Dₜ := finiteIncomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) t S
    have hfinite : A ≤
        Dₜ / (1 - ε / ((5 - 2 * Real.sqrt 6) / 3)) :=
      finiteWeightedAlphaPrimeSup_le_finiteIncoming_div
        hu₀.1 hu₀u₁ hu₁t htStar hε0 hε1 hfamily htail
    have hfinite' : A ≤ Dₜ / (1 - ε / ε₁) := by
      rw [hε₁eq]
      exact hfinite
    have hDₜ : Dₜ ≤ D :=
      finiteIncomingWeightedAlphaPrimeSup_le_incomingSup
        hu₀.1 (hu₀u₁.trans hu₁t) htStar hfamily hIncoming
    have hden : 0 < 1 - ε / ε₁ := by linarith [hcoeff.2]
    have hA : A ≤ C := by
      have hquot : Dₜ / (1 - ε / ε₁) ≤ D / (1 - ε / ε₁) := by
        apply (div_le_div_iff₀ hden hden).2
        exact mul_le_mul_of_nonneg_right hDₜ hden.le
      exact hfinite'.trans hquot
    have hvalue : (S b).r p.1.1 p.1.2 ^ ((1 : ℝ) / 2) *
        |alphaPrime (S b) p| ≤ A :=
      weighted_alphaPrime_le_finite_cutoff_sup
        (hu₀.1.trans (hu₀u₁.trans hu₁t)) htStar (by norm_num)
        hfamily hb p htrunc hp hpvt
    exact hvalue.trans hA
  have hnonempty := weightedAlphaPrimeValuesBeforeStar_nonempty
    (δ := ((1 : ℝ) / 2)) hu₀ hfamily
  have hbounded : BddAbove
      (weightedAlphaPrimeValuesBeforeStar u₀ vStar ((1 : ℝ) / 2) S) := by
    refine ⟨C, ?_⟩
    rintro x ⟨b, hb, p, hdev, hp, rfl⟩
    exact hpoint b hb p hdev hp
  refine ⟨hbounded, ?_⟩
  have hsup : weightedAlphaPrimeSupBeforeStar u₀ vStar ((1 : ℝ) / 2) S ≤ C := by
    apply csSup_le hnonempty
    rintro x ⟨b, hb, p, hdev, hp, rfl⟩
    exact hpoint b hb p hdev hp
  simpa only [C, hε₁eq, D] using hsup

end ChristodoulouBV.Uniqueness

end
