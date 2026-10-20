module

public import Mathlib

/-!
# Algebra of the old-domain absorption coefficient

The constants here are universal functions of the weight exponent. The
smallness threshold is chosen before any initial data or solution family.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The first coefficient in (5.10). -/
noncomputable def oldAbsorptionA (δ : ℝ) : ℝ :=
  (7 - 2 * δ) / (δ * (2 - δ))

/-- The second coefficient in (5.10). -/
noncomputable def oldAbsorptionB (δ : ℝ) : ℝ :=
  3 * (3 - δ) / (δ * (1 - δ) * (2 - δ))

/-- The multiplier of `A′` in (5.10). -/
noncomputable def oldAbsorptionCoefficient (δ ε : ℝ) : ℝ :=
  (oldAbsorptionA δ + oldAbsorptionB δ / (1 - ε)) * ε / (1 - ε)

/-- The positive root of the strict absorption condition (5.11). -/
noncomputable def oldAbsorptionThreshold (δ : ℝ) : ℝ :=
  let a := oldAbsorptionA δ
  let b := oldAbsorptionB δ
  (2 + a + b - Real.sqrt ((2 + a + b)^2 - 4 * (1 + a))) /
    (2 * (1 + a))

/-- Both rational coefficients in (5.10) are positive for `0<δ<1`. -/
theorem oldAbsorptionA_pos_and_B_pos {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < oldAbsorptionA δ ∧ 0 < oldAbsorptionB δ := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  constructor
  · unfold oldAbsorptionA
    exact div_pos (by linarith) (mul_pos hδ h2)
  · unfold oldAbsorptionB
    exact div_pos (by linarith) (mul_pos (mul_pos hδ h1) h2)

private theorem absorption_root_iff {a b ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (_hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    let T := 2 + a + b
    let q := 1 + a
    let c := (T - Real.sqrt (T^2 - 4*q)) / (2*q)
    0 < c ∧
      ((a + b / (1 - ε)) * ε / (1 - ε) < 1 ↔ ε < c) := by
  dsimp
  let T : ℝ := 2 + a + b
  let q : ℝ := 1 + a
  let s : ℝ := Real.sqrt (T^2 - 4*q)
  let c : ℝ := (T - s) / (2*q)
  let r : ℝ := (T + s) / (2*q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hT : 0 < T := by dsimp [T]; linarith
  have hdisc : 0 < T^2 - 4*q := by
    dsimp [T, q]
    nlinarith [sq_nonneg (a + b)]
  have hs : 0 < s := Real.sqrt_pos.2 hdisc
  have hs2 : s^2 = T^2 - 4*q := Real.sq_sqrt hdisc.le
  have hsT : s < T := by nlinarith [hs2]
  have hc : 0 < c := div_pos (sub_pos.2 hsT) (mul_pos (by norm_num) hq)
  have hr : 1 < r := by
    have hsab : a - b < s := by
      by_cases hab : a ≤ b
      · linarith
      · have hsq : (a - b)^2 < s^2 := by
          dsimp [T, q] at hs2
          nlinarith [mul_pos hb hq]
        nlinarith
    dsimp [r, T, q]
    apply (one_lt_div (mul_pos (by norm_num) hq)).2
    dsimp [T, q] at hsab ⊢
    linarith
  have hfactor (x : ℝ) :
      1 - T*x + q*x^2 = q*(x-c)*(x-r) := by
    dsimp [c, r]
    field_simp [ne_of_gt hq]
    nlinarith [hs2]
  have hd : 0 < 1 - ε := by linarith
  have hcoeff :
      (a + b / (1 - ε)) * ε / (1 - ε) =
        (a*ε*(1-ε) + b*ε) / (1-ε)^2 := by
    field_simp [ne_of_gt hd]
  have hpoly :
      (1-ε)^2 - (a*ε*(1-ε)+b*ε) = 1-T*ε+q*ε^2 := by
    dsimp [T, q]
    ring
  have hiff :
      (a + b / (1 - ε)) * ε / (1 - ε) < 1 ↔
        0 < 1 - T*ε + q*ε^2 := by
    rw [hcoeff, div_lt_iff₀ (sq_pos_of_pos hd)]
    rw [← hpoly]
    constructor <;> intro h <;> linarith
  refine ⟨?_, ?_⟩
  · simpa only [T, q, s, c] using hc
  · rw [hiff, hfactor]
    have hεr : ε - r < 0 := by linarith
    constructor
    · intro h
      by_contra hn
      have hεc : 0 ≤ ε - c := sub_nonneg.mpr (le_of_not_gt hn)
      have hnon : q * (ε - c) * (ε - r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hq.le hεc) hεr.le
      linarith
    · intro h
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg hq (sub_neg.mpr h)) hεr

/-- Equation (5.11): for `0<δ<1` and `0≤ε<1`, strict absorption is
equivalent to `ε` lying below the positive source threshold. -/
theorem absorption_coefficient_lt_one_iff {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    0 < oldAbsorptionThreshold δ ∧
      (oldAbsorptionCoefficient δ ε < 1 ↔
        ε < oldAbsorptionThreshold δ) := by
  obtain ⟨ha, hb⟩ := oldAbsorptionA_pos_and_B_pos hδ hδ1
  exact absorption_root_iff ha.le hb hε0 hε1

/-- Rationalizing the source's positive root makes its endpoint behavior
transparent. -/
theorem oldAbsorptionThreshold_eq_two_div {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    oldAbsorptionThreshold δ =
      2 / (2 + oldAbsorptionA δ + oldAbsorptionB δ +
        Real.sqrt ((2 + oldAbsorptionA δ + oldAbsorptionB δ)^2 -
          4 * (1 + oldAbsorptionA δ))) := by
  obtain ⟨ha, hb⟩ := oldAbsorptionA_pos_and_B_pos hδ hδ1
  let a := oldAbsorptionA δ
  let b := oldAbsorptionB δ
  let T : ℝ := 2 + a + b
  let q : ℝ := 1 + a
  let s : ℝ := Real.sqrt (T^2 - 4*q)
  have hT : 0 < T := by dsimp [T]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hdisc : 0 ≤ T^2 - 4*q := by
    dsimp [T, q]
    nlinarith [sq_nonneg (a + b)]
  have hs2 : s^2 = T^2 - 4*q := Real.sq_sqrt hdisc
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hTs : T + s ≠ 0 := ne_of_gt (by linarith)
  change (T - s) / (2*q) = 2 / (T + s)
  field_simp [ne_of_gt hq, hTs]
  nlinarith [hs2]

/-- The source threshold vanishes at both endpoints: on `0<δ<1` it is
bounded by both `δ` and `1-δ`. -/
theorem oldAbsorptionThreshold_le_weight {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ oldAbsorptionThreshold δ ∧
      oldAbsorptionThreshold δ ≤ δ ∧
      oldAbsorptionThreshold δ ≤ 1 - δ := by
  obtain ⟨ha, hb⟩ := oldAbsorptionA_pos_and_B_pos hδ hδ1
  let a := oldAbsorptionA δ
  let b := oldAbsorptionB δ
  let T : ℝ := 2 + a + b
  let s : ℝ := Real.sqrt (T^2 - 4*(1+a))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hTs : 0 < T + s := by dsimp [T]; linarith
  have hδa : 2 ≤ δ * a := by
    have hden : 0 < 2 - δ := by linarith
    have heq : δ * a = (7 - 2*δ) / (2-δ) := by
      dsimp [a, oldAbsorptionA]
      field_simp [ne_of_gt hδ, ne_of_gt hden]
    rw [heq]
    apply (le_div_iff₀ hden).2
    linarith
  have hδb : 2 ≤ (1-δ) * b := by
    have hden : 0 < δ * (2 - δ) := mul_pos hδ (by linarith)
    have heq : (1-δ) * b = 3*(3-δ) / (δ*(2-δ)) := by
      dsimp [b, oldAbsorptionB]
      field_simp [ne_of_gt hδ, ne_of_gt (by linarith : 0 < 1 - δ),
        ne_of_gt (by linarith : 0 < 2 - δ)]
    rw [heq]
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (δ - 1)]
  have hδTs : 2 ≤ δ * (T + s) := by
    have hrest : 0 ≤ δ * (2 + b + s) :=
      mul_nonneg hδ.le (by linarith)
    dsimp [T]
    nlinarith only [hδa, hrest]
  have hδ1Ts : 2 ≤ (1-δ) * (T + s) := by
    have hrest : 0 ≤ (1-δ) * (2 + a + s) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [T]
    nlinarith only [hδb, hrest]
  have hroot := oldAbsorptionThreshold_eq_two_div hδ hδ1
  change oldAbsorptionThreshold δ = 2 / (T+s) at hroot
  rw [hroot]
  refine ⟨(div_pos (by norm_num) hTs).le, ?_, ?_⟩
  · exact (div_le_iff₀ hTs).2 hδTs
  · exact (div_le_iff₀ hTs).2 hδ1Ts

/-- The strict absorption threshold is continuous at every interior weight. -/
theorem oldAbsorptionThreshold_continuousAt {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ContinuousAt oldAbsorptionThreshold δ := by
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < 2 - δ := by linarith
  have hA : ContinuousAt oldAbsorptionA δ := by
    unfold oldAbsorptionA
    fun_prop (disch := positivity)
  have hB : ContinuousAt oldAbsorptionB δ := by
    unfold oldAbsorptionB
    fun_prop (disch := positivity)
  have ha := (oldAbsorptionA_pos_and_B_pos hδ hδ1).1
  have hden : 2 * (1 + oldAbsorptionA δ) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (by linarith))
  let T : ℝ → ℝ := fun x => 2 + oldAbsorptionA x + oldAbsorptionB x
  let Q : ℝ → ℝ := fun x => 1 + oldAbsorptionA x
  have hT : ContinuousAt T δ :=
    (continuousAt_const.add hA).add hB
  have hQ : ContinuousAt Q δ := continuousAt_const.add hA
  have hdisc : ContinuousAt (fun x => T x ^ 2 - 4 * Q x) δ :=
    (hT.pow 2).sub (continuousAt_const.mul hQ)
  have hsqrt : ContinuousAt (fun x => Real.sqrt (T x ^ 2 - 4 * Q x)) δ :=
    Real.continuous_sqrt.continuousAt.comp hdisc
  change ContinuousAt
    (fun x => (T x - Real.sqrt (T x ^ 2 - 4 * Q x)) /
      (2 * Q x)) δ
  exact (hT.sub hsqrt).div (continuousAt_const.mul hQ) hden

/-- The source's endpoint extension of the absorption threshold, set to
zero at `δ=0` and `δ=1`. -/
noncomputable def oldAbsorptionThresholdClosed (δ : ℝ) : ℝ :=
  if δ ∈ Set.Ioo (0 : ℝ) 1 then oldAbsorptionThreshold δ else 0

/-- The positive threshold extends continuously to `[0,1]`, with value
zero at both endpoints. -/
theorem oldAbsorptionThreshold_continuous_extension :
    ContinuousOn oldAbsorptionThresholdClosed (Set.Icc (0 : ℝ) 1) ∧
      oldAbsorptionThresholdClosed 0 = 0 ∧
      oldAbsorptionThresholdClosed 1 = 0 ∧
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        oldAbsorptionThresholdClosed δ = oldAbsorptionThreshold δ) := by
  have hzero : oldAbsorptionThresholdClosed 0 = 0 := by
    simp [oldAbsorptionThresholdClosed]
  have hone : oldAbsorptionThresholdClosed 1 = 0 := by
    simp [oldAbsorptionThresholdClosed]
  refine ⟨?_, hzero, hone, ?_⟩
  · intro δ hδ
    by_cases hδ0 : δ = 0
    · subst δ
      have hbounds : ∀ᶠ x in 𝓝[Set.Icc (0 : ℝ) 1] 0,
          0 ≤ oldAbsorptionThresholdClosed x ∧
            oldAbsorptionThresholdClosed x ≤ x := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        by_cases hxi : x ∈ Set.Ioo (0 : ℝ) 1
        · have hb := oldAbsorptionThreshold_le_weight hxi.1 hxi.2
          simpa [oldAbsorptionThresholdClosed, hxi] using
            And.intro hb.1 hb.2.1
        · simpa [oldAbsorptionThresholdClosed, hxi] using hx.1
      have hlim : Tendsto oldAbsorptionThresholdClosed
          (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 (0 : ℝ)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds
          (tendsto_id.mono_left nhdsWithin_le_nhds)
          (hbounds.mono fun _ hx => hx.1)
          (hbounds.mono fun _ hx => hx.2)
      change Tendsto oldAbsorptionThresholdClosed
        (𝓝[Set.Icc (0 : ℝ) 1] 0) (𝓝 (oldAbsorptionThresholdClosed 0))
      rw [hzero]
      exact hlim
    · by_cases hδ1 : δ = 1
      · subst δ
        have hbounds : ∀ᶠ x in 𝓝[Set.Icc (0 : ℝ) 1] 1,
            0 ≤ oldAbsorptionThresholdClosed x ∧
              oldAbsorptionThresholdClosed x ≤ 1 - x := by
          filter_upwards [self_mem_nhdsWithin] with x hx
          by_cases hxi : x ∈ Set.Ioo (0 : ℝ) 1
          · have hb := oldAbsorptionThreshold_le_weight hxi.1 hxi.2
            simpa [oldAbsorptionThresholdClosed, hxi] using
              And.intro hb.1 hb.2.2
          · simpa [oldAbsorptionThresholdClosed, hxi] using
              (sub_nonneg.mpr hx.2)
        have hlimUpper : Tendsto (fun x : ℝ => 1 - x)
            (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (0 : ℝ)) := by
          have hcont : Continuous (fun x : ℝ => 1 - x) :=
            continuous_const.sub continuous_id
          have ht : Tendsto (fun x : ℝ => 1 - x)
              (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 ((1 : ℝ) - 1)) :=
            (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
          simpa only [sub_self] using ht
        have hlim : Tendsto oldAbsorptionThresholdClosed
            (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (0 : ℝ)) :=
          tendsto_of_tendsto_of_tendsto_of_le_of_le'
            tendsto_const_nhds hlimUpper
            (hbounds.mono fun _ hx => hx.1)
            (hbounds.mono fun _ hx => hx.2)
        change Tendsto oldAbsorptionThresholdClosed
          (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (oldAbsorptionThresholdClosed 1))
        rw [hone]
        exact hlim
      · have hInt : δ ∈ Set.Ioo (0 : ℝ) 1 := by
          exact ⟨lt_of_le_of_ne hδ.1 (Ne.symm hδ0),
            lt_of_le_of_ne hδ.2 hδ1⟩
        have hEq : oldAbsorptionThresholdClosed =ᶠ[𝓝 δ]
            oldAbsorptionThreshold := by
          filter_upwards [isOpen_Ioo.mem_nhds hInt] with x hx
          simp [oldAbsorptionThresholdClosed, hx]
        have hcont : ContinuousAt oldAbsorptionThreshold δ :=
          oldAbsorptionThreshold_continuousAt hInt.1 hInt.2
        have hclosed : ContinuousAt oldAbsorptionThresholdClosed δ :=
          hcont.congr_of_eventuallyEq hEq
        exact hclosed.continuousWithinAt
  · intro δ hδ
    simp [oldAbsorptionThresholdClosed, hδ]

/-- At weight `δ=1/2`, the two source coefficients are exactly `8` and
`20`. -/
theorem oldAbsorption_coefficients_half :
    oldAbsorptionA ((1 : ℝ) / 2) = 8 ∧
      oldAbsorptionB ((1 : ℝ) / 2) = 20 := by
  constructor <;> norm_num [oldAbsorptionA, oldAbsorptionB]

/-- The source's displayed denominator is weaker than exact absorption:
for `0≤ε≤ε₁`, the coefficient in (5.10) is at most `ε/ε₁`. -/
theorem oldAbsorptionCoefficient_half_le_ratio
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ (5 - 2 * Real.sqrt 6) / 3) :
    oldAbsorptionCoefficient ((1 : ℝ) / 2) ε ≤
      ε / ((5 - 2 * Real.sqrt 6) / 3) := by
  let s : ℝ := Real.sqrt 6
  let e₁ : ℝ := (5 - 2*s) / 3
  let d : ℝ := 1 - ε
  let d₁ : ℝ := 1 - e₁
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = 6 := Real.sq_sqrt (by norm_num)
  have hs22 : 11 / 5 < s := by nlinarith
  have he₁0 : 0 < e₁ := by dsimp [e₁]; nlinarith
  have he₁5 : e₁ < 1 / 5 := by dsimp [e₁]; linarith
  have hεle : ε ≤ e₁ := hε1
  have hd₁ : 0 < d₁ := by dsimp [d₁]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hroot : d₁^2 = e₁ * (8*d₁ + 20) := by
    dsimp [d₁, e₁]
    nlinarith [hs2]
  have hbase : e₁ * (8*d + 20) ≤ d^2 := by
    have hfactor : d^2 - e₁ * (8*d + 20) =
        (e₁ - ε) * (d + d₁ - 8*e₁) := by
      dsimp [d, d₁]
      nlinarith [hroot]
    have hfac0 : 0 ≤ e₁ - ε := sub_nonneg.mpr hεle
    have hfac1 : 0 ≤ d + d₁ - 8*e₁ := by
      dsimp [d, d₁]
      linarith
    have hprod := mul_nonneg hfac0 hfac1
    rw [← hfactor] at hprod
    linarith
  have hcoeff : oldAbsorptionCoefficient ((1 : ℝ) / 2) ε =
      ε * (8*d + 20) / d^2 := by
    rw [oldAbsorptionCoefficient, oldAbsorption_coefficients_half.1,
      oldAbsorption_coefficients_half.2]
    change (8 + 20 / d) * ε / d = ε * (8 * d + 20) / d^2
    field_simp [ne_of_gt hd]
  rw [hcoeff]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) he₁0).2
  have hscaled := mul_nonneg hε0 (sub_nonneg.mpr hbase)
  dsimp [e₁] at hscaled ⊢
  nlinarith only [hscaled]

/-- The universal source choice is made before the data and family binders.
It includes the numerical comparison needed for the displayed denominator
in (5.12). -/
theorem universal_epsilon_choice :
    ∃ ε₁ : ℝ,
      ε₁ = (5 - 2 * Real.sqrt 6) / 3 ∧
      0 < ε₁ ∧
      ε₁ < 1 ∧
      oldAbsorptionA ((1 : ℝ) / 2) = 8 ∧
      oldAbsorptionB ((1 : ℝ) / 2) = 20 ∧
      oldAbsorptionThreshold ((1 : ℝ) / 2) = ε₁ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < ε₁ →
        oldAbsorptionCoefficient ((1 : ℝ) / 2) ε ≤ ε / ε₁ ∧
        ε / ε₁ < 1 := by
  let s : ℝ := Real.sqrt 6
  let ε₁ : ℝ := (5 - 2*s) / 3
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = 6 := Real.sq_sqrt (by norm_num)
  have hε₁0 : 0 < ε₁ := by dsimp [ε₁]; nlinarith [hs2]
  have hs2gt : 2 < s := by nlinarith
  have hε₁lt1 : ε₁ < 1 := by dsimp [ε₁]; linarith
  have hsqrt : Real.sqrt (864 : ℝ) = 12*s := by
    have h864 : (Real.sqrt (864 : ℝ))^2 = 864 :=
      Real.sq_sqrt (by norm_num)
    have h8640 := Real.sqrt_nonneg (864 : ℝ)
    nlinarith [hs2]
  have hthreshold : oldAbsorptionThreshold ((1 : ℝ) / 2) = ε₁ := by
    unfold oldAbsorptionThreshold
    rw [oldAbsorption_coefficients_half.1,
      oldAbsorption_coefficients_half.2]
    norm_num
    rw [hsqrt]
    dsimp [ε₁, s]
    ring
  refine ⟨ε₁, rfl, hε₁0, hε₁lt1,
    oldAbsorption_coefficients_half.1,
    oldAbsorption_coefficients_half.2, hthreshold, ?_⟩
  intro ε hε0 hε1
  constructor
  · exact oldAbsorptionCoefficient_half_le_ratio hε0 hε1.le
  · exact (div_lt_one hε₁0).2 hε1

end ChristodoulouBV.Uniqueness

end
