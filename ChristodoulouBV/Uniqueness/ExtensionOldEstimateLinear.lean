module

public import ChristodoulouBV.Uniqueness.ExtensionTransport
import ChristodoulouBV.BVSolution.C1ToBV
import ChristodoulouBV.BVSolution.AxisIntegrals
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Linear estimates in the old extension domain

The estimates of Christodoulou (1993), equations (5.4)–(5.6), are proved
on finite cutoffs. Their weighted bound can then be supplied by the compatible
family's finite supremum, without assuming a full-domain supremum is finite.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem incoming_radius_hasDerivAt
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun s => S.r s v) (S.nu u v) u := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let F := C1Solution.canonicalRadius S
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    change 0 < u ∧ u < v ∧ v < B
    exact ⟨hu, huv, hvB⟩
  have hF : ContDiffOn ℝ 1 F K := C1Solution.canonicalRadius_contDiffOn hB hBb H
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hpi).differentiableAt
      (isOpen_interior.mem_nhds hpi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) (u, v) (interior_subset hpi)) hdiff
  have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun s => F (s, v))
      (fderiv ℝ F (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hjet := C1Solution.canonicalRadius_horizontal_jet hB hBb H
    (show (u, v) ∈ K from by
      change 0 ≤ u ∧ u ≤ v ∧ v ≤ B
      exact ⟨hu.le, huv.le, hvB.le⟩)
  rw [hwithin] at hjet
  rw [hjet] at hcomp
  have heq : (fun s => S.r s v) =ᶠ[𝓝 u] (fun s => F (s, v)) := by
    filter_upwards [Ioo_mem_nhds hu huv] with s hs
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H hs.1.le hs.2 hvB.le).symm
  exact hcomp.congr_of_eventuallyEq heq

private theorem incoming_radius_power_integral_le
    {R N : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hR : ContinuousOn R (Icc a b)) (hN : ContinuousOn N (Icc a b))
    (hRpos : ∀ s ∈ Icc a b, 0 < R s)
    (hD : ∀ s ∈ Icc a b, HasDerivAt R (N s) s) :
    IntervalIntegrable (fun s => (-N s) / R s * (R s)^(-δ)) volume a b ∧
      (∫ s in a..b, (-N s) / R s * (R s)^(-δ)) ≤ (R b)^(-δ) / δ := by
  let F : ℝ → ℝ := fun s => (R s)^(-δ) / δ
  let G : ℝ → ℝ := fun s => (-N s) / R s * (R s)^(-δ)
  have hpow : ContinuousOn (fun s => (R s)^(-δ)) (Icc a b) :=
    hR.rpow_const (fun s hs => Or.inl (ne_of_gt (hRpos s hs)))
  have hG : ContinuousOn G (Icc a b) :=
    (hN.neg.div hR (fun s hs => ne_of_gt (hRpos s hs))).mul hpow
  have hGI : IntervalIntegrable G volume a b :=
    hG.intervalIntegrable_of_Icc hab
  have hderiv : ∀ s ∈ Icc a b, HasDerivAt F (G s) s := by
    intro s hs
    have hspos := hRpos s hs
    have h := (Real.hasDerivAt_rpow_const
      (p := -δ) (Or.inl (ne_of_gt hspos))).comp s (hD s hs)
    have h' := h.div_const δ
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have heq : (-δ * (R s)^(-δ-1) * N s) / δ = G s := by
      dsimp [G]
      rw [show -δ - 1 = -δ + (-1 : ℝ) by ring,
        Real.rpow_add hspos, Real.rpow_neg_one]
      field_simp
    simpa only [F, G, Function.comp_apply, heq] using h'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le hab] using hderiv) hGI
  have hFa : 0 ≤ F a :=
    div_nonneg (Real.rpow_nonneg (hRpos a (left_mem_Icc.mpr hab)).le _) hδ.le
  dsimp [F] at hFa
  change (∫ s in a..b, G s) = F b - F a at hFTC
  constructor
  · exact hGI
  · rw [hFTC]
    dsimp [F]
    linarith only [hFa]

private theorem incoming_radius_power_integral_le_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v δ : ℝ} (hu₀u : u₀ ≤ u) (hδ : 0 < δ)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) :
    IntervalIntegrable
      (fun s => (-S.nu s v) / S.r s v * (S.r s v)^(-δ)) volume u₀ u ∧
      (∫ s in u₀..u, (-S.nu s v) / S.r s v * (S.r s v)^(-δ)) ≤
        (S.r u v)^(-δ) / δ := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  have hp := hseg u (right_mem_Icc.mpr hu₀u)
  have hB : 0 < B := by dsimp [B]; linarith [hp.1.1, hp.2.1, hp.2.2]
  have hBb : B < b := by dsimp [B]; linarith [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith [hp.2.2]
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc u₀ u) K := by
    intro s hs
    have hsp := hseg s hs
    change 0 ≤ s ∧ s ≤ v ∧ v ≤ B
    exact ⟨hsp.1.1.le, hsp.2.1.le, hvB.le⟩
  have hRcanon : ContinuousOn (fun s => C1Solution.canonicalRadius S (s, v))
      (Icc u₀ u) :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hR : ContinuousOn (fun s => S.r s v) (Icc u₀ u) := by
    apply hRcanon.congr
    intro s hs
    have hsp := hseg s hs
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H
      hsp.1.1.le hsp.2.1 hvB.le).symm
  have hN : ContinuousOn (fun s => S.nu s v) (Icc u₀ u) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).2.1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  exact incoming_radius_power_integral_le hu₀u hδ hR hN
    (fun s hs => H.solution.radius_pos (s, v)
      ⟨(hseg s hs).1.1.le, (hseg s hs).2.1, (hseg s hs).2.2⟩)
    (fun s hs => incoming_radius_hasDerivAt H (hseg s hs))

private theorem mass_ratio_coefficient_bounds {μ ε : ℝ}
    (hμ : 0 ≤ μ) (hμε : μ ≤ ε) (hε : ε < 1) :
    0 ≤ μ / (1 - μ) ∧ μ / (1 - μ) ≤ ε / (1 - ε) := by
  have hdenμ : 0 < 1 - μ := by linarith
  have hdenε : 0 < 1 - ε := by linarith
  constructor
  · exact div_nonneg hμ hdenμ.le
  · apply (div_le_div_iff₀ hdenμ hdenε).2
    nlinarith only [hμε]

private theorem outgoing_radius_power_integral_eq
    {R L : ℝ → ℝ} {a b δ : ℝ} (hab : a < b)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hR : ContinuousOn R (Icc a b))
    (hL : ContinuousOn L (Icc a b))
    (hR0 : R a = 0)
    (hRpos : ∀ s ∈ Ioo a b, 0 < R s)
    (hD : ∀ s ∈ Ioo a b, HasDerivAt R (L s) s) :
    (∫ s in a..b, (R s)^(1 - δ) * L s) =
      (R b)^(2 - δ) / (2 - δ) := by
  let F : ℝ → ℝ := fun s => (R s)^(2 - δ) / (2 - δ)
  let G : ℝ → ℝ := fun s => (R s)^(1 - δ) * L s
  have hexp : 0 ≤ 2 - δ := by linarith
  have hexp' : 0 ≤ 1 - δ := by linarith
  have hFC : ContinuousOn F (Icc a b) :=
    (hR.rpow_const (fun _ _ => Or.inr hexp)).div_const _
  have hGC : ContinuousOn G (Icc a b) :=
    (hR.rpow_const (fun _ _ => Or.inr hexp')).mul hL
  have hGI : IntervalIntegrable G volume a b :=
    hGC.intervalIntegrable_of_Icc hab.le
  have hderiv : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s := by
    intro s hs
    have hr := hRpos s hs
    have h := (Real.hasDerivAt_rpow_const
      (p := 2 - δ) (Or.inl (ne_of_gt hr))).comp s (hD s hs)
    have h' := h.div_const (2 - δ)
    have hden : 2 - δ ≠ 0 := by linarith
    have heq : ((2 - δ) * (R s)^(2 - δ - 1) * L s) / (2 - δ) = G s := by
      dsimp [G]
      have hexpEq : 2 - δ - 1 = 1 - δ := by ring
      rw [hexpEq]
      field_simp
    simpa only [F, G, Function.comp_apply, heq] using h'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab.le hFC hderiv hGI
  have hF0 : F a = 0 := by
    dsimp [F]
    rw [hR0, Real.zero_rpow (by linarith : 2 - δ ≠ 0)]
    simp
  change (∫ s in a..b, G s) = F b - F a at hFTC
  simpa only [hF0, sub_zero, F, G] using hFTC

/-- The axis integral expresses `θ/λ` as the deviation of the outgoing
quotient `α/λ` from its weighted outgoing average. This is the identity
preceding (5.5) on p. 1174. -/
theorem theta_ratio_axis_identity {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge b) :
    S.theta u v / S.lam u v =
      S.alpha u v / S.lam u v -
        (∫ w in u..v, S.alpha u w) / S.r u v := by
  have hb : 0 < b := by
    obtain ⟨hu, huv, hvb⟩ := hp
    linarith
  have hφ := (H.isBVSolution_development hb).phi_eq_outgoing_alpha_integral hp
  have hlam : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hp)
  dsimp [Fields.theta]
  rw [hφ]
  field_simp [hlam]

/-- Equation (5.4) with an arbitrary bound on the weighted `α′` values of
the incoming segment. On a compatible finite cutoff, `A` may be chosen as
`finiteWeightedAlphaPrimeSup`; no full-domain boundedness is used. -/
theorem integralI₁_le_weightedSup {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v δ ε A : ℝ} (hu₀u : u₀ < u) (hδ : 0 < δ)
    (hε : ε < 1)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b)
    (hμ : ∀ s ∈ Ioc u₀ u, 2 * S.m s v / S.r s v ≤ ε)
    (hA : ∀ s ∈ Ioc u₀ u,
      (S.r s v) ^ δ *
        |deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v| ≤ A) :
    |integralI₁ b S u₀ u v hseg| ≤
      (ε / (1 - ε)) * A / δ * (S.r u v)^(-δ) := by
  let C : ℝ := ε / (1 - ε)
  let P : ℝ → ℝ := fun s =>
    deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v
  let μ : ℝ → ℝ := fun s => 2 * S.m s v / S.r s v
  let F : ℝ → ℝ := fun s =>
    (S.nu s v / S.r s v) * (μ s / (1 - μ s)) * P s
  let G : ℝ → ℝ := fun s =>
    (-S.nu s v) / S.r s v * (S.r s v)^(-δ)
  have hC : 0 ≤ C := by
    have hs := hseg u (right_mem_Icc.mpr hu₀u.le)
    have hμu := H.mass_ratio_nonneg_of_c1
      (show (u, v) ∈ developmentWithInitialEdge b from
        ⟨hs.1.1.le, hs.2.1, hs.2.2⟩)
    have hε₀ : 0 ≤ ε := hμu.trans (hμ u (right_mem_Ioc.mpr hu₀u))
    exact div_nonneg hε₀ (by linarith : 0 ≤ 1 - ε)
  have hAnon : 0 ≤ A := by
    have hs := hseg u (right_mem_Icc.mpr hu₀u.le)
    have hr := H.solution.radius_pos (u, v)
      ⟨hs.1.1.le, hs.2.1, hs.2.2⟩
    exact (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans
      (hA u (right_mem_Ioc.mpr hu₀u))
  obtain ⟨hGI, hGbound⟩ :=
    incoming_radius_power_integral_le_of_c1 H hu₀u.le hδ hseg
  have hpoint : ∀ s ∈ Ioc u₀ u, |F s| ≤ C * A * G s := by
    intro s hs
    have hsp := hseg s ⟨hs.1.le, hs.2⟩
    have hp : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩
    have hr := H.solution.radius_pos (s, v) hp
    have hnu := (H.reduced_signs_of_c1 hp).1
    have hμ0 := H.mass_ratio_nonneg_of_c1 hp
    have ⟨hcoef0, hcoef⟩ :=
      mass_ratio_coefficient_bounds hμ0 (hμ s hs) hε
    have hnuFactor : 0 ≤ (-S.nu s v) / S.r s v :=
      div_nonneg (le_of_lt (neg_pos.mpr hnu)) hr.le
    have hrpow : 0 < (S.r s v)^δ := Real.rpow_pos_of_pos hr _
    have hP : |P s| ≤ A / (S.r s v)^δ :=
      (le_div_iff₀ hrpow).2 (by simpa only [P, mul_comm] using hA s hs)
    have hnuAbs : |S.nu s v / S.r s v| =
        (-S.nu s v) / S.r s v := by
      rw [abs_div, abs_of_neg hnu, abs_of_pos hr]
    have hFabs : |F s| =
        ((-S.nu s v) / S.r s v) * (μ s / (1 - μ s)) * |P s| := by
      dsimp [F]
      rw [abs_mul, abs_mul, hnuAbs, abs_of_nonneg hcoef0]
    rw [hFabs]
    calc
      ((-S.nu s v) / S.r s v) * (μ s / (1 - μ s)) * |P s|
          ≤ ((-S.nu s v) / S.r s v) * C * |P s| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcoef hnuFactor) (abs_nonneg _)
      _ ≤ ((-S.nu s v) / S.r s v) * C * (A / (S.r s v)^δ) := by
            exact mul_le_mul_of_nonneg_left hP
              (mul_nonneg hnuFactor hC)
      _ = C * A * G s := by
            dsimp [G, C]
            rw [Real.rpow_neg hr.le]
            ring
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u₀ u → ‖F s‖ ≤ C * A * G s :=
    Filter.Eventually.of_forall (fun s hs => by
      simpa only [Real.norm_eq_abs] using hpoint s hs)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hu₀u.le
    hmaj (hGI.const_mul (C * A))
  have hmain : |integralI₁ b S u₀ u v hseg| ≤
      C * A * ∫ s in u₀..u, G s := by
    simpa only [integralI₁, abs_neg, Real.norm_eq_abs,
      intervalIntegral.integral_const_mul] using hnorm
  calc
    |integralI₁ b S u₀ u v hseg|
        ≤ C * A * ∫ s in u₀..u, G s := hmain
    _ ≤ C * A * ((S.r u v)^(-δ) / δ) :=
      mul_le_mul_of_nonneg_left hGbound (mul_nonneg hC hAnon)
    _ = (ε / (1 - ε)) * A / δ * (S.r u v)^(-δ) := by
      dsimp [C]
      ring

/-- Equation (5.5) on one finite outgoing ray. The arbitrary number `A`
bounds every weighted `α′` value on that ray. A finite compatible cutoff
supremum supplies such a number before any limit toward `vStar`. -/
theorem theta_ratio_le_weightedAlphaPrime {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v δ A : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hA : ∀ s ∈ Ioc u v,
      (S.r u s) ^ δ *
        |deriv (fun t => S.alpha u t / S.lam u t) s / S.lam u s| ≤ A) :
    |S.theta u v / S.lam u v| ≤
      A / (2 - δ) * (S.r u v) ^ (1 - δ) := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun s => C1Solution.canonicalRadius S (u, s)
  let Q : ℝ → ℝ := fun s => S.alpha u s / S.lam u s
  let L : ℝ → ℝ := fun s => S.lam u s
  let P : ℝ → ℝ := fun s => deriv Q s / L s
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) K := by
    intro s hs
    change 0 ≤ u ∧ u ≤ s ∧ s ≤ B
    exact ⟨hu.le, hs.1, hs.2.trans hvB.le⟩
  have hpair : ContDiff ℝ 1 (fun s : ℝ => (u, s)) :=
    contDiff_const.prodMk contDiff_id
  have hRc1 : ContDiffOn ℝ 1 R (Icc u v) :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).comp
      hpair.contDiffOn hmap
  have hQc1 : ContDiffOn ℝ 1 Q (Icc u v) :=
    (C1Solution.alpha_div_lam_contDiffOn hB hBb H).comp
      hpair.contDiffOn hmap
  have hL : ContinuousOn L (Icc u v) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hR0 : R u = 0 := (C1Solution.canonical_outgoing_axis S u).1
  have hReq : ∀ s ∈ Ioc u v, R s = S.r u s := by
    intro s hs
    exact C1Solution.canonicalRadius_eq_radius hB hBb H hu.le hs.1
      (hs.2.trans hvB.le)
  have hRpos : ∀ s ∈ Ioc u v, 0 < R s := by
    intro s hs
    rw [hReq s hs]
    exact H.solution.radius_pos (u, s)
      ⟨hu.le, hs.1, hs.2.trans_lt hvb⟩
  have hRderiv : ∀ s ∈ Ioo u v, HasDerivAt R (L s) s := by
    intro s hs
    have hLint : IntervalIntegrable L volume u s :=
      (hL.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le
    have hLat : ContinuousAt L s := hL.continuousAt (Icc_mem_nhds hs.1 hs.2)
    have hMeas : StronglyMeasurableAtFilter L (𝓝 s) :=
      (hL.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter
        isOpen_Ioo s hs
    have hFTC := intervalIntegral.integral_hasDerivAt_right hLint hMeas hLat
    change HasDerivAt R (L s) s at hFTC
    exact hFTC
  have hRAC : AbsolutelyContinuousOnInterval R u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv.le] using hRc1
  have hQAC : AbsolutelyContinuousOnInterval Q u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv.le] using hQc1
  have hRderivEq : ∀ s ∈ Ioo u v, deriv R s = L s :=
    fun s hs => (hRderiv s hs).deriv
  have hαInt : (∫ s in u..v, deriv R s * Q s) =
      ∫ s in u..v, S.alpha u s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume v] with s hne hs
    have hsIoc : s ∈ Ioc u v := by
      simpa only [uIoc_of_le huv.le] using hs
    have hs' : s ∈ Ioo u v :=
      ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hne⟩
    rw [hRderivEq s hs']
    dsimp [L, Q]
    have hlam : S.lam u s ≠ 0 := ne_of_gt
      (H.solution.lam_pos (u, s) ⟨hu.le, hs'.1, hs'.2.trans hvb⟩)
    field_simp [hlam]
  have hIBP := hRAC.integral_mul_deriv_eq_deriv_mul hQAC
  have hIBP' : (∫ s in u..v, R s * deriv Q s) =
      (S.r u v) * Q v - ∫ s in u..v, S.alpha u s := by
    rw [hReq v (right_mem_Ioc.mpr huv), hR0, zero_mul, sub_zero, hαInt] at hIBP
    exact hIBP
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, huv, hvb⟩
  have hr := H.solution.radius_pos (u, v) hp
  have htheta : S.theta u v / S.lam u v =
      (∫ s in u..v, R s * deriv Q s) / S.r u v := by
    rw [theta_ratio_axis_identity H hp, hIBP']
    dsimp [Q]
    field_simp [hr.ne']
  have hA0 : 0 ≤ A := by
    have hsample := hA v (right_mem_Ioc.mpr huv)
    exact (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans hsample
  have hPower := outgoing_radius_power_integral_eq huv hδ hδ1
    hRc1.continuousOn hL hR0
    (fun s hs => hRpos s ⟨hs.1, hs.2.le⟩) hRderiv
  have hWint : IntervalIntegrable (fun s => (R s) ^ (1 - δ) * L s)
      volume u v := by
    have hpow : ContinuousOn (fun s => (R s) ^ (1 - δ)) (Icc u v) :=
      hRc1.continuousOn.rpow_const (fun _ _ => Or.inr (by linarith))
    exact (hpow.mul hL).intervalIntegrable_of_Icc huv.le
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u v →
      ‖R s * deriv Q s‖ ≤ A * ((R s) ^ (1 - δ) * L s) := by
    filter_upwards [Measure.ae_ne volume v] with s hne hsIoc
    have hs : s ∈ Ioo u v := ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hne⟩
    have hr_s := hRpos s hsIoc
    have hlam := H.solution.lam_pos (u, s)
      ⟨hu.le, hs.1, hs.2.trans hvb⟩
    have hbound := hA s hsIoc
    have hQprime : deriv Q s = L s * P s := by
      dsimp [P, L]
      field_simp [hlam.ne']
    have hpowMul : (R s) ^ (1 - δ) * (R s) ^ δ = R s := by
      rw [← Real.rpow_add hr_s]
      calc
        (R s) ^ (1 - δ + δ) = (R s) ^ (1 : ℝ) := by congr 1; ring
        _ = R s := Real.rpow_one _
    have hbound' : (R s) ^ δ * |P s| ≤ A := by
      simpa only [hReq s hsIoc, P, Q, L] using hbound
    rw [hQprime, Real.norm_eq_abs, abs_mul, abs_of_pos hr_s,
      abs_mul, abs_of_pos hlam]
    calc
      R s * (L s * |P s|) =
          ((R s) ^ (1 - δ) * L s) * ((R s) ^ δ * |P s|) := by
            calc
              R s * (L s * |P s|) =
                  ((R s) ^ (1 - δ) * (R s) ^ δ) * (L s * |P s|) := by
                    rw [hpowMul]
              _ = ((R s) ^ (1 - δ) * L s) * ((R s) ^ δ * |P s|) := by
                    ring
      _ ≤ ((R s) ^ (1 - δ) * L s) * A :=
        mul_le_mul_of_nonneg_left hbound'
          (mul_nonneg (Real.rpow_nonneg hr_s.le _) hlam.le)
      _ = A * ((R s) ^ (1 - δ) * L s) := mul_comm _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le huv.le hmaj
    (hWint.const_mul A)
  have hIntBound : |∫ s in u..v, R s * deriv Q s| ≤
      A * ((S.r u v) ^ (2 - δ) / (2 - δ)) := by
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      hPower, hReq v (right_mem_Ioc.mpr huv)] using hnorm
  rw [htheta, abs_div, abs_of_pos hr]
  have hden : 0 < 2 - δ := by linarith
  have hpowEq : (S.r u v) ^ (2 - δ) =
      (S.r u v) ^ (1 - δ) * S.r u v := by
    calc
      (S.r u v) ^ (2 - δ) = (S.r u v) ^ ((1 - δ) + 1) := by congr 1; ring
      _ = (S.r u v) ^ (1 - δ) * (S.r u v) ^ (1 : ℝ) :=
        Real.rpow_add hr _ _
      _ = (S.r u v) ^ (1 - δ) * S.r u v := by rw [Real.rpow_one]
  calc
    |∫ s in u..v, R s * deriv Q s| / S.r u v
        ≤ (A * ((S.r u v) ^ (2 - δ) / (2 - δ))) / S.r u v :=
          div_le_div_of_nonneg_right hIntBound hr.le
    _ = A / (2 - δ) * (S.r u v) ^ (1 - δ) := by
      rw [hpowEq]
      field_simp

/-- Equation (5.6) with a finite weighted bound on every outgoing point
above the incoming segment. The sign of `ν` is used before the radius
integration, and the outgoing bound is the proved equation (5.5). -/
theorem integralI₂_le_weightedSup {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v δ ε A : ℝ} (hu₀u : u₀ < u)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : ε < 1)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b)
    (hμ : ∀ s ∈ Ioc u₀ u, 2 * S.m s v / S.r s v ≤ ε)
    (hA : ∀ s ∈ Ioc u₀ u, ∀ w ∈ Ioc s v,
      (S.r s w) ^ δ *
        |deriv (fun t => S.alpha s t / S.lam s t) w / S.lam s w| ≤ A) :
    |integralI₂ b S u₀ u v hseg| ≤
      (ε / (1 - ε)) * A / (δ * (2 - δ)) * (S.r u v) ^ (-δ) := by
  let C : ℝ := ε / (1 - ε)
  let μ : ℝ → ℝ := fun s => 2 * S.m s v / S.r s v
  let T : ℝ → ℝ := fun s => S.theta s v / S.lam s v
  let F : ℝ → ℝ := fun s =>
    (S.nu s v / (S.r s v)^2) * (μ s / (1 - μ s)) * T s
  let G : ℝ → ℝ := fun s =>
    (-S.nu s v) / S.r s v * (S.r s v)^(-δ)
  have hden : 0 < 2 - δ := by linarith
  have hC : 0 ≤ C := by
    have hs := hseg u (right_mem_Icc.mpr hu₀u.le)
    have hμu := H.mass_ratio_nonneg_of_c1
      (show (u, v) ∈ developmentWithInitialEdge b from
        ⟨hs.1.1.le, hs.2.1, hs.2.2⟩)
    have hε₀ : 0 ≤ ε := hμu.trans (hμ u (right_mem_Ioc.mpr hu₀u))
    exact div_nonneg hε₀ (by linarith : 0 ≤ 1 - ε)
  have hAnon : 0 ≤ A := by
    have hs := hseg u (right_mem_Icc.mpr hu₀u.le)
    have hr := H.solution.radius_pos (u, v)
      ⟨hs.1.1.le, hs.2.1, hs.2.2⟩
    exact (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans
      (hA u (right_mem_Ioc.mpr hu₀u) v (right_mem_Ioc.mpr hs.2.1))
  obtain ⟨hGI, hGbound⟩ :=
    incoming_radius_power_integral_le_of_c1 H hu₀u.le hδ hseg
  have hpoint : ∀ s ∈ Ioc u₀ u,
      |F s| ≤ C * (A / (2 - δ)) * G s := by
    intro s hs
    have hsp := hseg s ⟨hs.1.le, hs.2⟩
    have hp : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩
    have hr := H.solution.radius_pos (s, v) hp
    have hnu := (H.reduced_signs_of_c1 hp).1
    have hμ0 := H.mass_ratio_nonneg_of_c1 hp
    have ⟨hcoef0, hcoef⟩ :=
      mass_ratio_coefficient_bounds hμ0 (hμ s hs) hε
    have hnuFactor : 0 ≤ (-S.nu s v) / (S.r s v)^2 :=
      div_nonneg (le_of_lt (neg_pos.mpr hnu)) (sq_nonneg _)
    have hT : |T s| ≤ A / (2 - δ) * (S.r s v) ^ (1 - δ) := by
      exact theta_ratio_le_weightedAlphaPrime H hsp.1.1 hsp.2.1 hsp.2.2
        hδ hδ1 (fun w hw => hA s hs w hw)
    have hnuAbs : |S.nu s v / (S.r s v)^2| =
        (-S.nu s v) / (S.r s v)^2 := by
      rw [abs_div, abs_of_neg hnu, abs_of_pos (sq_pos_of_pos hr)]
    have hFabs : |F s| =
        ((-S.nu s v) / (S.r s v)^2) * (μ s / (1 - μ s)) * |T s| := by
      dsimp [F]
      rw [abs_mul, abs_mul, hnuAbs, abs_of_nonneg hcoef0]
    rw [hFabs]
    calc
      ((-S.nu s v) / (S.r s v)^2) * (μ s / (1 - μ s)) * |T s|
          ≤ ((-S.nu s v) / (S.r s v)^2) * C * |T s| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcoef hnuFactor) (abs_nonneg _)
      _ ≤ ((-S.nu s v) / (S.r s v)^2) * C *
          (A / (2 - δ) * (S.r s v) ^ (1 - δ)) := by
            exact mul_le_mul_of_nonneg_left hT
              (mul_nonneg hnuFactor hC)
      _ = C * (A / (2 - δ)) * G s := by
            dsimp [G]
            rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add hr,
              Real.rpow_one]
            field_simp [hr.ne']
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u₀ u →
      ‖F s‖ ≤ C * (A / (2 - δ)) * G s :=
    Filter.Eventually.of_forall (fun s hs => by
      simpa only [Real.norm_eq_abs] using hpoint s hs)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hu₀u.le hmaj
    (hGI.const_mul (C * (A / (2 - δ))))
  have hmain : |integralI₂ b S u₀ u v hseg| ≤
      C * (A / (2 - δ)) * ∫ s in u₀..u, G s := by
    simpa only [integralI₂, abs_neg, Real.norm_eq_abs,
      intervalIntegral.integral_const_mul] using hnorm
  calc
    |integralI₂ b S u₀ u v hseg|
        ≤ C * (A / (2 - δ)) * ∫ s in u₀..u, G s := hmain
    _ ≤ C * (A / (2 - δ)) * ((S.r u v) ^ (-δ) / δ) :=
      mul_le_mul_of_nonneg_left hGbound
        (mul_nonneg hC (div_nonneg hAnon hden.le))
    _ = (ε / (1 - ε)) * A / (δ * (2 - δ)) *
        (S.r u v) ^ (-δ) := by
      dsimp [C]
      have hδne : δ ≠ 0 := ne_of_gt hδ
      have hdenne : 2 - δ ≠ 0 := ne_of_gt hden
      field_simp

end ChristodoulouBV.Uniqueness

end
