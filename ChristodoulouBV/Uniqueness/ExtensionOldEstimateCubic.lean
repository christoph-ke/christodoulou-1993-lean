module

public import ChristodoulouBV.Uniqueness.ExtensionOldEstimateCubicRay
public import ChristodoulouBV.Uniqueness.ExtensionTransport
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Signed cubic estimate in the old extension domain

Equation (5.9) is proved on a finite incoming segment. The outgoing
cubic bound uses the same arbitrary weighted bound `A` for every ray
appearing in that segment.
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

/-- Equation (5.9) with a bound on every finite outgoing ray above the
incoming segment. The negative incoming radius derivative is retained in the
integral before applying the radial power primitive. -/
theorem integralI₃_le_weightedSup {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v δ ε A : ℝ} (hu₀u : u₀ < u)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : ε < 1)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b)
    (hμ : ∀ s ∈ Ioc u₀ u, ∀ w ∈ Ioc s v,
      2 * S.m s w / S.r s w ≤ ε)
    (hA : ∀ s ∈ Ioc u₀ u, ∀ w ∈ Ioc s v,
      (S.r s w) ^ δ *
        |deriv (fun t => S.alpha s t / S.lam s t) w / S.lam s w| ≤ A) :
    |integralI₃ b S u₀ u v hseg| ≤
      (3 * ε / (1 - ε)^2) *
        ((3 - δ) / (δ * (1 - δ) * (2 - δ))) *
        A * (S.r u v)^(-δ) := by
  let C : ℝ := (3 * (3 - δ) / ((1 - δ) * (2 - δ))) *
    (ε / (1 - ε)) * A
  let μ : ℝ → ℝ := fun s => 2 * S.m s v / S.r s v
  let T : ℝ → ℝ := fun s => S.theta s v / S.lam s v
  let F : ℝ → ℝ := fun s =>
    (S.nu s v / (S.r s v)^2) * (1 / (1 - μ s)) * (T s)^3
  let G : ℝ → ℝ := fun s =>
    (-S.nu s v) / S.r s v * (S.r s v)^(-δ)
  have hpU := hseg u (right_mem_Icc.mpr hu₀u.le)
  have hrU : 0 < S.r u v := H.solution.radius_pos (u, v)
    ⟨hpU.1.1.le, hpU.2.1, hpU.2.2⟩
  have hε0 : 0 ≤ ε :=
    (H.mass_ratio_nonneg_of_c1
      (p := (u, v)) ⟨hpU.1.1.le, hpU.2.1, hpU.2.2⟩).trans
      (hμ u (right_mem_Ioc.mpr hu₀u) v
        (right_mem_Ioc.mpr hpU.2.1))
  have hA0 : 0 ≤ A :=
    (mul_nonneg (Real.rpow_nonneg hrU.le _) (abs_nonneg _)).trans
      (hA u (right_mem_Ioc.mpr hu₀u) v
        (right_mem_Ioc.mpr hpU.2.1))
  have hden : 0 < 1 - ε := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    have hd1 : 0 ≤ 1 - δ := by linarith
    have hd2 : 0 ≤ 2 - δ := by linarith
    have hn : 0 ≤ 3 - δ := by linarith
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hn) (mul_nonneg hd1 hd2))
        (div_nonneg hε0 hden.le)) hA0
  obtain ⟨hGI, hGbound⟩ :=
    incoming_radius_power_integral_le_of_c1 H hu₀u.le hδ hseg
  have hpoint : ∀ s ∈ Ioc u₀ u,
      |F s| ≤ (C / (1 - ε)) * G s := by
    intro s hs
    have hsp := hseg s ⟨hs.1.le, hs.2⟩
    have hp : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩
    have hr := H.solution.radius_pos (s, v) hp
    have hnu := (H.reduced_signs_of_c1 hp).1
    have hμs := hμ s hs v (right_mem_Ioc.mpr hsp.2.1)
    have hgap : 0 < 1 - μ s := by dsimp [μ]; linarith
    have hcoef : 1 / (1 - μ s) ≤ 1 / (1 - ε) := by
      apply (div_le_div_iff₀ hgap hden).2
      dsimp [μ] at hμs ⊢
      nlinarith
    have hT : |T s|^3 ≤ C * (S.r s v)^(1 - δ) := by
      let B := (v + b) / 2
      have hvB : v < B := by dsimp [B]; linarith [hsp.2.2]
      have hBb : B < b := by dsimp [B]; linarith [hsp.2.2]
      have h := theta_ratio_cubic_le hsp.1.1 hsp.2.1 hvB hBb
        hδ hδ1 hε H
        (fun w hw => hμ s hs w hw)
        (fun w hw => hA s hs w hw)
        v (right_mem_Ioc.mpr hsp.2.1)
      simpa only [T, C] using h
    have hnuFactor : 0 ≤ (-S.nu s v) / (S.r s v)^2 :=
      div_nonneg (le_of_lt (neg_pos.mpr hnu)) (sq_nonneg _)
    have hfactor : 0 ≤ ((-S.nu s v) / (S.r s v)^2) * |T s|^3 :=
      mul_nonneg hnuFactor (by positivity)
    have hFabs : |F s| =
        ((-S.nu s v) / (S.r s v)^2) *
          (1 / (1 - μ s)) * |T s|^3 := by
      dsimp [F]
      rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_neg hnu,
        abs_of_pos (sq_pos_of_pos hr), abs_of_pos (div_pos one_pos hgap)]
    rw [hFabs]
    calc
      ((-S.nu s v) / (S.r s v)^2) *
          (1 / (1 - μ s)) * |T s|^3
          ≤ ((-S.nu s v) / (S.r s v)^2) *
              (1 / (1 - ε)) * |T s|^3 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hcoef hnuFactor) (by positivity)
      _ ≤ ((-S.nu s v) / (S.r s v)^2) *
            (1 / (1 - ε)) * (C * (S.r s v)^(1 - δ)) := by
              exact mul_le_mul_of_nonneg_left hT
                (mul_nonneg hnuFactor (div_nonneg (by positivity) hden.le))
      _ = (C / (1 - ε)) * G s := by
        dsimp [G]
        rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add hr,
          Real.rpow_one]
        field_simp [hr.ne']
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u₀ u →
      ‖F s‖ ≤ (C / (1 - ε)) * G s :=
    Filter.Eventually.of_forall (fun s hs => by
      simpa only [Real.norm_eq_abs] using hpoint s hs)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hu₀u.le hmaj
    (hGI.const_mul (C / (1 - ε)))
  have hmain : |integralI₃ b S u₀ u v hseg| ≤
      (C / (1 - ε)) * ∫ s in u₀..u, G s := by
    simpa only [integralI₃, abs_neg, Real.norm_eq_abs,
      intervalIntegral.integral_const_mul] using hnorm
  calc
    |integralI₃ b S u₀ u v hseg|
        ≤ (C / (1 - ε)) * ∫ s in u₀..u, G s := hmain
    _ ≤ (C / (1 - ε)) * ((S.r u v)^(-δ) / δ) :=
      mul_le_mul_of_nonneg_left hGbound (div_nonneg hC hden.le)
    _ = (3 * ε / (1 - ε)^2) *
          ((3 - δ) / (δ * (1 - δ) * (2 - δ))) *
          A * (S.r u v)^(-δ) := by
      dsimp [C]
      have hδne : δ ≠ 0 := ne_of_gt hδ
      have hden1 : 1 - δ ≠ 0 := by linarith
      have hden2 : 2 - δ ≠ 0 := by linarith
      have hεne : 1 - ε ≠ 0 := ne_of_gt hden
      field_simp

end ChristodoulouBV.Uniqueness

end
