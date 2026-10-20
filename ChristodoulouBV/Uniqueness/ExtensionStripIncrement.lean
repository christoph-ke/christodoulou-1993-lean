module

public import ChristodoulouBV.Uniqueness.ExtensionStripStart
public import ChristodoulouBV.Uniqueness.ExtensionStripDomain
import ChristodoulouBV.Uniqueness.ExtensionStripTheta
import ChristodoulouBV.Uniqueness.ExtensionLocalSigns
import ChristodoulouBV.Uniqueness.ExtensionLocalRadius
import ChristodoulouBV.C1Solution.Uniqueness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Mass and radius increments on an adjacent extension strip

The sharp mass estimate retains the exact integral of `r * r_v`. The paper
prints a weaker estimate before (5.21); the sharp one supplies its coefficient.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem strip_initial_lam_eq_half
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    (hGauge : ∀ w ∈ Ioo (0 : ℝ) top, T.r 0 w = w / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) top) (hu₁ : 0 < u₁) :
    T.lam 0 v = 1 / 2 := by
  let B := (v + top) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hv.1, hv.2]
  have hvB : v < B := by dsimp [B]; linarith [hv.2]
  have hBtop : B < top := by dsimp [B]; linarith [hv.2]
  have hmap (t : ℝ) (ht : t ∈ Icc 0 B) :
      (0, t) ∈ closure (extensionWorkingDomain u₁ top) := by
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      have hp : (0, v) ∈ extensionWorkingDomain u₁ top :=
        ⟨le_refl 0, hv.1, hv.2, hu₁⟩
      exact H.solution.development.axis_mem hp
    · exact subset_closure ⟨le_refl 0, hpos, ht.2.trans_lt hBtop, hu₁⟩
  have hc : ContinuousOn (T.lam 0) (Icc 0 B) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  apply C1Solution.initial_outgoing_density_eq_of_integral_eq hB hc
    continuousOn_const ?_ ⟨hv.1, hvB⟩
  intro t ht
  have hp : (0, t) ∈ extensionWorkingDomain u₁ top :=
    ⟨le_refl 0, ht.1, ht.2.trans hBtop, hu₁⟩
  calc
    (∫ s in (0 : ℝ)..t, T.lam 0 s) = T.r 0 t :=
      (radius_eq_outgoing_lam_integral_of_c1_domain H hp).symm
    _ = t / 2 := hGauge t ⟨ht.1, ht.2.trans hBtop⟩
    _ = ∫ _s in (0 : ℝ)..t, (1 / 2 : ℝ) := by
      simp only [intervalIntegral.integral_const]
      ring

private theorem strip_lam_antitone
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    {a c v : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc₁ : c < u₁)
    (hcv : c < v) (hvtop : v < top) :
    T.lam c v ≤ T.lam a v := by
  have hseg : ∀ s ∈ Icc a c, (s, v) ∈ extensionWorkingDomain u₁ top := by
    intro s hs
    exact ⟨ha.trans hs.1, hs.2.trans_lt hcv, hvtop, hs.2.trans_lt hc₁⟩
  have hprim := H.solution.lam_in v a c hac (by
    intro p hp
    rcases p with ⟨s, y⟩
    obtain ⟨hs, rfl⟩ : s ∈ Icc a c ∧ y = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
    exact hseg s hs)
  have hcoef : ∀ s ∈ Icc a c,
      (2 * T.m s v / T.r s v) * T.lam s v * T.nu s v /
        ((1 - 2 * T.m s v / T.r s v) * T.r s v) ≤ 0 := by
    intro s hs
    have hp := hseg s hs
    have hμ := mass_ratio_nonneg_of_c1_domain H hp
    have hgap := mass_ratio_lt_one_of_c1_domain H hp
    have hlam := H.solution.lam_pos (s, v) hp
    have hnu := nu_neg_of_c1_domain H hp
    have hr := H.solution.radius_pos (s, v) hp
    have hden : 0 ≤ (1 - 2 * T.m s v / T.r s v) * T.r s v :=
      (mul_pos (by linarith) hr).le
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hμ hlam.le) hnu.le) hden
  have hint : (∫ s in a..c,
      (2 * T.m s v / T.r s v) * T.lam s v * T.nu s v /
        ((1 - 2 * T.m s v / T.r s v) * T.r s v)) ≤ 0 := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo
      hac hprim.1 (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a c)
      (fun s hs => hcoef s ⟨hs.1.le, hs.2.le⟩)
    simpa only [intervalIntegral.integral_zero] using h
  linarith only [hprim.2, hint]

private theorem strip_lam_le_half
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    (hGauge : ∀ w ∈ Ioo (0 : ℝ) top, T.r 0 w = w / 2)
    {u v : ℝ} (hu : 0 ≤ u) (hu₁ : u < u₁)
    (huv : u < v) (hvtop : v < top) :
    T.lam u v ≤ 1 / 2 := by
  have h0₁ : 0 < u₁ := lt_of_le_of_lt hu hu₁
  calc
    T.lam u v ≤ T.lam 0 v :=
      strip_lam_antitone H (le_refl 0) hu hu₁ huv hvtop
    _ = 1 / 2 := strip_initial_lam_eq_half H hGauge
      ⟨lt_of_le_of_lt hu huv, hvtop⟩ h0₁

private theorem strip_radius_sq_integral
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    {u a v : ℝ} (hu : 0 < u) (hu₁ : u < u₁)
    (hua : u < a) (hav : a ≤ v) (hvtop : v < top) :
    (∫ s in a..v, T.r u s * T.lam u s) =
      ((T.r u v)^2 - (T.r u a)^2) / 2 := by
  have hseg : ∀ s ∈ Icc a v, (u, s) ∈ extensionWorkingDomain u₁ top := by
    intro s hs
    exact ⟨hu.le, hua.trans_le hs.1, hs.2.trans_lt hvtop, hu₁⟩
  have hR : ContinuousOn (T.r u) (Icc a v) := by
    refine intervalPrimitive_continuousOn_of_subintervals
      (g := T.lam u) hav ?_
    intro t ht
    apply H.solution.radius_out u a t ht.1
    intro p hp
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
    exact hseg y ⟨hy.1, hy.2.trans ht.2⟩
  have hL : ContinuousOn (T.lam u) (Icc a v) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => subset_closure (hseg s hs))
  let F : ℝ → ℝ := fun s => (T.r u s)^2 / 2
  let G : ℝ → ℝ := fun s => T.r u s * T.lam u s
  have hFC : ContinuousOn F (Icc a v) := (hR.pow 2).div_const _
  have hGI : IntervalIntegrable G volume a v :=
    (hR.mul hL).intervalIntegrable_of_Icc hav
  have hD : ∀ s ∈ Ioo a v, HasDerivAt F (G s) s := by
    intro s hs
    have hpi : (u, s) ∈ interior (extensionWorkingDomain u₁ top) :=
      extensionWorkingDomain_mem_interior hu (hua.trans hs.1)
        (hs.2.trans hvtop) hu₁
    have hd := ((radius_hasDerivAt_v_of_c1_interior H hpi).pow 2).div_const 2
    convert hd using 1; dsimp [F, G]; ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hav hFC hD hGI
  change (∫ s in a..v, G s) = F v - F a at hFTC
  simpa only [F, G] using (show
    (∫ s in a..v, G s) = ((T.r u v)^2 - (T.r u a)^2) / 2 by
      rw [hFTC]
      ring)

/-- The unprinted sharp mass increment behind (5.21): the source mass
primitive integrates `r * r_v` exactly. `M` is a fixed full-ray weighted
`α′` bound, supplied by the old estimate and (5.20). -/
theorem strip_mass_increment_sharp
    {u₀ u₁ vStar η M : ℝ} {T : Fields}
    (hu₀ : 0 < u₀) (hu₁Star : u₁ ≤ vStar) (hη : 0 < η)
    (H : IsC1Solution (extensionWorkingDomain u₁ (vStar + η)) T)
    (hM : 0 ≤ M)
    (hWeighted : ∀ p ∈ truncatedDevelopment u₀ u₁ (vStar + η),
      (T.r p.1 p.2) ^ ((1 : ℝ) / 2) *
        |deriv (fun t => T.alpha p.1 t / T.lam p.1 t) p.2 /
          T.lam p.1 p.2| ≤ M)
    {u v : ℝ} (hu : u ∈ Ioo u₀ u₁)
    (hv : v ∈ Ico vStar (vStar + η)) :
    T.m u v - T.m u vStar ≤
      (M^2 / 9) * ((T.r u v)^2 - (T.r u vStar)^2) := by
  have huPos : 0 < u := hu₀.trans hu.1
  have huStar : u < vStar := hu.2.trans_le hu₁Star
  have hp (s : ℝ) (hs : s ∈ Icc vStar v) :
      (u, s) ∈ extensionWorkingDomain u₁ (vStar + η) :=
    ⟨huPos.le, huStar.trans_le hs.1, hs.2.trans_lt hv.2, hu.2⟩
  have hprim := H.solution.mass_out u vStar v hv.1 (by
    intro p hpseg
    rcases p with ⟨x, s⟩
    obtain ⟨rfl, hs⟩ : x = u ∧ s ∈ Icc vStar v := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hp s hs)
  let C : ℝ := 2 * M^2 / 9
  let F : ℝ → ℝ := fun s =>
    (1 - 2 * T.m u s / T.r u s) * (T.theta u s)^2 /
      (2 * T.lam u s)
  let G : ℝ → ℝ := fun s => T.r u s * T.lam u s
  have hGint : IntervalIntegrable G volume vStar v := by
    have hseg : ∀ s ∈ Icc vStar v,
        (u, s) ∈ extensionWorkingDomain u₁ (vStar + η) := hp
    have hR : ContinuousOn (T.r u) (Icc vStar v) := by
      refine intervalPrimitive_continuousOn_of_subintervals
        (g := T.lam u) hv.1 ?_
      intro t ht
      apply H.solution.radius_out u vStar t ht.1
      intro p hpseg
      rcases p with ⟨x, y⟩
      obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc vStar t := by
        simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
      exact hseg y ⟨hy.1, hy.2.trans ht.2⟩
    have hL : ContinuousOn (T.lam u) (Icc vStar v) :=
      H.lam_c1.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => subset_closure (hp s hs))
    exact (hR.mul hL).intervalIntegrable_of_Icc hv.1
  have hpoint : ∀ s ∈ Ioo vStar v, F s ≤ C * G s := by
    intro s hs
    have hscc : s ∈ Icc vStar v := ⟨hs.1.le, hs.2.le⟩
    have hsp := hp s hscc
    have hr := H.solution.radius_pos (u, s) hsp
    have hlam := H.solution.lam_pos (u, s) hsp
    have hμ0 := mass_ratio_nonneg_of_c1_domain H hsp
    have hμ1 := mass_ratio_lt_one_of_c1_domain H hsp
    have hA : ∀ w ∈ Ioc u s,
        (T.r u w) ^ ((1 : ℝ) / 2) *
          |deriv (fun t => T.alpha u t / T.lam u t) w /
            T.lam u w| ≤ M := by
      intro w hw
      have hwtr : (u, w) ∈ truncatedDevelopment u₀ u₁ (vStar + η) := by
        rw [mem_truncatedDevelopment_iff_of_le
          (hu₁Star.trans (le_add_of_nonneg_right hη.le))]
        exact ⟨hu.1, hu.2, hw.1, hw.2.trans_lt (hs.2.trans_le hv.2.le)⟩
      exact hWeighted (u, w) hwtr
    have hθ := strip_theta_ratio_le H huPos hsp hA
    have hsq : (T.theta u s / T.lam u s)^2 ≤
        (4 / 9 : ℝ) * M^2 * T.r u s := by
      have hsqrt : (T.r u s) ^ ((1 : ℝ) / 2) = Real.sqrt (T.r u s) := by
        rw [Real.sqrt_eq_rpow]
      rw [hsqrt] at hθ
      have hB0 : 0 ≤ ((2 : ℝ) / 3) * M * Real.sqrt (T.r u s) := by positivity
      have hsq' := mul_le_mul
        (show |T.theta u s / T.lam u s| ≤
          ((2 : ℝ) / 3) * M * Real.sqrt (T.r u s) from hθ)
        hθ (abs_nonneg _) hB0
      nlinarith only [hsq', sq_abs (T.theta u s / T.lam u s),
        Real.sq_sqrt hr.le]
    have hcoef : 0 ≤ 1 - 2 * T.m u s / T.r u s ∧
        1 - 2 * T.m u s / T.r u s ≤ 1 := by
      constructor <;> linarith only [hμ0, hμ1]
    have hF : F s =
        (1 - 2 * T.m u s / T.r u s) *
          (T.theta u s / T.lam u s)^2 * (T.lam u s / 2) := by
      dsimp [F]
      field_simp [ne_of_gt hlam]
    rw [hF]
    have hmul₁ : (1 - 2 * T.m u s / T.r u s) *
        (T.theta u s / T.lam u s)^2 ≤
        (T.theta u s / T.lam u s)^2 :=
      mul_le_of_le_one_left (sq_nonneg _) hcoef.2
    have hmul₂ : (1 - 2 * T.m u s / T.r u s) *
        (T.theta u s / T.lam u s)^2 ≤
        (4 / 9 : ℝ) * M^2 * T.r u s := hmul₁.trans hsq
    have := mul_le_mul_of_nonneg_right hmul₂ (by positivity : 0 ≤ T.lam u s / 2)
    dsimp [C, G]
    nlinarith only [this]
  have hCint : IntervalIntegrable (fun s => C * G s) volume vStar v :=
    hGint.const_mul C
  have hmass : T.m u v - T.m u vStar = ∫ s in vStar..v, F s := hprim.2
  have hbound : (∫ s in vStar..v, F s) ≤
      ∫ s in vStar..v, C * G s :=
    intervalIntegral.integral_mono_on_of_le_Ioo hv.1 hprim.1 hCint hpoint
  have hrInt := strip_radius_sq_integral H huPos hu.2 huStar hv.1 hv.2
  rw [intervalIntegral.integral_const_mul, hrInt] at hbound
  rw [hmass]
  dsimp [C] at hbound
  nlinarith only [hbound]

private theorem strip_radius_mono_outgoing
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    {u a v : ℝ} (hu : 0 ≤ u) (hu₁ : u < u₁)
    (hua : u < a) (hav : a ≤ v) (hvtop : v < top) :
    T.r u a ≤ T.r u v := by
  have hseg : outSeg u a v ⊆ extensionWorkingDomain u₁ top := by
    intro p hp
    rcases p with ⟨x, s⟩
    obtain ⟨rfl, hs⟩ : x = u ∧ s ∈ Icc a v := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
    exact ⟨hu, hua.trans_le hs.1, hs.2.trans_lt hvtop, hu₁⟩
  have hprim := H.solution.radius_out u a v hav hseg
  have hint : 0 ≤ ∫ s in a..v, T.lam u s := by
    apply intervalIntegral.integral_nonneg hav
    intro s hs
    exact (H.solution.lam_pos (u, s)
      (hseg (by simpa [outSeg] using hs))).le
  linarith only [hprim.2, hint]

/-- The mass increment as printed on p. 1179. The exact squared-radius
estimate proves this weaker display with the same `M`. -/
theorem strip_mass_increment_coarse
    {u₀ u₁ vStar η M : ℝ} {T : Fields}
    (hu₀ : 0 < u₀) (hu₁Star : u₁ ≤ vStar) (hη : 0 < η)
    (H : IsC1Solution (extensionWorkingDomain u₁ (vStar + η)) T)
    (hM : 0 ≤ M)
    (hWeighted : ∀ p ∈ truncatedDevelopment u₀ u₁ (vStar + η),
      (T.r p.1 p.2) ^ ((1 : ℝ) / 2) *
        |deriv (fun t => T.alpha p.1 t / T.lam p.1 t) p.2 /
          T.lam p.1 p.2| ≤ M)
    {u v : ℝ} (hu : u ∈ Ioo u₀ u₁)
    (hv : v ∈ Ico vStar (vStar + η)) :
    T.m u v - T.m u vStar ≤
      (4 / 9 : ℝ) * M^2 * T.r u v * (T.r u v - T.r u vStar) := by
  have hsharp := strip_mass_increment_sharp hu₀ hu₁Star hη H hM
    hWeighted hu hv
  have huStar : u < vStar := hu.2.trans_le hu₁Star
  have hmono : T.r u vStar ≤ T.r u v :=
    strip_radius_mono_outgoing H (hu₀.trans hu.1).le hu.2
      huStar hv.1 hv.2
  have hr : 0 ≤ T.r u v :=
    (H.solution.radius_pos (u, v)
      ⟨(hu₀.trans hu.1).le, huStar.trans_le hv.1, hv.2, hu.2⟩).le
  have hdiff : 0 ≤ T.r u v - T.r u vStar := sub_nonneg.mpr hmono
  have hsq : (T.r u v)^2 - (T.r u vStar)^2 ≤
      2 * T.r u v * (T.r u v - T.r u vStar) := by
    nlinarith only [sq_nonneg (T.r u v - T.r u vStar)]
  have hM2 : 0 ≤ M^2 / 9 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hM2
  have hnonneg : 0 ≤ M^2 * T.r u v * (T.r u v - T.r u vStar) := by
    positivity
  nlinarith only [hsharp, hmul, hnonneg]

/-- The radius increment decreases along the incoming direction and is at
most the strip height. The first comparison uses `λ_u ≤ 0`; the last uses
the initial gauge `r(0,v)=v/2`. -/
theorem strip_radius_increment_le_height
    {u₀ u₁ vStar η : ℝ} {T : Fields}
    (hu₀ : 0 < u₀) (hu₁Star : u₁ ≤ vStar) (hη : 0 < η)
    (H : IsC1Solution (extensionWorkingDomain u₁ (vStar + η)) T)
    (hGauge : ∀ w ∈ Ioo (0 : ℝ) (vStar + η), T.r 0 w = w / 2)
    {u v : ℝ} (hu : u ∈ Ioo u₀ u₁)
    (hv : v ∈ Ico vStar (vStar + η)) :
    T.r u v - T.r u vStar ≤ T.r u₀ v - T.r u₀ vStar ∧
      T.r u₀ v - T.r u₀ vStar ≤ η := by
  have huStar : u < vStar := hu.2.trans_le hu₁Star
  have hu₀Star : u₀ < vStar := hu.1.trans huStar
  have hseg (a : ℝ) (ha : 0 ≤ a) (ha₁ : a < u₁) (haStar : a < vStar) :
      outSeg a vStar v ⊆ extensionWorkingDomain u₁ (vStar + η) := by
    intro p hp
    rcases p with ⟨x, s⟩
    obtain ⟨rfl, hs⟩ : x = a ∧ s ∈ Icc vStar v := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
    exact ⟨ha, haStar.trans_le hs.1, hs.2.trans_lt hv.2, ha₁⟩
  have hprimU := H.solution.radius_out u vStar v hv.1
    (hseg u (hu₀.trans hu.1).le hu.2 huStar)
  have hprim₀ := H.solution.radius_out u₀ vStar v hv.1
    (hseg u₀ hu₀.le (hu.1.trans hu.2) hu₀Star)
  have hcomp : (∫ s in vStar..v, T.lam u s) ≤
      ∫ s in vStar..v, T.lam u₀ s := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hv.1 hprimU.1 hprim₀.1
    intro s hs
    exact strip_lam_antitone H hu₀.le hu.1.le hu.2
      (huStar.trans hs.1) (hs.2.trans_le hv.2.le)
  have hhalf : (∫ s in vStar..v, T.lam u₀ s) ≤
      ∫ _s in vStar..v, (1 / 2 : ℝ) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hv.1 hprim₀.1
      (intervalIntegrable_const)
    intro s hs
    exact strip_lam_le_half H hGauge hu₀.le (hu.1.trans hu.2)
      (hu₀Star.trans hs.1) (hs.2.trans_le hv.2.le)
  constructor
  · linarith only [hprimU.2, hprim₀.2, hcomp]
  · have hwidth : v - vStar ≤ η := by linarith only [hv.2]
    rw [intervalIntegral.integral_const] at hhalf
    simp only [smul_eq_mul] at hhalf
    linarith only [hprim₀.2, hhalf, hwidth, hη]

/-- Equation (5.21). The coefficient `4/9` follows from the sharp `1/9`
squared-radius mass estimate, positivity of the seam mass, and the radius
increment bound. -/
theorem strip_mass_ratio_increment_le
    {u₀ u₁ vStar η M : ℝ} {T : Fields}
    (hu₀ : 0 < u₀) (hu₁Star : u₁ ≤ vStar) (hη : 0 < η)
    (H : IsC1Solution (extensionWorkingDomain u₁ (vStar + η)) T)
    (hGauge : ∀ w ∈ Ioo (0 : ℝ) (vStar + η), T.r 0 w = w / 2)
    (hM : 0 ≤ M)
    (hWeighted : ∀ p ∈ truncatedDevelopment u₀ u₁ (vStar + η),
      (T.r p.1 p.2) ^ ((1 : ℝ) / 2) *
        |deriv (fun t => T.alpha p.1 t / T.lam p.1 t) p.2 /
          T.lam p.1 p.2| ≤ M)
    {u v : ℝ} (hu : u ∈ Ioo u₀ u₁)
    (hv : v ∈ Ico vStar (vStar + η)) :
    2 * T.m u v / T.r u v ≤
      2 * T.m u vStar / T.r u vStar +
        (4 / 9 : ℝ) * M^2 * η := by
  let r := T.r u v
  let rStar := T.r u vStar
  let m := T.m u v
  let mStar := T.m u vStar
  let c := M^2 / 9
  have hp : (u, v) ∈ extensionWorkingDomain u₁ (vStar + η) :=
    ⟨(hu₀.trans hu.1).le, (hu.2.trans_le hu₁Star).trans_le hv.1,
      hv.2, hu.2⟩
  have hpStar : (u, vStar) ∈ extensionWorkingDomain u₁ (vStar + η) :=
    ⟨(hu₀.trans hu.1).le, hu.2.trans_le hu₁Star,
      lt_add_of_pos_right _ hη, hu.2⟩
  have hr : 0 < r := H.solution.radius_pos _ hp
  have hrStar : 0 < rStar := H.solution.radius_pos _ hpStar
  have hmStar : 0 ≤ mStar := mass_nonneg_of_c1_domain H hpStar
  have hrMono : rStar ≤ r :=
    strip_radius_mono_outgoing H (hu₀.trans hu.1).le hu.2
      (hu.2.trans_le hu₁Star) hv.1 hv.2
  have hRad := strip_radius_increment_le_height hu₀ hu₁Star hη
    H hGauge hu hv
  have hWidth : r - rStar ≤ η := by
    dsimp [r, rStar]
    linarith only [hRad.1, hRad.2]
  have hMass := strip_mass_increment_sharp hu₀ hu₁Star hη H hM
    hWeighted hu hv
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hdiff : 0 ≤ r - rStar := sub_nonneg.mpr hrMono
  have hSq : r^2 - rStar^2 ≤ 2 * r * (r - rStar) := by
    nlinarith only [sq_nonneg (r - rStar)]
  have hMassLe : m - mStar ≤ 2 * c * r * (r - rStar) := by
    have h := mul_le_mul_of_nonneg_left hSq hc
    dsimp [c, m, mStar, r, rStar] at *
    nlinarith only [hMass, h]
  have hInc : 2 * (m - mStar) / r ≤ 4 * c * (r - rStar) := by
    apply (div_le_iff₀ hr).2
    nlinarith only [hMassLe]
  have hBase : 2 * mStar / r ≤ 2 * mStar / rStar :=
    div_le_div_of_nonneg_left (by positivity) hrStar hrMono
  have hWidthBound : 4 * c * (r - rStar) ≤ 4 * c * η := by
    exact mul_le_mul_of_nonneg_left hWidth (by positivity)
  have hAdd : 2 * m / r = 2 * (m - mStar) / r + 2 * mStar / r := by
    ring
  rw [hAdd]
  dsimp [r, rStar, m, mStar, c] at *
  nlinarith only [hInc, hBase, hWidthBound]

/-- A compact incoming trace on one fixed initial strip controls every
smaller-height incoming supremum. This prevents the bound in the height
choice from growing as the strip shrinks. -/
private theorem incoming_strip_weighted_sup_le_fixed
    {u₀ u₁ vStar η₀ D : ℝ} {T : Fields}
    (hu₀ : 0 < u₀) (hu₀Star : u₀ < vStar)
    (hu₀₁ : u₀ < u₁) (hη₀ : 0 < η₀)
    (H : IsC1Solution (extensionWorkingDomain u₁ (vStar + η₀)) T)
    (hD : ∀ v ∈ Ico vStar (vStar + η₀),
      (T.r u₀ v) ^ ((1 : ℝ) / 2) *
        |deriv (fun t => T.alpha u₀ t / T.lam u₀ t) v /
          T.lam u₀ v| ≤ D)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ η₀) :
    incomingStripWeightedSup u₀ vStar η T ≤ D := by
  let p : AlphaPrimeDomain T :=
    ⟨(u₀, vStar), ⟨hu₀, hu₀Star,
      H.solution.lam_pos (u₀, vStar)
        ⟨hu₀.le, hu₀Star, lt_add_of_pos_right _ hη₀, hu₀₁⟩⟩⟩
  have hNonempty : (incomingStripWeightedValues u₀ vStar η T).Nonempty := by
    refine ⟨(T.r u₀ vStar) ^ ((1 : ℝ) / 2) * |alphaPrime T p|, p, rfl,
      ⟨le_refl _, lt_add_of_pos_right _ hη⟩, rfl⟩
  unfold incomingStripWeightedSup
  apply csSup_le hNonempty
  intro x hx
  obtain ⟨q, hqU, hqV, rfl⟩ := hx
  have hqV₀ : q.1.2 ∈ Ico vStar (vStar + η₀) :=
    ⟨hqV.1, lt_of_lt_of_le hqV.2 (by
      simpa only [add_comm] using add_le_add_left hηle vStar)⟩
  subst hqU
  simpa only [alphaPrime_eq_deriv] using hD q.1.2 hqV₀

/-- Choose a common positive strip height after fixing the incoming C¹
trace on `η₀`. The constant in the strict bootstrap margin uses the actual
smaller-strip incoming supremum, as on p. 1179. -/
theorem exists_fixed_strip_height
    {η₀ ε ε₁ Aold D : ℝ}
    (hη₀ : 0 < η₀) (hε₁ : 0 < ε₁) (hε : ε < ε₁)
    (hAold : 0 ≤ Aold) :
    ∃ η : ℝ, 0 < η ∧ η ≤ η₀ ∧
      ∀ {u₀ u₁ vStar : ℝ} {T : Fields},
        0 < u₀ → u₀ < u₁ → u₁ ≤ vStar →
        IsC1Solution (extensionWorkingDomain u₁ (vStar + η₀)) T →
        (∀ v ∈ Ico vStar (vStar + η₀),
          (T.r u₀ v) ^ ((1 : ℝ) / 2) *
            |deriv (fun t => T.alpha u₀ t / T.lam u₀ t) v /
              T.lam u₀ v| ≤ D) →
        (4 / 9 : ℝ) *
          (max Aold
            (2 * incomingStripWeightedSup u₀ vStar η T /
              (1 - ε / ε₁)))^2 * η < (ε₁ - ε) / 2 := by
  let den : ℝ := 1 - ε / ε₁
  let M : ℝ := max Aold (2 * D / den)
  let K : ℝ := (4 / 9 : ℝ) * M^2
  let δ : ℝ := (ε₁ - ε) / 2
  have hden : 0 < den := by
    dsimp [den]
    have := (div_lt_one hε₁).2 hε
    linarith only [this]
  have hM0 : 0 ≤ M := hAold.trans (le_max_left _ _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hε]
  have hUpper : 0 < min η₀ (δ / (K + 1)) := by
    apply lt_min hη₀
    exact div_pos hδ (by linarith only [hK])
  obtain ⟨η, hη, hηUpper⟩ := exists_between hUpper
  have hη₀le : η ≤ η₀ := (lt_min_iff.mp hηUpper).1.le
  have hηK : η < δ / (K + 1) := (lt_min_iff.mp hηUpper).2
  have hKη : K * η < δ := by
    have hfrac : (K + 1) * η < δ := by
      simpa only [mul_comm] using
        ((lt_div_iff₀ (by linarith only [hK] : 0 < K + 1)).mp hηK)
    nlinarith only [hfrac, hK, hη]
  refine ⟨η, hη, hη₀le, ?_⟩
  intro u₀ u₁ vStar T hu₀ hu₀₁ hu₁Star H hD
  have hSup : incomingStripWeightedSup u₀ vStar η T ≤ D :=
    incoming_strip_weighted_sup_le_fixed hu₀
      (hu₀₁.trans_le hu₁Star) hu₀₁ hη₀ H hD hη hη₀le
  have hMax : max Aold
      (2 * incomingStripWeightedSup u₀ vStar η T / den) ≤ M := by
    dsimp [M]
    apply max_le_max le_rfl
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSup (by norm_num)) hden.le
  have hMax0 : 0 ≤ max Aold
      (2 * incomingStripWeightedSup u₀ vStar η T / den) :=
    hAold.trans (le_max_left _ _)
  have hSq : (max Aold
      (2 * incomingStripWeightedSup u₀ vStar η T / den))^2 ≤ M^2 :=
    (sq_le_sq₀ hMax0 hM0).2 hMax
  have hCoef : (4 / 9 : ℝ) *
      (max Aold
        (2 * incomingStripWeightedSup u₀ vStar η T / den))^2 ≤ K := by
    dsimp [K]
    exact mul_le_mul_of_nonneg_left hSq (by norm_num)
  have hsmall := mul_le_mul_of_nonneg_right hCoef hη.le
  dsimp [den, δ] at *
  exact lt_of_le_of_lt hsmall hKη

end ChristodoulouBV.Uniqueness

end
