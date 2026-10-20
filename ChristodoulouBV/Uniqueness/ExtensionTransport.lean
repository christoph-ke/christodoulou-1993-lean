module

public import ChristodoulouBV.Uniqueness.ExtensionTransportEquation
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Incoming integration of the extension transport equation

The three signed integrals are defined only for a closed incoming segment
inside one C¹ family member. The pointwise equation is integrated on exactly
that segment.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The signed integral `I₁` in Christodoulou (1993), p. 1173. The domain
argument records that the entire incoming closed segment belongs to one
member, where the `α′` integrand is defined. -/
noncomputable def integralI₁ (b : ℝ) (S : Fields) (u₀ u v : ℝ)
    (_hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) : ℝ :=
  -∫ s in u₀..u, (S.nu s v / S.r s v) *
    ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
    (deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v)

/-- The signed integral `I₂` in Christodoulou (1993), p. 1173. -/
noncomputable def integralI₂ (b : ℝ) (S : Fields) (u₀ u v : ℝ)
    (_hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) : ℝ :=
  -∫ s in u₀..u, (S.nu s v / (S.r s v)^2) *
    ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
    (S.theta s v / S.lam s v)

/-- The signed integral `I₃` in Christodoulou (1993), p. 1173. -/
noncomputable def integralI₃ (b : ℝ) (S : Fields) (u₀ u v : ℝ)
    (_hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) : ℝ :=
  -∫ s in u₀..u, (S.nu s v / (S.r s v)^2) *
    (1 / (1 - 2 * S.m s v / S.r s v)) *
    (S.theta s v / S.lam s v)^3

private theorem transport_rhs_continuousOn_segment {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v : ℝ} (hu₀u : u₀ ≤ u)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) :
    ContinuousOn (fun s =>
      -2 * (S.nu s v / S.r s v) *
        ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
        (deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v) +
      3 * (S.nu s v / (S.r s v)^2) *
        ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
        (S.theta s v / S.lam s v) -
      (S.nu s v / (S.r s v)^2) *
        (1 / (1 - 2 * S.m s v / S.r s v)) *
        (S.theta s v / S.lam s v)^3) (Icc u₀ u) := by
  have hp := hseg u ⟨hu₀u, le_rfl⟩
  obtain ⟨⟨_, _⟩, ⟨huv, hvb⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  let K := closedCoordTriangle 0 B
  let J := Icc u₀ u
  have hmap (s : ℝ) (hs : s ∈ J) : (s, v) ∈ K := by
    have hsp := hseg s hs
    exact ⟨hsp.1.1.le, hsp.2.1.le, hvB.le⟩
  have hmap' : MapsTo (fun s : ℝ => (s, v)) J K := fun s hs => hmap s hs
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hSourceJet : ContinuousOn
      (fun s => (fderivWithin ℝ (C1Solution.canonicalQuotientSource b S)
        K (s, v)) (0, 1)) J := by
    have h := (C1Solution.canonicalQuotientSource_contDiffOn hB hBb H).continuousOn_fderivWithin
      hunique (by norm_num)
    exact (h.clm_apply continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap'
  have hQuotientJet : ContinuousOn
      (fun s => (fderivWithin ℝ (C1Solution.outgoingQuotient S)
        K (s, v)) (0, 1)) J := by
    have h := (C1Solution.alpha_div_lam_contDiffOn hB hBb H).continuousOn_fderivWithin
      hunique (by norm_num)
    exact (h.clm_apply continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap'
  have hlam : ContinuousOn (fun s => S.lam s v) J :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap'
  have hcoeff : ContinuousOn
      (fun s => C1Solution.canonicalMixedCoefficient b S (s, v)) J :=
    (C1Solution.canonicalMixedCoefficient_contDiffOn hB hBb H).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap'
  have hlamNe : ∀ s ∈ J, S.lam s v ≠ 0 := by
    intro s hs
    have hsp := hseg s hs
    exact ne_of_gt (H.solution.lam_pos (s, v)
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩)
  have hJetC : ContinuousOn (fun s =>
      (((fderivWithin ℝ (C1Solution.canonicalQuotientSource b S)
          K (s, v)) (0, 1)) * S.lam s v -
        ((fderivWithin ℝ (C1Solution.outgoingQuotient S)
          K (s, v)) (0, 1)) *
          C1Solution.canonicalMixedCoefficient b S (s, v)) /
        (S.lam s v)^2) J :=
    ((hSourceJet.mul hlam).sub (hQuotientJet.mul hcoeff)).div
      (hlam.pow 2) (fun s hs => pow_ne_zero 2 (hlamNe s hs))
  apply hJetC.congr
  intro s hs
  have hsp := hseg s hs
  have hpOpen : (s, v) ∈ openCoordTriangle 0 B :=
    ⟨hsp.1.1, hsp.2.1, hvB⟩
  have hjet := alphaPrime_deriv_u_eq_closed_jet hB hBb H hpOpen
  have heq := alphaPrime_deriv_u H hsp
  exact (hjet.symm.trans heq).symm

private theorem transport_terms_integrable_segment {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v : ℝ} (hu₀u : u₀ ≤ u)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) :
    IntervalIntegrable (fun s => (S.nu s v / S.r s v) *
      ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
      (deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v)) volume u₀ u ∧
    IntervalIntegrable (fun s => (S.nu s v / (S.r s v)^2) *
      ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
      (S.theta s v / S.lam s v)) volume u₀ u ∧
    IntervalIntegrable (fun s => (S.nu s v / (S.r s v)^2) *
      (1 / (1 - 2 * S.m s v / S.r s v)) *
      (S.theta s v / S.lam s v)^3) volume u₀ u := by
  have hp := hseg u ⟨hu₀u, le_rfl⟩
  obtain ⟨⟨_, _⟩, ⟨huv, hvb⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  let J := Icc u₀ u
  let K := closedCoordTriangle 0 B
  have hmap : MapsTo (fun s : ℝ => (s, v)) J K := by
    intro s hs
    have hsp := hseg s hs
    exact ⟨hsp.1.1.le, hsp.2.1.le, hvB.le⟩
  have hRcanon : ContinuousOn (fun s => C1Solution.canonicalRadius S (s, v)) J :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hR : ContinuousOn (fun s => S.r s v) J := by
    apply hRcanon.congr
    intro s hs
    have hsp := hseg s hs
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H
      hsp.1.1.le hsp.2.1 hvB.le).symm
  have hMuCanon : ContinuousOn
      (fun s => C1Solution.canonicalMassRatio b S (s, v)) J :=
    (C1Solution.canonicalMassRatio_contDiffOn hB hBb H).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hMu : ContinuousOn (fun s => 2 * S.m s v / S.r s v) J := by
    apply hMuCanon.congr
    intro s hs
    have hsp := hseg s hs
    exact (C1Solution.canonicalMassRatio_eq_mass_ratio H
      (show (s, v) ∈ developmentWithInitialEdge b from
        ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩)).symm
  obtain ⟨hlamC1, hnuC1, _, hthetaC1, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  have hLam : ContinuousOn (fun s => S.lam s v) J :=
    hlamC1.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hNu : ContinuousOn (fun s => S.nu s v) J :=
    hnuC1.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hTheta : ContinuousOn (fun s => S.theta s v) J :=
    hthetaC1.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hAlphaDer : ContinuousOn
      (fun s => deriv (fun t => S.alpha s t / S.lam s t) v) J := by
    intro s hs
    exact (alpha_ratio_mixed_partial_bridge H (hseg s hs)).continuousAt.continuousWithinAt
  have hRne : ∀ s ∈ J, S.r s v ≠ 0 := by
    intro s hs
    have hsp := hseg s hs
    exact ne_of_gt (H.solution.radius_pos (s, v)
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩)
  have hLamNe : ∀ s ∈ J, S.lam s v ≠ 0 := by
    intro s hs
    have hsp := hseg s hs
    exact ne_of_gt (H.solution.lam_pos (s, v)
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩)
  have hGapNe : ∀ s ∈ J, 1 - 2 * S.m s v / S.r s v ≠ 0 := by
    intro s hs
    have hsp := hseg s hs
    have hgap := C1Solution.mass_gap_pos hB hBb H
      hsp.1.1.le hsp.2.1 hvB.le
    have hr := H.solution.radius_pos (s, v)
      ⟨hsp.1.1.le, hsp.2.1, hsp.2.2⟩
    have heq : 1 - 2 * S.m s v / S.r s v =
        (S.r s v - 2 * S.m s v) / S.r s v := by field_simp
    rw [heq]
    exact ne_of_gt (div_pos hgap hr)
  have hMuFrac : ContinuousOn
      (fun s => (2 * S.m s v / S.r s v) /
        (1 - 2 * S.m s v / S.r s v)) J :=
    hMu.div (continuousOn_const.sub hMu) hGapNe
  have hNuFrac : ContinuousOn (fun s => S.nu s v / S.r s v) J :=
    hNu.div hR hRne
  have hNuR2 : ContinuousOn (fun s => S.nu s v / (S.r s v)^2) J :=
    hNu.div (hR.pow 2) (fun s hs => pow_ne_zero 2 (hRne s hs))
  have hThetaFrac : ContinuousOn
      (fun s => S.theta s v / S.lam s v) J :=
    hTheta.div hLam hLamNe
  have hAlphaPrime : ContinuousOn
      (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v) J :=
    hAlphaDer.div hLam hLamNe
  have hGapInv : ContinuousOn
      (fun s => (1 : ℝ) / (1 - 2 * S.m s v / S.r s v)) J :=
    continuousOn_const.div (continuousOn_const.sub hMu) hGapNe
  exact ⟨((hNuFrac.mul hMuFrac).mul hAlphaPrime).intervalIntegrable_of_Icc hu₀u,
    ((hNuR2.mul hMuFrac).mul hThetaFrac).intervalIntegrable_of_Icc hu₀u,
    ((hNuR2.mul hGapInv).mul (hThetaFrac.pow 3)).intervalIntegrable_of_Icc hu₀u⟩

/-- Integrate (5.2) along a complete incoming closed segment contained in a
single family member. This is the signed identity before (5.3). -/
theorem alphaPrime_transport_integral {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v : ℝ} (hu₀u : u₀ < u)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) :
    deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v =
      deriv (fun t => S.alpha u₀ t / S.lam u₀ t) v / S.lam u₀ v +
        2 * integralI₁ b S u₀ u v hseg -
        3 * integralI₂ b S u₀ u v hseg +
        integralI₃ b S u₀ u v hseg := by
  let f : ℝ → ℝ := fun s =>
    deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v
  let g : ℝ → ℝ := fun s =>
    -2 * (S.nu s v / S.r s v) *
      ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) * f s +
    3 * (S.nu s v / (S.r s v)^2) *
      ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
      (S.theta s v / S.lam s v) -
    (S.nu s v / (S.r s v)^2) *
      (1 / (1 - 2 * S.m s v / S.r s v)) *
      (S.theta s v / S.lam s v)^3
  have hgC : ContinuousOn g (Icc u₀ u) :=
    transport_rhs_continuousOn_segment H hu₀u.le hseg
  have hgInt : IntervalIntegrable g volume u₀ u :=
    hgC.intervalIntegrable_of_Icc hu₀u.le
  have hderiv : ∀ s ∈ Icc u₀ u, HasDerivAt f (g s) s := by
    intro s hs
    exact alphaPrime_hasDerivAt_u H (hseg s hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le hu₀u.le] using hderiv) hgInt
  let t₁ : ℝ → ℝ := fun s => (S.nu s v / S.r s v) *
    ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) * f s
  let t₂ : ℝ → ℝ := fun s => (S.nu s v / (S.r s v)^2) *
    ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
    (S.theta s v / S.lam s v)
  let t₃ : ℝ → ℝ := fun s => (S.nu s v / (S.r s v)^2) *
    (1 / (1 - 2 * S.m s v / S.r s v)) *
    (S.theta s v / S.lam s v)^3
  obtain ⟨hi₁, hi₂, hi₃⟩ :=
    transport_terms_integrable_segment H hu₀u.le hseg
  have hgEq : g = fun s => -2 * t₁ s + 3 * t₂ s - t₃ s := by
    funext s
    dsimp [g, t₁, t₂, t₃]
    ring
  have hI : (∫ s in u₀..u, g s) =
      2 * integralI₁ b S u₀ u v hseg -
        3 * integralI₂ b S u₀ u v hseg +
        integralI₃ b S u₀ u v hseg := by
    rw [hgEq]
    have hsum := intervalIntegral.integral_sub
      ((hi₁.const_mul (-2)).add (hi₂.const_mul 3)) hi₃
    have hadd := intervalIntegral.integral_add
      (hi₁.const_mul (-2)) (hi₂.const_mul 3)
    rw [hsum, hadd]
    simp only [intervalIntegral.integral_const_mul, integralI₁, integralI₂, integralI₃]
    ring
  dsimp [f] at hFTC
  linarith only [hFTC, hI]

/-- The pointwise form of the (5.3) triangle inequality. The source's
global `D′` bound requires the separate incoming-trace finiteness result. -/
theorem alphaPrime_le_initial_add_integrals_pointwise
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ u v : ℝ} (hu₀u : u₀ < u)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b) :
    |deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v| ≤
      |deriv (fun t => S.alpha u₀ t / S.lam u₀ t) v / S.lam u₀ v| +
        2 * |integralI₁ b S u₀ u v hseg| +
        3 * |integralI₂ b S u₀ u v hseg| +
        |integralI₃ b S u₀ u v hseg| := by
  rw [alphaPrime_transport_integral H hu₀u hseg]
  set a := deriv (fun t => S.alpha u₀ t / S.lam u₀ t) v / S.lam u₀ v
  set x := integralI₁ b S u₀ u v hseg
  set y := integralI₂ b S u₀ u v hseg
  set z := integralI₃ b S u₀ u v hseg
  have h₁ := abs_add_le (a + 2 * x - 3 * y) z
  have h₂ := abs_sub_le (a + 2 * x) 0 (3 * y)
  have h₃ := abs_add_le a (2 * x)
  simp only [sub_zero, zero_sub, abs_neg, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h₂ h₃
  linarith only [h₁, h₂, h₃]

end ChristodoulouBV.Uniqueness

end
