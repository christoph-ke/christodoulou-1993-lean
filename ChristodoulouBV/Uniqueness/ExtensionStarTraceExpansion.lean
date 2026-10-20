module

public import ChristodoulouBV.ForMathlib.ODE.RadiusAttenuation
public import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import ChristodoulouBV.Uniqueness.ExtensionStarTraceBootstrap
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Expansion comparison from the cubic mass estimate

The mass ratio is quadratic in radius, so the mixed coefficient is linear in
radius. Incoming attenuation of the expansion is consequently controlled by
the change of radius squared.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The improved mass estimate bounds the mixed coefficient by a multiple of
radius. The positive mass gap supplies the denominator. -/
theorem mass_ratio_coefficient_le_linear_radius
    {r μ q q₀ B : ℝ}
    (hr : 0 < r) (hq₀ : 0 < q₀) (hq : q₀ ≤ q)
    (hμ : μ ≤ B ^ 2 * r ^ 2 / 12) :
    μ / (q * r) ≤ (B ^ 2 / (12 * q₀)) * r := by
  have hqr : 0 < q * r := mul_pos (hq₀.trans_le hq) hr
  apply (div_le_iff₀ hqr).2
  calc
    μ ≤ B ^ 2 * r ^ 2 / 12 := hμ
    _ ≤ (B ^ 2 / (12 * q₀) * r) * (q * r) := by
      have heq : (B ^ 2 / (12 * q₀) * r) * (q * r) =
          B ^ 2 * r ^ 2 * q / (12 * q₀) := by ring
      rw [heq]
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12) hq₀)).2
      have hp : 0 ≤ B ^ 2 * r ^ 2 * (q - q₀) :=
        mul_nonneg (mul_nonneg (sq_nonneg B) (sq_nonneg r))
          (sub_nonneg.mpr hq)
      nlinarith only [hp]

/-- Equation (5): an incoming expansion lower bound from the cubic mass
estimate and a fixed positive mass gap. The incoming derivative of radius
does not appear in the constant. -/
theorem lam_lower_of_cubic_mass_on_incoming
    {b u₀ u v B q₀ : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hu₀ : 0 < u₀) (hu₀u : u₀ < u) (huv : u < v) (hvb : v < b)
    (hq₀ : 0 < q₀)
    (hmass : ∀ s ∈ Ioo u₀ u,
      2 * S.m s v / S.r s v ≤ B ^ 2 / 12 * (S.r s v) ^ 2)
    (hgap : ∀ s ∈ Ioo u₀ u,
      q₀ ≤ 1 - 2 * S.m s v / S.r s v) :
    S.lam u₀ v * Real.exp
      (-(B ^ 2 / (24 * q₀)) * (S.r u₀ v) ^ 2) ≤ S.lam u v := by
  let K : Set (ℝ × ℝ) := closedCoordTriangle 0 ((v + b) / 2)
  have hvB : v < (v + b) / 2 := by linarith only [hvb]
  have hBpos : 0 < (v + b) / 2 := by linarith only [hu₀, hu₀u, huv, hvb]
  have hBb : (v + b) / 2 < b := by linarith only [hvb]
  have hseg (s : ℝ) (hs : s ∈ Icc u₀ u) : (s, v) ∈ K :=
    ⟨hu₀.le.trans hs.1, hs.2.trans huv.le, hvB.le⟩
  have hsegU (s : ℝ) (hs : s ∈ Icc u₀ u) :
      (s, v) ∈ developmentWithInitialEdge b :=
    ⟨hu₀.le.trans hs.1, hs.2.trans_lt huv, hvb⟩
  have hlamcont : ContinuousOn (fun s => S.lam s v) (Icc u₀ u) :=
    H.lam_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => subset_closure (hsegU s hs))
  have hradcont : ContinuousOn (fun s => S.r s v) (Icc u₀ u) := by
    have hcanon : ContinuousOn
        (fun s => C1Solution.canonicalRadius S (s, v)) (Icc u₀ u) :=
      (C1Solution.canonicalRadius_contDiffOn hBpos hBb H).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hseg
    apply hcanon.congr
    intro s hs
    exact (C1Solution.canonicalRadius_eq_radius hBpos hBb H
      (hu₀.le.trans hs.1) (hs.2.trans_lt huv) hvB.le).symm
  have hlampos : ∀ s ∈ Icc u₀ u, 0 < S.lam s v := by
    intro s hs
    exact H.solution.lam_pos (s, v) (hsegU s hs)
  have hcoeff : ∀ s ∈ Ioo u₀ u,
      (2 * S.m s v / S.r s v) /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v) ≤
        (B ^ 2 / (12 * q₀)) * S.r s v := by
    intro s hs
    have hr : 0 < S.r s v := H.solution.radius_pos (s, v)
      (hsegU s ⟨hs.1.le, hs.2.le⟩)
    apply mass_ratio_coefficient_le_linear_radius hr hq₀ (hgap s hs)
    convert hmass s hs using 1
    ring
  have hnu : ∀ s ∈ Ioo u₀ u, S.nu s v ≤ 0 := by
    intro s hs
    exact (H.reduced_signs_of_c1 (hsegU s ⟨hs.1.le, hs.2.le⟩)).1.le
  have hlamderiv : ∀ s ∈ Ioo u₀ u,
      HasDerivAt (fun t => S.lam t v)
        (S.lam s v * S.nu s v *
          ((2 * S.m s v / S.r s v) /
            ((1 - 2 * S.m s v / S.r s v) * S.r s v))) s := by
    intro s hs
    have hsi : (s, v) ∈ interior K := by
      rw [show K = closedCoordTriangle 0 ((v + b) / 2) from rfl,
        interior_closedCoordTriangle]
      exact ⟨hu₀.trans hs.1, hs.2.trans huv, hvB⟩
    have hdiff : DifferentiableAt ℝ
        (fun p : ℝ × ℝ => S.lam p.1 p.2) (s, v) :=
      (((C1Solution.five_fields_contDiffOn hBpos hBb H).1.differentiableOn
        (by norm_num)).mono interior_subset (s, v) hsi).differentiableAt
        (isOpen_interior.mem_nhds hsi)
    have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s v)
    have hd : HasDerivAt (fun t => S.lam t v)
        (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (s, v) (1, 0)) s := by
      simpa only [Function.comp_def] using
        hdiff.hasFDerivAt.comp_hasDerivAt s hpair
    have hvalue := H.lam_deriv_u_of_c1 (hu₀.trans hs.1)
      (hs.2.trans huv) hvb
    convert hd using 1
    rw [← hd.deriv]
    rw [hvalue]
    ring
  have hradderiv : ∀ s ∈ Ioo u₀ u,
      HasDerivAt (fun t => S.r t v) (S.nu s v) s := by
    intro s hs
    exact radius_hasDerivAt_u_of_c1 H (hu₀.trans hs.1)
      (hs.2.trans huv) hvb
  have hmain := ChristodoulouBV.ForMathlib.expansion_lower_of_radius_coefficient
    hu₀u.le (div_nonneg (sq_nonneg B) (by positivity : 0 ≤ 12 * q₀))
    hlamcont hradcont hlampos hnu hcoeff hlamderiv hradderiv
    u ⟨hu₀u.le, le_rfl⟩
  convert hmain using 1
  ring_nf

end ChristodoulouBV.Uniqueness

end
