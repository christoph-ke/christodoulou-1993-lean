module

public import ChristodoulouBV.C1Solution.Extraction
public import ChristodoulouBV.C1Solution.UniquenessSlice
public import ChristodoulouBV.C1Solution.ExtractionRemovable
public import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Uniqueness of regular C¹ developments

This module begins the comparison of two frozen C¹ solutions by recovering
their outgoing initial densities from the prescribed radius and scalar data.
The comparison always uses canonical extensions at the excluded axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- Integrating the continuous outgoing relative jet of a C¹ field recovers
its difference between the axis and any point on the same outgoing ray. -/
theorem integral_vertical_jet_eq_sub {B : ℝ} (hB : 0 < B)
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    (∫ t in u..v,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, t)) (0, 1)) =
      F (u, v) - F (u, u) := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG : ContinuousOn (fun p : ℝ × ℝ =>
      (fderivWithin ℝ F K p) (0, 1)) K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hmap : Set.MapsTo (fun t : ℝ => (u, t)) (Icc u v) K := by
    intro t ht
    exact ⟨hu, ht.1, ht.2.trans hv⟩
  have hFslice : ContinuousOn (fun t : ℝ => F (u, t)) (Icc u v) :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hGslice : ContinuousOn (fun t : ℝ =>
      (fderivWithin ℝ F K (u, t)) (0, 1)) (Icc u v) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hint : IntervalIntegrable (fun t : ℝ =>
      (fderivWithin ℝ F K (u, t)) (0, 1)) volume u v :=
    hGslice.intervalIntegrable_of_Icc huv
  have hderiv (t : ℝ) (ht : t ∈ Ioo u v) :
      HasDerivAt (fun s : ℝ => F (u, s))
        ((fderivWithin ℝ F K (u, t)) (0, 1)) t := by
    have hp : (u, t) ∈ K := ⟨hu, ht.1.le, ht.2.le.trans hv⟩
    have hFd := (hF.differentiableOn (by norm_num) (u, t) hp).hasFDerivWithinAt
    have hpair : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) t :=
      (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
    have hlocal : ∀ᶠ s in 𝓝 t, (u, s) ∈ K := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact ⟨hu, hs.1.le, hs.2.le.trans hv⟩
    simpa only [Function.comp_def] using hFd.comp_hasDerivAt t hpair hlocal
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hFslice hderiv hint

/-- The regular outgoing linear mass coefficient. Its explicit coordinate-gap
factor removes the apparent singularity at the axis. -/
@[expose] noncomputable def canonicalMassLinearCoefficient (B : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  -(p.2 - p.1) * (normalizedTheta B S p)^2 /
    (S.lam p.1 p.2 * canonicalNormalizedRadius S p)

/-- The regular outgoing source in the mass equation. -/
@[expose] noncomputable def canonicalMassLinearSource (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  (S.theta p.1 p.2)^2 / (2 * S.lam p.1 p.2)

/-- The outgoing mass coefficient is continuous on a smaller closed triangle. -/
theorem canonicalMassLinearCoefficient_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMassLinearCoefficient B S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨hρ, c, hc, hρlower⟩ :=
    canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
  obtain ⟨d, hd, hdlam⟩ := exists_lam_lower_bound hB hBb H
  have hden : ∀ p ∈ K,
      S.lam p.1 p.2 * canonicalNormalizedRadius S p ≠ 0 := by
    intro p hp
    exact mul_ne_zero (ne_of_gt (hd.trans_le (hdlam p hp)))
      (ne_of_gt (hc.trans_le (hρlower p hp)))
  change ContinuousOn (fun p : ℝ × ℝ =>
    -(p.2 - p.1) * (normalizedTheta B S p)^2 /
      (S.lam p.1 p.2 * canonicalNormalizedRadius S p)) K
  have hgap : ContinuousOn (fun p : ℝ × ℝ => -(p.2 - p.1)) K := by fun_prop
  exact (hgap.mul ((normalizedTheta_continuousOn hB hBb H).pow 2)).div
    ((five_fields_contDiffOn hB hBb H).1.continuousOn.mul hρ) hden

/-- The outgoing mass source is continuous on a smaller closed triangle. -/
theorem canonicalMassLinearSource_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMassLinearSource S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hden : ∀ p ∈ K, 2 * S.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact mul_ne_zero (by norm_num) (ne_of_gt (hc.trans_le (hcl p hp)))
  change ContinuousOn (fun p : ℝ × ℝ =>
    (S.theta p.1 p.2)^2 / (2 * S.lam p.1 p.2)) K
  exact ((five_fields_contDiffOn hB hBb H).2.2.2.1.continuousOn.pow 2).div
    (continuousOn_const.mul (five_fields_contDiffOn hB hBb H).1.continuousOn)
    hden

/-- The canonical mass density is a scalar linear equation with continuous
coefficients all the way to the axis. -/
theorem canonicalMass_outgoing_linear_equation {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMassOutgoingDensity b S p =
      canonicalMassLinearCoefficient B S p * canonicalMass b S p +
        canonicalMassLinearSource S p := by
  rcases p with ⟨u, v⟩
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hpK : (u, v) ∈ closedCoordTriangle 0 B := hp
    have hd : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    obtain ⟨c, hc, hρlower⟩ :=
      (canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H).2
    have hρ : canonicalNormalizedRadius S (u, v) ≠ 0 :=
      ne_of_gt (hc.trans_le (hρlower (u, v) hpK))
    obtain ⟨d, hdpos, hdlam⟩ := exists_lam_lower_bound hB hBb H
    have hlam : S.lam u v ≠ 0 := ne_of_gt (hdpos.trans_le (hdlam (u, v) hpK))
    have hr := canonicalRadius_eq_gap_mul_normalized S u v
    have hθ := theta_eq_gap_mul_normalizedTheta hB hBb H hpK
    have hμ : canonicalMassRatio b S (u, v) =
        2 * canonicalMass b S (u, v) /
          ((v - u) * canonicalNormalizedRadius S (u, v)) := by
      rw [canonicalMassRatio, hr]
    dsimp [canonicalMassOutgoingDensity, canonicalMassLinearCoefficient,
      canonicalMassLinearSource]
    rw [hθ, hμ]
    field_simp [hd, hρ, hlam]
    ring
  · change u = v at huv
    subst v
    simp [canonicalMassOutgoingDensity, canonicalMassLinearCoefficient,
      canonicalMassLinearSource, canonicalMass_axis,
      theta_axis_eq_zero hB hBb H ⟨hp.1, hp.2.2⟩]

/-- The regular mass coefficient and source agree wherever two solutions have
the same outgoing radius, expansion, and scalar amplitude. -/
theorem canonicalMass_linear_data_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : EqOn (canonicalRadius S₁) (canonicalRadius S₂)
      (closedCoordTriangle 0 B))
    (hlam : EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 B))
    (htheta : EqOn (fun p : ℝ × ℝ => S₁.theta p.1 p.2)
      (fun p => S₂.theta p.1 p.2) (closedCoordTriangle 0 B))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMassLinearCoefficient B S₁ p =
      canonicalMassLinearCoefficient B S₂ p ∧
    canonicalMassLinearSource S₁ p = canonicalMassLinearSource S₂ p := by
  have hg : canonicalMassLinearSource S₁ p = canonicalMassLinearSource S₂ p := by
    simp only [canonicalMassLinearSource, htheta hp, hlam hp]
  refine ⟨?_, hg⟩
  rcases p with ⟨u, v⟩
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hpK : (u, v) ∈ closedCoordTriangle 0 B := hp
    have hd : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    have hη : normalizedTheta B S₁ (u, v) = normalizedTheta B S₂ (u, v) := by
      have h₁ := theta_eq_gap_mul_normalizedTheta hB hB₁ H₁ hpK
      have h₂ := theta_eq_gap_mul_normalizedTheta hB hB₂ H₂ hpK
      change S₁.theta u v = (v - u) * normalizedTheta B S₁ (u, v) at h₁
      change S₂.theta u v = (v - u) * normalizedTheta B S₂ (u, v) at h₂
      have hθeq := htheta hpK
      change S₁.theta u v = S₂.theta u v at hθeq
      rw [hθeq] at h₁
      exact mul_left_cancel₀ hd (h₁.symm.trans h₂)
    have hρ : canonicalNormalizedRadius S₁ (u, v) =
        canonicalNormalizedRadius S₂ (u, v) := by
      have h₁ := canonicalRadius_eq_gap_mul_normalized S₁ u v
      have h₂ := canonicalRadius_eq_gap_mul_normalized S₂ u v
      rw [hr hpK] at h₁
      exact mul_left_cancel₀ hd (h₁.symm.trans h₂)
    simp only [canonicalMassLinearCoefficient, hη, hρ, hlam hpK]
  · change u = v at huv
    subst v
    simp [canonicalMassLinearCoefficient]

/-- Equal outgoing geometry and scalar amplitude determine the canonical
mass on the entire smaller triangle by uniqueness of its regular scalar
linear ODE with zero axis datum. -/
theorem canonicalMass_eq_of_outgoing_data_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : EqOn (canonicalRadius S₁) (canonicalRadius S₂)
      (closedCoordTriangle 0 B))
    (hlam : EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 B))
    (htheta : EqOn (fun p : ℝ × ℝ => S₁.theta p.1 p.2)
      (fun p => S₂.theta p.1 p.2) (closedCoordTriangle 0 B)) :
    EqOn (canonicalMass b₁ S₁) (canonicalMass b₂ S₂)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  intro p hp
  rcases p with ⟨u, v⟩
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hu : 0 ≤ u := hp.1
    have hv : v ≤ B := hp.2.2
    let k : ℝ → ℝ := fun t => canonicalMassLinearCoefficient B S₁ (u, t)
    let g : ℝ → ℝ := fun t => canonicalMassLinearSource S₁ (u, t)
    let y : ℝ → ℝ := fun t => canonicalMass b₁ S₁ (u, t)
    let z : ℝ → ℝ := fun t => canonicalMass b₂ S₂ (u, t)
    have hmap : Set.MapsTo (fun t : ℝ => (u, t)) (Icc u v) K := by
      intro t ht
      exact ⟨hu, ht.1, ht.2.trans hv⟩
    have hkcont : ContinuousOn k (Icc u v) :=
      (canonicalMassLinearCoefficient_continuousOn hB hB₁ H₁).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hgcont : ContinuousOn g (Icc u v) :=
      (canonicalMassLinearSource_continuousOn hB hB₁ H₁).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hycont : ContinuousOn y (Icc u v) :=
      (canonicalMass_contDiffOn hB hB₁ H₁).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hzcont : ContinuousOn z (Icc u v) :=
      (canonicalMass_contDiffOn hB hB₂ H₂).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    have hk : IntervalIntegrable k volume u v :=
      hkcont.intervalIntegrable_of_Icc huv.le
    have hg : IntervalIntegrable g volume u v :=
      hgcont.intervalIntegrable_of_Icc huv.le
    have hky : IntervalIntegrable (fun t => k t * y t) volume u v :=
      (hkcont.mul hycont).intervalIntegrable_of_Icc huv.le
    have hkz : IntervalIntegrable (fun t => k t * z t) volume u v :=
      (hkcont.mul hzcont).intervalIntegrable_of_Icc huv.le
    have hODE₁ : ∀ t ∈ Icc u v,
        y t - y u = ∫ s in u..t, (k s * y s + g s) := by
      intro t ht
      have hFTC := integral_vertical_jet_eq_sub hB
        (canonicalMass_contDiffOn hB hB₁ H₁) hu ht.1 (ht.2.trans hv)
      dsimp [y]
      rw [← hFTC]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hsK : (u, s) ∈ K := ⟨hu, hs.1, hs.2.trans (ht.2.trans hv)⟩
      change (fderivWithin ℝ (canonicalMass b₁ S₁) K (u, s)) (0, 1) =
        k s * y s + g s
      rw [(canonicalMass_coordinate_jets hB hB₁ H₁ hsK).2,
        canonicalMass_outgoing_linear_equation hB hB₁ H₁ hsK]
    have hODE₂ : ∀ t ∈ Icc u v,
        z t - z u = ∫ s in u..t, (k s * z s + g s) := by
      intro t ht
      have hFTC := integral_vertical_jet_eq_sub hB
        (canonicalMass_contDiffOn hB hB₂ H₂) hu ht.1 (ht.2.trans hv)
      dsimp [z]
      rw [← hFTC]
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hsK : (u, s) ∈ K := ⟨hu, hs.1, hs.2.trans (ht.2.trans hv)⟩
      change (fderivWithin ℝ (canonicalMass b₂ S₂) K (u, s)) (0, 1) =
        k s * z s + g s
      rw [(canonicalMass_coordinate_jets hB hB₂ H₂ hsK).2,
        canonicalMass_outgoing_linear_equation hB hB₂ H₂ hsK]
      obtain ⟨hkEq, hgEq⟩ := canonicalMass_linear_data_eq
        hB hB₁ hB₂ H₁ H₂ hr hlam htheta hsK
      simp only [k, g, hkEq, hgEq]
      rfl
    have hzero : y u = z u := by
      simp [y, z, canonicalMass_axis]
    exact intervalIntegral.eq_on_of_integral_eq huv.le hk hg hky hkz
      hODE₁ hODE₂ hzero ⟨huv.le, le_rfl⟩
  · change u = v at huv
    subst v
    simp [canonicalMass_axis]

/-- Equality of two outgoing primitives on the open initial edge determines
their continuous densities pointwise on that edge. -/
theorem initial_outgoing_density_eq_of_integral_eq {B : ℝ} (_hB : 0 < B)
    {g₁ g₂ : ℝ → ℝ}
    (hg₁ : ContinuousOn g₁ (Icc 0 B))
    (hg₂ : ContinuousOn g₂ (Icc 0 B))
    (hEq : ∀ t ∈ Ioo 0 B,
      (∫ s in (0 : ℝ)..t, g₁ s) = ∫ s in (0 : ℝ)..t, g₂ s)
    {v : ℝ} (hv : v ∈ Ioo 0 B) : g₁ v = g₂ v := by
  have hInt₁ : IntervalIntegrable g₁ volume 0 v :=
    (hg₁.mono (fun t ht => ⟨ht.1, ht.2.trans hv.2.le⟩)).intervalIntegrable_of_Icc
      hv.1.le
  have hInt₂ : IntervalIntegrable g₂ volume 0 v :=
    (hg₂.mono (fun t ht => ⟨ht.1, ht.2.trans hv.2.le⟩)).intervalIntegrable_of_Icc
      hv.1.le
  have hcont₁ : ContinuousAt g₁ v :=
    ((hg₁.mono Ioo_subset_Icc_self) v hv).continuousAt
      (isOpen_Ioo.mem_nhds hv)
  have hcont₂ : ContinuousAt g₂ v :=
    ((hg₂.mono Ioo_subset_Icc_self) v hv).continuousAt
      (isOpen_Ioo.mem_nhds hv)
  have hmeas₁ : StronglyMeasurableAtFilter g₁ (𝓝 v) volume :=
    (hg₁.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo v hv
  have hmeas₂ : StronglyMeasurableAtFilter g₂ (𝓝 v) volume :=
    (hg₂.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo v hv
  have hd₁ : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, g₁ s) (g₁ v) v :=
    intervalIntegral.integral_hasDerivAt_right hInt₁ hmeas₁ hcont₁
  have hd₂ : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, g₂ s) (g₂ v) v :=
    intervalIntegral.integral_hasDerivAt_right hInt₂ hmeas₂ hcont₂
  have hlocal : (fun t => ∫ s in (0 : ℝ)..t, g₁ s) =ᶠ[𝓝 v]
      (fun t => ∫ s in (0 : ℝ)..t, g₂ s) :=
    (show EqOn (fun t => ∫ s in (0 : ℝ)..t, g₁ s)
      (fun t => ∫ s in (0 : ℝ)..t, g₂ s) (Ioo 0 B) from hEq).eventuallyEq_of_mem
        (isOpen_Ioo.mem_nhds hv)
  exact (hd₁.congr_of_eventuallyEq hlocal.symm).unique hd₂

/-- Equal initial radii force equality of the outgoing expansion at every
point of the open common initial edge. -/
theorem initial_lam_eq_of_radius_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : ∀ v ∈ Ioo 0 B, S₁.r 0 v = S₂.r 0 v)
    {v : ℝ} (hv : v ∈ Ioo 0 B) : S₁.lam 0 v = S₂.lam 0 v := by
  let g₁ : ℝ → ℝ := fun t => S₁.lam 0 t
  let g₂ : ℝ → ℝ := fun t => S₂.lam 0 t
  have hc₁ : ContinuousOn g₁ (Icc 0 B) :=
    (five_fields_contDiffOn hB hB₁ H₁).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => by
        change 0 ≤ (0 : ℝ) ∧ 0 ≤ t ∧ t ≤ B
        exact ⟨le_rfl, ht.1, ht.2⟩)
  have hc₂ : ContinuousOn g₂ (Icc 0 B) :=
    (five_fields_contDiffOn hB hB₂ H₂).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => by
        change 0 ≤ (0 : ℝ) ∧ 0 ≤ t ∧ t ≤ B
        exact ⟨le_rfl, ht.1, ht.2⟩)
  apply initial_outgoing_density_eq_of_integral_eq hB hc₁ hc₂ ?_ hv
  intro t ht
  have hr₁ := canonicalRadius_eq_radius hB hB₁ H₁ le_rfl ht.1 ht.2.le
  have hr₂ := canonicalRadius_eq_radius hB hB₂ H₂ le_rfl ht.1 ht.2.le
  simpa only [g₁, g₂, canonicalRadius, intervalIntegral.weightedDiagonalRadius]
    using hr₁.trans ((hr t ht).trans hr₂.symm)

/-- Equal initial radius and scalar traces force equality of the outgoing
scalar-radius density on the open common initial edge. -/
theorem initial_alpha_eq_of_radius_phi_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : ∀ v ∈ Ioo 0 B, S₁.r 0 v = S₂.r 0 v)
    (hphi : ∀ v ∈ Ioo 0 B, S₁.phi 0 v = S₂.phi 0 v)
    {v : ℝ} (hv : v ∈ Ioo 0 B) : S₁.alpha 0 v = S₂.alpha 0 v := by
  let g₁ : ℝ → ℝ := fun t => S₁.alpha 0 t
  let g₂ : ℝ → ℝ := fun t => S₂.alpha 0 t
  have hc₁ : ContinuousOn g₁ (Icc 0 B) :=
    (alpha_contDiffOn hB hB₁ H₁).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => by
        change 0 ≤ (0 : ℝ) ∧ 0 ≤ t ∧ t ≤ B
        exact ⟨le_rfl, ht.1, ht.2⟩)
  have hc₂ : ContinuousOn g₂ (Icc 0 B) :=
    (alpha_contDiffOn hB hB₂ H₂).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => by
        change 0 ≤ (0 : ℝ) ∧ 0 ≤ t ∧ t ≤ B
        exact ⟨le_rfl, ht.1, ht.2⟩)
  apply initial_outgoing_density_eq_of_integral_eq hB hc₁ hc₂ ?_ hv
  intro t ht
  have hψ₁ := canonicalScalarRadius_eq_radius_mul_phi hB hB₁ H₁ le_rfl ht.1 ht.2.le
  have hψ₂ := canonicalScalarRadius_eq_radius_mul_phi hB hB₂ H₂ le_rfl ht.1 ht.2.le
  simpa only [g₁, g₂, canonicalScalarRadius,
    intervalIntegral.weightedDiagonalRadius] using
    hψ₁.trans (by rw [hr t ht, hphi t ht]; exact hψ₂.symm)

/-- The outgoing quotient `h=α/λ` has the same open initial trace for two
solutions with the same initial radius and scalar field. -/
theorem initial_outgoingQuotient_eq_of_radius_phi_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : ∀ v ∈ Ioo 0 B, S₁.r 0 v = S₂.r 0 v)
    (hphi : ∀ v ∈ Ioo 0 B, S₁.phi 0 v = S₂.phi 0 v)
    {v : ℝ} (hv : v ∈ Ioo 0 B) :
    outgoingQuotient S₁ (0, v) = outgoingQuotient S₂ (0, v) := by
  rw [outgoingQuotient, outgoingQuotient,
    initial_alpha_eq_of_radius_phi_eq hB hB₁ hB₂ H₁ H₂ hr hphi hv,
    initial_lam_eq_of_radius_eq hB hB₁ hB₂ H₁ H₂ hr hv]

/-- Two C¹ fields agreeing on the open initial edge have equal values and
outgoing relative jets on the full closed initial edge, including its ends. -/
theorem initial_vertical_jets_eq_of_initial_eq {B : ℝ} (hB : 0 < B)
    {F₁ F₂ : ℝ × ℝ → ℝ}
    (hF₁ : ContDiffOn ℝ 1 F₁ (closedCoordTriangle 0 B))
    (hF₂ : ContDiffOn ℝ 1 F₂ (closedCoordTriangle 0 B))
    (hEq : ∀ t ∈ Ioo 0 B, F₁ (0, t) = F₂ (0, t)) :
    ∀ t ∈ Icc 0 B,
      F₁ (0, t) = F₂ (0, t) ∧
      (fderivWithin ℝ F₁ (closedCoordTriangle 0 B) (0, t)) (0, 1) =
        (fderivWithin ℝ F₂ (closedCoordTriangle 0 B) (0, t)) (0, 1) := by
  let K := closedCoordTriangle 0 B
  let g₁ : ℝ → ℝ := fun t => (fderivWithin ℝ F₁ K (0, t)) (0, 1)
  let g₂ : ℝ → ℝ := fun t => (fderivWithin ℝ F₂ K (0, t)) (0, 1)
  have hmap : Set.MapsTo (fun t : ℝ => (0, t)) (Icc 0 B) K := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hval₁ : ContinuousOn (fun t => F₁ (0, t)) (Icc 0 B) :=
    hF₁.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hval₂ : ContinuousOn (fun t => F₂ (0, t)) (Icc 0 B) :=
    hF₂.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hvalues : EqOn (fun t => F₁ (0, t)) (fun t => F₂ (0, t)) (Icc 0 B) := by
    have hopen : EqOn (fun t => F₁ (0, t)) (fun t => F₂ (0, t))
        (Ioo 0 B) := hEq
    exact hopen.of_subset_closure hval₁ hval₂ Ioo_subset_Icc_self
      (by rw [closure_Ioo hB.ne])
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG₁ : ContinuousOn (fun p : ℝ × ℝ =>
      (fderivWithin ℝ F₁ K p) (0, 1)) K :=
    (hF₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hG₂ : ContinuousOn (fun p : ℝ × ℝ =>
      (fderivWithin ℝ F₂ K p) (0, 1)) K :=
    (hF₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hg₁ : ContinuousOn g₁ (Icc 0 B) :=
    hG₁.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hg₂ : ContinuousOn g₂ (Icc 0 B) :=
    hG₂.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hjetOpen : EqOn g₁ g₂ (Ioo 0 B) := by
    intro t ht
    apply initial_outgoing_density_eq_of_integral_eq hB hg₁ hg₂ ?_ ht
    intro s hs
    have hFTC₁ := integral_vertical_jet_eq_sub hB hF₁ le_rfl hs.1.le hs.2.le
    have hFTC₂ := integral_vertical_jet_eq_sub hB hF₂ le_rfl hs.1.le hs.2.le
    change (∫ w in (0 : ℝ)..s, g₁ w) = F₁ (0, s) - F₁ (0, 0) at hFTC₁
    change (∫ w in (0 : ℝ)..s, g₂ w) = F₂ (0, s) - F₂ (0, 0) at hFTC₂
    have hsEq : F₁ (0, s) = F₂ (0, s) := hvalues ⟨hs.1.le, hs.2.le⟩
    have h0Eq : F₁ (0, 0) = F₂ (0, 0) := hvalues ⟨le_rfl, hB.le⟩
    rw [hFTC₁, hFTC₂, hsEq, h0Eq]
  have hjets : EqOn g₁ g₂ (Icc 0 B) :=
    hjetOpen.of_subset_closure hg₁ hg₂ Ioo_subset_Icc_self
      (by rw [closure_Ioo hB.ne])
  intro t ht
  exact ⟨hvalues ht, hjets ht⟩

/-- Equal initial radius and scalar data supply the complete `λ,h` value
and outgoing-jet traces required at the lower boundary of (U). -/
theorem initial_lam_outgoingQuotient_jets_eq_of_data {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : ∀ v ∈ Ioo 0 B, S₁.r 0 v = S₂.r 0 v)
    (hphi : ∀ v ∈ Ioo 0 B, S₁.phi 0 v = S₂.phi 0 v)
    {v : ℝ} (hv : v ∈ Icc 0 B) :
    S₁.lam 0 v = S₂.lam 0 v ∧
    outgoingQuotient S₁ (0, v) = outgoingQuotient S₂ (0, v) ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (closedCoordTriangle 0 B) (0, v)) (0, 1) =
      (fderivWithin ℝ (fun p : ℝ × ℝ => S₂.lam p.1 p.2)
        (closedCoordTriangle 0 B) (0, v)) (0, 1) ∧
    (fderivWithin ℝ (outgoingQuotient S₁)
      (closedCoordTriangle 0 B) (0, v)) (0, 1) =
      (fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) (0, v)) (0, 1) := by
  have hlam := initial_vertical_jets_eq_of_initial_eq hB
    (five_fields_contDiffOn hB hB₁ H₁).1
    (five_fields_contDiffOn hB hB₂ H₂).1
    (fun t ht => initial_lam_eq_of_radius_eq hB hB₁ hB₂ H₁ H₂ hr ht) v hv
  have hh := initial_vertical_jets_eq_of_initial_eq hB
    (alpha_div_lam_contDiffOn hB hB₁ H₁)
    (alpha_div_lam_contDiffOn hB hB₂ H₂)
    (fun t ht => initial_outgoingQuotient_eq_of_radius_phi_eq
      hB hB₁ hB₂ H₁ H₂ hr hphi ht) v hv
  exact ⟨hlam.1, hh.1, hlam.2, hh.2⟩

/-- Equality of the three canonical primitive fields on a smaller closed
triangle determines every original field at its in-domain points. The
statement deliberately makes no claim about total radius or mass values on
the excluded diagonal or top edge. -/
theorem fields_eq_of_canonical_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : EqOn (canonicalRadius S₁) (canonicalRadius S₂)
      (closedCoordTriangle 0 B))
    (hψ : EqOn (canonicalScalarRadius S₁) (canonicalScalarRadius S₂)
      (closedCoordTriangle 0 B))
    (hm : EqOn (canonicalMass b₁ S₁) (canonicalMass b₂ S₂)
      (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v := by
  let K := closedCoordTriangle 0 B
  have hp : (u, v) ∈ K := ⟨hu, huv.le, hv⟩
  have hrval : S₁.r u v = S₂.r u v := by
    rw [← canonicalRadius_eq_radius hB hB₁ H₁ hu huv hv,
      ← canonicalRadius_eq_radius hB hB₂ H₂ hu huv hv]
    exact hr hp
  have hψval : S₁.r u v * S₁.phi u v = S₂.r u v * S₂.phi u v := by
    rw [← canonicalScalarRadius_eq_radius_mul_phi hB hB₁ H₁ hu huv hv,
      ← canonicalScalarRadius_eq_radius_mul_phi hB hB₂ H₂ hu huv hv]
    exact hψ hp
  have hrpos : 0 < S₁.r u v := H₁.solution.radius_pos (u, v)
    ⟨hu, huv, hv.trans_lt hB₁⟩
  have hphival : S₁.phi u v = S₂.phi u v := by
    rw [hrval] at hψval
    exact (mul_left_cancel₀ (ne_of_gt (hrval ▸ hrpos)) hψval)
  have hmval : S₁.m u v = S₂.m u v := by
    rw [← canonicalMass_eq_mass (show (u, v) ∈ developmentWithInitialEdge b₁
        from ⟨hu, huv, hv.trans_lt hB₁⟩),
      ← canonicalMass_eq_mass (show (u, v) ∈ developmentWithInitialEdge b₂
        from ⟨hu, huv, hv.trans_lt hB₂⟩)]
    exact hm hp
  have hrjet := fderivWithin_congr' (𝕜 := ℝ) hr hp
  have hψjet := fderivWithin_congr' (𝕜 := ℝ) hψ hp
  have hlam : S₁.lam u v = S₂.lam u v := by
    rw [← canonicalRadius_vertical_jet hB hB₁ H₁ hp,
      ← canonicalRadius_vertical_jet hB hB₂ H₂ hp]
    exact congrArg (fun G : (ℝ × ℝ) →L[ℝ] ℝ => G (0, 1)) hrjet
  have hnu : S₁.nu u v = S₂.nu u v := by
    rw [← canonicalRadius_horizontal_jet hB hB₁ H₁ hp,
      ← canonicalRadius_horizontal_jet hB hB₂ H₂ hp]
    exact congrArg (fun G : (ℝ × ℝ) →L[ℝ] ℝ => G (1, 0)) hrjet
  have halpha : S₁.alpha u v = S₂.alpha u v := by
    rw [← canonicalScalarRadius_vertical_jet hB hB₁ H₁ hp,
      ← canonicalScalarRadius_vertical_jet hB hB₂ H₂ hp]
    exact congrArg (fun G : (ℝ × ℝ) →L[ℝ] ℝ => G (0, 1)) hψjet
  have hbeta : S₁.beta u v = S₂.beta u v := by
    rw [← canonicalScalarRadius_horizontal_jet hB hB₁ H₁ hp,
      ← canonicalScalarRadius_horizontal_jet hB hB₂ H₂ hp]
    exact congrArg (fun G : (ℝ × ℝ) →L[ℝ] ℝ => G (1, 0)) hψjet
  exact ⟨hrval, hphival, hmval, hlam, hnu, halpha, hbeta⟩

/-- Equality of the outgoing expansion and outgoing scalar derivative on a
smaller triangle determines all seven original fields at its in-domain
points. The proof reconstructs the two outgoing primitives, solves the
regular linear mass equation, and recovers the incoming fields from jets. -/
theorem fields_eq_of_lam_alpha_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hlam : EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 B))
    (halpha : EqOn (fun p : ℝ × ℝ => S₁.alpha p.1 p.2)
      (fun p => S₂.alpha p.1 p.2) (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v := by
  let K := closedCoordTriangle 0 B
  have hr : EqOn (canonicalRadius S₁) (canonicalRadius S₂) K := by
    rintro ⟨a, z⟩ hp
    change 0 ≤ a ∧ a ≤ z ∧ z ≤ B at hp
    change (∫ t in a..z, S₁.lam a t) = ∫ t in a..z, S₂.lam a t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hp.2.1] at ht
    have htK : (a, t) ∈ K := ⟨hp.1, ht.1, ht.2.trans hp.2.2⟩
    exact hlam htK
  have hψ : EqOn (canonicalScalarRadius S₁) (canonicalScalarRadius S₂) K := by
    rintro ⟨a, z⟩ hp
    change 0 ≤ a ∧ a ≤ z ∧ z ≤ B at hp
    change (∫ t in a..z, S₁.alpha a t) = ∫ t in a..z, S₂.alpha a t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hp.2.1] at ht
    have htK : (a, t) ∈ K := ⟨hp.1, ht.1, ht.2.trans hp.2.2⟩
    exact halpha htK
  have hphi : EqOn (fun p : ℝ × ℝ => S₁.phi p.1 p.2)
      (fun p => S₂.phi p.1 p.2) K := by
    rintro ⟨a, z⟩ hp
    rcases lt_or_eq_of_le hp.2.1 with haz | haz
    · have hrval : S₁.r a z = S₂.r a z := by
        rw [← canonicalRadius_eq_radius hB hB₁ H₁ hp.1 haz hp.2.2,
          ← canonicalRadius_eq_radius hB hB₂ H₂ hp.1 haz hp.2.2]
        exact hr hp
      have hψval : S₁.r a z * S₁.phi a z = S₂.r a z * S₂.phi a z := by
        rw [← canonicalScalarRadius_eq_radius_mul_phi hB hB₁ H₁ hp.1 haz hp.2.2,
          ← canonicalScalarRadius_eq_radius_mul_phi hB hB₂ H₂ hp.1 haz hp.2.2]
        exact hψ hp
      have hrpos : 0 < S₂.r a z := by
        rw [← hrval]
        exact H₁.solution.radius_pos (a, z) ⟨hp.1, haz, hp.2.2.trans_lt hB₁⟩
      rw [hrval] at hψval
      exact mul_left_cancel₀ (ne_of_gt hrpos) hψval
    · change a = z at haz
      subst z
      have ha₁ := alpha_eq_lam_mul_phi_axis hB hB₁ H₁ ⟨hp.1, hp.2.2⟩
      have ha₂ := alpha_eq_lam_mul_phi_axis hB hB₂ H₂ ⟨hp.1, hp.2.2⟩
      have hla : S₁.lam a a = S₂.lam a a := hlam hp
      have haa : S₁.alpha a a = S₂.alpha a a := halpha hp
      have hne : S₂.lam a a ≠ 0 := by
        obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hB₂ H₂
        exact ne_of_gt (hc.trans_le (hcl (a, a) hp))
      rw [haa, hla, ha₂] at ha₁
      exact mul_left_cancel₀ hne ha₁.symm
  have htheta : EqOn (fun p : ℝ × ℝ => S₁.theta p.1 p.2)
      (fun p => S₂.theta p.1 p.2) K := by
    intro p hp
    simp only [Fields.theta]
    have ha := halpha hp
    have hl := hlam hp
    have hφ := hphi hp
    change S₁.alpha p.1 p.2 = S₂.alpha p.1 p.2 at ha
    change S₁.lam p.1 p.2 = S₂.lam p.1 p.2 at hl
    change S₁.phi p.1 p.2 = S₂.phi p.1 p.2 at hφ
    rw [ha, hl, hφ]
  have hm := canonicalMass_eq_of_outgoing_data_eq
    hB hB₁ hB₂ H₁ H₂ hr hlam htheta
  exact fields_eq_of_canonical_eq hB hB₁ hB₂ H₁ H₂ hr hψ hm hu huv hv

/-- Equality of `λ` and the actual outgoing quotient `h=α/λ` on a smaller
triangle implies equality of all seven original fields in its development. -/
theorem fields_eq_of_lam_outgoingQuotient_eq {b₁ b₂ B : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hlam : EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 B))
    (hh : EqOn (outgoingQuotient S₁) (outgoingQuotient S₂)
      (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v := by
  have ha : EqOn (fun p : ℝ × ℝ => S₁.alpha p.1 p.2)
      (fun p => S₂.alpha p.1 p.2) (closedCoordTriangle 0 B) := by
    intro p hp
    obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hB₁ H₁
    have hne : S₁.lam p.1 p.2 ≠ 0 := ne_of_gt (hc.trans_le (hcl p hp))
    have hq := hh hp
    have hl := hlam hp
    change S₁.lam p.1 p.2 = S₂.lam p.1 p.2 at hl
    change S₁.alpha p.1 p.2 / S₁.lam p.1 p.2 =
      S₂.alpha p.1 p.2 / S₂.lam p.1 p.2 at hq
    rw [← hl] at hq
    exact (div_left_inj' hne).mp hq
  exact fields_eq_of_lam_alpha_eq hB hB₁ hB₂ H₁ H₂ hlam ha hu huv hv

/-- Compact-triangle equality of `λ,h` exhausts the common development.
Every asserted equality is at a point in both frozen domains, where the
canonical radius and mass agree with the original total fields. -/
theorem fields_eq_on_common_development_of_compact_lam_h_eq
    {b₁ b₂ : ℝ} {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hcompact : ∀ B : ℝ, 0 < B → B < b₁ → B < b₂ →
      EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
        (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 B) ∧
      EqOn (outgoingQuotient S₁) (outgoingQuotient S₂)
        (closedCoordTriangle 0 B))
    {u v : ℝ}
    (hp₁ : (u, v) ∈ developmentWithInitialEdge b₁)
    (hp₂ : (u, v) ∈ developmentWithInitialEdge b₂) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v ∧ S₁.theta u v = S₂.theta u v ∧
    S₁.zeta u v = S₂.zeta u v := by
  change 0 ≤ u ∧ u < v ∧ v < b₁ at hp₁
  change 0 ≤ u ∧ u < v ∧ v < b₂ at hp₂
  let B := (v + min b₁ b₂) / 2
  have hvmin : v < min b₁ b₂ := lt_min hp₁.2.2 hp₂.2.2
  have hvB : v < B := by dsimp [B]; linarith
  have hBmin : B < min b₁ b₂ := by dsimp [B]; linarith
  have hB : 0 < B := by linarith only [hp₁.1, hp₁.2.1, hvB]
  have hB₁ : B < b₁ := hBmin.trans_le (min_le_left b₁ b₂)
  have hB₂ : B < b₂ := hBmin.trans_le (min_le_right b₁ b₂)
  obtain ⟨hlam, hh⟩ := hcompact B hB hB₁ hB₂
  obtain ⟨hr, hphi, hm, hlam', hnu, halpha, hbeta⟩ :=
    fields_eq_of_lam_outgoingQuotient_eq hB hB₁ hB₂ H₁ H₂
      hlam hh hp₁.1 hp₁.2.1 hvB.le
  have htheta : S₁.theta u v = S₂.theta u v := by
    simp only [Fields.theta]
    rw [halpha, hlam', hphi]
  have hzeta : S₁.zeta u v = S₂.zeta u v := by
    simp only [Fields.zeta]
    rw [hbeta, hnu, hphi]
  exact ⟨hr, hphi, hm, hlam', hnu, halpha, hbeta, htheta, hzeta⟩

end ChristodoulouBV.C1Solution

end
