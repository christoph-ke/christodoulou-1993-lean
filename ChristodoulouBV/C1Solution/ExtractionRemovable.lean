module

public import ChristodoulouBV.C1Solution.ExtractionMassCubic
public import ChristodoulouBV.C1Solution.ExtractionCoefficient
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# The C¹ removable mixed coefficient

The canonical mass has a continuous cubic normalization. Its outgoing and
incoming equations provide the two continuous derivative limits needed to
differentiate the mass divided by the squared radius at the axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The positive normalized canonical radius. -/
@[expose] noncomputable def canonicalNormalizedRadius (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.normalizedDiagonalRadius (fun q => S.lam q.1 q.2) p

/-- The canonical radius is the coordinate gap times its normalized radius. -/
theorem canonicalRadius_eq_gap_mul_normalized (S : Fields) (u v : ℝ) :
    canonicalRadius S (u, v) = (v - u) * canonicalNormalizedRadius S (u, v) :=
  intervalIntegral.weightedDiagonalRadius_eq_gap_mul_normalized
    (fun q => S.lam q.1 q.2) u v

/-- The normalized radius is continuous and positive on smaller triangles. -/
theorem canonicalNormalizedRadius_continuousOn_and_lower_bound {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalNormalizedRadius S) (closedCoordTriangle 0 B) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ canonicalNormalizedRadius S p := by
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hlam := (five_fields_contDiffOn hB hBb H).1.continuousOn
  exact ⟨intervalIntegral.continuousOn_normalizedDiagonalRadius hlam,
    ⟨c, hc, fun p hp => intervalIntegral.le_normalizedDiagonalRadius hlam hcl hp⟩⟩

/-- The continuous coefficient of the linearly vanishing normalized mass. -/
@[expose] noncomputable def normalizedMassOverRadiusSq
    (b B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  2 * normalizedMassCubic b B S p / (canonicalNormalizedRadius S p)^2

/-- The normalized mass-over-radius coefficient is continuous on the triangle. -/
theorem normalizedMassOverRadiusSq_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedMassOverRadiusSq b B S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨hρ, c, hc, hρlower⟩ :=
    canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
  change ContinuousOn (fun p : ℝ × ℝ =>
    2 * normalizedMassCubic b B S p / (canonicalNormalizedRadius S p)^2) K
  exact (continuousOn_const.mul (normalizedMassCubic_continuousOn hB hBb H)).div
    (hρ.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (hc.trans_le (hρlower p hp))))

/-- The normalized mass over squared radius has a single coordinate-gap factor. -/
theorem canonicalMassOverRadiusSq_eq_gap_mul_normalized {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMassOverRadiusSq b S p =
      (p.2 - p.1) * normalizedMassOverRadiusSq b B S p := by
  rcases p with ⟨u, v⟩
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hd : v - u ≠ 0 := sub_ne_zero.mpr huv.ne'
    obtain ⟨_, c, hc, hρlower⟩ :=
      canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
    have hρ : canonicalNormalizedRadius S (u, v) ≠ 0 :=
      ne_of_gt (hc.trans_le (hρlower (u, v) hp))
    rw [canonicalMassOverRadiusSq, normalizedMassOverRadiusSq,
      canonicalMass_eq_gap_cubed_mul_normalizedMassCubic hB hBb H hp,
      canonicalRadius_eq_gap_mul_normalized]
    field_simp [hd, hρ]
  · change u = v at huv
    subst v
    simp [canonicalMassOverRadiusSq_axis]

/-- The continuous horizontal coefficient of the normalized mass-over-radius jet. -/
@[expose] noncomputable def normalizedMassOverRadiusSqHorizontalJet
    (b B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  2 * (normalizedIncomingMassDensity b B S p /
        (canonicalNormalizedRadius S p)^2 -
      2 * normalizedMassCubic b B S p * S.nu p.1 p.2 /
        (canonicalNormalizedRadius S p)^3)

/-- The continuous vertical coefficient of the normalized mass-over-radius jet. -/
@[expose] noncomputable def normalizedMassOverRadiusSqVerticalJet
    (b B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  2 * (normalizedMassDensity b B S p /
        (canonicalNormalizedRadius S p)^2 -
      2 * normalizedMassCubic b B S p * S.lam p.1 p.2 /
        (canonicalNormalizedRadius S p)^3)

/-- Both candidate coordinate jets are continuous on the closed triangle. -/
theorem normalizedMassOverRadiusSq_jets_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedMassOverRadiusSqHorizontalJet b B S)
      (closedCoordTriangle 0 B) ∧
    ContinuousOn (normalizedMassOverRadiusSqVerticalJet b B S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨hρ, c, hc, hρlower⟩ :=
    canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
  have hρne : ∀ p ∈ K, canonicalNormalizedRadius S p ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hρlower p hp))
  have hQ := normalizedMassCubic_continuousOn hB hBb H
  obtain ⟨hlam, hnu, _, _, _⟩ := five_fields_contDiffOn hB hBb H
  constructor
  · change ContinuousOn (fun p : ℝ × ℝ =>
      2 * (normalizedIncomingMassDensity b B S p /
        (canonicalNormalizedRadius S p)^2 -
      2 * normalizedMassCubic b B S p * S.nu p.1 p.2 /
        (canonicalNormalizedRadius S p)^3)) K
    exact continuousOn_const.mul
      ((normalizedIncomingMassDensity_continuousOn hB hBb H).div
        (hρ.pow 2) (fun p hp => pow_ne_zero 2 (hρne p hp)) |>.sub
        (((continuousOn_const.mul hQ).mul hnu.continuousOn).div
          (hρ.pow 3) (fun p hp => pow_ne_zero 3 (hρne p hp))))
  · change ContinuousOn (fun p : ℝ × ℝ =>
      2 * (normalizedMassDensity b B S p /
        (canonicalNormalizedRadius S p)^2 -
      2 * normalizedMassCubic b B S p * S.lam p.1 p.2 /
        (canonicalNormalizedRadius S p)^3)) K
    exact continuousOn_const.mul
      ((normalizedMassDensity_continuousOn hB hBb H).div
        (hρ.pow 2) (fun p hp => pow_ne_zero 2 (hρne p hp)) |>.sub
        (((continuousOn_const.mul hQ).mul hlam.continuousOn).div
          (hρ.pow 3) (fun p hp => pow_ne_zero 3 (hρne p hp))))

private theorem canonicalRadius_horizontal_hasDerivAt_interior {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => canonicalRadius S (t, v)) (S.nu u v) u := by
  let K := closedCoordTriangle 0 B
  have hqi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hdiff : DifferentiableAt ℝ (canonicalRadius S) (u, v) :=
    (((canonicalRadius_contDiffOn hB hBb H).differentiableOn (by norm_num)).mono
      interior_subset (u, v) hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, v) (interior_subset hqi)
  have hwithin : fderivWithin ℝ (canonicalRadius S) K (u, v) =
      fderiv ℝ (canonicalRadius S) (u, v) :=
    fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun t => canonicalRadius S (t, v))
      (fderiv ℝ (canonicalRadius S) (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  rw [← hwithin] at hcomp
  rwa [canonicalRadius_horizontal_jet hB hBb H (interior_subset hqi)] at hcomp

private theorem canonicalRadius_vertical_hasDerivAt_interior {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => canonicalRadius S (u, t)) (S.lam u v) v := by
  let K := closedCoordTriangle 0 B
  have hqi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hdiff : DifferentiableAt ℝ (canonicalRadius S) (u, v) :=
    (((canonicalRadius_contDiffOn hB hBb H).differentiableOn (by norm_num)).mono
      interior_subset (u, v) hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, v) (interior_subset hqi)
  have hwithin : fderivWithin ℝ (canonicalRadius S) K (u, v) =
      fderiv ℝ (canonicalRadius S) (u, v) :=
    fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hcomp : HasDerivAt (fun t => canonicalRadius S (u, t))
      (fderiv ℝ (canonicalRadius S) (u, v) (0, 1)) v := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt v hpair
  rw [← hwithin] at hcomp
  rwa [canonicalRadius_vertical_jet hB hBb H (interior_subset hqi)] at hcomp

private theorem canonicalMassOverRadiusSq_horizontal_hasDerivAt_interior {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => canonicalMassOverRadiusSq b S (t, v))
      (normalizedMassOverRadiusSqHorizontalJet b B S (u, v)) u := by
  have hparts : 0 < u ∧ u < v ∧ v < B := hp
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  have hrpos : 0 < canonicalRadius S (u, v) := by
    obtain ⟨c, hc, hcl⟩ := canonicalRadius_lower_bound hB hBb H
    exact lt_of_lt_of_le (mul_pos hc (sub_pos.mpr hparts.2.1)) (hcl (u, v) hpK)
  have hmder := canonicalMass_horizontal_hasDerivAt hB hBb H hp
  have hrder := canonicalRadius_horizontal_hasDerivAt_interior hB hBb H hp
  have hquot := ((hmder.const_mul 2).div (hrder.pow 2)
    (pow_ne_zero 2 (ne_of_gt hrpos)))
  have hformula :
      (2 * canonicalMassIncomingDensity b S (u, v) * (canonicalRadius S (u, v))^2 -
        (2 * canonicalMass b S (u, v)) *
          (2 * canonicalRadius S (u, v) * S.nu u v)) /
        ((canonicalRadius S (u, v))^2)^2 =
      normalizedMassOverRadiusSqHorizontalJet b B S (u, v) := by
    have hd : v - u ≠ 0 := sub_ne_zero.mpr hparts.2.1.ne'
    obtain ⟨_, c, hc, hρlower⟩ :=
      canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
    have hρ : canonicalNormalizedRadius S (u, v) ≠ 0 :=
      ne_of_gt (hc.trans_le (hρlower (u, v) hpK))
    rw [canonicalMassIncomingDensity_eq_gap_sq_mul_normalized hB hBb H hpK,
      canonicalMass_eq_gap_cubed_mul_normalizedMassCubic hB hBb H hpK,
      canonicalRadius_eq_gap_mul_normalized,
      normalizedMassOverRadiusSqHorizontalJet]
    field_simp [hd, hρ]
  rw [← hformula]
  have heq : ((fun y => 2 * canonicalMass b S (y, v)) /
      (fun t => canonicalRadius S (t, v))^2) =
      (fun t => canonicalMassOverRadiusSq b S (t, v)) := by
    funext t
    simp [canonicalMassOverRadiusSq]
  rw [heq] at hquot
  simpa using hquot

private theorem canonicalMassOverRadiusSq_vertical_hasDerivAt_interior {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => canonicalMassOverRadiusSq b S (u, t))
      (normalizedMassOverRadiusSqVerticalJet b B S (u, v)) v := by
  have hparts : 0 < u ∧ u < v ∧ v < B := hp
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  have hrpos : 0 < canonicalRadius S (u, v) := by
    obtain ⟨c, hc, hcl⟩ := canonicalRadius_lower_bound hB hBb H
    exact lt_of_lt_of_le (mul_pos hc (sub_pos.mpr hparts.2.1)) (hcl (u, v) hpK)
  have hmder := canonicalMass_vertical_hasDerivAt hB hBb H hp
  have hrder := canonicalRadius_vertical_hasDerivAt_interior hB hBb H hp
  have hquot := ((hmder.const_mul 2).div (hrder.pow 2)
    (pow_ne_zero 2 (ne_of_gt hrpos)))
  have hformula :
      (2 * canonicalMassOutgoingDensity b S (u, v) * (canonicalRadius S (u, v))^2 -
        (2 * canonicalMass b S (u, v)) *
          (2 * canonicalRadius S (u, v) * S.lam u v)) /
        ((canonicalRadius S (u, v))^2)^2 =
      normalizedMassOverRadiusSqVerticalJet b B S (u, v) := by
    have hd : v - u ≠ 0 := sub_ne_zero.mpr hparts.2.1.ne'
    obtain ⟨_, c, hc, hρlower⟩ :=
      canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
    have hρ : canonicalNormalizedRadius S (u, v) ≠ 0 :=
      ne_of_gt (hc.trans_le (hρlower (u, v) hpK))
    rw [canonicalMassOutgoingDensity_eq_gap_sq_mul_normalized hB hBb H hpK,
      canonicalMass_eq_gap_cubed_mul_normalizedMassCubic hB hBb H hpK,
      canonicalRadius_eq_gap_mul_normalized,
      normalizedMassOverRadiusSqVerticalJet]
    field_simp [hd, hρ]
  rw [← hformula]
  have heq : ((fun y => 2 * canonicalMass b S (u, y)) /
      (fun t => canonicalRadius S (u, t))^2) =
      (fun t => canonicalMassOverRadiusSq b S (u, t)) := by
    funext t
    simp [canonicalMassOverRadiusSq]
  rw [heq] at hquot
  simpa using hquot

/-- Twice the canonical mass divided by squared canonical radius is C¹ on a
smaller closed triangle, with its removable zero axis value. -/
theorem canonicalMassOverRadiusSq_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalMassOverRadiusSq b S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  let fu := normalizedMassOverRadiusSqHorizontalJet b B S
  let fv := normalizedMassOverRadiusSqVerticalJet b B S
  let L : ℝ → ℝ →L[ℝ] ℝ :=
    fun x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) x
  let J : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ :=
    fun p => (L (fu p)).coprod (L (fv p))
  have hL : Continuous L :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous
  obtain ⟨hfu, hfv⟩ := normalizedMassOverRadiusSq_jets_continuousOn hB hBb H
  have hJ : ContinuousOn J K := by
    have h₁ : ContinuousOn (fun p => L (fu p)) K :=
      hL.comp_continuousOn hfu
    have h₂ : ContinuousOn (fun p => L (fv p)) K :=
      hL.comp_continuousOn hfv
    exact (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := ℝ)
      (G := ℝ) ℝ).continuous.comp_continuousOn (h₁.prodMk h₂)
  have hstrict (p : ℝ × ℝ) (hp : p ∈ interior K) :
      HasStrictFDerivAt (canonicalMassOverRadiusSq b S) (J p) p := by
    have hnear : openCoordTriangle 0 B ∈ 𝓝 p := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior.mem_nhds hp
    have hdu : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun s => canonicalMassOverRadiusSq b S (s, q.2))
          (L (fu q)) q.1 := by
      filter_upwards [hnear] with q hq
      exact (canonicalMassOverRadiusSq_horizontal_hasDerivAt_interior
        hB hBb H hq).hasFDerivAt
    have hdv : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun t => canonicalMassOverRadiusSq b S (q.1, t))
          (L (fv q)) q.2 := by
      filter_upwards [hnear] with q hq
      exact (canonicalMassOverRadiusSq_vertical_hasDerivAt_interior
        hB hBb H hq).hasFDerivAt
    have hKmem : K ∈ 𝓝 p :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset
    have hfuAt : ContinuousAt fu p :=
      (hfu p (interior_subset hp)).continuousAt hKmem
    have hfvAt : ContinuousAt fv p :=
      (hfv p (interior_subset hp)).continuousAt hKmem
    exact hasStrictFDerivAt_uncurry_coprod
      (f := fun u v => canonicalMassOverRadiusSq b S (u, v))
      (f₁ := fun u v => L (fu (u, v)))
      (f₂ := fun u v => L (fv (u, v)))
      hdu hdv (hL.continuousAt.comp hfuAt) (hL.continuousAt.comp hfvAt)
  have hdiff : DifferentiableOn ℝ (canonicalMassOverRadiusSq b S)
      (interior K) :=
    fun p hp => (hstrict p hp).hasFDerivAt.differentiableAt.differentiableWithinAt
  have hderiv : ∀ p ∈ interior K,
      fderiv ℝ (canonicalMassOverRadiusSq b S) p = J p :=
    fun p hp => (hstrict p hp).hasFDerivAt.fderiv
  exact (convex_closedCoordTriangle 0 B).contDiffOn_one_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle 0 B)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
    (canonicalMassOverRadiusSq_continuousOn hB hBb H) hJ hdiff hderiv

/-- The canonical mass ratio has a continuous full first jet on a smaller
closed triangle, with its canonical zero axis value. -/
theorem canonicalMassRatio_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalMassRatio b S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hprod := (canonicalMassOverRadiusSq_contDiffOn hB hBb H).mul
    (canonicalRadius_contDiffOn hB hBb H)
  apply hprod.congr
  intro p hp
  rcases p with ⟨u, v⟩
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hrad : canonicalRadius S (u, v) ≠ 0 := by
      obtain ⟨c, hc, hcl⟩ := canonicalRadius_lower_bound hB hBb H
      exact ne_of_gt (lt_of_lt_of_le (mul_pos hc (sub_pos.mpr huv))
        (hcl (u, v) hp))
    dsimp [canonicalMassOverRadiusSq, canonicalMassRatio]
    field_simp [hrad]
  · change u = v at huv
    subst v
    simp [canonicalMassRatio_axis, canonicalMassOverRadiusSq_axis,
      canonical_outgoing_axis]

/-- The canonical mixed coefficient has a continuous full first jet on every
smaller closed triangle. -/
theorem canonicalMixedCoefficient_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalMixedCoefficient b S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨ε, hε, hgap⟩ := exists_canonical_mass_gap_lower_bound hB hBb H
  obtain ⟨hlam, hnu, _, _, _⟩ := five_fields_contDiffOn hB hBb H
  have hden : ∀ p ∈ K, 1 - canonicalMassRatio b S p ≠ 0 :=
    fun p hp => ne_of_gt (hε.trans_le (hgap p hp))
  change ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
    canonicalMassOverRadiusSq b S p * S.lam p.1 p.2 * S.nu p.1 p.2 /
      (1 - canonicalMassRatio b S p)) K
  exact (((canonicalMassOverRadiusSq_contDiffOn hB hBb H).mul hlam).mul hnu).div
    (contDiffOn_const.sub (canonicalMassRatio_contDiffOn hB hBb H)) hden

end ChristodoulouBV.C1Solution

end
