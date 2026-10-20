module

public import ChristodoulouBV.C1Solution.ExtractionJets
public import ChristodoulouBV.C1Solution.ExtractionMass
public import ChristodoulouBV.AreaEstimates.SourceInputs
public import ChristodoulouBV.BVSolution.C1ToBV
public import ChristodoulouBV.AreaEstimates.GaugeAxisMixedPartial
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Mixed coefficient regularity on strict C¹ triangles

The integrated system supplies a continuous first derivative of the canonical
mass. On a strict triangle all denominators stay away from zero, so the mixed
transport coefficient is C¹. The four already extracted first jets then have
C¹ densities even though the original C¹ fields need not be C² in both pure
coordinate directions.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

/-- The removable mixed coefficient is C¹ on each strict subtriangle. This is
the local regularity needed to differentiate the four mixed transports. -/
theorem mixed_coefficient_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (C1Solution.canonicalMixedCoefficient b S)
      (openCoordTriangle 0 B) := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  have hsub : T ⊆ K := by
    intro p hp
    simp only [T, openCoordTriangle, mem_ofPred_eq] at hp
    simpa only [K, closedCoordTriangle, mem_ofPred_eq] using
      (show 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ B from
        ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
  have hr : ContDiffOn ℝ 1 (C1Solution.canonicalRadius S) T :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).mono hsub
  have hm : ContDiffOn ℝ 1 (C1Solution.canonicalMass b S) T :=
    (C1Solution.canonicalMass_contDiffOn hB hBb H).mono hsub
  obtain ⟨hlamK, hnuK, _, _, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  have hlam := hlamK.mono hsub
  have hnu := hnuK.mono hsub
  obtain ⟨c, hc, hrad⟩ := C1Solution.canonicalRadius_lower_bound hB hBb H
  have hrne : ∀ p ∈ T, C1Solution.canonicalRadius S p ≠ 0 := by
    intro p hp
    simp only [T, openCoordTriangle, mem_ofPred_eq] at hp
    have hpK : p ∈ K := hsub hp
    have hgap : 0 < p.2 - p.1 := sub_pos.mpr hp.2.1
    exact ne_of_gt (lt_of_lt_of_le (mul_pos hc hgap) (hrad p hpK))
  have hratio : ContDiffOn ℝ 1 (C1Solution.canonicalMassRatio b S) T := by
    change ContDiffOn ℝ 1
      (fun p => 2 * C1Solution.canonicalMass b S p /
        C1Solution.canonicalRadius S p) T
    exact (contDiffOn_const.mul hm).div hr hrne
  have hmsq : ContDiffOn ℝ 1
      (C1Solution.canonicalMassOverRadiusSq b S) T := by
    change ContDiffOn ℝ 1
      (fun p => 2 * C1Solution.canonicalMass b S p /
        (C1Solution.canonicalRadius S p)^2) T
    exact (contDiffOn_const.mul hm).div (hr.pow 2)
      (fun p hp => pow_ne_zero 2 (hrne p hp))
  obtain ⟨ε, hε, hmassgap⟩ :=
    C1Solution.exists_canonical_mass_gap_lower_bound hB hBb H
  have hgapne : ∀ p ∈ T,
      1 - C1Solution.canonicalMassRatio b S p ≠ 0 := by
    intro p hp
    exact ne_of_gt (hε.trans_le (hmassgap p (hsub hp)))
  change ContDiffOn ℝ 1 (fun p =>
    C1Solution.canonicalMassOverRadiusSq b S p * S.lam p.1 p.2 *
      S.nu p.1 p.2 / (1 - C1Solution.canonicalMassRatio b S p)) T
  exact ((hmsq.mul hlam).mul hnu).div (contDiffOn_const.sub hratio) hgapne

/-- Both logarithmic transport densities are C¹ on a strict subtriangle.
This supplies the differentiation regularity used in (4.7a,b); their
expanded source formulas are handled with the mass equations. -/
theorem log_transport_coefficients_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (fun p =>
      C1Solution.canonicalMixedCoefficient b S p / S.lam p.1 p.2)
      (openCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1 (fun p =>
      C1Solution.canonicalMixedCoefficient b S p / S.nu p.1 p.2)
      (openCoordTriangle 0 B) := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  have hsub : T ⊆ K := by
    intro p hp
    have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
    exact ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  have hg := mixed_coefficient_contDiffOn hB hBb H
  obtain ⟨hlamK, hnuK, _, _, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  obtain ⟨c, hc, hlamLower⟩ := C1Solution.exists_lam_lower_bound hB hBb H
  have hlamNe : ∀ p ∈ T, S.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (hc.trans_le (hlamLower p (hsub hp)))
  have hnuNe : ∀ p ∈ T, S.nu p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_lt (C1Solution.nu_neg_closed_triangle hB hBb H (hsub hp))
  exact ⟨hg.div (hlamK.mono hsub) hlamNe,
    hg.div (hnuK.mono hsub) hnuNe⟩

private theorem fderiv_eq_fderivWithin_strict {B : ℝ} (hB : 0 < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 B) :
    fderiv ℝ f p = fderivWithin ℝ f (closedCoordTriangle 0 B) p := by
  have hpK : p ∈ closedCoordTriangle 0 B := by
    have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
    exact ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  have hpInt : p ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hUnique : UniqueDiffWithinAt ℝ (closedCoordTriangle 0 B) p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      p hpK
  have hDiff : DifferentiableAt ℝ f p :=
    (hf.differentiableOn (by norm_num) p hpK).differentiableAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset)
  exact (fderivWithin_eq_fderiv hUnique hDiff).symm

/-- The logarithmic first transports hold as ordinary derivatives on the
strict triangle. Together with the C¹ densities above, this justifies the
second differentiations at the start of (4.7a,b). Since `ν < 0`, the second
logarithm equals the source's `log |ν|`. -/
theorem log_transport_first_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 B) :
    (fderiv ℝ (fun q : ℝ × ℝ => Real.log (S.lam q.1 q.2)) p) (1, 0) =
      C1Solution.canonicalMixedCoefficient b S p / S.lam p.1 p.2 ∧
    (fderiv ℝ (fun q : ℝ × ℝ => Real.log (-S.nu q.1 q.2)) p) (0, 1) =
      C1Solution.canonicalMixedCoefficient b S p / S.nu p.1 p.2 := by
  have hpK : p ∈ closedCoordTriangle 0 B := by
    have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
    exact ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  obtain ⟨hlamK, hnuK, _, _, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  have hpInt : p ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hnhds : closedCoordTriangle 0 B ∈ 𝓝 p :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  have hLamDiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2) p :=
    (hlamK.differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hNuDiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2) p :=
    (hnuK.differentiableOn (by norm_num) p hpK).differentiableAt hnhds
  have hLamPos : 0 < S.lam p.1 p.2 := by
    have hpU : p ∈ developmentWithInitialEdge b := by
      have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
      exact ⟨hparts.1.le, hparts.2.1, hparts.2.2.trans hBb⟩
    exact H.solution.lam_pos p hpU
  have hNuNeg := C1Solution.nu_neg_closed_triangle hB hBb H hpK
  have hJets := C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  have hLamJet :
      (fderiv ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2) p) (1, 0) =
        C1Solution.canonicalMixedCoefficient b S p := by
    rw [fderiv_eq_fderivWithin_strict hB hlamK hp]
    exact hJets.1
  have hNuJet :
      (fderiv ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2) p) (0, 1) =
        C1Solution.canonicalMixedCoefficient b S p := by
    rw [fderiv_eq_fderivWithin_strict hB hnuK hp]
    exact hJets.2.1
  constructor
  · rw [fderiv.log hLamDiff hLamPos.ne', smul_apply,
      smul_eq_mul, hLamJet]
    ring
  · have hNegDiff : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => -S.nu q.1 q.2) p := hNuDiff.neg
    rw [fderiv.log hNegDiff (neg_ne_zero.mpr hNuNeg.ne),
      smul_apply, smul_eq_mul, fderiv_fun_neg, neg_apply, hNuJet]
    ring

/-- On each strict subtriangle, the four mixed first-coordinate densities
are C¹. They are the common coefficient or its product with `φ`. This is the
C¹ differentiation bridge used in the Section 4 Jacobian transports. -/
theorem mixed_coordinate_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (C1Solution.canonicalMixedCoefficient b S)
      (openCoordTriangle 0 B) ∧
    ∀ p ∈ openCoordTriangle 0 B,
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
        (closedCoordTriangle 0 B) p) (1, 0) =
          C1Solution.canonicalMixedCoefficient b S p ∧
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1) =
          C1Solution.canonicalMixedCoefficient b S p ∧
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.alpha q.1 q.2)
        (closedCoordTriangle 0 B) p) (1, 0) =
          C1Solution.canonicalMixedCoefficient b S p * S.phi p.1 p.2 ∧
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1) =
          C1Solution.canonicalMixedCoefficient b S p * S.phi p.1 p.2 := by
  refine ⟨mixed_coefficient_contDiffOn hB hBb H, ?_⟩
  intro p hp
  simp only [openCoordTriangle, mem_ofPred_eq] at hp
  exact C1Solution.four_mixed_coordinate_jets hB hBb H
    ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

/-- The four §4 mixed transports support both orders of mixed differentiation
on every closed rectangle strictly inside a C¹ development. Endpoint
derivatives are relative to the rectangle; at interior points they are the
ordinary classical mixed partials. -/
theorem mixed_regularities {b B a a' d d' : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (haa' : a < a') (hdd' : d < d')
    (hR : Icc a a' ×ˢ Icc d d' ⊆ openCoordTriangle 0 B)
    {u v : ℝ} (hu : u ∈ Icc a a') (hv : v ∈ Icc d d') :
    let g := C1Solution.canonicalMixedCoefficient b S
    HasDerivWithinAt
      (fun x => (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (x, v)) (0, 1))
      ((fderiv ℝ g (u, v)) (0, 1)) (Icc a a') u ∧
    HasDerivWithinAt
      (fun y => (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, y)) (1, 0))
      ((fderiv ℝ g (u, v)) (1, 0)) (Icc d d') v ∧
    HasDerivWithinAt
      (fun x => (fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2) (x, v)) (0, 1))
      ((fderiv ℝ (fun p => g p * S.phi p.1 p.2) (u, v)) (0, 1))
      (Icc a a') u ∧
    HasDerivWithinAt
      (fun y => (fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, y)) (1, 0))
      ((fderiv ℝ (fun p => g p * S.phi p.1 p.2) (u, v)) (1, 0))
      (Icc d d') v := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  let g := C1Solution.canonicalMixedCoefficient b S
  let gp : ℝ × ℝ → ℝ := fun p => g p * S.phi p.1 p.2
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ K := by
    intro p hp
    have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
    exact ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  obtain ⟨hlamK, hnuK, hphiK, _, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  have hAlphaK := C1Solution.alpha_contDiffOn hB hBb H
  have hBetaK := C1Solution.beta_contDiffOn hB hBb H
  have hlam := hlamK.mono hsub
  have hnu := hnuK.mono hsub
  have halpha := hAlphaK.mono hsub
  have hbeta := hBetaK.mono hsub
  have hg := mixed_coefficient_contDiffOn hB hBb H
  have hgp : ContDiffOn ℝ 1 gp T := hg.mul (hphiK.mono hsub)
  have hJets (p : ℝ × ℝ) (hp : p ∈ T) :
      (fderiv ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2) p) (1, 0) = g p ∧
      (fderiv ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2) p) (0, 1) = g p ∧
      (fderiv ℝ (fun q : ℝ × ℝ => S.alpha q.1 q.2) p) (1, 0) = gp p ∧
      (fderiv ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2) p) (0, 1) = gp p := by
    have hpK : p ∈ K := hsub hp
    obtain ⟨hlu, hnv, hau, hbv⟩ :=
      C1Solution.four_mixed_coordinate_jets hB hBb H hpK
    rw [← fderiv_eq_fderivWithin_strict hB hlamK hp] at hlu
    rw [← fderiv_eq_fderivWithin_strict hB hnuK hp] at hnv
    rw [← fderiv_eq_fderivWithin_strict hB hAlphaK hp] at hau
    rw [← fderiv_eq_fderivWithin_strict hB hBetaK hp] at hbv
    exact ⟨hlu, hnv, hau, hbv⟩
  exact ⟨mixed_horizontal_on_rectangle hT hlam hg
      (fun p hp => (hJets p hp).1) haa' hdd' hR hu hv,
    mixed_vertical_on_rectangle hT hnu hg
      (fun p hp => (hJets p hp).2.1) haa' hdd' hR hu hv,
    mixed_horizontal_on_rectangle hT halpha hgp
      (fun p hp => (hJets p hp).2.2.1) haa' hdd' hR hu hv,
    mixed_vertical_on_rectangle hT hbeta hgp
      (fun p hp => (hJets p hp).2.2.2) haa' hdd' hR hu hv⟩

/-- The two logarithmic transports have the mixed derivatives and coordinate
interchanges used before expanding (4.7a,b). Each assertion is valid up to
the edge of a rectangle compactly contained in the strict triangle. -/
theorem log_transport_mixed_regularities {b B a a' d d' : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (haa' : a < a') (hdd' : d < d')
    (hR : Icc a a' ×ˢ Icc d d' ⊆ openCoordTriangle 0 B)
    {u v : ℝ} (hu : u ∈ Icc a a') (hv : v ∈ Icc d d') :
    let g := C1Solution.canonicalMixedCoefficient b S
    HasDerivWithinAt
      (fun x => (fderiv ℝ
        (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) (x, v)) (0, 1))
      ((fderiv ℝ (fun p => g p / S.lam p.1 p.2) (u, v)) (0, 1))
      (Icc a a') u ∧
    HasDerivWithinAt
      (fun y => (fderiv ℝ
        (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) (u, y)) (1, 0))
      ((fderiv ℝ (fun p => g p / S.nu p.1 p.2) (u, v)) (1, 0))
      (Icc d d') v := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  let g := C1Solution.canonicalMixedCoefficient b S
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ K := by
    intro p hp
    have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
    exact ⟨hparts.1.le, hparts.2.1.le, hparts.2.2.le⟩
  obtain ⟨hlamK, hnuK, _, _, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  have hlam : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) T :=
    (hlamK.mono hsub).log (fun p hp =>
      (H.solution.lam_pos p (by
        have hparts : 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B := hp
        exact ⟨hparts.1.le, hparts.2.1, hparts.2.2.trans hBb⟩)).ne')
  have hnu : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) T :=
    (hnuK.mono hsub).neg.log (fun p hp =>
      neg_ne_zero.mpr
        (C1Solution.nu_neg_closed_triangle hB hBb H (hsub hp)).ne)
  obtain ⟨hgLam, hgNu⟩ := log_transport_coefficients_contDiffOn hB hBb H
  have hJets (p : ℝ × ℝ) (hp : p ∈ T) :=
    log_transport_first_jets hB hBb H hp
  exact ⟨mixed_horizontal_on_rectangle hT hlam hgLam
      (fun p hp => (hJets p hp).1) haa' hdd' hR hu hv,
    mixed_vertical_on_rectangle hT hnu hgNu
      (fun p hp => (hJets p hp).2) haa' hdd' hR hu hv⟩

/-- The strict C¹ causal signs include the signs of both mixed expansion
derivatives. The pointwise mass ratio comes from the C¹-to-BV bridge and the
proved reduced-axis sign argument. -/
theorem c1_causal_signs {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B)
    (huv : p.1 < p.2) :
    S.nu p.1 p.2 < 0 ∧ 0 ≤ S.m p.1 p.2 ∧
    0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
    2 * S.m p.1 p.2 / S.r p.1 p.2 < 1 ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
      (closedCoordTriangle 0 B) p) (1, 0) ≤ 0 ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1) ≤ 0 := by
  have hparts : 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ B :=
    ⟨hp.1, huv, hp.2.2⟩
  have hpU : p ∈ developmentWithInitialEdge b :=
    ⟨hparts.1, hparts.2.1, hparts.2.2.trans_lt hBb⟩
  have hBV := H.isBVSolution_development (hB.trans hBb)
  obtain ⟨⟨c, hc, hsign⟩, _, _⟩ := source_axis_signs hBV
  obtain ⟨_, hnu, hm, hmu, hmuLt⟩ := hsign _ _ hpU
  have hnuNeg : S.nu p.1 p.2 < 0 := lt_of_le_of_lt hnu (by linarith)
  have hlamPos : 0 < S.lam p.1 p.2 := H.solution.lam_pos p hpU
  have hrPos : 0 < S.r p.1 p.2 := H.solution.radius_pos p hpU
  have hcoef : C1Solution.canonicalMixedCoefficient b S p ≤ 0 := by
    have hnumer :
        (2 * S.m p.1 p.2 / S.r p.1 p.2) *
          S.lam p.1 p.2 * S.nu p.1 p.2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hmu hlamPos.le) hnuNeg.le
    have hden : 0 <
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
          S.r p.1 p.2 := mul_pos (by linarith) hrPos
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
      hparts.1 hparts.2.1 hparts.2.2]
    exact div_nonpos_of_nonpos_of_nonneg hnumer hden.le
  have hpK : p ∈ closedCoordTriangle 0 B := hp
  obtain ⟨hlamJet, hnuJet, _, _⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  exact ⟨hnuNeg, hm, hmu, hmuLt,
    hlamJet.trans_le hcoef, hnuJet.trans_le hcoef⟩

end ChristodoulouBV

end
