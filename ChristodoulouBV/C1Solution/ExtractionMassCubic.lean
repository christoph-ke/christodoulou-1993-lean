module

public import ChristodoulouBV.C1Solution.ExtractionMass
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Cubic normalization of the canonical mass

The normalization records the mass's leading axis coefficient without
requiring second derivatives of the frozen fields.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The continuous vertical divided difference of the outgoing amplitude. -/
@[expose] noncomputable def normalizedTheta (B : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.verticalJetMean
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.theta q.1 q.2)
      (closedCoordTriangle 0 B)) p

/-- The normalized outgoing amplitude is continuous on a smaller triangle. -/
theorem normalizedTheta_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedTheta B S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  let f : ℝ × ℝ → ℝ := fun q => S.theta q.1 q.2
  have hC1 := (five_fields_contDiffOn hB hBb H).2.2.2.1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  exact intervalIntegral.continuousOn_verticalJetMean
    (hC1.continuousOn_fderivWithin hunique (by norm_num))

/-- The outgoing amplitude factors as the coordinate gap times its
continuous normalized derivative, including on the diagonal. -/
theorem theta_eq_gap_mul_normalizedTheta {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.theta p.1 p.2 = (p.2 - p.1) * normalizedTheta B S p := by
  let K := closedCoordTriangle 0 B
  let f : ℝ × ℝ → ℝ := fun q => S.theta q.1 q.2
  let G := fderivWithin ℝ f K
  have hC1 := (five_fields_contDiffOn hB hBb H).2.2.2.1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG : ContinuousOn G K :=
    hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) :=
    (hC1.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ q ∈ interior K, fderiv ℝ f q = G q := by
    intro q hq
    exact (fderivWithin_eq_fderiv (hunique q (interior_subset hq))
      (hdiff.differentiableAt (isOpen_interior.mem_nhds hq))).symm
  have hmain := intervalIntegral.sub_diag_eq_gap_mul_verticalJetMean hB
    hC1.continuousOn hG hdiff hderiv hp
  rcases p with ⟨u, v⟩
  have hdiag : u ∈ Icc 0 B := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  simpa only [f, theta_axis_eq_zero hB hBb H hdiag, sub_zero,
    normalizedTheta] using hmain

/-- The continuous coefficient of the quadratic outgoing mass density. -/
@[expose] noncomputable def normalizedMassDensity
    (b B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  (1 - canonicalMassRatio b S p) * (normalizedTheta B S p)^2 /
    (2 * S.lam p.1 p.2)

/-- The normalized quadratic mass density is continuous on the closed triangle. -/
theorem normalizedMassDensity_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedMassDensity b B S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hA : ContinuousOn (fun p : ℝ × ℝ =>
      1 - canonicalMassRatio b S p) K :=
    continuousOn_const.sub (canonicalMassRatio_continuousOn hB hBb H)
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  change ContinuousOn (fun p : ℝ × ℝ =>
    (1 - canonicalMassRatio b S p) * (normalizedTheta B S p)^2 /
      (2 * S.lam p.1 p.2)) K
  exact (hA.mul ((normalizedTheta_continuousOn hB hBb H).pow 2)).div
    (continuousOn_const.mul (five_fields_contDiffOn hB hBb H).1.continuousOn)
    (fun p hp => ne_of_gt (mul_pos (by norm_num) (hc.trans_le (hcl p hp))))

/-- The average quadratic coefficient along a normalized outgoing segment. -/
@[expose] noncomputable def normalizedMassCubic
    (b B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t^2 *
    normalizedMassDensity b B S (intervalIntegral.diagonalSegment p t)

/-- The normalized cubic mass coefficient is continuous on the closed triangle. -/
theorem normalizedMassCubic_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedMassCubic b B S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  let P := normalizedMassDensity b B S
  let fK : C(K, ℝ) := ⟨_, (normalizedMassDensity_continuousOn hB hBb H).domRestrict⟩
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq (isClosed_closedCoordTriangle 0 B)
  have hF_eq : ∀ p ∈ K, F p = P p := by
    intro p hp
    have h := congrArg (fun G : C(K, ℝ) => G ⟨p, hp⟩) hF
    simpa [fK, P] using h
  have hseg : Continuous (fun pt : (ℝ × ℝ) × ℝ =>
      intervalIntegral.diagonalSegment pt.1 pt.2) := by
    unfold intervalIntegral.diagonalSegment
    fun_prop
  have hcont : Continuous (fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..1, t^2 * F (intervalIntegral.diagonalSegment p t)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact (continuous_snd.pow 2).mul (F.continuous.comp hseg)
  apply hcont.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact congrArg (t^2 * ·) (hF_eq (intervalIntegral.diagonalSegment p t)
    (intervalIntegral.diagonalSegment_mem_closedCoordTriangle hp htI)).symm

/-- The outgoing canonical mass density has a quadratic coordinate-gap factor. -/
theorem canonicalMassOutgoingDensity_eq_gap_sq_mul_normalized {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMassOutgoingDensity b S p =
      (p.2 - p.1)^2 * normalizedMassDensity b B S p := by
  rw [canonicalMassOutgoingDensity, normalizedMassDensity,
    theta_eq_gap_mul_normalizedTheta hB hBb H hp]
  ring

/-- Canonical mass factors cubically with a continuous coefficient throughout
the smaller closed triangle. -/
theorem canonicalMass_eq_gap_cubed_mul_normalizedMassCubic {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMass b S p = (p.2 - p.1)^3 * normalizedMassCubic b B S p := by
  let K := closedCoordTriangle 0 B
  let m := canonicalMass b S
  let G := fderivWithin ℝ m K
  have hC1 := canonicalMass_contDiffOn hB hBb H
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG : ContinuousOn G K :=
    hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ m (interior K) :=
    (hC1.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ q ∈ interior K, fderiv ℝ m q = G q := by
    intro q hq
    exact (fderivWithin_eq_fderiv (hunique q (interior_subset hq))
      (hdiff.differentiableAt (isOpen_interior.mem_nhds hq))).symm
  have hmain := intervalIntegral.sub_diag_eq_gap_mul_verticalJetMean hB
    hC1.continuousOn hG hdiff hderiv hp
  rcases p with ⟨u, v⟩
  have huAxis : u ∈ Icc 0 B := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  rw [canonicalMass_axis] at hmain
  simp only [sub_zero] at hmain
  have hmean : intervalIntegral.verticalJetMean G (u, v) =
      (v - u)^2 * normalizedMassCubic b B S (u, v) := by
    rw [intervalIntegral.verticalJetMean, normalizedMassCubic,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hqK : intervalIntegral.diagonalSegment (u, v) t ∈ K :=
      intervalIntegral.diagonalSegment_mem_closedCoordTriangle hp htI
    have hjet := (canonicalMass_coordinate_jets hB hBb H hqK).2
    dsimp only
    have hjet' : (G (intervalIntegral.diagonalSegment (u, v) t)) (0, 1) =
        canonicalMassOutgoingDensity b S
          (intervalIntegral.diagonalSegment (u, v) t) := hjet
    rw [hjet', canonicalMassOutgoingDensity_eq_gap_sq_mul_normalized
      hB hBb H hqK]
    simp only [intervalIntegral.diagonalSegment]
    ring
  rw [hmean] at hmain
  nlinarith only [hmain]

/-- The continuous vertical divided difference of the incoming amplitude. -/
@[expose] noncomputable def normalizedZeta (B : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.verticalJetMean
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.zeta q.1 q.2)
      (closedCoordTriangle 0 B)) p

/-- The normalized incoming amplitude is continuous on a smaller triangle. -/
theorem normalizedZeta_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedZeta B S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hC1 := (five_fields_contDiffOn hB hBb H).2.2.2.2
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  exact intervalIntegral.continuousOn_verticalJetMean
    (hC1.continuousOn_fderivWithin hunique (by norm_num))

/-- The incoming amplitude also factors through the coordinate gap. -/
theorem zeta_eq_gap_mul_normalizedZeta {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.zeta p.1 p.2 = (p.2 - p.1) * normalizedZeta B S p := by
  let K := closedCoordTriangle 0 B
  let f : ℝ × ℝ → ℝ := fun q => S.zeta q.1 q.2
  let G := fderivWithin ℝ f K
  have hC1 := (five_fields_contDiffOn hB hBb H).2.2.2.2
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG : ContinuousOn G K :=
    hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) :=
    (hC1.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ q ∈ interior K, fderiv ℝ f q = G q := by
    intro q hq
    exact (fderivWithin_eq_fderiv (hunique q (interior_subset hq))
      (hdiff.differentiableAt (isOpen_interior.mem_nhds hq))).symm
  have hmain := intervalIntegral.sub_diag_eq_gap_mul_verticalJetMean hB
    hC1.continuousOn hG hdiff hderiv hp
  rcases p with ⟨u, v⟩
  have hdiag : u ∈ Icc 0 B := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  simpa only [f, zeta_axis_eq_zero hB hBb H hdiag, sub_zero,
    normalizedZeta] using hmain

/-- The continuous coefficient of the quadratic incoming mass density. -/
@[expose] noncomputable def normalizedIncomingMassDensity
    (b B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  (1 - canonicalMassRatio b S p) * (normalizedZeta B S p)^2 /
    (2 * S.nu p.1 p.2)

/-- The normalized incoming mass density is continuous on the triangle. -/
theorem normalizedIncomingMassDensity_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (normalizedIncomingMassDensity b B S)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hA : ContinuousOn (fun p : ℝ × ℝ =>
      1 - canonicalMassRatio b S p) K :=
    continuousOn_const.sub (canonicalMassRatio_continuousOn hB hBb H)
  change ContinuousOn (fun p : ℝ × ℝ =>
    (1 - canonicalMassRatio b S p) * (normalizedZeta B S p)^2 /
      (2 * S.nu p.1 p.2)) K
  exact (hA.mul ((normalizedZeta_continuousOn hB hBb H).pow 2)).div
    (continuousOn_const.mul (five_fields_contDiffOn hB hBb H).2.1.continuousOn)
    (fun p hp => ne_of_lt (mul_neg_of_pos_of_neg (by norm_num)
      (nu_neg_closed_triangle hB hBb H hp)))

/-- The incoming canonical mass density has a quadratic coordinate-gap factor. -/
theorem canonicalMassIncomingDensity_eq_gap_sq_mul_normalized {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalMassIncomingDensity b S p =
      (p.2 - p.1)^2 * normalizedIncomingMassDensity b B S p := by
  rw [canonicalMassIncomingDensity, normalizedIncomingMassDensity,
    zeta_eq_gap_mul_normalizedZeta hB hBb H hp]
  ring

end ChristodoulouBV.C1Solution

end
