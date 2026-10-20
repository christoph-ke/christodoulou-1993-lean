module

public import ChristodoulouBV.C1Solution.ExtractionCore
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMean
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Boundary consequences of C¹ extraction

The regular-axis identities in this module concern the canonical outgoing
integrals and the five actual C¹ fields.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The actual outgoing quotient `h = α/λ`. -/
@[expose] noncomputable def outgoingQuotient (S : Fields) (p : ℝ × ℝ) : ℝ :=
  S.alpha p.1 p.2 / S.lam p.1 p.2

/-- The scalar field is the positive weighted mean of the actual outgoing
quotient throughout the closed triangle. -/
theorem phi_eq_weightedDiagonalMean {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.phi p.1 p.2 = intervalIntegral.weightedDiagonalMean
      (fun q => S.lam q.1 q.2) (outgoingQuotient S) p := by
  let K := closedCoordTriangle 0 B
  let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let h := outgoingQuotient S
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hw : ContinuousOn w K := (five_fields_contDiffOn hB hBb H).1.continuousOn
  have hh : ContinuousOn h K := (alpha_div_lam_contDiffOn hB hBb H).continuousOn
  have hmean : ContinuousOn (intervalIntegral.weightedDiagonalMean w h) K :=
    intervalIntegral.continuousOn_weightedDiagonalMean hw hh hcl hc
  have hphi : ContinuousOn (fun q : ℝ × ℝ => S.phi q.1 q.2) K :=
    (five_fields_contDiffOn hB hBb H).2.2.1.continuousOn
  have hopen : EqOn (fun q : ℝ × ℝ => S.phi q.1 q.2)
      (intervalIntegral.weightedDiagonalMean w h) (openCoordTriangle 0 B) := by
    rintro ⟨u, v⟩ hq
    have hparts : 0 < u ∧ u < v ∧ v < B := hq
    have hrad : 0 < canonicalRadius S (u, v) :=
      intervalIntegral.weightedDiagonalRadius_pos hw hcl hc
        hparts.1.le hparts.2.1 hparts.2.2.le
    have hnum : intervalIntegral.weightedDiagonalNumerator w h (u, v) =
        canonicalScalarRadius S (u, v) := by
      change (∫ s in u..v, S.lam u s *
        (S.alpha u s / S.lam u s)) = ∫ s in u..v, S.alpha u s
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hparts.2.1.le] at hs
      have hsK : (u, s) ∈ K :=
        ⟨hparts.1.le, hs.1, hs.2.trans hparts.2.2.le⟩
      have hl : S.lam u s ≠ 0 := ne_of_gt (hc.trans_le (hcl (u, s) hsK))
      field_simp
    have hpsi := canonicalScalarRadius_eq_radius_mul_phi hB hBb H
      hparts.1.le hparts.2.1 hparts.2.2.le
    rw [← canonicalRadius_eq_radius hB hBb H hparts.1.le
      hparts.2.1 hparts.2.2.le] at hpsi
    have hdiv : S.phi u v =
        canonicalScalarRadius S (u, v) / canonicalRadius S (u, v) := by
      rw [hpsi]
      field_simp
    rw [intervalIntegral.weightedDiagonalMean_eq_div hparts.2.1.ne]
    change S.phi u v = intervalIntegral.weightedDiagonalNumerator w h (u, v) /
      canonicalRadius S (u, v)
    rw [hnum]
    exact hdiv
  have hEq := hopen.of_subset_closure hphi hmean
    (fun _ hq => interior_subset (by
      change _ ∈ interior (closedCoordTriangle 0 B)
      rw [interior_closedCoordTriangle]
      exact hq))
    (by change closedCoordTriangle 0 B ⊆ closure (openCoordTriangle 0 B)
        rw [closure_openCoordTriangle hB])
  exact hEq hp

private theorem closed_triangle_c1_jet_data {B : ℝ} (hB : 0 < B)
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B)) :
    ContinuousOn (fderivWithin ℝ f (closedCoordTriangle 0 B))
      (closedCoordTriangle 0 B) ∧
    DifferentiableOn ℝ f (interior (closedCoordTriangle 0 B)) ∧
    ∀ p ∈ interior (closedCoordTriangle 0 B),
      fderiv ℝ f p = fderivWithin ℝ f (closedCoordTriangle 0 B) p := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG := hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) := by
    intro p hp
    exact (hf.differentiableOn (by norm_num) p (interior_subset hp)).mono
      (interior_subset : interior K ⊆ K)
  refine ⟨hG, hdiff, ?_⟩
  intro p hp
  exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
    ((hdiff p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm

/-- The axis scalar jets are those of the outgoing weighted mean. -/
theorem phi_axis_jets {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) =
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) / 2 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (1, 0) +
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) / 2 := by
  let K := closedCoordTriangle 0 B
  let w : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let h := outgoingQuotient S
  have hwC1 := (five_fields_contDiffOn hB hBb H).1
  have hhC1 := alpha_div_lam_contDiffOn hB hBb H
  obtain ⟨hwG, hwdiff, hwderiv⟩ := closed_triangle_c1_jet_data hB hwC1
  obtain ⟨hhG, hhdiff, hhderiv⟩ := closed_triangle_c1_jet_data hB hhC1
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hmean := intervalIntegral.weightedDiagonalMean_diag_coordinate_derivatives hB
    hwC1.continuousOn hhC1.continuousOn hwG hhG hwdiff hhdiff
    hwderiv hhderiv hcl hc hu.1 hu.2
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hEq : EqOn (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (intervalIntegral.weightedDiagonalMean w h) K :=
    fun p hp => phi_eq_weightedDiagonalMean hB hBb H hp
  have hjet := fderivWithin_congr' (𝕜 := ℝ) hEq hp
  constructor
  · rw [hjet]
    exact hmean.1
  · rw [hjet]
    exact hmean.2.1

/-- The canonical scalar radius is the canonical radius times the actual scalar
field on the entire closed triangle. This equality does not use boundary values
of the frozen total radius. -/
theorem canonicalScalarRadius_eq_canonicalRadius_mul_phi
    {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    canonicalScalarRadius S p = canonicalRadius S p * S.phi p.1 p.2 := by
  let K := closedCoordTriangle 0 B
  have hpsi : ContinuousOn (canonicalScalarRadius S) K :=
    (canonicalScalarRadius_contDiffOn hB hBb H).continuousOn
  have hprod : ContinuousOn
      (fun q : ℝ × ℝ => canonicalRadius S q * S.phi q.1 q.2) K :=
    (canonicalRadius_contDiffOn hB hBb H).continuousOn.mul
      (five_fields_contDiffOn hB hBb H).2.2.1.continuousOn
  have hEqOpen : EqOn (canonicalScalarRadius S)
      (fun q : ℝ × ℝ => canonicalRadius S q * S.phi q.1 q.2)
      (openCoordTriangle 0 B) := by
    rintro ⟨u, v⟩ hq
    have hparts : 0 < u ∧ u < v ∧ v < B := hq
    rw [canonicalScalarRadius_eq_radius_mul_phi hB hBb H hparts.1.le
        hparts.2.1 hparts.2.2.le]
    change S.r u v * S.phi u v = canonicalRadius S (u, v) * S.phi u v
    rw [canonicalRadius_eq_radius hB hBb H hparts.1.le hparts.2.1 hparts.2.2.le]
  have hEq := hEqOpen.of_subset_closure hpsi hprod
    (fun _ hq => interior_subset (by
      change _ ∈ interior (closedCoordTriangle 0 B)
      rw [interior_closedCoordTriangle]
      exact hq))
    (by change closedCoordTriangle 0 B ⊆ closure (openCoordTriangle 0 B)
        rw [closure_openCoordTriangle hB])
  exact hEq hp

/-- At an axis point, the canonical scalar-radius jet is the scalar trace times
the canonical radius jet. -/
theorem canonicalScalarRadius_axis_jet {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) (e : ℝ × ℝ) :
    (fderivWithin ℝ (canonicalScalarRadius S) (closedCoordTriangle 0 B) (u, u)) e =
      S.phi u u *
        (fderivWithin ℝ (canonicalRadius S) (closedCoordTriangle 0 B) (u, u)) e := by
  let K := closedCoordTriangle 0 B
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hunique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, u) hp
  have hrDiff : DifferentiableWithinAt ℝ (canonicalRadius S) K (u, u) :=
    (canonicalRadius_contDiffOn hB hBb H).differentiableOn (by norm_num) (u, u) hp
  have hphiDiff : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => S.phi q.1 q.2) K (u, u) :=
    (five_fields_contDiffOn hB hBb H).2.2.1.differentiableOn (by norm_num) (u, u) hp
  have hEq : EqOn (canonicalScalarRadius S)
      (fun q : ℝ × ℝ => canonicalRadius S q * S.phi q.1 q.2) K :=
    fun q hq => canonicalScalarRadius_eq_canonicalRadius_mul_phi hB hBb H hq
  rw [fderivWithin_congr' hEq hp]
  change (fderivWithin ℝ
    (canonicalRadius S * fun q : ℝ × ℝ => S.phi q.1 q.2) K (u, u)) e = _
  rw [fderivWithin_mul hunique hrDiff hphiDiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [(canonical_outgoing_axis S u).1]
  ring

/-- Product differentiation identifies the scalar-radius jet throughout the
closed triangle using the canonical radius. -/
theorem canonicalScalarRadius_product_jet {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) (e : ℝ × ℝ) :
    (fderivWithin ℝ (canonicalScalarRadius S) (closedCoordTriangle 0 B) p) e =
      S.phi p.1 p.2 *
        (fderivWithin ℝ (canonicalRadius S) (closedCoordTriangle 0 B) p) e +
      canonicalRadius S p *
        (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
          (closedCoordTriangle 0 B) p) e := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB) p hp
  have hrDiff : DifferentiableWithinAt ℝ (canonicalRadius S) K p :=
    (canonicalRadius_contDiffOn hB hBb H).differentiableOn (by norm_num) p hp
  have hphiDiff : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => S.phi q.1 q.2) K p :=
    (five_fields_contDiffOn hB hBb H).2.2.1.differentiableOn (by norm_num) p hp
  have hEq : EqOn (canonicalScalarRadius S)
      (fun q : ℝ × ℝ => canonicalRadius S q * S.phi q.1 q.2) K :=
    fun q hq => canonicalScalarRadius_eq_canonicalRadius_mul_phi hB hBb H hq
  rw [fderivWithin_congr' hEq hp]
  change (fderivWithin ℝ
    (canonicalRadius S * fun q : ℝ × ℝ => S.phi q.1 q.2) K p) e = _
  rw [fderivWithin_mul hunique hrDiff hphiDiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The outgoing amplitude is the canonical radius times the outgoing scalar jet. -/
theorem theta_eq_canonicalRadius_mul_phi_vertical_jet
    {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.theta p.1 p.2 = canonicalRadius S p *
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1) := by
  have h := canonicalScalarRadius_product_jet hB hBb H hp (0, 1)
  rw [canonicalScalarRadius_vertical_jet hB hBb H hp,
    canonicalRadius_vertical_jet hB hBb H hp] at h
  unfold Fields.theta
  linarith only [h]

/-- The incoming amplitude is the canonical radius times the incoming scalar jet. -/
theorem zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.zeta p.1 p.2 = canonicalRadius S p *
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) p) (1, 0) := by
  have h := canonicalScalarRadius_product_jet hB hBb H hp (1, 0)
  rw [canonicalScalarRadius_horizontal_jet hB hBb H hp,
    canonicalRadius_horizontal_jet hB hBb H hp] at h
  unfold Fields.zeta
  linarith only [h]

/-- The outgoing scalar derivative equals `λφ` on the regular axis. -/
theorem alpha_eq_lam_mul_phi_axis {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) : S.alpha u u = S.lam u u * S.phi u u := by
  have hp : (u, u) ∈ closedCoordTriangle 0 B := ⟨hu.1, le_rfl, hu.2⟩
  have h := canonicalScalarRadius_axis_jet hB hBb H hu (0, 1)
  rw [canonicalScalarRadius_vertical_jet hB hBb H hp,
    canonicalRadius_vertical_jet hB hBb H hp] at h
  nlinarith

/-- The incoming scalar derivative equals `νφ` on the regular axis. -/
theorem beta_eq_nu_mul_phi_axis {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) : S.beta u u = S.nu u u * S.phi u u := by
  have hp : (u, u) ∈ closedCoordTriangle 0 B := ⟨hu.1, le_rfl, hu.2⟩
  have h := canonicalScalarRadius_axis_jet hB hBb H hu (1, 0)
  rw [canonicalScalarRadius_horizontal_jet hB hBb H hp,
    canonicalRadius_horizontal_jet hB hBb H hp] at h
  nlinarith

/-- The outgoing scalar amplitude vanishes on the regular axis. -/
theorem theta_axis_eq_zero {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) : S.theta u u = 0 := by
  rw [Fields.theta, alpha_eq_lam_mul_phi_axis hB hBb H hu]
  ring

/-- The incoming scalar amplitude vanishes on the regular axis. -/
theorem zeta_axis_eq_zero {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) : S.zeta u u = 0 := by
  rw [Fields.zeta, beta_eq_nu_mul_phi_axis hB hBb H hu]
  ring

/-- The incoming expansion is strictly negative everywhere on a smaller
closed triangle, including the diagonal and its two vertices. -/
theorem nu_neg_closed_triangle {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.nu p.1 p.2 < 0 := by
  rcases p with ⟨u, v⟩
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · exact nu_neg hB hBb H hp.1 huv hp.2.2
  · subst v
    rw [nu_eq_neg_lam_axis hB hBb H ⟨hp.1, hp.2.2⟩]
    obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
    exact neg_neg_of_pos (hc.trans_le (hcl (u, u) hp))

/-- Compactness turns the strict incoming-expansion sign into a uniform
positive lower bound. -/
theorem exists_neg_nu_lower_bound {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p ∈ closedCoordTriangle 0 B, c ≤ -S.nu p.1 p.2 := by
  let K := closedCoordTriangle 0 B
  have hnonempty : K.Nonempty := ⟨(0, 0), by
    change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ B
    exact ⟨le_rfl, le_rfl, hB.le⟩⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => -S.nu p.1 p.2) K :=
    (five_fields_contDiffOn hB hBb H).2.1.continuousOn.neg
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedCoordTriangle 0 B).exists_isMinOn
    hnonempty hcont
  refine ⟨-S.nu p.1 p.2, neg_pos.mpr (nu_neg_closed_triangle hB hBb H hp), ?_⟩
  intro q hq
  exact hmin hq

/-- The frozen mass is nonnegative at every in-domain point of a smaller
triangle. The statement concerns only in-domain total-field values. -/
theorem mass_nonneg {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    0 ≤ S.m u v := by
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have haxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq huvU] using
      H.solution.mass_axis u (H.solution.development.axis_mem huvU)
  have hbound : ∀ᶠ a in 𝓝[>] u, S.m u a ≤ S.m u v := by
    filter_upwards [Ioo_mem_nhdsGT huv] with a ha
    have hseg := H.solution.development.out_seg_subset huvU
      ha.1 ha.2.le le_rfl
    have hprim := H.solution.mass_out u a v ha.2.le hseg
    have hnonneg : 0 ≤ ∫ t in a..v,
        (1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 /
          (2 * S.lam u t) := by
      apply intervalIntegral.integral_nonneg ha.2.le
      intro t ht
      have htU := H.solution.development.outgoing_mem huvU
        (ha.1.trans_le ht.1) ht.2
      have hr : 0 < S.r u t := H.solution.radius_pos (u, t) htU
      have hl : 0 < S.lam u t := H.solution.lam_pos (u, t) htU
      have hgap := mass_gap_pos hB hBb H hu (ha.1.trans_le ht.1)
        (ht.2.trans hv)
      have hA : 0 ≤ 1 - 2 * S.m u t / S.r u t := by
        have heq : 1 - 2 * S.m u t / S.r u t =
            (S.r u t - 2 * S.m u t) / S.r u t := by
          field_simp
        rw [heq]
        exact (div_pos hgap hr).le
      exact div_nonneg (mul_nonneg hA (sq_nonneg _))
        (mul_nonneg (by norm_num) hl.le)
    linarith only [hprim.2, hnonneg]
  exact le_of_tendsto haxis hbound

/-- The outgoing scalar amplitude vanishes linearly at the axis on every
smaller closed triangle. -/
theorem exists_theta_linear_axis_bound {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ closedCoordTriangle 0 B,
      |S.theta p.1 p.2| ≤ M * (p.2 - p.1) := by
  let K := closedCoordTriangle 0 B
  let f : ℝ × ℝ → ℝ := fun p => S.theta p.1 p.2
  let G := fderivWithin ℝ f K
  have hC1 : ContDiffOn ℝ 1 f K :=
    (five_fields_contDiffOn hB hBb H).2.2.2.1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hGcont : ContinuousOn G K :=
    hC1.continuousOn_fderivWithin hunique (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedCoordTriangle 0 B).exists_bound_of_continuousOn
    (hGcont.clm_apply continuousOn_const)
  have hMnonneg : 0 ≤ M := by
    have h0 : (0, 0) ∈ K := ⟨le_rfl, le_rfl, hB.le⟩
    exact (norm_nonneg (G (0, 0) (0, 1))).trans (hM (0, 0) h0)
  refine ⟨M, hMnonneg, ?_⟩
  rintro ⟨u, v⟩ hp
  have hjet : ∀ p ∈ K, HasFDerivWithinAt f (G p) K p := by
    intro p hp
    exact (hC1.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hbound := intervalIntegral.norm_sub_vertical_le_of_jet hjet hM
    hp.1 le_rfl hp.2.1 hp.2.2
  have haxis : f (u, u) = 0 := theta_axis_eq_zero hB hBb H
    ⟨hp.1, hp.2.1.trans hp.2.2⟩
  simpa only [f, haxis, sub_zero, Real.norm_eq_abs] using hbound

/-- The in-domain mass vanishes cubically toward the regular axis. -/
theorem exists_mass_cubic_axis_bound {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, 0 ≤ u → u < v → v ≤ B →
      0 ≤ S.m u v ∧ S.m u v ≤ C * (v - u)^3 := by
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  obtain ⟨M, hM, htheta⟩ := exists_theta_linear_axis_bound hB hBb H
  let C : ℝ := M^2 / (2 * c)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u v hu huv hv
  have hmnonneg := mass_nonneg hB hBb H hu huv hv
  refine ⟨hmnonneg, ?_⟩
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have hmAxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq huvU] using
      H.solution.mass_axis u (H.solution.development.axis_mem huvU)
  have hpoly : Tendsto (fun a : ℝ => S.m u a +
      C * (v - u)^2 * (v - a)) (𝓝[>] u)
      (𝓝 (C * (v - u)^3)) := by
    have hcont0 : Continuous (fun a : ℝ => C * (v - u)^2 * (v - a)) := by
      fun_prop
    have hcont : Tendsto (fun a : ℝ => C * (v - u)^2 * (v - a))
        (𝓝[>] u) (𝓝 (C * (v - u)^2 * (v - u))) :=
      (hcont0.tendsto u).mono_left inf_le_left
    simpa [pow_succ, mul_assoc] using hmAxis.add hcont
  have hbound : ∀ᶠ a in 𝓝[>] u,
      S.m u v ≤ S.m u a + C * (v - u)^2 * (v - a) := by
    filter_upwards [Ioo_mem_nhdsGT huv] with a ha
    have hseg := H.solution.development.out_seg_subset huvU
      ha.1 ha.2.le le_rfl
    have hprim := H.solution.mass_out u a v ha.2.le hseg
    have hqbound : ∀ t ∈ Icc a v,
        (1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 /
          (2 * S.lam u t) ≤ C * (v - u)^2 := by
      intro t ht
      have hut : u < t := ha.1.trans_le ht.1
      have htK : (u, t) ∈ closedCoordTriangle 0 B :=
        ⟨hu, hut.le, ht.2.trans hv⟩
      have hr : 0 < S.r u t := H.solution.radius_pos (u, t)
        (H.solution.development.outgoing_mem huvU hut ht.2)
      have hmt : 0 ≤ S.m u t := mass_nonneg hB hBb H hu hut (ht.2.trans hv)
      have hgap := mass_gap_pos hB hBb H hu hut (ht.2.trans hv)
      have hA : 0 ≤ 1 - 2 * S.m u t / S.r u t := by
        have heq : 1 - 2 * S.m u t / S.r u t =
            (S.r u t - 2 * S.m u t) / S.r u t := by field_simp
        rw [heq]
        exact (div_pos hgap hr).le
      have hAone : 1 - 2 * S.m u t / S.r u t ≤ 1 := by
        have hratio : 0 ≤ 2 * S.m u t / S.r u t :=
          div_nonneg (mul_nonneg (by norm_num) hmt) hr.le
        linarith
      have hthetaT := htheta (u, t) htK
      have htd : 0 ≤ t - u := sub_nonneg.mpr hut.le
      have htdv : t - u ≤ v - u := sub_le_sub_right ht.2 u
      have hMD : 0 ≤ M * (v - u) := mul_nonneg hM (sub_nonneg.mpr huv.le)
      have hthetaSq : (S.theta u t)^2 ≤ M^2 * (v - u)^2 := by
        have hsmall : |S.theta u t| ≤ M * (v - u) :=
          hthetaT.trans (mul_le_mul_of_nonneg_left htdv hM)
        have hsquare := (sq_le_sq₀ (abs_nonneg (S.theta u t)) hMD).2 hsmall
        nlinarith only [hsquare, sq_abs (S.theta u t)]
      have hnum : (1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 ≤
          M^2 * (v - u)^2 := by
        calc
          _ ≤ 1 * (S.theta u t)^2 :=
            mul_le_mul_of_nonneg_right hAone (sq_nonneg _)
          _ = (S.theta u t)^2 := one_mul _
          _ ≤ M^2 * (v - u)^2 := hthetaSq
      have hlamT : c ≤ S.lam u t := hcl (u, t) htK
      have hden : 0 < 2 * S.lam u t := by
        have hlpos : 0 < S.lam u t := hc.trans_le hlamT
        positivity
      have hnumNonneg : 0 ≤ (1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 :=
        mul_nonneg hA (sq_nonneg _)
      calc
        _ ≤ (M^2 * (v - u)^2) / (2 * S.lam u t) :=
          div_le_div_of_nonneg_right hnum hden.le
        _ ≤ (M^2 * (v - u)^2) / (2 * c) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hlamT (by norm_num))
        _ = C * (v - u)^2 := by dsimp [C]; ring
    have hIntBound := intervalIntegral.integral_mono_on ha.2.le hprim.1
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => C * (v - u)^2) volume a v) hqbound
    rw [intervalIntegral.integral_const] at hIntBound
    simp only [smul_eq_mul] at hIntBound
    linarith only [hprim.2, hIntBound]
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hpoly hbound

/-- A totalization of the canonical mass: it uses frozen mass values only
inside the development and is zero elsewhere. On every smaller closed
triangle, the only added values are the zero axis trace. -/
@[expose] noncomputable def canonicalMass (b : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  by
    classical
    exact if p ∈ developmentWithInitialEdge b then S.m p.1 p.2 else 0

/-- The canonical mass agrees with the total mass on the frozen domain. -/
theorem canonicalMass_eq_mass {b : ℝ} {S : Fields} {p : ℝ × ℝ}
    (hp : p ∈ developmentWithInitialEdge b) :
    canonicalMass b S p = S.m p.1 p.2 := by
  simp [canonicalMass, hp]

/-- The canonical mass, rather than the frozen total mass, is zero on the axis. -/
theorem canonicalMass_axis (b : ℝ) (S : Fields) (u : ℝ) :
    canonicalMass b S (u, u) = 0 := by
  simp [canonicalMass, developmentWithInitialEdge]

/-- The canonical mass has a uniform cubic axis bound on every smaller
closed triangle. -/
theorem exists_canonicalMass_cubic_axis_bound {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ closedCoordTriangle 0 B,
      0 ≤ canonicalMass b S p ∧
        canonicalMass b S p ≤ C * (p.2 - p.1)^3 := by
  obtain ⟨C, hC, hm⟩ := exists_mass_cubic_axis_bound hB hBb H
  refine ⟨C, hC, ?_⟩
  rintro ⟨u, v⟩ hp
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hU : (u, v) ∈ developmentWithInitialEdge b :=
      ⟨hp.1, huv, hp.2.2.trans_lt hBb⟩
    rw [canonicalMass_eq_mass hU]
    exact hm u v hp.1 huv hp.2.2
  · subst v
    simp [canonicalMass_axis]

/-- The canonical mass is continuous at every axis point relative to a
smaller closed triangle. -/
theorem canonicalMass_continuousWithinAt_axis {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (_hu : u ∈ Icc 0 B) :
    ContinuousWithinAt (canonicalMass b S) (closedCoordTriangle 0 B) (u, u) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨C, hC, hbound⟩ := exists_canonicalMass_cubic_axis_bound hB hBb H
  have hgap : Tendsto (fun p : ℝ × ℝ => p.2 - p.1)
      (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous (fun p : ℝ × ℝ => p.2 - p.1) := by fun_prop
    change Tendsto (fun p : ℝ × ℝ => p.2 - p.1)
      (𝓝 (u, u) ⊓ 𝓟 K) (𝓝 (0 : ℝ))
    simpa using (hcont.tendsto (u, u)).mono_left inf_le_left
  have hcubic : Tendsto (fun p : ℝ × ℝ => C * (p.2 - p.1)^3)
      (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) := by
    simpa using (hgap.pow 3).const_mul C
  have hnonneg : ∀ᶠ p in 𝓝[K] (u, u), 0 ≤ canonicalMass b S p := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hbound p hp).1
  have hupper : ∀ᶠ p in 𝓝[K] (u, u),
      canonicalMass b S p ≤ C * (p.2 - p.1)^3 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hbound p hp).2
  have hlim : Tendsto (canonicalMass b S) (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) :=
    squeeze_zero' hnonneg hupper hcubic
  change Tendsto (canonicalMass b S) (𝓝[K] (u, u))
    (𝓝 (canonicalMass b S (u, u)))
  rw [canonicalMass_axis]
  exact hlim

end ChristodoulouBV.C1Solution

end
