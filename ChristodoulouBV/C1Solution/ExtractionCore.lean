module

public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanIntegral
public import ChristodoulouBV.BVSolution.Geometry
import ChristodoulouBV.BVSolution.SignAux
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Extraction from a frozen C¹ solution

The radius, mass, and scalar radius are represented by canonical extensions.
Their values outside the solution domain are not constrained by `IsC1Solution`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The closed smaller triangle lies in the closure of the frozen development. -/
theorem closedCoordTriangle_subset_closure_developmentWithInitialEdge
    {b B : ℝ} (hB : 0 < B) (hBb : B < b) :
    closedCoordTriangle 0 B ⊆ closure (developmentWithInitialEdge b) := by
  have hb : 0 < b := lt_trans hB hBb
  rw [developmentWithInitialEdge, closure_initialEdgeTriangle hb]
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.trans hBb.le⟩

/-- Every strict point of a smaller closed triangle is in the frozen development. -/
theorem openCoordTriangle_subset_developmentWithInitialEdge
    {b B : ℝ} (hBb : B < b) :
    openCoordTriangle 0 B ⊆ developmentWithInitialEdge b := by
  intro p hp
  exact ⟨hp.1.le, hp.2.1, hp.2.2.trans hBb⟩

/-- The frozen outgoing expansion has a positive lower bound on every smaller
closed triangle, including the axis and top edge. -/
theorem exists_lam_lower_bound {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2 := by
  obtain ⟨c, hc, hcl⟩ := H.lam_bounded_below
  refine ⟨c, hc, ?_⟩
  intro p hp
  have hcont : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closure (developmentWithInitialEdge b)) := H.lam_c1.continuousOn
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (developmentWithInitialEdge b) (Set.Ici c) := fun q hq => hcl q hq
  have hpcl := closedCoordTriangle_subset_closure_developmentWithInitialEdge
    hB hBb hp
  have h := hmap.closure_of_continuousOn hcont hpcl
  simpa only [isClosed_Ici.closure_eq, Set.mem_Ici] using h

/-- The frozen C¹ clauses restrict to every smaller closed triangle. -/
theorem five_fields_contDiffOn {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2) (closedCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2) (closedCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) (closedCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) (closedCoordTriangle 0 B) ∧
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.zeta p.1 p.2) (closedCoordTriangle 0 B) := by
  have hsub := closedCoordTriangle_subset_closure_developmentWithInitialEdge hB hBb
  exact ⟨H.lam_c1.mono hsub, H.nu_c1.mono hsub, H.phi_c1.mono hsub,
    H.theta_c1.mono hsub, H.zeta_c1.mono hsub⟩

/-- The actual outgoing scalar derivative is C¹ on the closed triangle. -/
theorem alpha_contDiffOn {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
      (closedCoordTriangle 0 B) := by
  obtain ⟨hlam, _, hphi, htheta, _⟩ := five_fields_contDiffOn hB hBb H
  have h := htheta.add (hlam.mul hphi)
  apply h.congr
  intro p hp
  simp only [Fields.theta]
  ring

/-- The actual incoming scalar derivative is C¹ on the closed triangle. -/
theorem beta_contDiffOn {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2)
      (closedCoordTriangle 0 B) := by
  obtain ⟨_, hnu, hphi, _, hzeta⟩ := five_fields_contDiffOn hB hBb H
  have h := hzeta.add (hnu.mul hphi)
  apply h.congr
  intro p hp
  simp only [Fields.zeta]
  ring

/-- The outgoing quotient `h = α / λ` is C¹ on a smaller closed triangle. -/
theorem alpha_div_lam_contDiffOn {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2 / S.lam p.1 p.2)
      (closedCoordTriangle 0 B) := by
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hne : ∀ p ∈ closedCoordTriangle 0 B, S.lam p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hcl p hp))
  exact (alpha_contDiffOn hB hBb H).div
    (five_fields_contDiffOn hB hBb H).1 hne

/-- The canonical radius is the outgoing integral of the actual expansion. -/
@[expose] noncomputable def canonicalRadius (S : Fields) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalRadius (fun q => S.lam q.1 q.2) p

/-- The canonical scalar radius is the outgoing integral of the actual scalar derivative. -/
@[expose] noncomputable def canonicalScalarRadius (S : Fields) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalRadius (fun q => S.alpha q.1 q.2) p

/-- Both canonical outgoing integrals vanish on the axis. -/
theorem canonical_outgoing_axis (S : Fields) (u : ℝ) :
    canonicalRadius S (u, u) = 0 ∧ canonicalScalarRadius S (u, u) = 0 := by
  simp [canonicalRadius, canonicalScalarRadius,
    intervalIntegral.weightedDiagonalRadius]

/-- The canonical radius grows at least linearly away from the axis. -/
theorem canonicalRadius_lower_bound {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ closedCoordTriangle 0 B,
      c * (p.2 - p.1) ≤ canonicalRadius S p := by
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  refine ⟨c, hc, ?_⟩
  rintro ⟨u, v⟩ hp
  exact intervalIntegral.mul_sub_le_weightedDiagonalRadius
    (five_fields_contDiffOn hB hBb H).1.continuousOn hcl hp.1 hp.2.1 hp.2.2

/-- A C¹ integrand on a closed coordinate triangle has a C¹ outgoing
integral, including on the diagonal and at both vertices. -/
theorem weightedDiagonalRadius_contDiffOn {B : ℝ} (hB : 0 < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B)) :
    ContDiffOn ℝ 1 (intervalIntegral.weightedDiagonalRadius f)
      (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  let G := fderivWithin ℝ f K
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG : ContinuousOn G K :=
    hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) := by
    intro p hp
    exact (hf.differentiableOn (by norm_num) p (interior_subset hp)).mono
      (interior_subset : interior K ⊆ K)
  have hderiv : ∀ p ∈ interior K, fderiv ℝ f p = G p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdiff p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hint := intervalIntegral.contDiffOn_integral_diagonalSegment hB
    hf.continuousOn hG hdiff hderiv
  have hgap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.2 - p.1) K := by
    fun_prop
  have hprod := hgap.mul hint
  apply hprod.congr
  intro p hp
  rcases p with ⟨u, v⟩
  exact intervalIntegral.weightedDiagonalRadius_eq_mul_integral f u v

/-- The canonical radius has a continuous first jet on a closed smaller triangle. -/
theorem canonicalRadius_contDiffOn {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalRadius S) (closedCoordTriangle 0 B) :=
  weightedDiagonalRadius_contDiffOn hB (five_fields_contDiffOn hB hBb H).1

/-- The canonical scalar radius has a continuous first jet on a closed smaller triangle. -/
theorem canonicalScalarRadius_contDiffOn {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalScalarRadius S) (closedCoordTriangle 0 B) :=
  weightedDiagonalRadius_contDiffOn hB (alpha_contDiffOn hB hBb H)

private theorem outgoing_integral_eq_of_axis_limit
    {B u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B)
    {f : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (closedCoordTriangle 0 B))
    (hR : ContinuousOn (intervalIntegral.weightedDiagonalRadius g)
      (closedCoordTriangle 0 B))
    (hprim : ∀ a, u < a → a ≤ v → IntervalPrimitive f (fun t => g (u, t)) a v)
    (haxis : Tendsto f (𝓝[>] u) (𝓝 (0 : ℝ))) :
    f v = intervalIntegral.weightedDiagonalRadius g (u, v) := by
  let K := closedCoordTriangle 0 B
  let R := intervalIntegral.weightedDiagonalRadius g
  have hdiag : (u, u) ∈ K := ⟨hu, le_rfl, huv.le.trans hv⟩
  have hmap : Tendsto (fun a : ℝ => (u, a)) (𝓝[>] u) (𝓝[K] (u, u)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((show Continuous (fun a : ℝ => (u, a)) by fun_prop).tendsto u).mono_left
        inf_le_left
    · filter_upwards [Ioo_mem_nhdsGT huv] with a ha
      exact ⟨hu, ha.1.le, ha.2.le.trans hv⟩
  have hRlim : Tendsto (fun a : ℝ => R (u, a)) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have h := (hR (u, u) hdiag).tendsto.comp hmap
    change Tendsto (fun a : ℝ => R (u, a)) (𝓝[>] u) (𝓝 (R (u, u))) at h
    simpa [R, intervalIntegral.weightedDiagonalRadius] using h
  have hInt : ∀ a, u ≤ a → a ≤ v →
      IntervalIntegrable (fun t => g (u, t)) volume u a := by
    intro a hua hav
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hua]
    apply hg.comp (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨hu, ht.1, ht.2.trans (hav.trans hv)⟩
  have hEq : ∀ᶠ a in 𝓝[>] u,
      f v = R (u, v) + (f a - R (u, a)) := by
    filter_upwards [Ioo_mem_nhdsGT huv] with a ha
    have heq := (hprim a ha.1 ha.2.le).2
    have hsub := intervalIntegral.integral_interval_sub_left
      (hInt v huv.le le_rfl) (hInt a ha.1.le ha.2.le)
    rw [← hsub] at heq
    dsimp [R, intervalIntegral.weightedDiagonalRadius]
    linarith only [heq]
  have hlim : Tendsto (fun a : ℝ => R (u, v) + (f a - R (u, a)))
      (𝓝[>] u) (𝓝 (R (u, v))) := by
    convert tendsto_const_nhds.add (haxis.sub hRlim) using 1; simp
  exact (tendsto_nhds_unique
    (hlim.congr' (hEq.mono fun _ hh => hh.symm)) tendsto_const_nhds).symm

/-- The canonical radius equals the frozen total radius only inside the development. -/
theorem canonicalRadius_eq_radius {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    canonicalRadius S (u, v) = S.r u v := by
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have haxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq huvU] using
      H.solution.radius_axis u (H.solution.development.axis_mem huvU)
  have heq := outgoing_integral_eq_of_axis_limit hu huv hv
    (five_fields_contDiffOn hB hBb H).1.continuousOn
    (canonicalRadius_contDiffOn hB hBb H).continuousOn
    (fun a hua hav => H.solution.radius_out u a v hav
      (H.solution.development.out_seg_subset huvU hua hav le_rfl)) haxis
  exact heq.symm

private theorem frozen_field_tendsto_axis {B u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B)
    {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (closedCoordTriangle 0 B)) :
    Tendsto (fun t => f (u, t)) (𝓝[>] u) (𝓝 (f (u, u))) := by
  let K := closedCoordTriangle 0 B
  have hdiag : (u, u) ∈ K := ⟨hu, le_rfl, huv.le.trans hv⟩
  have hmap : Tendsto (fun t : ℝ => (u, t)) (𝓝[>] u) (𝓝[K] (u, u)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((show Continuous (fun t : ℝ => (u, t)) by fun_prop).tendsto u).mono_left
        inf_le_left
    · filter_upwards [Ioo_mem_nhdsGT huv] with t ht
      exact ⟨hu, ht.1.le, ht.2.le.trans hv⟩
  exact (hf (u, u) hdiag).tendsto.comp hmap

/-- The canonical scalar radius equals the actual product `rφ` only inside the development. -/
theorem canonicalScalarRadius_eq_radius_mul_phi {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    canonicalScalarRadius S (u, v) = S.r u v * S.phi u v := by
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have hr : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq huvU] using
      H.solution.radius_axis u (H.solution.development.axis_mem huvU)
  have hphi := frozen_field_tendsto_axis hu huv hv
    (five_fields_contDiffOn hB hBb H).2.2.1.continuousOn
  have haxis : Tendsto (fun t => S.r u t * S.phi u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa using hr.mul hphi
  have heq := outgoing_integral_eq_of_axis_limit hu huv hv
    (alpha_contDiffOn hB hBb H).continuousOn
    (canonicalScalarRadius_contDiffOn hB hBb H).continuousOn
    (fun a hua hav => H.solution.scalar_radius_out u a v hav
      (H.solution.development.out_seg_subset huvU hua hav le_rfl)) haxis
  exact heq.symm

/-- The nonsingular mass-gap coefficient along one outgoing ray. -/
@[expose] noncomputable def massGapCoefficient (S : Fields) (u t : ℝ) : ℝ :=
  -(S.theta u t)^2 / (S.r u t * S.lam u t)

private theorem mass_gap_coefficient_mul
    {b : ℝ} {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u t : ℝ} (hut : (u, t) ∈ developmentWithInitialEdge b) :
    massGapCoefficient S u t * (S.r u t - 2 * S.m u t) =
      -2 * ((1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 /
        (2 * S.lam u t)) := by
  have hr : S.r u t ≠ 0 := ne_of_gt (H.solution.radius_pos (u, t) hut)
  have hl : S.lam u t ≠ 0 := ne_of_gt (H.solution.lam_pos (u, t) hut)
  unfold massGapCoefficient
  field_simp

private theorem mass_gap_local_linear_equation
    {b B u v a d : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B)
    (hua : u < a) (had : a ≤ d) (hdv : d ≤ v) :
    IntervalIntegrable (massGapCoefficient S u) volume a d ∧
    IntervalIntegrable (S.lam u) volume a d ∧
    IntervalIntegrable
      (fun s => massGapCoefficient S u s * (S.r u s - 2 * S.m u s))
      volume a d ∧
    ∀ t ∈ Icc a d,
      (S.r u t - 2 * S.m u t) - (S.r u a - 2 * S.m u a) =
        ∫ s in a..t,
          (massGapCoefficient S u s * (S.r u s - 2 * S.m u s) + S.lam u s) := by
  let K := closedCoordTriangle 0 B
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have hseg (t : ℝ) (ht : t ∈ Icc a d) :
      outSeg u a t ⊆ developmentWithInitialEdge b :=
    H.solution.development.out_seg_subset huvU hua ht.1 (ht.2.trans hdv)
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc a d) K := by
    intro s hs
    exact ⟨hu, hua.le.trans hs.1, hs.2.trans (hdv.trans hv)⟩
  have hcanon : ContinuousOn (fun s => canonicalRadius S (u, s)) (Icc a d) :=
    (canonicalRadius_contDiffOn hB hBb H).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hrcont : ContinuousOn (S.r u) (Icc a d) := by
    apply hcanon.congr
    intro s hs
    exact (canonicalRadius_eq_radius hB hBb H hu
      (hua.trans_le hs.1) (hs.2.trans (hdv.trans hv))).symm
  obtain ⟨hlam, _, _, htheta, _⟩ := five_fields_contDiffOn hB hBb H
  have hlamcont : ContinuousOn (S.lam u) (Icc a d) :=
    hlam.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hthetacont : ContinuousOn (S.theta u) (Icc a d) :=
    htheta.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hden : ∀ s ∈ Icc a d, S.r u s * S.lam u s ≠ 0 := by
    intro s hs
    have hsU : (u, s) ∈ developmentWithInitialEdge b :=
      H.solution.development.outgoing_mem huvU (hua.trans_le hs.1)
        (hs.2.trans hdv)
    exact mul_ne_zero (ne_of_gt (H.solution.radius_pos (u, s) hsU))
      (ne_of_gt (H.solution.lam_pos (u, s) hsU))
  have hkcont : ContinuousOn (massGapCoefficient S u) (Icc a d) := by
    change ContinuousOn (fun s => -(S.theta u s)^2 /
      (S.r u s * S.lam u s)) (Icc a d)
    exact ((hthetacont.pow 2).neg).div (hrcont.mul hlamcont) hden
  have hk : IntervalIntegrable (massGapCoefficient S u) volume a d :=
    hkcont.intervalIntegrable_of_Icc had
  have hlamInt : IntervalIntegrable (S.lam u) volume a d :=
    hlamcont.intervalIntegrable_of_Icc had
  have hMfull := H.solution.mass_out u a d had (hseg d ⟨had, le_rfl⟩)
  have hkg : IntervalIntegrable
      (fun s => massGapCoefficient S u s * (S.r u s - 2 * S.m u s))
      volume a d := by
    have htwo : IntervalIntegrable
        (fun s => -2 * ((1 - 2 * S.m u s / S.r u s) * (S.theta u s)^2 /
          (2 * S.lam u s))) volume a d := hMfull.1.const_mul (-2)
    apply htwo.congr_uIoo
    intro s hs
    rw [uIoo_of_le had] at hs
    have hsU := H.solution.development.outgoing_mem huvU
      (hua.trans_le hs.1.le) (hs.2.le.trans hdv)
    exact (mass_gap_coefficient_mul H hsU).symm
  refine ⟨hk, hlamInt, hkg, ?_⟩
  intro t ht
  have hR := H.solution.radius_out u a t ht.1 (hseg t ht)
  have hM := H.solution.mass_out u a t ht.1 (hseg t ht)
  have hkgAt : IntervalIntegrable
      (fun s => massGapCoefficient S u s * (S.r u s - 2 * S.m u s))
      volume a t := hkg.mono_set (by
        rw [uIcc_of_le had, uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)
  have hId : (∫ s in a..t,
      massGapCoefficient S u s * (S.r u s - 2 * S.m u s)) =
      ∫ s in a..t, -2 * ((1 - 2 * S.m u s / S.r u s) *
        (S.theta u s)^2 / (2 * S.lam u s)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    have hsU := H.solution.development.outgoing_mem huvU
      (hua.trans_le hs.1.le) (hs.2.le.trans (ht.2.trans hdv))
    exact mass_gap_coefficient_mul H hsU
  calc
    (S.r u t - 2 * S.m u t) - (S.r u a - 2 * S.m u a) =
        (S.r u t - S.r u a) - 2 * (S.m u t - S.m u a) := by ring
    _ = (∫ s in a..t, S.lam u s) -
        2 * (∫ s in a..t,
          (1 - 2 * S.m u s / S.r u s) * (S.theta u s)^2 /
            (2 * S.lam u s)) := by rw [hR.2, hM.2]
    _ = (∫ s in a..t, S.lam u s) +
        (∫ s in a..t,
          massGapCoefficient S u s * (S.r u s - 2 * S.m u s)) := by
      rw [hId, intervalIntegral.integral_const_mul]
      ring
    _ = ∫ s in a..t,
          (massGapCoefficient S u s * (S.r u s - 2 * S.m u s) + S.lam u s) := by
      rw [intervalIntegral.integral_add hkgAt hR.1]
      ring

/-- The outgoing mass gap is positive at each in-domain point of a smaller triangle. -/
theorem mass_gap_pos {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    0 < S.r u v - 2 * S.m u v := by
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  obtain ⟨c, hc, hlam⟩ := H.lam_bounded_below
  have hrAxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq huvU] using
      H.solution.radius_axis u (H.solution.development.axis_mem huvU)
  have hmAxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq huvU] using
      H.solution.mass_axis u (H.solution.development.axis_mem huvU)
  have hgapAxis : Tendsto (fun t => S.r u t - 2 * S.m u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have htwo : Tendsto (fun t => 2 * S.m u t) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hmAxis
    simpa using hrAxis.sub htwo
  apply IsBVSolution.linear_solution_pos_of_axis_trace
    (u := u) (b := v) (c := c)
    (k := massGapCoefficient S u) (g := S.lam u)
    (y := fun t => S.r u t - 2 * S.m u t)
    huv hc hgapAxis
  · intro a d hua had hdv
    exact mass_gap_local_linear_equation hB hBb H hu huv hv hua had hdv
  · intro t hut htv
    have htU := H.solution.development.outgoing_mem huvU hut htv
    have hr : 0 < S.r u t := H.solution.radius_pos (u, t) htU
    have hl : 0 < S.lam u t := H.solution.lam_pos (u, t) htU
    unfold massGapCoefficient
    simpa only [neg_div] using
      (neg_nonpos.mpr (div_nonneg (sq_nonneg (S.theta u t))
        (mul_nonneg hr.le hl.le)))
  · intro t hut htv
    exact hlam (u, t) (H.solution.development.outgoing_mem huvU hut htv)

/-- The frozen conformal relation and the mass-gap barrier force the incoming
expansion to be negative at every in-domain point of a smaller triangle. -/
theorem nu_neg {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    S.nu u v < 0 := by
  have huvU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v) huvU
  have hgap := mass_gap_pos hB hBb H hu huv hv
  have hA : 0 < 1 - 2 * S.m u v / S.r u v := by
    have heq : 1 - 2 * S.m u v / S.r u v =
        (S.r u v - 2 * S.m u v) / S.r u v := by
      field_simp
    rw [heq]
    exact div_pos hgap hr
  obtain ⟨Ω, hΩ, hconf⟩ := H.solution.conformal (u, v) huvU
  have hright : 0 < -(4 * S.lam u v * S.nu u v) := by
    rw [← hconf]
    exact mul_pos hA (sq_pos_of_pos hΩ)
  have hl : 0 < S.lam u v := H.solution.lam_pos (u, v) huvU
  by_contra hn
  have hnu : 0 ≤ S.nu u v := le_of_not_gt hn
  have hnonneg : 0 ≤ 4 * S.lam u v * S.nu u v :=
    mul_nonneg (mul_nonneg (by norm_num) hl.le) hnu
  linarith

/-- The vertical first jet of an outgoing integral is its integrand, even on
the closed triangle's axis and vertices. -/
theorem weightedDiagonalRadius_vertical_jet {B : ℝ} (hB : 0 < B)
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (intervalIntegral.weightedDiagonalRadius f)
      (closedCoordTriangle 0 B) p) (0, 1) = f p := by
  let K := closedCoordTriangle 0 B
  let R := intervalIntegral.weightedDiagonalRadius f
  have hR : ContDiffOn ℝ 1 R K := weightedDiagonalRadius_contDiffOn hB hf
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hjetcont : ContinuousOn
      (fun q => (fderivWithin ℝ R K q) (0, 1)) K :=
    (hR.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hopen : ∀ q ∈ openCoordTriangle 0 B,
      (fderivWithin ℝ R K q) (0, 1) = f q := by
    rintro ⟨u, v⟩ hq
    have hqi : (u, v) ∈ interior K := by
      change (u, v) ∈ interior (closedCoordTriangle 0 B)
      rw [interior_closedCoordTriangle]
      exact hq
    have hparts : 0 < u ∧ u < v ∧ v < B := hq
    have hK : K ∈ 𝓝 (u, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hqi) interior_subset
    have hRdiff : DifferentiableAt ℝ R (u, v) :=
      (hR.differentiableOn (by norm_num) (u, v) (interior_subset hqi)).differentiableAt hK
    have hwithin : fderivWithin ℝ R K (u, v) = fderiv ℝ R (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hqi)) hRdiff
    have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) K := by
      intro s hs
      exact ⟨hparts.1.le, hs.1, hs.2.trans hparts.2.2.le⟩
    have hcontIcc : ContinuousOn (fun s => f (u, s)) (Icc u v) :=
      hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
    have hInt : IntervalIntegrable (fun s => f (u, s)) volume u v :=
      hcontIcc.intervalIntegrable_of_Icc hparts.2.1.le
    have hmapOpen : MapsTo (fun s : ℝ => (u, s)) (Ioo u B) K := by
      intro s hs
      exact ⟨hparts.1.le, hs.1.le, hs.2.le⟩
    have hcontOpen : ContinuousOn (fun s => f (u, s)) (Ioo u B) :=
      hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmapOpen
    have hvOpen : v ∈ Ioo u B := ⟨hparts.2.1, hparts.2.2⟩
    have hmeas : StronglyMeasurableAtFilter (fun s => f (u, s)) (𝓝 v) volume :=
      hcontOpen.stronglyMeasurableAtFilter isOpen_Ioo v hvOpen
    have hcontAt : ContinuousAt (fun s => f (u, s)) v :=
      (hcontOpen v hvOpen).continuousAt (isOpen_Ioo.mem_nhds hvOpen)
    have hFTC : HasDerivAt (fun t => R (u, t)) (f (u, v)) v :=
      intervalIntegral.integral_hasDerivAt_right hInt hmeas hcontAt
    have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hcomp : HasDerivAt (fun t => R (u, t))
        (fderiv ℝ R (u, v) (0, 1)) v := by
      simpa only [Function.comp_def] using hRdiff.hasFDerivAt.comp_hasDerivAt v hpair
    rw [hwithin]
    exact hcomp.unique hFTC
  have hEq : EqOn (fun q => (fderivWithin ℝ R K q) (0, 1)) f K :=
    (show EqOn (fun q => (fderivWithin ℝ R K q) (0, 1)) f
      (openCoordTriangle 0 B) from hopen).of_subset_closure
      hjetcont hf.continuousOn
      (fun _ hq => interior_subset (by
        change _ ∈ interior (closedCoordTriangle 0 B)
        rw [interior_closedCoordTriangle]
        exact hq))
      (by change closedCoordTriangle 0 B ⊆ closure (openCoordTriangle 0 B)
          rw [closure_openCoordTriangle hB])
  exact hEq hp

/-- The canonical radius has the expected outgoing derivative on the entire
closed smaller triangle. -/
theorem canonicalRadius_vertical_jet {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (canonicalRadius S) (closedCoordTriangle 0 B) p) (0, 1) =
      S.lam p.1 p.2 :=
  weightedDiagonalRadius_vertical_jet hB (five_fields_contDiffOn hB hBb H).1 hp

/-- The canonical scalar radius has the expected outgoing derivative on the
entire closed smaller triangle. -/
theorem canonicalScalarRadius_vertical_jet {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (canonicalScalarRadius S) (closedCoordTriangle 0 B) p) (0, 1) =
      S.alpha p.1 p.2 :=
  weightedDiagonalRadius_vertical_jet hB (alpha_contDiffOn hB hBb H) hp

private theorem horizontal_jet_of_incoming_primitive {B : ℝ} (hB : 0 < B)
    {F g : ℝ × ℝ → ℝ} {T : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hg : ContDiffOn ℝ 1 g (closedCoordTriangle 0 B))
    (hEq : ∀ u v, 0 ≤ u → u < v → v ≤ B → F (u, v) = T u v)
    (hprim : ∀ a s v, 0 ≤ a → a ≤ s → s < v → v ≤ B →
      IntervalPrimitive (fun t => T t v) (fun t => g (t, v)) a s)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = g p := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hjetcont : ContinuousOn
      (fun q => (fderivWithin ℝ F K q) (1, 0)) K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hopen : ∀ q ∈ openCoordTriangle 0 B,
      (fderivWithin ℝ F K q) (1, 0) = g q := by
    rintro ⟨u, v⟩ hq
    have hqi : (u, v) ∈ interior K := by
      change (u, v) ∈ interior (closedCoordTriangle 0 B)
      rw [interior_closedCoordTriangle]
      exact hq
    have hparts : 0 < u ∧ u < v ∧ v < B := hq
    have hK : K ∈ 𝓝 (u, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hqi) interior_subset
    have hFdiff : DifferentiableAt ℝ F (u, v) :=
      (hF.differentiableOn (by norm_num) (u, v) (interior_subset hqi)).differentiableAt hK
    have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hqi)) hFdiff
    let a : ℝ := u / 2
    let d : ℝ := (u + v) / 2
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hau : a < u := by dsimp [a]; linarith
    have hud : u < d := by dsimp [d]; linarith
    have hdv : d < v := by dsimp [d]; linarith
    have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc a u) K := by
      intro s hs
      exact ⟨ha.trans hs.1, hs.2.trans hparts.2.1.le,
        hparts.2.2.le⟩
    have hcontIcc : ContinuousOn (fun s => g (s, v)) (Icc a u) :=
      hg.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmap
    have hInt : IntervalIntegrable (fun s => g (s, v)) volume a u :=
      hcontIcc.intervalIntegrable_of_Icc hau.le
    have hmapOpen : MapsTo (fun s : ℝ => (s, v)) (Ioo a d) K := by
      intro s hs
      exact ⟨ha.trans hs.1.le, hs.2.le.trans hdv.le,
        hparts.2.2.le⟩
    have hcontOpen : ContinuousOn (fun s => g (s, v)) (Ioo a d) :=
      hg.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmapOpen
    have huOpen : u ∈ Ioo a d := ⟨hau, hud⟩
    have hmeas : StronglyMeasurableAtFilter (fun s => g (s, v)) (𝓝 u) volume :=
      hcontOpen.stronglyMeasurableAtFilter isOpen_Ioo u huOpen
    have hcontAt : ContinuousAt (fun s => g (s, v)) u :=
      (hcontOpen u huOpen).continuousAt (isOpen_Ioo.mem_nhds huOpen)
    have hFTC : HasDerivAt (fun s => T a v + ∫ t in a..s, g (t, v))
        (g (u, v)) u :=
      (intervalIntegral.integral_hasDerivAt_right hInt hmeas hcontAt).const_add (T a v)
    have hlocalEq : (fun s => F (s, v)) =ᶠ[𝓝 u]
        (fun s => T a v + ∫ t in a..s, g (t, v)) := by
      filter_upwards [Ioo_mem_nhds hau hud] with s hs
      have hsV : s < v := hs.2.trans hdv
      have hTs := hEq s v (ha.trans hs.1.le) hsV hparts.2.2.le
      have hTa := hEq a v ha (hau.trans hparts.2.1) hparts.2.2.le
      have hPr := (hprim a s v ha hs.1.le hsV hparts.2.2.le).2
      rw [hTs]
      linarith only [hPr]
    have hderived : HasDerivAt (fun s => F (s, v)) (g (u, v)) u :=
      hFTC.congr_of_eventuallyEq hlocalEq
    have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    have hcomp : HasDerivAt (fun s => F (s, v))
        (fderiv ℝ F (u, v) (1, 0)) u := by
      simpa only [Function.comp_def] using hFdiff.hasFDerivAt.comp_hasDerivAt u hpair
    rw [hwithin]
    exact hcomp.unique hderived
  have hEqK : EqOn (fun q => (fderivWithin ℝ F K q) (1, 0)) g K :=
    (show EqOn (fun q => (fderivWithin ℝ F K q) (1, 0)) g
      (openCoordTriangle 0 B) from hopen).of_subset_closure
      hjetcont hg.continuousOn
      (fun _ hq => interior_subset (by
        change _ ∈ interior (closedCoordTriangle 0 B)
        rw [interior_closedCoordTriangle]
        exact hq))
      (by change closedCoordTriangle 0 B ⊆ closure (openCoordTriangle 0 B)
          rw [closure_openCoordTriangle hB])
  exact hEqK hp

/-- The incoming first jet of the canonical radius is the actual `ν` field. -/
theorem canonicalRadius_horizontal_jet {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (canonicalRadius S) (closedCoordTriangle 0 B) p) (1, 0) =
      S.nu p.1 p.2 := by
  apply horizontal_jet_of_incoming_primitive hB
    (canonicalRadius_contDiffOn hB hBb H)
    (five_fields_contDiffOn hB hBb H).2.1
    (fun u v hu huv hv => canonicalRadius_eq_radius hB hBb H hu huv hv)
  · intro a s v ha has hsv hv
    apply H.solution.radius_in v a s has
    intro p hpSeg
    rcases p with ⟨x, y⟩
    have hxy : x ∈ Icc a s ∧ y = v := by simpa [inSeg] using hpSeg
    rcases hxy with ⟨hx, rfl⟩
    exact ⟨ha.trans hx.1, hx.2.trans_lt hsv, hv.trans_lt hBb⟩
  · exact hp

/-- The incoming first jet of the canonical scalar radius is the actual `β` field. -/
theorem canonicalScalarRadius_horizontal_jet {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (canonicalScalarRadius S) (closedCoordTriangle 0 B) p) (1, 0) =
      S.beta p.1 p.2 := by
  apply horizontal_jet_of_incoming_primitive hB
    (canonicalScalarRadius_contDiffOn hB hBb H)
    (beta_contDiffOn hB hBb H)
    (fun u v hu huv hv => canonicalScalarRadius_eq_radius_mul_phi hB hBb H hu huv hv)
  · intro a s v ha has hsv hv
    apply H.solution.scalar_radius_in v a s has
    intro p hpSeg
    rcases p with ⟨x, y⟩
    have hxy : x ∈ Icc a s ∧ y = v := by simpa [inSeg] using hpSeg
    rcases hxy with ⟨hx, rfl⟩
    exact ⟨ha.trans hx.1, hx.2.trans_lt hsv, hv.trans_lt hBb⟩
  · exact hp

private theorem diagonal_jet_sum_zero {B : ℝ} (hB : 0 < B)
    {F G H : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContinuousOn G (closedCoordTriangle 0 B))
    (hH : ContinuousOn H (closedCoordTriangle 0 B))
    (haxis : ∀ u, F (u, u) = 0)
    (hhor : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p)
    (hver : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (0, 1) = H p)
    {u : ℝ} (hu : u ∈ Icc 0 B) : G (u, u) + H (u, u) = 0 := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hdiagOpen : ∀ t ∈ Ioo 0 B, G (t, t) + H (t, t) = 0 := by
    intro t ht
    have htK : (t, t) ∈ K := ⟨ht.1.le, le_rfl, ht.2.le⟩
    have hdiff : DifferentiableWithinAt ℝ F K (t, t) :=
      hF.differentiableOn (by norm_num) (t, t) htK
    have hpair : HasDerivAt (fun s : ℝ => (s, s)) (1, 1) t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_id' t)
    have hnear : ∀ᶠ s in 𝓝 t, (s, s) ∈ K := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact ⟨hs.1.le, le_rfl, hs.2.le⟩
    have hcomp : HasDerivAt (fun s => F (s, s))
        ((fderivWithin ℝ F K (t, t)) (1, 1)) t :=
      by simpa only [Function.comp_def] using
        (hdiff.hasFDerivWithinAt.comp_hasDerivAt
          (f := fun s : ℝ => (s, s)) t hpair hnear)
    have hzero : HasDerivAt (fun s => F (s, s)) 0 t := by
      convert hasDerivAt_const t (0 : ℝ) using 1
      · funext s
        exact haxis s
    have hsum : (fderivWithin ℝ F K (t, t)) (1, 1) =
        G (t, t) + H (t, t) := by
      have hvec : ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
        ext <;> norm_num
      rw [hvec, map_add, hhor (t, t) htK, hver (t, t) htK]
    rw [← hsum]
    exact hcomp.unique hzero
  have hmap : MapsTo (fun t : ℝ => (t, t)) (Icc 0 B) K :=
    fun t ht => ⟨ht.1, le_rfl, ht.2⟩
  have hcont : ContinuousOn (fun t => G (t, t) + H (t, t)) (Icc 0 B) :=
    (hG.add hH).comp (continuous_id.prodMk continuous_id).continuousOn hmap
  have hEq : EqOn (fun t => G (t, t) + H (t, t)) (fun _ => 0)
      (Icc 0 B) :=
    (show EqOn (fun t => G (t, t) + H (t, t)) (fun _ => 0)
      (Ioo 0 B) from hdiagOpen).of_subset_closure hcont continuousOn_const
      Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt hB)])
  exact hEq hu

/-- The regular axis has opposite incoming and outgoing radius jets. -/
theorem nu_eq_neg_lam_axis {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) : S.nu u u = -S.lam u u := by
  have h := diagonal_jet_sum_zero hB
    (canonicalRadius_contDiffOn hB hBb H)
    (five_fields_contDiffOn hB hBb H).2.1.continuousOn
    (five_fields_contDiffOn hB hBb H).1.continuousOn
    (fun u => (canonical_outgoing_axis S u).1)
    (fun p hp => canonicalRadius_horizontal_jet hB hBb H hp)
    (fun p hp => canonicalRadius_vertical_jet hB hBb H hp) hu
  linarith

/-- The regular axis has opposite incoming and outgoing scalar-radius jets. -/
theorem beta_eq_neg_alpha_axis {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) : S.beta u u = -S.alpha u u := by
  have h := diagonal_jet_sum_zero hB
    (canonicalScalarRadius_contDiffOn hB hBb H)
    (beta_contDiffOn hB hBb H).continuousOn
    (alpha_contDiffOn hB hBb H).continuousOn
    (fun u => (canonical_outgoing_axis S u).2)
    (fun p hp => canonicalScalarRadius_horizontal_jet hB hBb H hp)
    (fun p hp => canonicalScalarRadius_vertical_jet hB hBb H hp) hu
  linarith

end ChristodoulouBV.C1Solution

end
