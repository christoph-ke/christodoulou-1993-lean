module

public import ChristodoulouBV.Existence.C1FamilyZ
public import ChristodoulouBV.AreaEstimates.GaugeAxis
public import ChristodoulouBV.C1Solution.AxisTranslationFrozen
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Starting the Section 6 bootstrap near the initial vertex

The initial radius gauge fixes both null expansions at the vertex. Compact
C¹ regularity and the regular-axis quadratic mass ratio then give strict
bootstrap geometry on a short cone; the scalar null size is controlled by
the Lipschitz argument in `C1FamilyZ`.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The radius gauge fixes the outgoing expansion at the included initial
vertex by continuity from the open characteristic edge. -/
theorem s6_initial_lam_vertex {b : ℝ} (hb : 0 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2) :
    S.lam 0 0 = 1 / 2 := by
  let B := b / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hBb : B < b := by dsimp [B]; linarith only [hb]
  have hlam : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1
  have hmap : MapsTo (fun v : ℝ => ((0 : ℝ), v)) (Icc 0 B)
      (closedCoordTriangle 0 B) := by
    intro v hv
    exact ⟨le_rfl, hv.1, hv.2⟩
  have hedge : ContinuousOn (fun v : ℝ => S.lam 0 v) (Icc 0 B) :=
    hlam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hopen : EqOn (fun v : ℝ => S.lam 0 v)
      (fun _ => (1 / 2 : ℝ)) (Ioo 0 B) := by
    intro v hv
    exact initial_lam_eq_of_gauge H hr
      ⟨hv.1, hv.2.trans hBb⟩
  have hclosed := hopen.of_subset_closure hedge continuousOn_const
    Ioo_subset_Icc_self (by rw [closure_Ioo hB.ne])
  exact hclosed ⟨le_rfl, hB.le⟩

private theorem small_lipschitz_product {L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hbound : h ≤ 1 / (6 * (L + 1))) :
    L * h ≤ 1 / 6 := by
  have hden : 0 < 6 * (L + 1) := by positivity
  have hmul := (le_div_iff₀ hden).1 hbound
  nlinarith only [hmul, hL, hh]

private theorem small_quadratic_product {C h : ℝ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hunit : h ≤ 1)
    (hbound : h ≤ 1 / (3 * (C + 1))) :
    C * h ^ 2 ≤ 1 / 3 := by
  have hden : 0 < 3 * (C + 1) := by positivity
  have hmul := (le_div_iff₀ hden).1 hbound
  have hsq : h ^ 2 ≤ h := by nlinarith only [hh, hunit]
  have hprod : C * h ^ 2 ≤ C * h :=
    mul_le_mul_of_nonneg_left hsq hC
  nlinarith only [hmul, hprod, hC, hh]

/-- Strictly inside a local C¹ development, all three Section 4 geometric
bootstrap inequalities hold after dilation to unit width. The cutoff is
chosen from compact C¹ bounds and the regular-axis quadratic mass estimate. -/
theorem s6_exists_short_cone_geometry {b : ℝ} (hb : 0 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ h : ℝ, 0 < h → h < A →
      s4_bootstrap (Uniqueness.rescaledFields S 0 h) := by
  let B := b / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hBb : B < b := by dsimp [B]; linarith only [hb]
  have hlam0 := s6_initial_lam_vertex hb H hr
  have hnu0 : S.nu 0 0 = -(1 / 2 : ℝ) := by
    have haxis := C1Solution.nu_eq_neg_lam_axis hB hBb H
      (show (0 : ℝ) ∈ Icc 0 B by exact ⟨le_rfl, hB.le⟩)
    rw [hlam0] at haxis
    exact haxis
  have hlamC : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1
  have hnuC : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).2.1
  obtain ⟨Llam, hLlam⟩ :=
    hlamC.exists_lipschitzOnWith (by norm_num)
      (convex_closedCoordTriangle 0 B)
      (isCompact_closedCoordTriangle 0 B)
  obtain ⟨Lnu, hLnu⟩ :=
    hnuC.exists_lipschitzOnWith (by norm_num)
      (convex_closedCoordTriangle 0 B)
      (isCompact_closedCoordTriangle 0 B)
  obtain ⟨C, hC, hmass⟩ :=
    C1Solution.exists_canonicalMassRatio_quadratic_axis_bound hB hBb H
  let A : ℝ := min B (min (1 / (6 * ((Llam : ℝ) + 1)))
    (min (1 / (6 * ((Lnu : ℝ) + 1)))
      (min 1 (1 / (3 * (C + 1))))))
  have hA : 0 < A := by
    dsimp [A]
    apply lt_min hB
    apply lt_min
    · positivity
    apply lt_min
    · positivity
    apply lt_min
    · norm_num
    · positivity
  refine ⟨A, hA, ?_⟩
  intro h hh hhA
  have hhB : h < B := hhA.trans_le (min_le_left _ _)
  have hhb : h < b := hhB.trans hBb
  have hLamScale : (Llam : ℝ) * h ≤ 1 / 6 :=
    small_lipschitz_product (NNReal.coe_nonneg Llam) hh.le
      (hhA.le.trans ((min_le_right B _).trans (min_le_left _ _)))
  have hNuScale : (Lnu : ℝ) * h ≤ 1 / 6 :=
    small_lipschitz_product (NNReal.coe_nonneg Lnu) hh.le
      (hhA.le.trans ((min_le_right B _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
  have hUnit : h ≤ 1 :=
    hhA.le.trans ((min_le_right B _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
  have hMassScale : C * h ^ 2 ≤ 1 / 3 :=
    small_quadratic_product hC hh.le hUnit
      (hhA.le.trans ((min_le_right B _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))))
  have h0K : ((0 : ℝ), (0 : ℝ)) ∈ closedCoordTriangle 0 B :=
    ⟨le_rfl, le_rfl, hB.le⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    let q : ℝ × ℝ := (h * p.1, h * p.2)
    have hqK : q ∈ closedCoordTriangle 0 B := by
      change 0 ≤ h * p.1 ∧ h * p.1 ≤ h * p.2 ∧ h * p.2 ≤ B
      exact ⟨mul_nonneg hh.le hp.1,
        mul_le_mul_of_nonneg_left hp.2.1.le hh.le,
        (calc
          h * p.2 ≤ h * 1 := mul_le_mul_of_nonneg_left hp.2.2.le hh.le
          _ = h := by ring
          _ ≤ B := hhB.le)⟩
    have hdist : dist q (0, 0) ≤ h := by
      simp only [q, Prod.dist_eq, Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg hh.le hp.1),
        abs_of_nonneg (mul_nonneg hh.le (hp.1.trans hp.2.1.le))]
      exact max_le (by nlinarith only [hh, hp.1, hp.2.1, hp.2.2])
        (by nlinarith only [hh, hp.2.2])
    have hdiff := hLlam.dist_le_mul q hqK (0, 0) h0K
    have hbound : dist (S.lam q.1 q.2) (S.lam 0 0) ≤ 1 / 6 :=
      hdiff.trans ((mul_le_mul_of_nonneg_left hdist
        (NNReal.coe_nonneg Llam)).trans hLamScale)
    rw [Real.dist_eq, hlam0] at hbound
    have hlow := (abs_le.mp hbound).1
    have hgoal : (1 / 3 : ℝ) ≤ S.lam q.1 q.2 := by
      nlinarith only [hlow]
    simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add] using hgoal
  · intro p hp
    let q : ℝ × ℝ := (h * p.1, h * p.2)
    have hqK : q ∈ closedCoordTriangle 0 B := by
      change 0 ≤ h * p.1 ∧ h * p.1 ≤ h * p.2 ∧ h * p.2 ≤ B
      exact ⟨mul_nonneg hh.le hp.1,
        mul_le_mul_of_nonneg_left hp.2.1.le hh.le,
        (calc
          h * p.2 ≤ h * 1 := mul_le_mul_of_nonneg_left hp.2.2.le hh.le
          _ = h := by ring
          _ ≤ B := hhB.le)⟩
    have hdist : dist q (0, 0) ≤ h := by
      simp only [q, Prod.dist_eq, Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg hh.le hp.1),
        abs_of_nonneg (mul_nonneg hh.le (hp.1.trans hp.2.1.le))]
      exact max_le (by nlinarith only [hh, hp.1, hp.2.1, hp.2.2])
        (by nlinarith only [hh, hp.2.2])
    have hdiff := hLnu.dist_le_mul q hqK (0, 0) h0K
    have hbound : dist (S.nu q.1 q.2) (S.nu 0 0) ≤ 1 / 6 :=
      hdiff.trans ((mul_le_mul_of_nonneg_left hdist
        (NNReal.coe_nonneg Lnu)).trans hNuScale)
    rw [Real.dist_eq, hnu0] at hbound
    have hlow := (abs_le.mp hbound).1
    have hgoal : -(2 / 3 : ℝ) ≤ S.nu q.1 q.2 := by
      nlinarith only [hlow]
    simpa only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add] using hgoal
  · intro p hp
    let q : ℝ × ℝ := (h * p.1, h * p.2)
    have hqK : q ∈ closedCoordTriangle 0 B := by
      change 0 ≤ h * p.1 ∧ h * p.1 ≤ h * p.2 ∧ h * p.2 ≤ B
      exact ⟨mul_nonneg hh.le hp.1,
        mul_le_mul_of_nonneg_left hp.2.1.le hh.le,
        (calc
          h * p.2 ≤ h * 1 := mul_le_mul_of_nonneg_left hp.2.2.le hh.le
          _ = h := by ring
          _ ≤ B := hhB.le)⟩
    have hqD : q ∈ developmentWithInitialEdge b :=
      ⟨mul_nonneg hh.le hp.1,
        mul_lt_mul_of_pos_left hp.2.1 hh,
        (calc
          h * p.2 < h * 1 := mul_lt_mul_of_pos_left hp.2.2 hh
          _ = h := by ring
          _ < b := hhb)⟩
    have hratio := (hmass q hqK).2
    rw [C1Solution.canonicalMassRatio_eq_mass_ratio H hqD] at hratio
    have hgap : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1.le
    have hgap1 : p.2 - p.1 ≤ 1 := by linarith only [hp.1, hp.2.2]
    have hquad : C * (q.2 - q.1) ^ 2 ≤ C * h ^ 2 := by
      dsimp [q]
      have hg : 0 ≤ h * p.2 - h * p.1 := by nlinarith only [hh, hgap]
      have hg1 : h * p.2 - h * p.1 ≤ h := by nlinarith only [hh, hgap1]
      gcongr
    have hfinal := (hratio.trans hquad).trans hMassScale
    have hrescale := Uniqueness.rescaled_mass_ratio S (a := 0) hh p.1 p.2
    rw [hrescale]
    simpa only [Uniqueness.affineCoordinate, zero_add, q] using hfinal

/-- A local C¹ development with the prescribed initial gauge starts the
Section 4 bootstrap on some shorter cone. After dilation to unit width the
three geometric bounds and `Z ≤ ε₀` hold with the universal §4 threshold;
the selected cutoff depends on the local solution. -/
theorem bootstrap_start {alpha₀ : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) :
    ∃ h : ℝ, 0 < h ∧ h < b ∧
      let T := Uniqueness.rescaledFields S 0 h
      IsC1Solution (developmentWithInitialEdge 1) T ∧
      s4_bootstrap T ∧ sourceZ T ≤ s4Epsilon0 ∧
      ∀ v ∈ Ioo (0 : ℝ) 1,
        T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ (h * v) := by
  have hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2 :=
    fun v hv => (hdata v hv).1
  obtain ⟨A, hA, hgeom⟩ := s6_exists_short_cone_geometry hb H hr
  obtain ⟨h, hh, hhA, hhb, hZ⟩ :=
    s6_exists_short_cone_sourceZ hb hA H
  have hunit : 1 < b / h := by
    apply (lt_div_iff₀ hh).2
    simpa only [one_mul] using hhb
  let T := Uniqueness.rescaledFields S 0 h
  have HT : IsC1Solution (developmentWithInitialEdge 1) T :=
    C1Solution.isC1Solution_restrict_initialEdge
      (C1Solution.rescaled_development_isC1Solution H hh) hunit.le
  refine ⟨h, hh, hhb, HT, hgeom h hh hhA, hZ, ?_⟩
  intro v hv
  have hvb : h * v ∈ Ioo (0 : ℝ) b := by
    constructor
    · exact mul_pos hh hv.1
    · calc
        h * v < h * 1 := mul_lt_mul_of_pos_left hv.2 hh
        _ = h := by ring
        _ < b := hhb
  obtain ⟨hrv, hαv⟩ := hdata (h * v) hvb
  constructor
  · dsimp [T, Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate]
    simp only [mul_zero, zero_add]
    rw [hrv]
    field_simp [hh.ne']
  · simpa only [T, Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate, mul_zero, zero_add] using hαv

end ChristodoulouBV

end
