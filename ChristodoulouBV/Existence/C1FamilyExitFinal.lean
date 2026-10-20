module

public import ChristodoulouBV.Existence.C1FamilyExitUpper
public import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# First-exit topology for finite C¹ developments

The geometric bootstrap quantities are continuous under changes of the
cutoff because their fields extend continuously to a compact triangle.
The null size has the stronger uniform estimate proved in `C1FamilyExitUpper`.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- A continuous field on a compact physical triangle is uniformly close
after nearby dilations, uniformly over the unit triangle. -/
theorem s6_scaled_field_uniformly_close {B a₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : ℝ, 0 < a → a < B → |a - a₀| < δ →
        ∀ p ∈ closedCoordTriangle 0 1,
          |f (a • p) - f (a₀ • p)| ≤ ε := by
  let J : Set ℝ := Icc (a₀ / 2) B
  let K : Set (ℝ × ℝ) := closedCoordTriangle 0 1
  let P : Set (ℝ × (ℝ × ℝ)) := J ×ˢ K
  have hP : IsCompact P :=
    isCompact_Icc.prod (isCompact_closedCoordTriangle 0 1)
  let G : (ℝ × (ℝ × ℝ)) → ℝ :=
    fun z => f (z.1 • z.2)
  have hmap : MapsTo (fun z : ℝ × (ℝ × ℝ) => z.1 • z.2)
      P (closedCoordTriangle 0 B) := by
    intro z hz
    have ha : 0 ≤ z.1 := by
      have h := hz.1.1
      linarith only [h, ha₀]
    have hp := hz.2
    change 0 ≤ z.2.1 ∧ z.2.1 ≤ z.2.2 ∧ z.2.2 ≤ 1 at hp
    change 0 ≤ (z.1 • z.2).1 ∧
      (z.1 • z.2).1 ≤ (z.1 • z.2).2 ∧
      (z.1 • z.2).2 ≤ B
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨mul_nonneg ha hp.1,
      mul_le_mul_of_nonneg_left hp.2.1 ha,
      (by calc
        z.1 * z.2.2 ≤ z.1 * 1 := mul_le_mul_of_nonneg_left hp.2.2 ha
        _ = z.1 := by ring
        _ ≤ B := hz.1.2)⟩
  have hchart : Continuous (fun z : ℝ × (ℝ × ℝ) => z.1 • z.2) := by
    fun_prop
  have hG : ContinuousOn G P :=
    hf.comp hchart.continuousOn hmap
  have hUC : UniformContinuousOn G P :=
    hP.uniformContinuousOn_of_continuous hG
  intro ε hε
  obtain ⟨δ₀, hδ₀, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  let δ := min δ₀ (a₀ / 2)
  have hδ : 0 < δ := lt_min hδ₀ (half_pos ha₀)
  refine ⟨δ, hδ, ?_⟩
  intro a ha haB hdist p hp
  have haJ : a ∈ J := by
    dsimp [J]
    constructor
    · have hbound : |a - a₀| < a₀ / 2 :=
        hdist.trans_le (min_le_right _ _)
      have hlow := (abs_lt.mp hbound).1
      linarith only [hlow]
    · exact haB.le
  have ha₀J : a₀ ∈ J := by
    dsimp [J]
    exact ⟨by linarith only [ha₀], ha₀B.le⟩
  have hpairDist : dist (a, p) (a₀, p) < δ₀ := by
    rw [Prod.dist_eq]
    rw [dist_self, max_eq_left (dist_nonneg : 0 ≤ dist a a₀),
      Real.dist_eq]
    exact hdist.trans_le (min_le_left _ _)
  have hclose' := hclose (a, p) ⟨haJ, hp⟩
    (a₀, p) ⟨ha₀J, hp⟩ hpairDist
  dsimp [G] at hclose'
  rw [Real.dist_eq] at hclose'
  exact hclose'.le

/-- A pointwise bound at every smaller positive cutoff passes to the
finite interior endpoint for a field continuous on the closed triangle. -/
theorem s6_scaled_field_endpoint_bound {B a₀ c : ℝ}
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B))
    (hbound : ∀ a : ℝ, 0 < a → a < a₀ →
      ∀ p ∈ developmentWithInitialEdge 1, c ≤ f (a • p)) :
    ∀ p ∈ developmentWithInitialEdge 1, c ≤ f (a₀ • p) := by
  intro p hp
  let F : ℝ → ℝ := fun a => f (a • p)
  have hmap : MapsTo (fun a : ℝ => a • p) (Icc 0 a₀)
      (closedCoordTriangle 0 B) := by
    intro a ha
    change 0 ≤ a * p.1 ∧ a * p.1 ≤ a * p.2 ∧ a * p.2 ≤ B
    have hp' : 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 :=
      ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
    refine ⟨mul_nonneg ha.1 hp'.1,
      mul_le_mul_of_nonneg_left hp'.2.1 ha.1, ?_⟩
    calc
      a * p.2 ≤ a * 1 := mul_le_mul_of_nonneg_left hp'.2.2 ha.1
      _ = a := by ring
      _ ≤ a₀ := ha.2
      _ ≤ B := ha₀B.le
  have hF : ContinuousOn F (Icc 0 a₀) := by
    exact hf.comp (by fun_prop) hmap
  have hsmall : ∀ a ∈ Ioo (0 : ℝ) a₀, c ≤ F a := by
    intro a ha
    exact hbound a ha.1 ha.2 p hp
  have hclosure : a₀ ∈ closure (Ioo (0 : ℝ) a₀) := by
    rw [closure_Ioo ha₀.ne]
    exact ⟨ha₀.le, le_rfl⟩
  have hF' : ContinuousOn F (closure (Ioo (0 : ℝ) a₀)) := by
    rw [closure_Ioo ha₀.ne]
    exact hF
  exact le_on_closure hsmall continuousOn_const hF' hclosure

private theorem scaled_ratio_eq_canonical {b B a : ℝ}
    (_hB : 0 < B) (hBb : B < b) (ha : 0 < a) (haB : a < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    2 * (Uniqueness.rescaledFields S 0 a).m p.1 p.2 /
        (Uniqueness.rescaledFields S 0 a).r p.1 p.2 =
      C1Solution.canonicalMassRatio b S (a • p) := by
  have hmem : a • p ∈ developmentWithInitialEdge b := by
    change 0 ≤ a * p.1 ∧ a * p.1 < a * p.2 ∧ a * p.2 < b
    refine ⟨mul_nonneg ha.le hp.1,
      mul_lt_mul_of_pos_left hp.2.1 ha, ?_⟩
    calc
      a * p.2 < a * 1 := mul_lt_mul_of_pos_left hp.2.2 ha
      _ = a := by ring
      _ < b := haB.trans hBb
  rw [C1Solution.canonicalMassRatio_eq_mass_ratio H hmem]
  have hr := Uniqueness.rescaled_mass_ratio S (a := 0) ha p.1 p.2
  simpa only [Uniqueness.affineCoordinate, zero_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hr

/-- A bootstrap bound holding on every smaller cutoff persists at an
interior endpoint of a larger C¹ development. The mass ratio uses its
continuous canonical axis extension. -/
theorem s6_bootstrap_endpoint {b B a₀ : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hprev : ∀ a : ℝ, 0 < a → a < a₀ →
      s4_bootstrap (Uniqueness.rescaledFields S 0 a)) :
    s4_bootstrap (Uniqueness.rescaledFields S 0 a₀) := by
  have hLam : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn
  have hNu : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).2.1.continuousOn
  have hMu : ContinuousOn
      (fun p : ℝ × ℝ => -C1Solution.canonicalMassRatio b S p)
      (closedCoordTriangle 0 B) :=
    (C1Solution.canonicalMassRatio_continuousOn hB hBb H).neg
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h := s6_scaled_field_endpoint_bound ha₀ ha₀B hLam
      (fun a ha ha₀' q hq => by
        have hq' := (hprev a ha ha₀').1 q hq
        simpa only [Uniqueness.rescaledFields,
          Uniqueness.affineCoordinate, zero_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hq') p hp
    simpa only [Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate, zero_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h
  · intro p hp
    have h := s6_scaled_field_endpoint_bound ha₀ ha₀B hNu
      (fun a ha ha₀' q hq => by
        have hq' := (hprev a ha ha₀').2.1 q hq
        simpa only [Uniqueness.rescaledFields,
          Uniqueness.affineCoordinate, zero_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hq') p hp
    simpa only [Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate, zero_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h
  · intro p hp
    have h := s6_scaled_field_endpoint_bound ha₀ ha₀B hMu
      (fun a ha ha₀' q hq => by
        have hq' := (hprev a ha ha₀').2.2 q hq
        rw [scaled_ratio_eq_canonical hB hBb ha (ha₀'.trans ha₀B) H hq] at hq'
        exact neg_le_neg hq') p hp
    have h' := neg_le_neg h
    rw [scaled_ratio_eq_canonical hB hBb ha₀ ha₀B H hp]
    simpa only [neg_neg] using h'

/-- The supremum-defined null size also retains its universal bound at an
interior first-exit cutoff. Its proof uses uniform continuity of both
axis-extended null densities and a common bound for all null slices. -/
theorem s6_sourceZ_endpoint {b B a₀ : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hprev : ∀ a : ℝ, 0 < a → a < a₀ →
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0) :
    sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤ s4Epsilon0 := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  obtain ⟨δ, hδ, hnear⟩ :=
    s6_sourceZ_nearby hB hBb ha₀ ha₀B H
      (show 0 < (ε : ℝ) by exact_mod_cast hε)
  let a := a₀ - min δ a₀ / 2
  have hmin : 0 < min δ a₀ := lt_min hδ ha₀
  have ha : 0 < a := by
    dsimp [a]
    have hle := min_le_right δ a₀
    linarith only [hmin, hle, ha₀]
  have ha₀' : a < a₀ := by dsimp [a]; linarith only [hmin]
  have haB : a < B := ha₀'.trans ha₀B
  have hdist : |a - a₀| < δ := by
    dsimp [a]
    rw [show a₀ - min δ a₀ / 2 - a₀ = -(min δ a₀ / 2) by ring,
      abs_neg, abs_of_pos (half_pos hmin)]
    have hle := min_le_left δ a₀
    linarith only [hmin, hle]
  have hle := (hnear a ha haB hdist).2
  calc
    sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤
        sourceZ (Uniqueness.rescaledFields S 0 a) + ENNReal.ofReal (ε : ℝ) := hle
    _ ≤ s4Epsilon0 + ε := by
      rw [ENNReal.ofReal_coe_nnreal]
      gcongr
      exact hprev a ha ha₀'

/-- At a finite interior first-exit cutoff, all four weak bootstrap bounds
persist. If the three geometric bounds have a common strict margin on the
closed unit triangle and `Z` has a strict margin below the universal
threshold, the admissible interval extends beyond that cutoff. The common
margin is the quantitative form of no bootstrap quantity being saturated. -/
theorem first_exit_continuity_margin {b B a₀ : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hprev : ∀ a : ℝ, 0 < a → a < a₀ →
      s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0) :
    s4_bootstrap (Uniqueness.rescaledFields S 0 a₀) ∧
    sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤ s4Epsilon0 ∧
    ((∃ η : ℝ, 0 < η ∧
      (∀ p ∈ closedCoordTriangle 0 1,
        (1 / 3 : ℝ) + η ≤ S.lam (a₀ * p.1) (a₀ * p.2) ∧
        -(2 / 3 : ℝ) + η ≤ S.nu (a₀ * p.1) (a₀ * p.2) ∧
        C1Solution.canonicalMassRatio b S (a₀ • p) + η ≤ (1 / 3 : ℝ)) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a₀) +
          ENNReal.ofReal η ≤ s4Epsilon0) →
      ∃ a : ℝ, a₀ < a ∧ a < B ∧
        s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
        sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0) := by
  have hendpoint : s4_bootstrap (Uniqueness.rescaledFields S 0 a₀) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤ s4Epsilon0 := by
    constructor
    · exact s6_bootstrap_endpoint hB hBb ha₀ ha₀B H
        (fun a ha ha₀' => (hprev a ha ha₀').1)
    · exact s6_sourceZ_endpoint hB hBb ha₀ ha₀B H
        (fun a ha ha₀' => (hprev a ha ha₀').2)
  refine ⟨hendpoint.1, hendpoint.2, ?_⟩
  rintro ⟨η, hη, hstrict, hZstrict⟩
  have hLam : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn
  have hNu : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).2.1.continuousOn
  have hMu : ContinuousOn (C1Solution.canonicalMassRatio b S)
      (closedCoordTriangle 0 B) :=
    C1Solution.canonicalMassRatio_continuousOn hB hBb H
  obtain ⟨δLam, hδLam, hcloseLam⟩ :=
    s6_scaled_field_uniformly_close ha₀ ha₀B hLam (η / 2) (half_pos hη)
  obtain ⟨δNu, hδNu, hcloseNu⟩ :=
    s6_scaled_field_uniformly_close ha₀ ha₀B hNu (η / 2) (half_pos hη)
  obtain ⟨δMu, hδMu, hcloseMu⟩ :=
    s6_scaled_field_uniformly_close ha₀ ha₀B hMu (η / 2) (half_pos hη)
  obtain ⟨δZ, hδZ, hcloseZ⟩ :=
    s6_sourceZ_nearby hB hBb ha₀ ha₀B H (half_pos hη)
  let d := min δLam (min δNu (min δMu (min δZ (B - a₀))))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδLam (lt_min hδNu (lt_min hδMu
      (lt_min hδZ (sub_pos.mpr ha₀B))))
  let a := a₀ + d / 2
  have ha₀a : a₀ < a := by dsimp [a]; linarith only [hd]
  have ha : 0 < a := ha₀.trans ha₀a
  have haB : a < B := by
    have hdB : d ≤ B - a₀ := by
      dsimp [d]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))
    dsimp [a]
    linarith only [hd, hdB]
  have hdist : |a - a₀| = d / 2 := by
    dsimp [a]
    rw [show a₀ + d / 2 - a₀ = d / 2 by ring,
      abs_of_pos (half_pos hd)]
  have hdistLam : |a - a₀| < δLam := by
    rw [hdist]
    have hle : d ≤ δLam := min_le_left _ _
    linarith only [hd, hle]
  have hdistNu : |a - a₀| < δNu := by
    rw [hdist]
    have hle : d ≤ δNu :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hd, hle]
  have hdistMu : |a - a₀| < δMu := by
    rw [hdist]
    have hle : d ≤ δMu :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hd, hle]
  have hdistZ : |a - a₀| < δZ := by
    rw [hdist]
    have hle : d ≤ δZ :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
    linarith only [hd, hle]
  have hgeometry : s4_bootstrap (Uniqueness.rescaledFields S 0 a) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      have hpK : p ∈ closedCoordTriangle 0 1 :=
        ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
      have hnear := hcloseLam a ha haB hdistLam p hpK
      have hlow := (abs_le.mp hnear).1
      have hmargin := (hstrict p hpK).1
      have hfinal : (1 / 3 : ℝ) ≤ S.lam (a * p.1) (a * p.2) := by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hlow
        linarith only [hlow, hmargin, hη]
      simpa only [Uniqueness.rescaledFields,
        Uniqueness.affineCoordinate, zero_add] using hfinal
    · intro p hp
      have hpK : p ∈ closedCoordTriangle 0 1 :=
        ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
      have hnear := hcloseNu a ha haB hdistNu p hpK
      have hlow := (abs_le.mp hnear).1
      have hmargin := (hstrict p hpK).2.1
      have hfinal : -(2 / 3 : ℝ) ≤ S.nu (a * p.1) (a * p.2) := by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hlow
        linarith only [hlow, hmargin, hη]
      simpa only [Uniqueness.rescaledFields,
        Uniqueness.affineCoordinate, zero_add] using hfinal
    · intro p hp
      have hpK : p ∈ closedCoordTriangle 0 1 :=
        ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
      have hnear := hcloseMu a ha haB hdistMu p hpK
      have hupp := (abs_le.mp hnear).2
      have hmargin := (hstrict p hpK).2.2
      have hfinal : C1Solution.canonicalMassRatio b S (a • p) ≤
          (1 / 3 : ℝ) := by
        linarith only [hupp, hmargin, hη]
      rw [scaled_ratio_eq_canonical hB hBb ha haB H hp]
      exact hfinal
  have hZ : sourceZ (Uniqueness.rescaledFields S 0 a) ≤
      s4Epsilon0 := by
    have hnear := (hcloseZ a ha haB hdistZ).1
    calc
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤
          sourceZ (Uniqueness.rescaledFields S 0 a₀) +
            ENNReal.ofReal (η / 2) := hnear
      _ ≤ sourceZ (Uniqueness.rescaledFields S 0 a₀) +
            ENNReal.ofReal η := by
        gcongr
        linarith only [hη]
      _ ≤ s4Epsilon0 := hZstrict
  exact ⟨a, ha₀a, haB, hgeometry, hZ⟩

/-- A continuous physical field remains continuous on the closed unit
triangle after dilation by a positive cutoff inside the physical triangle. -/
theorem s6_dilated_field_continuousOn {B a : ℝ}
    (ha : 0 < a) (haB : a < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B)) :
    ContinuousOn (fun p : ℝ × ℝ => f (a • p))
      (closedCoordTriangle 0 1) := by
  have hmap : MapsTo (fun p : ℝ × ℝ => a • p)
      (closedCoordTriangle 0 1) (closedCoordTriangle 0 B) := by
    intro p hp
    change 0 ≤ a * p.1 ∧ a * p.1 ≤ a * p.2 ∧ a * p.2 ≤ B
    exact ⟨mul_nonneg ha.le hp.1,
      mul_le_mul_of_nonneg_left hp.2.1 ha.le,
      (by calc
        a * p.2 ≤ a * 1 := mul_le_mul_of_nonneg_left hp.2.2 ha.le
        _ = a := by ring
        _ ≤ B := haB.le)⟩
  exact hf.comp (by fun_prop) hmap

/-- An open-development bound for a continuous field also holds on its
closed triangular boundary. -/
theorem s6_open_bound_on_closed_triangle {c : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 1))
    (hbound : ∀ p ∈ developmentWithInitialEdge 1, c ≤ f p) :
    ∀ p ∈ closedCoordTriangle 0 1, c ≤ f p := by
  have hclosure : closure (developmentWithInitialEdge 1) =
      closedCoordTriangle 0 1 :=
    C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num)
  rw [← hclosure] at hf ⊢
  exact le_on_closure hbound continuousOn_const hf

/-- Source-form first-exit continuity. If the three infimum or supremum
bootstrap quantities and `Z` are all strictly inside their thresholds,
the admissible interval extends beyond the finite interior endpoint. -/
theorem first_exit_continuity {b B a₀ : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hprev : ∀ a : ℝ, 0 < a → a < a₀ →
      s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0) :
    s4_bootstrap (Uniqueness.rescaledFields S 0 a₀) ∧
    sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤ s4Epsilon0 ∧
    ((∃ ηG : ℝ, 0 < ηG ∧
        ∀ p ∈ developmentWithInitialEdge 1,
          (1 / 3 : ℝ) + ηG ≤ S.lam (a₀ * p.1) (a₀ * p.2) ∧
          -(2 / 3 : ℝ) + ηG ≤ S.nu (a₀ * p.1) (a₀ * p.2) ∧
          C1Solution.canonicalMassRatio b S (a₀ • p) + ηG ≤ (1 / 3 : ℝ)) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a₀) < s4Epsilon0 →
      ∃ a : ℝ, a₀ < a ∧ a < B ∧
        s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
        sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0) := by
  have hbase := first_exit_continuity_margin hB hBb ha₀ ha₀B H hprev
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  rintro ⟨⟨ηG, hηG, hstrict⟩, hZStrict⟩
  obtain ⟨r, hr, hZgap⟩ :=
    ENNReal.lt_iff_exists_add_pos_lt.mp hZStrict
  let η : ℝ := min ηG (r : ℝ)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min hηG (by exact_mod_cast hr)
  have hηGle : η ≤ ηG := min_le_left _ _
  have hηr : η ≤ (r : ℝ) := min_le_right _ _
  have hLamCont : ContinuousOn
      (fun p : ℝ × ℝ => S.lam (a₀ * p.1) (a₀ * p.2))
      (closedCoordTriangle 0 1) := by
    have h := s6_dilated_field_continuousOn ha₀ ha₀B
      (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn
    simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h
  have hNuCont : ContinuousOn
      (fun p : ℝ × ℝ => S.nu (a₀ * p.1) (a₀ * p.2))
      (closedCoordTriangle 0 1) := by
    have h := s6_dilated_field_continuousOn ha₀ ha₀B
      (C1Solution.five_fields_contDiffOn hB hBb H).2.1.continuousOn
    simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h
  have hMuCont : ContinuousOn
      (fun p : ℝ × ℝ => -C1Solution.canonicalMassRatio b S (a₀ • p))
      (closedCoordTriangle 0 1) := by
    exact (s6_dilated_field_continuousOn ha₀ ha₀B
      (C1Solution.canonicalMassRatio_continuousOn hB hBb H)).neg
  have hLamOpen : ∀ p ∈ developmentWithInitialEdge 1,
      (1 / 3 : ℝ) + η ≤ S.lam (a₀ * p.1) (a₀ * p.2) := by
    intro p hp
    have h := (hstrict p hp).1
    linarith only [h, hηGle]
  have hNuOpen : ∀ p ∈ developmentWithInitialEdge 1,
      -(2 / 3 : ℝ) + η ≤ S.nu (a₀ * p.1) (a₀ * p.2) := by
    intro p hp
    have h := (hstrict p hp).2.1
    linarith only [h, hηGle]
  have hMuOpen : ∀ p ∈ developmentWithInitialEdge 1,
      -(1 / 3 : ℝ) + η ≤
        -C1Solution.canonicalMassRatio b S (a₀ • p) := by
    intro p hp
    have h := (hstrict p hp).2.2
    linarith only [h, hηGle]
  have hLamClosed :=
    s6_open_bound_on_closed_triangle hLamCont hLamOpen
  have hNuClosed :=
    s6_open_bound_on_closed_triangle hNuCont hNuOpen
  have hMuClosed :=
    s6_open_bound_on_closed_triangle hMuCont hMuOpen
  have hmargin : ∀ p ∈ closedCoordTriangle 0 1,
      (1 / 3 : ℝ) + η ≤ S.lam (a₀ * p.1) (a₀ * p.2) ∧
      -(2 / 3 : ℝ) + η ≤ S.nu (a₀ * p.1) (a₀ * p.2) ∧
      C1Solution.canonicalMassRatio b S (a₀ • p) + η ≤ (1 / 3 : ℝ) := by
    intro p hp
    refine ⟨hLamClosed p hp, hNuClosed p hp, ?_⟩
    have h := hMuClosed p hp
    linarith only [h]
  have hηZ : ENNReal.ofReal η ≤ (r : ℝ≥0∞) := by
    have h := ENNReal.ofReal_le_ofReal hηr
    simpa only [ENNReal.ofReal_coe_nnreal] using h
  have hZmargin : sourceZ (Uniqueness.rescaledFields S 0 a₀) +
      ENNReal.ofReal η ≤ s4Epsilon0 := by
    calc
      sourceZ (Uniqueness.rescaledFields S 0 a₀) + ENNReal.ofReal η ≤
          sourceZ (Uniqueness.rescaledFields S 0 a₀) + (r : ℝ≥0∞) := by
        gcongr
      _ ≤ s4Epsilon0 := hZgap.le
  exact hbase.2.2 ⟨η, hη, hmargin, hZmargin⟩

/-- If no larger cutoff in the same finite C¹ development is admissible,
one of the four Section 6 first-exit thresholds is saturated. Saturation of
a geometric infimum or supremum is expressed by failure of every positive
uniform margin on the open development. -/
theorem first_exit_saturation {b B a₀ : ℝ}
    (hB : 0 < B) (hBb : B < b)
    (ha₀ : 0 < a₀) (ha₀B : a₀ < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hprev : ∀ a : ℝ, 0 < a → a < a₀ →
      s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
      sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0)
    (hno : ∀ a : ℝ, a₀ < a → a < B →
      ¬(s4_bootstrap (Uniqueness.rescaledFields S 0 a) ∧
        sourceZ (Uniqueness.rescaledFields S 0 a) ≤ s4Epsilon0)) :
    s4_bootstrap (Uniqueness.rescaledFields S 0 a₀) ∧
    sourceZ (Uniqueness.rescaledFields S 0 a₀) ≤ s4Epsilon0 ∧
    ((¬∃ η : ℝ, 0 < η ∧ ∀ p ∈ developmentWithInitialEdge 1,
        (1 / 3 : ℝ) + η ≤ S.lam (a₀ * p.1) (a₀ * p.2)) ∨
      (¬∃ η : ℝ, 0 < η ∧ ∀ p ∈ developmentWithInitialEdge 1,
        -(2 / 3 : ℝ) + η ≤ S.nu (a₀ * p.1) (a₀ * p.2)) ∨
      (¬∃ η : ℝ, 0 < η ∧ ∀ p ∈ developmentWithInitialEdge 1,
        C1Solution.canonicalMassRatio b S (a₀ • p) + η ≤ (1 / 3 : ℝ)) ∨
      sourceZ (Uniqueness.rescaledFields S 0 a₀) = s4Epsilon0) := by
  have hsource := first_exit_continuity hB hBb ha₀ ha₀B H hprev
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rcases lt_or_eq_of_le hsource.2.1 with hZlt | hZeq
  · classical
    by_cases hLam : ∃ η : ℝ, 0 < η ∧
        ∀ p ∈ developmentWithInitialEdge 1,
          (1 / 3 : ℝ) + η ≤ S.lam (a₀ * p.1) (a₀ * p.2)
    · by_cases hNu : ∃ η : ℝ, 0 < η ∧
          ∀ p ∈ developmentWithInitialEdge 1,
            -(2 / 3 : ℝ) + η ≤ S.nu (a₀ * p.1) (a₀ * p.2)
      · by_cases hMu : ∃ η : ℝ, 0 < η ∧
            ∀ p ∈ developmentWithInitialEdge 1,
              C1Solution.canonicalMassRatio b S (a₀ • p) + η ≤ (1 / 3 : ℝ)
        · obtain ⟨ηLam, hηLam, hLamBound⟩ := hLam
          obtain ⟨ηNu, hηNu, hNuBound⟩ := hNu
          obtain ⟨ηMu, hηMu, hMuBound⟩ := hMu
          let ηG := min ηLam (min ηNu ηMu)
          have hηG : 0 < ηG :=
            lt_min hηLam (lt_min hηNu hηMu)
          have hηGLam : ηG ≤ ηLam := min_le_left _ _
          have hηGNu : ηG ≤ ηNu :=
            (min_le_right _ _).trans (min_le_left _ _)
          have hηGMu : ηG ≤ ηMu :=
            (min_le_right _ _).trans (min_le_right _ _)
          have hG : ∀ p ∈ developmentWithInitialEdge 1,
              (1 / 3 : ℝ) + ηG ≤ S.lam (a₀ * p.1) (a₀ * p.2) ∧
              -(2 / 3 : ℝ) + ηG ≤ S.nu (a₀ * p.1) (a₀ * p.2) ∧
              C1Solution.canonicalMassRatio b S (a₀ • p) + ηG ≤
                (1 / 3 : ℝ) := by
            intro p hp
            refine ⟨?_, ?_, ?_⟩
            · have h := hLamBound p hp
              linarith only [h, hηGLam]
            · have h := hNuBound p hp
              linarith only [h, hηGNu]
            · have h := hMuBound p hp
              linarith only [h, hηGMu]
          obtain ⟨a, ha₀a, haB, hgood⟩ :=
            hsource.2.2 ⟨⟨ηG, hηG, hG⟩, hZlt⟩
          exact False.elim ((hno a ha₀a haB) hgood)
        · exact Or.inr (Or.inr (Or.inl hMu))
      · exact Or.inr (Or.inl hNu)
    · exact Or.inl hLam
  · exact Or.inr (Or.inr (Or.inr hZeq))

end ChristodoulouBV

end
