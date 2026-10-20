module

public import ChristodoulouBV.C1Solution.Uniqueness
public import ChristodoulouBV.C1Solution.ExtractionMass
public import ChristodoulouBV.BVSolution.C1ToBV
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Initial data and overlap compatibility for C¹ developments

The scalar radius is integrated from the axis, fixing its origin constant.
On overlaps, the canonical continuous extensions recover the auxiliary fields.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV

/-- The initial radius gauge determines the outgoing expansion on the open
initial edge of a single C¹ development. -/
theorem initial_lam_eq_of_gauge {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) : S.lam 0 v = 1 / 2 := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hv.1, hv.2]
  have hvB : v < B := by dsimp [B]; linarith [hv.2]
  have hBb : B < b := by dsimp [B]; linarith [hv.2]
  have hc : ContinuousOn (fun t : ℝ => S.lam 0 t) (Icc 0 B) :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨le_rfl, ht.1, ht.2⟩))
  apply C1Solution.initial_outgoing_density_eq_of_integral_eq hB hc
    continuousOn_const ?_ ⟨hv.1, hvB⟩
  intro t ht
  calc
    (∫ s in (0 : ℝ)..t, S.lam 0 s) = S.r 0 t := by
      exact C1Solution.canonicalRadius_eq_radius hB hBb H le_rfl ht.1 ht.2.le
    _ = t / 2 := hr t ⟨ht.1, ht.2.trans hBb⟩
    _ = ∫ _s in (0 : ℝ)..t, (1 / 2 : ℝ) := by
      simp only [intervalIntegral.integral_const]
      ring

/-- Equal initial gauge radii and outgoing scalar-radius densities give equal
scalar data. The canonical scalar radius has zero axis trace, so there is no
free integration constant at the origin. -/
theorem initial_phi_eq_of_radius_alpha_data
    {b₁ b₂ : ℝ} {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr₁ : ∀ v ∈ Ioo (0 : ℝ) b₁, S₁.r 0 v = v / 2)
    (hr₂ : ∀ v ∈ Ioo (0 : ℝ) b₂, S₂.r 0 v = v / 2)
    (hα : ∀ v ∈ Ioo (0 : ℝ) (min b₁ b₂), S₁.alpha 0 v = S₂.alpha 0 v) :
    ∀ v ∈ Ioo (0 : ℝ) (min b₁ b₂), S₁.phi 0 v = S₂.phi 0 v := by
  intro v hv
  let B : ℝ := (v + min b₁ b₂) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hv.1, hv.2]
  have hvB : v < B := by dsimp [B]; linarith [hv.2]
  have hBb₁ : B < b₁ := by dsimp [B]; have := min_le_left b₁ b₂; linarith [hv.2]
  have hBb₂ : B < b₂ := by dsimp [B]; have := min_le_right b₁ b₂; linarith [hv.2]
  have hc₁ : ContinuousOn (fun t : ℝ => S₁.alpha 0 t) (Icc 0 B) :=
    (C1Solution.alpha_contDiffOn hB hBb₁ H₁).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
  have hc₂ : ContinuousOn (fun t : ℝ => S₂.alpha 0 t) (Icc 0 B) :=
    (C1Solution.alpha_contDiffOn hB hBb₂ H₂).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
  have hαB : EqOn (fun t : ℝ => S₁.alpha 0 t)
      (fun t => S₂.alpha 0 t) (Icc 0 B) := by
    have hopen : EqOn (fun t : ℝ => S₁.alpha 0 t)
        (fun t => S₂.alpha 0 t) (Ioo 0 B) := by
      intro t ht
      exact hα t ⟨ht.1, ht.2.trans (by dsimp [B] at hBb₁ hBb₂ ⊢; linarith [hv.2])⟩
    exact hopen.of_subset_closure hc₁ hc₂ Ioo_subset_Icc_self
      (by rw [closure_Ioo hB.ne])
  have hψ : C1Solution.canonicalScalarRadius S₁ (0, v) =
      C1Solution.canonicalScalarRadius S₂ (0, v) := by
    change (∫ t in (0 : ℝ)..v, S₁.alpha 0 t) =
      ∫ t in (0 : ℝ)..v, S₂.alpha 0 t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1.le] at ht
    exact hαB ⟨ht.1, ht.2.trans hvB.le⟩
  have hp : (0, v) ∈ closedCoordTriangle 0 B := ⟨le_rfl, hv.1.le, hvB.le⟩
  rw [C1Solution.canonicalScalarRadius_eq_canonicalRadius_mul_phi hB hBb₁ H₁ hp,
    C1Solution.canonicalScalarRadius_eq_canonicalRadius_mul_phi hB hBb₂ H₂ hp,
    C1Solution.canonicalRadius_eq_radius hB hBb₁ H₁ le_rfl hv.1 hvB.le,
    C1Solution.canonicalRadius_eq_radius hB hBb₂ H₂ le_rfl hv.1 hvB.le,
    hr₁ v ⟨hv.1, hv.2.trans_le (min_le_left _ _)⟩,
    hr₂ v ⟨hv.1, hv.2.trans_le (min_le_right _ _)⟩] at hψ
  exact mul_left_cancel₀ (ne_of_gt (half_pos hv.1)) hψ

private theorem eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle {B : ℝ}
    (hB : 0 < B) {F₁ F₂ : ℝ × ℝ → ℝ}
    (hF₁ : ContinuousOn F₁ (closedCoordTriangle 0 B))
    (hF₂ : ContinuousOn F₂ (closedCoordTriangle 0 B))
    (hEq : EqOn F₁ F₂ (openCoordTriangle 0 B)) :
    EqOn F₁ F₂ (closedCoordTriangle 0 B) :=
  hEq.of_subset_closure hF₁ hF₂
    (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
    (by rw [closure_openCoordTriangle hB])

/-- Equal radius, scalar field, and mass on the strict common overlap recover
all six auxiliary fields there. Canonical extensions are used only on smaller
closed triangles, where the frozen total radius and mass need not have values
on the excluded axis. -/
theorem fields_eq_on_open_overlap_of_r_phi_m_eq
    {b₁ b₂ : ℝ} {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (heq : ∀ p ∈ openDevelopment 0 (min b₁ b₂),
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.m p.1 p.2 = S₂.m p.1 p.2) :
    ∀ p ∈ openDevelopment 0 (min b₁ b₂),
      S₁.lam p.1 p.2 = S₂.lam p.1 p.2 ∧
      S₁.nu p.1 p.2 = S₂.nu p.1 p.2 ∧
      S₁.alpha p.1 p.2 = S₂.alpha p.1 p.2 ∧
      S₁.beta p.1 p.2 = S₂.beta p.1 p.2 ∧
      S₁.theta p.1 p.2 = S₂.theta p.1 p.2 ∧
      S₁.zeta p.1 p.2 = S₂.zeta p.1 p.2 := by
  intro p hp
  let B : ℝ := (p.2 + min b₁ b₂) / 2
  have hBmin : B < min b₁ b₂ := by dsimp [B]; linarith [hp.2.2]
  have hB : 0 < B := by dsimp [B]; linarith [hp.1.1, hp.2.1, hp.2.2]
  have hBb₁ : B < b₁ := hBmin.trans_le (min_le_left _ _)
  have hBb₂ : B < b₂ := hBmin.trans_le (min_le_right _ _)
  have hpB : p ∈ closedCoordTriangle 0 B :=
    ⟨hp.1.1.le, hp.2.1.le, by dsimp [B]; linarith [hp.2.2]⟩
  have hsubset : openCoordTriangle 0 B ⊆ openDevelopment 0 (min b₁ b₂) := by
    intro q hq
    exact ⟨⟨hq.1, (hq.2.1.trans hq.2.2).trans hBmin⟩,
      ⟨hq.2.1, hq.2.2.trans hBmin⟩⟩
  have hrOpen : EqOn (C1Solution.canonicalRadius S₁)
      (C1Solution.canonicalRadius S₂) (openCoordTriangle 0 B) := by
    rintro ⟨u, v⟩ hq
    rw [C1Solution.canonicalRadius_eq_radius hB hBb₁ H₁ hq.1.le hq.2.1 hq.2.2.le,
      C1Solution.canonicalRadius_eq_radius hB hBb₂ H₂ hq.1.le hq.2.1 hq.2.2.le]
    exact (heq (u, v) (hsubset hq)).1
  have hr : EqOn (C1Solution.canonicalRadius S₁)
      (C1Solution.canonicalRadius S₂) (closedCoordTriangle 0 B) :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.canonicalRadius_contDiffOn hB hBb₁ H₁).continuousOn
      (C1Solution.canonicalRadius_contDiffOn hB hBb₂ H₂).continuousOn hrOpen
  have hψOpen : EqOn (C1Solution.canonicalScalarRadius S₁)
      (C1Solution.canonicalScalarRadius S₂) (openCoordTriangle 0 B) := by
    rintro ⟨u, v⟩ hq
    rw [C1Solution.canonicalScalarRadius_eq_radius_mul_phi hB hBb₁ H₁
        hq.1.le hq.2.1 hq.2.2.le,
      C1Solution.canonicalScalarRadius_eq_radius_mul_phi hB hBb₂ H₂
        hq.1.le hq.2.1 hq.2.2.le]
    obtain ⟨hrval, hphival, _⟩ := heq (u, v) (hsubset hq)
    rw [hrval, hphival]
  have hψ : EqOn (C1Solution.canonicalScalarRadius S₁)
      (C1Solution.canonicalScalarRadius S₂) (closedCoordTriangle 0 B) :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.canonicalScalarRadius_contDiffOn hB hBb₁ H₁).continuousOn
      (C1Solution.canonicalScalarRadius_contDiffOn hB hBb₂ H₂).continuousOn hψOpen
  have hmOpen : EqOn (C1Solution.canonicalMass b₁ S₁)
      (C1Solution.canonicalMass b₂ S₂) (openCoordTriangle 0 B) := by
    intro q hq
    have hqD := hsubset hq
    rw [C1Solution.canonicalMass_eq_mass
        (show q ∈ developmentWithInitialEdge b₁ from
          ⟨hq.1.le, hq.2.1, hq.2.2.trans hBb₁⟩),
      C1Solution.canonicalMass_eq_mass
        (show q ∈ developmentWithInitialEdge b₂ from
          ⟨hq.1.le, hq.2.1, hq.2.2.trans hBb₂⟩)]
    exact (heq q hqD).2.2
  have hm : EqOn (C1Solution.canonicalMass b₁ S₁)
      (C1Solution.canonicalMass b₂ S₂) (closedCoordTriangle 0 B) :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.canonicalMass_contDiffOn hB hBb₁ H₁).continuousOn
      (C1Solution.canonicalMass_contDiffOn hB hBb₂ H₂).continuousOn hmOpen
  obtain ⟨_, _, _, hlam, hnu, halpha, hbeta⟩ :=
    C1Solution.fields_eq_of_canonical_eq hB hBb₁ hBb₂ H₁ H₂ hr hψ hm
      hp.1.1.le hp.2.1 hpB.2.2
  have hphi := (heq p hp).2.1
  refine ⟨hlam, hnu, halpha, hbeta, ?_, ?_⟩
  · simp only [Fields.theta]
    rw [halpha, hlam, hphi]
  · simp only [Fields.zeta]
    rw [hbeta, hnu, hphi]

/-- On a smaller compact triangle, equality on the strict overlap extends to
equality of the relative first jets of all seven C¹ fields. These are jets of
the actual fields, not claims about total radius or mass values on the axis. -/
theorem c1_field_jets_eq_on_compact_closure_of_r_phi_m_eq
    {b₁ b₂ B : ℝ} (hB : 0 < B) (hBb₁ : B < b₁) (hBb₂ : B < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (heq : ∀ p ∈ openDevelopment 0 (min b₁ b₂),
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.m p.1 p.2 = S₂.m p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.nu q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.nu q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.alpha q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.alpha q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.beta q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.beta q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.phi q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.phi q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.theta q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.theta q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.zeta q.1 q.2)
      (closedCoordTriangle 0 B) p) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.zeta q.1 q.2)
          (closedCoordTriangle 0 B) p) ∧
    S₁.lam p.1 p.2 = S₂.lam p.1 p.2 ∧
    S₁.nu p.1 p.2 = S₂.nu p.1 p.2 ∧
    S₁.alpha p.1 p.2 = S₂.alpha p.1 p.2 ∧
    S₁.beta p.1 p.2 = S₂.beta p.1 p.2 ∧
    S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
    S₁.theta p.1 p.2 = S₂.theta p.1 p.2 ∧
    S₁.zeta p.1 p.2 = S₂.zeta p.1 p.2 := by
  let K := closedCoordTriangle 0 B
  have hBmin : B < min b₁ b₂ := lt_min hBb₁ hBb₂
  have hsubset : openCoordTriangle 0 B ⊆ openDevelopment 0 (min b₁ b₂) := by
    intro q hq
    exact ⟨⟨hq.1, (hq.2.1.trans hq.2.2).trans hBmin⟩,
      ⟨hq.2.1, hq.2.2.trans hBmin⟩⟩
  have hfields (q : ℝ × ℝ) (hq : q ∈ openCoordTriangle 0 B) :=
    fields_eq_on_open_overlap_of_r_phi_m_eq H₁ H₂ heq q (hsubset hq)
  have hKlam : EqOn (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
      (fun q => S₂.lam q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.five_fields_contDiffOn hB hBb₁ H₁).1.continuousOn
      (C1Solution.five_fields_contDiffOn hB hBb₂ H₂).1.continuousOn
      (fun q hq => (hfields q hq).1)
  have hKnu : EqOn (fun q : ℝ × ℝ => S₁.nu q.1 q.2)
      (fun q => S₂.nu q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.five_fields_contDiffOn hB hBb₁ H₁).2.1.continuousOn
      (C1Solution.five_fields_contDiffOn hB hBb₂ H₂).2.1.continuousOn
      (fun q hq => (hfields q hq).2.1)
  have hKalpha : EqOn (fun q : ℝ × ℝ => S₁.alpha q.1 q.2)
      (fun q => S₂.alpha q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.alpha_contDiffOn hB hBb₁ H₁).continuousOn
      (C1Solution.alpha_contDiffOn hB hBb₂ H₂).continuousOn
      (fun q hq => (hfields q hq).2.2.1)
  have hKbeta : EqOn (fun q : ℝ × ℝ => S₁.beta q.1 q.2)
      (fun q => S₂.beta q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.beta_contDiffOn hB hBb₁ H₁).continuousOn
      (C1Solution.beta_contDiffOn hB hBb₂ H₂).continuousOn
      (fun q hq => (hfields q hq).2.2.2.1)
  have hKphi : EqOn (fun q : ℝ × ℝ => S₁.phi q.1 q.2)
      (fun q => S₂.phi q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.five_fields_contDiffOn hB hBb₁ H₁).2.2.1.continuousOn
      (C1Solution.five_fields_contDiffOn hB hBb₂ H₂).2.2.1.continuousOn
      (fun q hq => (heq q (hsubset hq)).2.1)
  have hKtheta : EqOn (fun q : ℝ × ℝ => S₁.theta q.1 q.2)
      (fun q => S₂.theta q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.five_fields_contDiffOn hB hBb₁ H₁).2.2.2.1.continuousOn
      (C1Solution.five_fields_contDiffOn hB hBb₂ H₂).2.2.2.1.continuousOn
      (fun q hq => (hfields q hq).2.2.2.2.1)
  have hKzeta : EqOn (fun q : ℝ × ℝ => S₁.zeta q.1 q.2)
      (fun q => S₂.zeta q.1 q.2) K :=
    eqOn_closedCoordTriangle_of_eqOn_openCoordTriangle hB
      (C1Solution.five_fields_contDiffOn hB hBb₁ H₁).2.2.2.2.continuousOn
      (C1Solution.five_fields_contDiffOn hB hBb₂ H₂).2.2.2.2.continuousOn
      (fun q hq => (hfields q hq).2.2.2.2.2)
  exact ⟨fderivWithin_congr' hKlam hp,
    fderivWithin_congr' hKnu hp,
    fderivWithin_congr' hKalpha hp,
    fderivWithin_congr' hKbeta hp,
    fderivWithin_congr' hKphi hp,
    fderivWithin_congr' hKtheta hp,
    fderivWithin_congr' hKzeta hp,
    hKlam hp, hKnu hp, hKalpha hp, hKbeta hp, hKphi hp, hKtheta hp, hKzeta hp⟩

end ChristodoulouBV

end
