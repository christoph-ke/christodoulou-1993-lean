module

public import ChristodoulouBV.Existence.C1EndpointMeasure
public import ChristodoulouBV.AreaEstimates.SmallData
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Coordinate dilation for endpoint analytic areas

The rescaling of Section 6 acts on both null coordinates by the same
positive factor. Its coordinate map takes the unit triangle onto the
corresponding finite triangle.
-/

public section

open Set

namespace ChristodoulouBV

/-- The positive coordinate dilation as a homeomorphism of the null plane. -/
noncomputable def s6Dilation (a : ℝ) (ha : a ≠ 0) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Homeomorph.smulOfNeZero a ha

/-- Evaluation of the positive coordinate dilation. -/
theorem s6Dilation_apply (a : ℝ) (ha : a ≠ 0) (p : ℝ × ℝ) :
    s6Dilation a ha p = (a * p.1, a * p.2) := by
  ext <;> simp [s6Dilation, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]

/-- Evaluation of the inverse coordinate dilation. -/
theorem s6Dilation_symm_apply (a : ℝ) (ha : a ≠ 0) (p : ℝ × ℝ) :
    (s6Dilation a ha).symm p = (p.1 / a, p.2 / a) := by
  ext <;> simp [s6Dilation, div_eq_mul_inv, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, mul_comm]

/-- A positive dilation maps the open unit triangle exactly to the open
triangle with terminal parameter `a`. -/
theorem s6Dilation_image_unit {a : ℝ} (ha : 0 < a) :
    s6Dilation a ha.ne' '' openCoordTriangle 0 1 =
      openCoordTriangle 0 a := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp only [openCoordTriangle, mem_ofPred_eq] at hq ⊢
    rw [s6Dilation_apply]
    constructor
    · exact mul_pos ha hq.1
    constructor
    · exact mul_lt_mul_of_pos_left hq.2.1 ha
    · have := mul_lt_mul_of_pos_left hq.2.2 ha
      nlinarith
  · intro hp
    simp only [openCoordTriangle, mem_ofPred_eq] at hp
    refine ⟨(p.1 / a, p.2 / a), ?_, ?_⟩
    · simp only [openCoordTriangle, mem_ofPred_eq]
      exact ⟨div_pos hp.1 ha,
        div_lt_div_of_pos_right hp.2.1 ha,
        (div_lt_one ha).mpr hp.2.2⟩
    · rw [s6Dilation_apply]
      simp only [mul_div_cancel₀ _ ha.ne']

/-- Analytic area is unchanged when a smooth map on the unit triangle is
expressed in coordinates dilated by a positive factor. -/
theorem s6_analytic_area_dilation (F : ℝ × ℝ → ℝ × ℝ)
    {a : ℝ} (ha : 0 < a)
    (hF : ContDiffOn ℝ 1 F (openCoordTriangle 0 1)) :
    smoothAnalyticArea (F ∘ (s6Dilation a ha.ne').symm)
      (openCoordTriangle 0 a) =
      smoothAnalyticArea F (openCoordTriangle 0 1) := by
  let e := s6Dilation a ha.ne'
  have hOpen : IsOpen (openCoordTriangle 0 1) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have he : ContDiffOn ℝ 1 (e.symm : ℝ × ℝ → ℝ × ℝ)
      (e '' openCoordTriangle 0 1) := by
    have heEq : (e.symm : ℝ × ℝ → ℝ × ℝ) =
        fun p => a⁻¹ • p := by
      exact Homeomorph.smulOfNeZero_symm_apply ha.ne'
    rw [heEq]
    exact (ContDiff.const_smul a⁻¹ contDiff_id).contDiffOn
  have h := analytic_area_change F e hOpen hF he
  rw [s6Dilation_image_unit ha] at h
  exact h

/-- The four source maps are C¹ on the strict unit triangle.  The scalar
quotients need the nonvanishing null expansions supplied by the bootstrap. -/
theorem s6_source_maps_contDiffOn_open {T : Fields}
    (HT : IsC1Solution (developmentWithInitialEdge 1) T)
    (hboot : s4_bootstrap T) :
    ContDiffOn ℝ 1 (sourcePhiAlphaLamMap T) (openCoordTriangle 0 1) ∧
    ContDiffOn ℝ 1 (sourcePhiBetaNuMap T) (openCoordTriangle 0 1) ∧
    ContDiffOn ℝ 1 (sourceLamPhiMap T) (openCoordTriangle 0 1) ∧
    ContDiffOn ℝ 1 (sourceNuPhiMap T) (openCoordTriangle 0 1) := by
  let U := openCoordTriangle (0 : ℝ) 1
  have hUK : U ⊆ closedCoordTriangle 0 1 := by
    change openCoordTriangle 0 1 ⊆ closedCoordTriangle 0 1
    rw [← interior_closedCoordTriangle]
    exact interior_subset
  obtain ⟨hlam, hnu, hphi, halpha, hbeta⟩ := unit_field_contDiffOn HT
  have hLamNe : ∀ p ∈ U, T.lam p.1 p.2 ≠ 0 := by
    intro p hp
    have hp' : p ∈ developmentWithInitialEdge 1 := by
      simp only [U, openCoordTriangle, mem_ofPred_eq] at hp
      exact ⟨hp.1.le, hp.2.1, hp.2.2⟩
    exact ne_of_gt (HT.solution.lam_pos p hp')
  have hNuNe : ∀ p ∈ U, T.nu p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_lt (lt_of_le_of_lt
      (sourceNu_le_neg_third HT hboot hp) (by norm_num))
  exact ⟨(hphi.mono hUK).prodMk
      ((halpha.mono hUK).div (hlam.mono hUK) hLamNe),
    (hphi.mono hUK).prodMk
      ((hbeta.mono hUK).div (hnu.mono hUK) hNuNe),
    (sourceLamPhiMap_contDiffOn HT).mono hUK,
    (sourceNuPhiMap_contDiffOn HT).mono hUK⟩

/-- The four analytic areas of a rescaled C¹ solution agree with the areas
on its original finite triangle. -/
theorem s6_rescaled_four_areas (S : Fields) {a : ℝ} (ha : 0 < a)
    (HT : IsC1Solution (developmentWithInitialEdge 1)
      (Uniqueness.rescaledFields S 0 a))
    (hboot : s4_bootstrap (Uniqueness.rescaledFields S 0 a)) :
    let T := Uniqueness.rescaledFields S 0 a
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourcePhiAlphaLamMap T) (openCoordTriangle 0 1) ∧
    smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourcePhiBetaNuMap T) (openCoordTriangle 0 1) ∧
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourceLamPhiMap T) (openCoordTriangle 0 1) ∧
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourceNuPhiMap T) (openCoordTriangle 0 1) := by
  let e := s6Dilation a ha.ne'
  let T := Uniqueness.rescaledFields S 0 a
  have hcoord (p : ℝ × ℝ) :
      Uniqueness.affineCoordinate 0 a ((e.symm p).1) = p.1 ∧
      Uniqueness.affineCoordinate 0 a ((e.symm p).2) = p.2 := by
    rw [s6Dilation_symm_apply]
    simp only [Uniqueness.affineCoordinate, zero_add,
      mul_div_cancel₀ _ ha.ne', and_self]
  have hAe : sourcePhiAlphaLamMap T ∘ e.symm = sourcePhiAlphaLamMap S := by
    funext p
    simp only [Function.comp_apply, sourcePhiAlphaLamMap,
      T, Uniqueness.rescaledFields, (hcoord p).1, (hcoord p).2]
  have hBe : sourcePhiBetaNuMap T ∘ e.symm = sourcePhiBetaNuMap S := by
    funext p
    simp only [Function.comp_apply, sourcePhiBetaNuMap,
      T, Uniqueness.rescaledFields, (hcoord p).1, (hcoord p).2]
  have hLe : sourceLamPhiMap T ∘ e.symm = sourceLamPhiMap S := by
    funext p
    simp only [Function.comp_apply, sourceLamPhiMap,
      T, Uniqueness.rescaledFields, (hcoord p).1, (hcoord p).2]
  have hNe : sourceNuPhiMap T ∘ e.symm = sourceNuPhiMap S := by
    funext p
    simp only [Function.comp_apply, sourceNuPhiMap,
      T, Uniqueness.rescaledFields, (hcoord p).1, (hcoord p).2]
  obtain ⟨hA, hB, hL, hN⟩ := s6_source_maps_contDiffOn_open HT hboot
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hAe]
    exact s6_analytic_area_dilation _ ha hA
  · rw [← hBe]
    exact s6_analytic_area_dilation _ ha hB
  · rw [← hLe]
    exact s6_analytic_area_dilation _ ha hL
  · rw [← hNe]
    exact s6_analytic_area_dilation _ ha hN

/-- Positive dilation takes a moving unit wedge to the corresponding wedge
inside the original finite cutoff. -/
theorem s6Dilation_image_wedge {a u : ℝ} (ha : 0 < a)
    (_hu : 0 < u) (_hua : u < a) :
    s6Dilation a ha.ne' ''
      (Ioo (0 : ℝ) (u / a) ×ˢ Ioo (u / a) 1) =
      Ioo (0 : ℝ) u ×ˢ Ioo u a := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq₁, hq₂⟩, rfl⟩
    rw [s6Dilation_apply]
    constructor
    · exact ⟨mul_pos ha hq₁.1,
        by simpa only [mul_div_cancel₀ _ ha.ne'] using
          (mul_lt_mul_of_pos_left hq₁.2 ha)⟩
    · exact ⟨by simpa only [mul_div_cancel₀ _ ha.ne'] using
          (mul_lt_mul_of_pos_left hq₂.1 ha),
        by simpa only [mul_one] using
          (mul_lt_mul_of_pos_left hq₂.2 ha)⟩
  · rintro ⟨hp₁, hp₂⟩
    refine ⟨(p.1 / a, p.2 / a), ?_, ?_⟩
    · exact ⟨⟨div_pos hp₁.1 ha,
          div_lt_div_of_pos_right hp₁.2 ha⟩,
        ⟨div_lt_div_of_pos_right hp₂.1 ha,
          (div_lt_one ha).mpr hp₂.2⟩⟩
    · rw [s6Dilation_apply]
      simp only [mul_div_cancel₀ _ ha.ne']

/-- Change of coordinates for analytic area on any open subset of the unit
triangle. -/
theorem s6_analytic_area_dilation_open (F : ℝ × ℝ → ℝ × ℝ)
    {a : ℝ} (ha : 0 < a) {E : Set (ℝ × ℝ)}
    (hOpen : IsOpen E) (hF : ContDiffOn ℝ 1 F E) :
    smoothAnalyticArea (F ∘ (s6Dilation a ha.ne').symm)
      (s6Dilation a ha.ne' '' E) = smoothAnalyticArea F E := by
  let e := s6Dilation a ha.ne'
  have he : ContDiffOn ℝ 1 (e.symm : ℝ × ℝ → ℝ × ℝ)
      (e '' E) := by
    have heEq : (e.symm : ℝ × ℝ → ℝ × ℝ) =
        fun p => a⁻¹ • p := by
      exact Homeomorph.smulOfNeZero_symm_apply ha.ne'
    rw [heEq]
    exact (ContDiff.const_smul a⁻¹ contDiff_id).contDiffOn
  exact analytic_area_change F e hOpen hF he

/-- The two analytic-area terms in the outgoing transport inequalities are
unchanged when a finite cutoff is rescaled to the unit triangle. -/
theorem s6_rescaled_outgoing_wedge_areas
    (S : Fields) {a u : ℝ} (ha : 0 < a) (hu : 0 < u) (hua : u < a)
    (HT : IsC1Solution (developmentWithInitialEdge 1)
      (Uniqueness.rescaledFields S 0 a))
    (hboot : s4_bootstrap (Uniqueness.rescaledFields S 0 a)) :
    let T := Uniqueness.rescaledFields S 0 a
    smoothAnalyticArea (sourceLamPhiMap S)
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) =
      smoothAnalyticArea (sourceLamPhiMap T)
        (Ioo (0 : ℝ) (u / a) ×ˢ Ioo (u / a) 1) ∧
    smoothAnalyticArea (sourcePhiBetaNuMap S)
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) =
      smoothAnalyticArea (sourcePhiBetaNuMap T)
        (Ioo (0 : ℝ) (u / a) ×ˢ Ioo (u / a) 1) := by
  let e := s6Dilation a ha.ne'
  let T := Uniqueness.rescaledFields S 0 a
  let E := Ioo (0 : ℝ) (u / a) ×ˢ Ioo (u / a) 1
  have hEopen : IsOpen E := isOpen_Ioo.prod isOpen_Ioo
  have huUnit : 0 < u / a ∧ u / a < 1 :=
    ⟨div_pos hu ha, (div_lt_one ha).mpr hua⟩
  have hEsub : E ⊆ openCoordTriangle 0 1 := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩
  have hcoord (p : ℝ × ℝ) :
      Uniqueness.affineCoordinate 0 a ((e.symm p).1) = p.1 ∧
      Uniqueness.affineCoordinate 0 a ((e.symm p).2) = p.2 := by
    rw [s6Dilation_symm_apply]
    simp only [Uniqueness.affineCoordinate, zero_add,
      mul_div_cancel₀ _ ha.ne', and_self]
  have hLamMap : sourceLamPhiMap T ∘ e.symm = sourceLamPhiMap S := by
    funext p
    simp only [Function.comp_apply, sourceLamPhiMap,
      T, Uniqueness.rescaledFields, (hcoord p).1, (hcoord p).2]
  have hBetaMap : sourcePhiBetaNuMap T ∘ e.symm =
      sourcePhiBetaNuMap S := by
    funext p
    simp only [Function.comp_apply, sourcePhiBetaNuMap,
      T, Uniqueness.rescaledFields, (hcoord p).1, (hcoord p).2]
  obtain ⟨_, hBetaC1, hLamC1, _⟩ :=
    s6_source_maps_contDiffOn_open HT hboot
  constructor
  · rw [← s6Dilation_image_wedge ha hu hua, ← hLamMap]
    exact s6_analytic_area_dilation_open _ ha hEopen (hLamC1.mono hEsub)
  · rw [← s6Dilation_image_wedge ha hu hua, ← hBetaMap]
    exact s6_analytic_area_dilation_open _ ha hEopen (hBetaC1.mono hEsub)

end ChristodoulouBV

end
