module

public import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationUnit
public import ChristodoulouBV.AreaEstimates.SmallDataFirstCoupled
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Short-cone null-integral control

On a finite closed triangle, the source null integrals are the outgoing and
incoming variations of the scalar field. A Lipschitz constant therefore
controls both suprema uniformly, including their approach to the axis.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem variation_le_lipschitz_width {f : ℝ → ℝ} {L : NNReal}
    {a b : ℝ} (_hab : a ≤ b)
    (hL : LipschitzOnWith L f (Ioo a b)) :
    eVariationOn f (Ioo a b) ≤
      (L : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  calc
    eVariationOn f (Ioo a b) ≤
        (L : ℝ≥0∞) * eVariationOn id (Ioo a b) := by
      simpa only [Function.comp_id] using
        (hL.comp_eVariationOn_le (g := id) (s := Ioo a b)
          (mapsTo_id (Ioo a b)))
    _ ≤ (L : ℝ≥0∞) * eVariationOn id (Icc a b) := by
      gcongr
      exact eVariationOn.mono id Ioo_subset_Icc_self
    _ = (L : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
      rw [eVariationOn_id_Icc]

/-- A Lipschitz constant for `phi` on the closed unit triangle bounds both
Section 4 null-integral suprema. The C¹ hypothesis is taken on a slightly
larger development so the terminal side of the unit triangle is regular. -/
theorem s6_sourceZ_le_lipschitz {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {L : NNReal}
    (hL : LipschitzOnWith L
      (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1)) :
    sourceZ S ≤ (L : ℝ≥0∞) := by
  have hphi : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) :=
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1
  have hX : sourceX S ≤ (L : ℝ≥0∞) := by
    rw [sourceX]
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
        (closedCoordTriangle 0 1) := by
      intro t ht
      simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
        (show 0 ≤ u ∧ u ≤ t ∧ t ≤ 1 from ⟨hu.1.le, ht.1, ht.2⟩)
    have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
      fun_prop
    have hslice : ContDiffOn ℝ 1 (S.phi u) (Icc u 1) :=
      hphi.comp hpair hmap
    have hAC : AbsolutelyContinuousOnInterval (S.phi u) u 1 :=
      (show ContDiffOn ℝ 1 (S.phi u) (uIcc u 1) by
        simpa only [uIcc_of_le hu.2.le] using hslice).absolutelyContinuousOnInterval
    have hsliceL : LipschitzOnWith L (S.phi u) (Ioo u 1) := by
      intro x hx y hy
      have hxK : (u, x) ∈ closedCoordTriangle 0 1 := by
        simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
          (show 0 ≤ u ∧ u ≤ x ∧ x ≤ 1 from
            ⟨hu.1.le, hx.1.le, hx.2.le⟩)
      have hyK : (u, y) ∈ closedCoordTriangle 0 1 := by
        simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
          (show 0 ≤ u ∧ u ≤ y ∧ y ≤ 1 from
            ⟨hu.1.le, hy.1.le, hy.2.le⟩)
      simpa [Prod.edist_eq] using hL hxK hyK
    have hvar := variation_le_lipschitz_width hu.2.le hsliceL
    have hwidth : ENNReal.ofReal (1 - u) ≤ (1 : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show 1 - u ≤ 1 by linarith [hu.1]))
    calc
      (∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t)) =
          eVariationOn (S.phi u) (Ioo u 1) :=
        null_lintegral_eq_scalar_variation hu.2.le hAC
          (fun t ht => outgoing_theta_over_r_eq_abs_phi_deriv hb hu ht H)
      _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (1 - u) := hvar
      _ ≤ (L : ℝ≥0∞) := by
        calc
          (L : ℝ≥0∞) * ENNReal.ofReal (1 - u) ≤
              (L : ℝ≥0∞) * 1 := by gcongr
          _ = L := mul_one _
  have hY : sourceY S ≤ (L : ℝ≥0∞) := by
    rw [sourceY]
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v)
        (closedCoordTriangle 0 1) := by
      intro t ht
      simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
        (show 0 ≤ t ∧ t ≤ v ∧ v ≤ 1 from ⟨ht.1, ht.2, hv.2.le⟩)
    have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
      fun_prop
    have hslice : ContDiffOn ℝ 1 (fun t => S.phi t v) (Icc 0 v) :=
      hphi.comp hpair hmap
    have hAC : AbsolutelyContinuousOnInterval (fun t => S.phi t v) 0 v :=
      (show ContDiffOn ℝ 1 (fun t => S.phi t v) (uIcc 0 v) by
        simpa only [uIcc_of_le hv.1.le] using hslice).absolutelyContinuousOnInterval
    have hsliceL : LipschitzOnWith L (fun t => S.phi t v) (Ioo 0 v) := by
      intro x hx y hy
      have hxK : (x, v) ∈ closedCoordTriangle 0 1 := by
        simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
          (show 0 ≤ x ∧ x ≤ v ∧ v ≤ 1 from
            ⟨hx.1.le, hx.2.le, hv.2.le⟩)
      have hyK : (y, v) ∈ closedCoordTriangle 0 1 := by
        simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
          (show 0 ≤ y ∧ y ≤ v ∧ v ≤ 1 from
            ⟨hy.1.le, hy.2.le, hv.2.le⟩)
      simpa [Prod.edist_eq] using hL hxK hyK
    have hvar := variation_le_lipschitz_width hv.1.le hsliceL
    have hwidth : ENNReal.ofReal (v - 0) ≤ (1 : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show v - 0 ≤ 1 by linarith [hv.2]))
    calc
      (∫⁻ t in Ioo 0 v, ENNReal.ofReal (|S.zeta t v| / S.r t v)) =
          eVariationOn (fun t => S.phi t v) (Ioo 0 v) :=
        null_lintegral_eq_scalar_variation hv.1.le hAC
          (fun t ht => incoming_zeta_over_r_eq_abs_phi_deriv hb hv ht H)
      _ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (v - 0) := hvar
      _ ≤ (L : ℝ≥0∞) := by
        calc
          (L : ℝ≥0∞) * ENNReal.ofReal (v - 0) ≤
              (L : ℝ≥0∞) * 1 := by gcongr
          _ = L := mul_one _
  exact max_le hX hY

/-- Dilation of a compact C¹ triangle scales a scalar Lipschitz constant by
the dilation factor. The bound is uniform over the whole unit triangle. -/
theorem s6_rescaled_phi_lipschitz {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ L : NNReal,
      ∀ h : ℝ, ∀ hh : 0 < h, ∀ _hhB : h ≤ B,
      LipschitzOnWith (L * ⟨h, hh.le⟩)
        (fun p : ℝ × ℝ =>
          (Uniqueness.rescaledFields S 0 h).phi p.1 p.2)
        (closedCoordTriangle 0 1) := by
  have hphi : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 B) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1
  obtain ⟨L, hL⟩ :=
    hphi.exists_lipschitzOnWith (by norm_num)
      (convex_closedCoordTriangle 0 B)
      (isCompact_closedCoordTriangle 0 B)
  refine ⟨L, ?_⟩
  intro h hh hhB
  have hscale : LipschitzOnWith (⟨h, hh.le⟩ : NNReal)
      (fun p : ℝ × ℝ => h • p) (closedCoordTriangle 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p _ q _
    calc
      dist (h • p) (h • q) = h * dist p q := by
        rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_pos hh, dist_eq_norm]
      _ ≤ (⟨h, hh.le⟩ : NNReal) * dist p q := by simp
  have hmap : MapsTo (fun p : ℝ × ℝ => h • p)
      (closedCoordTriangle 0 1) (closedCoordTriangle 0 B) := by
    intro p hp
    change 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 at hp
    change 0 ≤ (h • p).1 ∧ (h • p).1 ≤ (h • p).2 ∧
      (h • p).2 ≤ B
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨mul_nonneg hh.le hp.1,
      mul_le_mul_of_nonneg_left hp.2.1 hh.le,
      (mul_le_mul_of_nonneg_left hp.2.2 hh.le).trans (by simpa using hhB)⟩
  have hcomp := hL.comp hscale hmap
  have heq : ((fun p : ℝ × ℝ => S.phi p.1 p.2) ∘
      (fun p : ℝ × ℝ => h • p)) =
      (fun p : ℝ × ℝ =>
        (Uniqueness.rescaledFields S 0 h).phi p.1 p.2) := by
    funext p
    rcases p with ⟨u, v⟩
    simp [Function.comp_apply, Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate]
  rw [heq] at hcomp
  exact hcomp

/-- On every local C¹ development the Section 4 null-integral size is below
the universal threshold after restricting to a sufficiently short cone and
rescaling that cone to unit width. The cutoff depends on the solution. -/
theorem s6_exists_short_cone_sourceZ {b A : ℝ} (hb : 0 < b)
    (hA : 0 < A)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ h : ℝ, 0 < h ∧ h < A ∧ h < b ∧
      sourceZ (Uniqueness.rescaledFields S 0 h) ≤ s4Epsilon0 := by
  let B := b / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hBb : B < b := by dsimp [B]; linarith only [hb]
  obtain ⟨L, hL⟩ := s6_rescaled_phi_lipschitz hB hBb H
  let δ : ℝ := min B (min A (1 / (1000000000000 * ((L : ℝ) + 1))))
  have hden : 0 < 1000000000000 * ((L : ℝ) + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hB (lt_min hA (div_pos (by norm_num) hden))
  let h := δ / 2
  have hh : 0 < h := by dsimp [h]; positivity
  have hhδ : h ≤ δ := by dsimp [h]; linarith only [hδ]
  have hhB : h ≤ B := hhδ.trans (min_le_left _ _)
  have hhδlt : h < δ := by dsimp [h]; linarith only [hδ]
  have hhA : h < A :=
    hhδlt.trans_le ((min_le_right B _).trans (min_le_left A _))
  have hhb : h < b := lt_of_le_of_lt hhB hBb
  have hhlow : h ≤ 1 / (1000000000000 * ((L : ℝ) + 1)) :=
    (hhδ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hreal : (L : ℝ) * h ≤ 1 / 1000000000000 := by
    have hmult := (le_div_iff₀ hden).1 hhlow
    have hLnonneg : 0 ≤ (L : ℝ) := NNReal.coe_nonneg L
    have hhnonneg : 0 ≤ h := hh.le
    have hrecip : (1 / 1000000000000 : ℝ) * 1000000000000 = 1 := by
      norm_num
    nlinarith only [hmult, hLnonneg, hhnonneg, hrecip]
  let hNN : NNReal := ⟨h, hh.le⟩
  have hsmall : L * hNN ≤
      (1 / 1000000000000 : NNReal) := by
    apply NNReal.coe_le_coe.mp
    have hhcast : (hNN : ℝ) = h := rfl
    have hright : ((1 / 1000000000000 : NNReal) : ℝ) =
        1 / 1000000000000 := by norm_num
    calc
      ((L * hNN : NNReal) : ℝ) = (L : ℝ) * h := by
        rw [NNReal.coe_mul, hhcast]
      _ ≤ 1 / 1000000000000 := hreal
      _ = ((1 / 1000000000000 : NNReal) : ℝ) := hright.symm
  have hunit : 1 < b / h := by
    apply (lt_div_iff₀ hh).2
    simpa only [one_mul] using hhb
  have HT := C1Solution.rescaled_development_isC1Solution H hh
  refine ⟨h, hh, hhA, hhb, ?_⟩
  calc
    sourceZ (Uniqueness.rescaledFields S 0 h) ≤
        (↑(L * hNN) : ℝ≥0∞) := by
      exact s6_sourceZ_le_lipschitz hunit HT (hL h hh hhB)
    _ ≤ s4Epsilon0 := by
      have hcast : ((1 / 1000000000000 : NNReal) : ℝ≥0∞) =
          s4Epsilon0 := by norm_num [s4Epsilon0]
      rw [← hcast]
      exact_mod_cast hsmall

end ChristodoulouBV

end
