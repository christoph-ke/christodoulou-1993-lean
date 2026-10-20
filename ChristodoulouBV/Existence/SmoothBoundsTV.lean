module

public import ChristodoulouBV.Existence.SmoothBoundsCore
import all ChristodoulouBV.AreaEstimates.SmallDataLemma
import Mathlib.Tactic

/-!+# Uniform ray variation of the centered smooth fields

Lemma 4.3 is used on every physical cutoff. Finite ordered partitions then
exhaust outgoing rays. The initial ray is treated using the exact gauge and
datum trace, so the three-term estimates retain `u = 0`.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The fixed universal area and variation coefficient is at least one. -/
theorem s4UniversalC_one_le : (1 : ℝ≥0∞) ≤ s4UniversalC := by
  norm_num [s4UniversalC]

/-- Bounds on every finite outgoing interval control the full outgoing
ray, by the finite-partition definition of variation. -/
theorem smooth_variation_Ioi_le_of_cutoffs (f : ℝ → ℝ) (u : ℝ) {C : ℝ≥0∞}
    (hcut : ∀ a : ℝ, u < a → eVariationOn f (Ioo u a) ≤ C) :
    eVariationOn f (Ioi u) ≤ C := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  refine iSup_le (fun p => iSup_le (fun hp => ?_))
  obtain ⟨_, hp₂, _⟩ := hp
  have hsub : Ioi u ∩ Icc p.1 p.2 ⊆ Ioo u (p.2 + 1) :=
    fun _ hx => ⟨hx.1, hx.2.2.trans_lt (lt_add_one p.2)⟩
  exact (eVariationOn.mono f hsub).trans
    (hcut (p.2 + 1) (hp₂.trans (lt_add_one p.2)))

/-- Centered field and logarithmic expansion variation on finite physical
null segments. All constants are independent of the cutoff. -/
theorem smooth_centered_variation_cutoffs
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    let P := smoothCenteredFields S
    let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
    (∀ u a : ℝ, 0 ≤ u → u < a →
      eVariationOn (P.alpha u) (Ioo u a) ≤ s4UniversalC * D ∧
      eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u a) ≤ s4UniversalC * D ^ 2) ∧
    (∀ v : ℝ, 0 < v →
      eVariationOn (fun u => P.beta u v) (Ioo 0 v) ≤ s4UniversalC * D ∧
      eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤ s4UniversalC * D ^ 2) := by
  let P := smoothCenteredFields S
  let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
  have hlocal (a : ℝ) (ha : 0 < a) :=
    smooth_centered_chart_bounds hfinite hdata hD ha
  constructor
  · intro u a hu hua
    have ha := hu.trans_lt hua
    let Q := Uniqueness.rescaledFields P 0 a
    obtain ⟨HQ, hr, hc, hb, hQD, hDsmall, hZsmall⟩ := hlocal a ha
    rcases eq_or_lt_of_le hu with hzero | hpos
    · subst u
      have hα : eVariationOn (P.alpha 0) (Ioo 0 a) = sourceD Q := by
        simpa only [Q] using (sourceD_rescaled_eq_cutoff P ha).symm
      have hlam : EqOn (fun v => Real.log (S.lam 0 v))
          (fun _ => Real.log (1 / 2 : ℝ)) (Ioo 0 a) := by
        intro v hv
        change Real.log (S.lam 0 v) = Real.log (1 / 2 : ℝ)
        rw [initial_lam_eq_of_gauge (hfinite a ha)
          (fun w hw => (hdata w hw.1).1) hv]
      rw [eVariationOn.congr hlam]
      refine ⟨?_, ?_⟩
      · rw [hα]
        exact hQD.trans (by
          simpa only [one_mul] using (mul_le_mul' s4UniversalC_one_le (le_refl D)))
      · have hconst : eVariationOn (fun _ : ℝ => Real.log (1 / 2 : ℝ)) (Ioo 0 a) = 0 :=
          (eVariationOn.eq_zero_iff _).mpr (fun _ _ _ _ => edist_self _)
        exact hconst ▸ bot_le
    · have hu' : u / a ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos hpos ha, (div_lt_one ha).mpr hua⟩
      have hlemma := lemma4_3 HQ hr hc hb hDsmall hZsmall
      have hα := (le_iSup_of_le (u / a) (le_iSup_of_le hu' le_rfl)).trans hlemma.2.1.2.1
      have hl := (le_iSup_of_le (u / a) (le_iSup_of_le hu' le_rfl)).trans hlemma.2.2.1.2.1
      have hscaleα := e1_variation_scale_Ioo (P.alpha u) (a := u / a) (b := 1) ha
      have hscalel := e1_variation_scale_Ioo (fun v => Real.log (S.lam u v))
        (a := u / a) (b := 1) ha
      have hau : a * (u / a) = u := mul_div_cancel₀ _ ha.ne'
      have hαD : eVariationOn (Q.alpha (u / a)) (Ioo (u / a) 1) ≤
          s4UniversalC * D := hα.trans (mul_le_mul' le_rfl hQD)
      have hlD : eVariationOn (fun v => Real.log (Q.lam (u / a) v)) (Ioo (u / a) 1) ≤
          s4UniversalC * D ^ 2 := hl.trans (by gcongr)
      simp only [Q, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
        zero_add, hau] at hαD hlD
      rw [hscaleα] at hαD
      change eVariationOn (fun v => Real.log (S.lam u (a * v))) (Ioo (u / a) 1) ≤ _ at hlD
      rw [hscalel] at hlD
      simpa only [hau, mul_one] using And.intro hαD hlD
  · intro v hv
    let a := v + 1
    have ha : 0 < a := by dsimp [a]; linarith only [hv]
    let Q := Uniqueness.rescaledFields P 0 a
    obtain ⟨HQ, hr, hc, hb, hQD, hDsmall, hZsmall⟩ := hlocal a ha
    have hv' : v / a ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hv ha, (div_lt_one ha).mpr (lt_add_one v)⟩
    have hlemma := lemma4_3 HQ hr hc hb hDsmall hZsmall
    have hβ := (le_iSup_of_le (v / a) (le_iSup_of_le hv' le_rfl)).trans hlemma.2.1.2.2
    have hn := (le_iSup_of_le (v / a) (le_iSup_of_le hv' le_rfl)).trans hlemma.2.2.1.2.2
    have hscaleβ := e1_variation_scale_Ioo (fun u => P.beta u v)
      (a := 0) (b := v / a) ha
    have hscalen := e1_variation_scale_Ioo (fun u => Real.log (-S.nu u v))
      (a := 0) (b := v / a) ha
    have hav : a * (v / a) = v := mul_div_cancel₀ _ ha.ne'
    have hβD : eVariationOn (fun u => Q.beta u (v / a)) (Ioo 0 (v / a)) ≤
        s4UniversalC * D := hβ.trans (mul_le_mul' le_rfl hQD)
    have hnD : eVariationOn (fun u => Real.log (-Q.nu u (v / a))) (Ioo 0 (v / a)) ≤
        s4UniversalC * D ^ 2 := hn.trans (by gcongr)
    simp only [Q, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, hav] at hβD hnD
    rw [hscaleβ] at hβD
    change eVariationOn (fun u => Real.log (-S.nu (a * u) v)) (Ioo 0 (v / a)) ≤ _ at hnD
    rw [hscalen] at hnD
    simpa only [hav, mul_zero] using And.intro hβD hnD

/-- On complete rays, centered scalar-radius derivatives have `O(D)`
variation and the two expansions have `O(D²)` variation. -/
theorem smooth_centered_variation_bounds
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    let P := smoothCenteredFields S
    let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
    (∀ u : ℝ, 0 ≤ u →
      eVariationOn (P.alpha u) (Ioi u) ≤ s4UniversalC * D ∧
      eVariationOn (S.lam u) (Ioi u) ≤ s4UniversalC * D ^ 2) ∧
    (∀ v : ℝ, 0 < v →
      eVariationOn (fun u => P.beta u v) (Ioo 0 v) ≤ s4UniversalC * D ∧
      eVariationOn (fun u => S.nu u v) (Ioo 0 v) ≤ s4UniversalC * D ^ 2) := by
  obtain ⟨hout, hin⟩ := smooth_centered_variation_cutoffs hfinite hdata hD
  have hg := global_c1_geometry hfinite hdata hD
  constructor
  · intro u hu
    have hl : eVariationOn (fun v => Real.log (S.lam u v)) (Ioi u) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi 0) ^ 2 :=
      smooth_variation_Ioi_le_of_cutoffs _ _ (fun a hua => (hout u a hu hua).2)
    refine ⟨smooth_variation_Ioi_le_of_cutoffs _ _
      (fun a hua => (hout u a hu hua).1), ?_⟩
    exact (s4_variation_le_log_of_pos_le_one
      (fun v hv => (by norm_num : (0 : ℝ) < 1 / 3).trans_le (hg (u, v) ⟨hu, hv⟩).1)
      (fun v hv => (hg (u, v) ⟨hu, hv⟩).2.1.trans (by norm_num))).trans hl
  · intro v hv
    refine ⟨(hin v hv).1, ?_⟩
    have hneg : eVariationOn (fun u => S.nu u v) (Ioo 0 v) =
        eVariationOn (fun u => -S.nu u v) (Ioo 0 v) := by
      simp only [eVariationOn, edist_neg_neg]
    rw [hneg]
    exact (s4_variation_le_log_of_pos_le_one
      (fun u hu => (by norm_num : (0 : ℝ) < 1 / 3).trans_le
        (hg (u, v) ⟨hu.1.le, hu.2⟩).2.2.1)
      (fun u hu => (hg (u, v) ⟨hu.1.le, hu.2⟩).2.2.2.1.trans (by norm_num))).trans
        (hin v hv).2

/-- Inverse scalar centering adds only the offset times the expansion
variation. This elementary estimate applies on arbitrary section sets. -/
theorem smooth_variation_add_const_mul_le (f g : ℝ → ℝ) (c : ℝ) (s : Set ℝ) :
    eVariationOn (fun t => f t + c * g t) s ≤
      eVariationOn f s + ENNReal.ofReal |c| * eVariationOn g s := by
  have hmul : eVariationOn (fun t => c * g t) s ≤
      ENNReal.ofReal |c| * eVariationOn g s := by
    apply eVariationOn.le_of_dist_le (abs_nonneg c)
    intro x _ y _
    simp only [Real.dist_eq, ← mul_sub, abs_mul, le_refl]
  exact (eVariationOn.add_le f (fun t => c * g t) s).trans (add_le_add le_rfl hmul)

/-- Uniform raw scalar-radius derivative variations retain the original
scalar offset, while the expansion variations remain universal. -/
theorem smooth_raw_variation_bounds
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
    (∀ u : ℝ, 0 ≤ u → eVariationOn (S.alpha u) (Ioi u) ≤
      s4UniversalC * D + ENNReal.ofReal |S.phi 0 0| * (s4UniversalC * D ^ 2)) ∧
    (∀ v : ℝ, 0 < v → eVariationOn (fun u => S.beta u v) (Ioo 0 v) ≤
      s4UniversalC * D + ENNReal.ofReal |S.phi 0 0| * (s4UniversalC * D ^ 2)) := by
  obtain ⟨hout, hin⟩ := smooth_centered_variation_bounds hfinite hdata hD
  constructor
  · intro u hu
    have heq : S.alpha u = fun v => (smoothCenteredFields S).alpha u v +
        S.phi 0 0 * S.lam u v :=
      (congrArg (fun T : Fields => T.alpha u) (smoothCenteredFields_restore S)).symm
    rw [heq]
    exact (smooth_variation_add_const_mul_le _ _ _ _).trans
      (add_le_add (hout u hu).1 (mul_le_mul' le_rfl (hout u hu).2))
  · intro v hv
    have heq : (fun u => S.beta u v) =
        fun u => (smoothCenteredFields S).beta u v + S.phi 0 0 * S.nu u v :=
      (congrArg (fun T : Fields => fun u => T.beta u v)
        (smoothCenteredFields_restore S)).symm
    rw [heq]
    exact (smooth_variation_add_const_mul_le _ _ _ _).trans
      (add_le_add (hin v hv).1 (mul_le_mul' le_rfl (hin v hv).2))

end ChristodoulouBV

end
