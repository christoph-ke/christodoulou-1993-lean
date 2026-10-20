module

public import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import ChristodoulouBV.Existence.BVStieltjesCalculus
import Mathlib.Tactic

/-!
# Derivative bounds on open BV sections

Rational compact subintervals exhaust the open section. This bounds the
ordinary scalar density without assigning a value at the axis endpoint.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The lower integral of the absolute derivative on an open section
is bounded by its pointwise variation, including singular and jump variation. -/
theorem bv_lintegral_abs_deriv_le_variation {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (Ioo a b)) :
    (∫⁻ t in Ioo a b, ENNReal.ofReal |deriv f t|) ≤ eVariationOn f (Ioo a b) := by
  let ι := {p : ℚ × ℚ // a < (p.1 : ℝ) ∧ (p.2 : ℝ) < b ∧ p.1 ≤ p.2}
  let E : ι → Set ℝ := fun p => Icc (p.val.1 : ℝ) (p.val.2 : ℝ)
  have hs (p : ι) : E p ⊆ Ioo a b := by
    intro t ht
    exact ⟨p.property.1.trans_le ht.1, ht.2.trans_lt p.property.2.1⟩
  have he : Ioo a b = ⋃ p : ι, E p := by
    apply Subset.antisymm
    · intro t ht
      obtain ⟨x, hax, hxt⟩ := exists_rat_btwn ht.1
      obtain ⟨y, hty, hyb⟩ := exists_rat_btwn ht.2
      have hxy : x ≤ y := by exact_mod_cast (hxt.trans hty).le
      exact mem_iUnion.mpr ⟨⟨(x, y), hax, hyb, hxy⟩, hxt.le, hty.le⟩
    · exact iUnion_subset hs
  have hd : Directed (· ⊆ ·) E := by
    intro p q
    let r : ι := ⟨(min p.val.1 q.val.1, max p.val.2 q.val.2), by
      constructor
      · simpa only [Rat.cast_min] using lt_min p.property.1 q.property.1
      · constructor
        · simpa only [Rat.cast_max] using max_lt p.property.2.1 q.property.2.1
        · exact (min_le_left _ _).trans (p.property.2.2.trans (le_max_left _ _))⟩
    refine ⟨r, ?_, ?_⟩
    · exact Icc_subset_Icc (by exact_mod_cast min_le_left p.val.1 q.val.1)
        (by exact_mod_cast le_max_left p.val.2 q.val.2)
    · exact Icc_subset_Icc (by exact_mod_cast min_le_right p.val.1 q.val.1)
        (by exact_mod_cast le_max_right p.val.2 q.val.2)
  conv_lhs => rw [he, setLIntegral_iUnion_of_directed _ hd]
  apply iSup_le
  intro p
  have hab : (p.val.1 : ℝ) ≤ p.val.2 := by exact_mod_cast p.property.2.2
  have hb := hf.mono (hs p)
  have hb' : BoundedVariationOn f (uIcc (p.val.1 : ℝ) p.val.2) := by
    simpa only [uIcc_of_le hab] using hb
  have hdi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    hb'.intervalIntegrable_deriv.abs
  rw [← ofReal_integral_eq_lintegral_ofReal hdi (Eventually.of_forall fun _ => abs_nonneg _),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  calc
    ENNReal.ofReal (∫ t in (p.val.1 : ℝ)..p.val.2, |deriv f t|) ≤
        ENNReal.ofReal (eVariationOn f (E p)).toReal :=
      ENNReal.ofReal_le_ofReal (hb.integral_abs_deriv_le_eVariationOn hab)
    _ = eVariationOn f (E p) := ENNReal.ofReal_toReal hb
    _ ≤ _ := eVariationOn.mono _ (hs p)

/-- The derivative is integrable on an open finite-variation section,
with no regularity requirement on the assigned endpoint values. -/
theorem bv_deriv_integrableOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (Ioo a b)) : IntegrableOn (deriv f) (Ioo a b) := by
  refine ⟨(stronglyMeasurable_deriv f).aestronglyMeasurable, ?_⟩
  change (∫⁻ t in Ioo a b, ‖deriv f t‖ₑ) < ∞
  simp_rw [Real.enorm_eq_ofReal_abs]
  exact (bv_lintegral_abs_deriv_le_variation hf).trans_lt (lt_top_iff_ne_top.mpr hf)

/-- The canonical outgoing scalar density is the derivative almost
everywhere on the whole open axis-based section. -/
theorem bv_ae_deriv_phi_out_open
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b : ℝ} (hu : 0 ≤ u) :
    ∀ᵐ t ∂volume, t ∈ Ioo u b → deriv (d.scalarRightFields.phi u) t =
      d.scalarRightFields.theta u t / d.scalarRightFields.r u t := by
  have hall : ∀ᵐ t ∂volume, ∀ q : ℚ, u < (q : ℝ) → (q : ℝ) ≤ b →
      t ∈ Icc (q : ℝ) b → deriv (d.scalarRightFields.phi u) t =
        d.scalarRightFields.theta u t / d.scalarRightFields.r u t := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : u < (q : ℝ) ∧ (q : ℝ) ≤ b
    · filter_upwards [bv_ae_deriv_phi_out h hD d (u := u) hq.2 (fun p hp => by
        rcases hp with ⟨rfl, ht⟩
        exact ⟨hu, hq.1.trans_le ht.1⟩)] with t ht _ _ htI
      exact ht htI
    · exact Eventually.of_forall fun _ h₁ h₂ => (hq ⟨h₁, h₂⟩).elim
  filter_upwards [hall] with t ht htI
  obtain ⟨q, huq, hqt⟩ := exists_rat_btwn htI.1
  exact ht q huq (hqt.le.trans htI.2.le) ⟨hqt.le, htI.2.le⟩

/-- The symmetric incoming scalar derivative identity on an open section. -/
theorem bv_ae_deriv_phi_in_open
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ t ∂volume, t ∈ Ioo a v → deriv (fun s => d.scalarRightFields.phi s v) t =
      d.scalarRightFields.zeta t v / d.scalarRightFields.r t v := by
  have hall : ∀ᵐ t ∂volume, ∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) < v →
      t ∈ Icc a (q : ℝ) → deriv (fun s => d.scalarRightFields.phi s v) t =
        d.scalarRightFields.zeta t v / d.scalarRightFields.r t v := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : a ≤ (q : ℝ) ∧ (q : ℝ) < v
    · filter_upwards [bv_ae_deriv_phi_in h hD d (v := v) hq.1 (fun p hp => by
        rcases hp with ⟨ht, rfl⟩
        exact ⟨ha.trans ht.1, ht.2.trans_lt hq.2⟩)] with t ht _ _ htI
      exact ht htI
    · exact Eventually.of_forall fun _ h₁ h₂ => (hq ⟨h₁, h₂⟩).elim
  filter_upwards [hall] with t ht htI
  obtain ⟨q, htq, hqv⟩ := exists_rat_btwn htI.2
  exact ht q (htI.1.le.trans htq.le) hqv ⟨htI.1.le, htq.le⟩

/-- A real density agreeing with a BV function's derivative on an open
section is integrable there, with the sharp variation majorant. -/
theorem bv_density_integrable_and_bound {f p : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Ioo a b))
    (he : ∀ᵐ t ∂volume, t ∈ Ioo a b → deriv f t = p t) :
    IntervalIntegrable p volume a b ∧
      (∫ t in a..b, |p t|) ≤ (eVariationOn f (Ioo a b)).toReal := by
  have he' : deriv f =ᵐ[volume.restrict (Ioo a b)] p :=
    (ae_restrict_iff' measurableSet_Ioo).mpr he
  have hpi : IntegrableOn p (Ioo a b) := (bv_deriv_integrableOn_Ioo hf).congr he'
  have hi : IntervalIntegrable p volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((integrableOn_Ioc_iff_integrableOn_Ioo (f := p) (a := a) (b := b)).mpr hpi)
  refine ⟨hi, ?_⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hf).mp
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hpi.abs (Eventually.of_forall fun _ => abs_nonneg _)]
  calc
    (∫⁻ t in Ioo a b, ENNReal.ofReal |p t|) =
        ∫⁻ t in Ioo a b, ENNReal.ofReal |deriv f t| := by
      apply lintegral_congr_ae
      filter_upwards [he'] with t ht
      rw [ht]
    _ ≤ _ := bv_lintegral_abs_deriv_le_variation hf

end ChristodoulouBV

end
