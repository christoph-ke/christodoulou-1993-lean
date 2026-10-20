module

public import ChristodoulouBV.Existence.RepresentativesCore
public import ChristodoulouBV.Existence.BVBasic
import Mathlib.Tactic

/-!
# Variation bounds after incoming representative replacement

Outgoing fields are unchanged. Incoming fields agree with the canonical
record of the radius and scalar limits. Both full three-term variations therefore retain one
universal coefficient, and all already established frozen BV clauses
retain global uniform bounds.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Incoming selection decreases the full incoming TV and leaves the
full outgoing TV unchanged, including the outgoing initial ray. -/
theorem incoming_right_fields_tv_le
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, e1OutgoingTV d.incomingRightFields u = e1OutgoingTV d.rawFields u) ∧
    ∀ v, 0 < v → e1IncomingTV d.incomingRightFields v ≤ e1IncomingTV d.rawFields v :=
  ⟨fun _ => rfl, (scalar_right_fields_tv_le h hD d).2⟩

/-- The final incoming representative record has the same universal
three-term TV bound on every null ray, independently of scalar offsets. -/
theorem incoming_right_fields_three_term_tv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → e1OutgoingTV d.incomingRightFields u ≤
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal)) ∧
    ∀ v, 0 < v → e1IncomingTV d.incomingRightFields v ≤
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) :=
  ⟨(scalar_limit_three_term_tv h d).1, (scalar_right_fields_three_term_tv h hD d).2⟩

private theorem section_bounds {f g : ℝ → ℝ → ℝ} {V : ℝ≥0∞}
    (hout : ∀ u, 0 ≤ u → eVariationOn (f u) (Ioi u) ≤ V)
    (hin : ∀ v, 0 < v → eVariationOn (fun u => g u v) (Ico 0 v) ≤ V) :
    (∀ u, eVariationOn (f u) {v | (u, v) ∈ globalDomain} ≤ V) ∧
    ∀ v, eVariationOn (fun u => g u v) {u | (u, v) ∈ globalDomain} ≤ V := by
  constructor
  · intro u
    by_cases hu : 0 ≤ u
    · have hs : {v | (u, v) ∈ globalDomain} = Ioi u := by
        ext v
        simp only [globalDomain, Set.mem_ofPred_eq, mem_Ioi, hu, true_and]
      rw [hs]
      exact hout u hu
    · have hs : {v | (u, v) ∈ globalDomain} = ∅ := by
        ext v
        simp only [globalDomain, Set.mem_ofPred_eq, hu, false_and, Set.mem_empty_iff_false]
      rw [hs, eVariationOn.subsingleton _ Set.subsingleton_empty]
      exact bot_le
  · intro v
    change eVariationOn (fun u => g u v) (Ico 0 v) ≤ V
    by_cases hv : 0 < v
    · exact hin v hv
    · rw [Ico_eq_empty_of_le (le_of_not_gt hv),
        eVariationOn.subsingleton _ Set.subsingleton_empty]
      exact bot_le

/-- The incoming representative change preserves the frozen uniform
expansion variation clause (item 1), with the same quantitative radius limit budget. -/
theorem incoming_right_fields_item1
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ K : ℝ,
      (∀ u, eVariationOn (d.incomingRightFields.lam u)
        {v | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K) ∧
      ∀ v, eVariationOn (fun u => d.incomingRightFields.nu u v)
        {u | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K := by
  have hV : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  refine ⟨(s4UniversalC * D ^ 2).toReal, ?_⟩
  rw [ENNReal.ofReal_toReal hV]
  exact section_bounds (expansions_limit h d).1 (right_expansions_variation h hD d).2

private theorem raw_theta_variation
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {u : ℝ} (hu : 0 ≤ u) :
    let V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)
    eVariationOn (d.rawFields.theta u) (Ioi u) ≤
      (V + V) + ENNReal.ofReal (24 * D.toReal) * (s4UniversalC * D ^ 2) := by
  let V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)
  let q := fun v => d.alpha u v / d.lam u v
  have hTV := (scalar_limit_three_term_tv h d).1 u hu
  have hVe : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) = V := by
    dsimp only [V]
    have he := ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)
      (q := s6EndpointTVK * D.toReal)
    simpa only [mul_assoc, ENNReal.ofReal_ofNat] using he.symm
  rw [hVe] at hTV
  have hqV : eVariationOn q (Ioi u) ≤ V :=
    (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans hTV)
  have hφV : eVariationOn (d.rawFields.phi u) (Ioi u) ≤ V :=
    (le_add_of_nonneg_left bot_le).trans ((le_add_of_nonneg_right bot_le).trans hTV)
  have hgeom := (expansions_limit h d).2.2
  have he : EqOn (d.rawFields.theta u)
      (fun v => d.lam u v * (q v - d.rawFields.phi u v)) (Ioi u) := by
    intro v hv
    have hl : d.lam u v ≠ 0 := (lt_of_lt_of_le (by norm_num)
      (hgeom (u, v) ⟨hu, hv⟩).1).ne'
    dsimp only [q, Fields.theta, RadiusLimitData.rawFields]
    field_simp [hl]
  rw [eVariationOn.congr he]
  have hlB (v : ℝ) (hv : v ∈ Ioi u) : |d.lam u v| ≤ 1 := by
    obtain ⟨hl0, hl1, _⟩ := hgeom (u, v) ⟨hu, hv⟩
    rw [abs_of_nonneg (by linarith only [hl0])]
    linarith only [hl1]
  have hqB (v : ℝ) (hv : v ∈ Ioi u) : |q v - d.rawFields.phi u v| ≤
      24 * D.toReal := by
    have hl0 := (hgeom (u, v) ⟨hu, hv⟩).1
    have hlpos : 0 < d.lam u v := lt_of_lt_of_le (by norm_num) hl0
    have heq : q v - d.rawFields.phi u v = d.rawFields.theta u v / d.lam u v := by
      dsimp only [q, Fields.theta, RadiusLimitData.rawFields]
      field_simp [hlpos.ne']
    rw [heq, abs_div, abs_of_pos hlpos]
    apply (div_le_iff₀ hlpos).mpr
    have hm := mul_le_mul_of_nonneg_left hl0
      (show 0 ≤ 24 * D.toReal by positivity)
    have ht := (scalar_limit_invariant_amplitudes h d (u, v) ⟨hu, hv⟩).1
    nlinarith only [hm, ht, ENNReal.toReal_nonneg (a := D)]
  have hprod := eVariationOn.mul_le_of_abs_le hlB hqB
  have hsub := (eVariationOn.sub_le q (d.rawFields.phi u) (Ioi u)).trans
    (add_le_add hqV hφV)
  change eVariationOn (fun v => d.lam u v * (q v - d.rawFields.phi u v)) (Ioi u) ≤ _
  calc
    _ ≤ eVariationOn (q - d.rawFields.phi u) (Ioi u) +
        ENNReal.ofReal (24 * D.toReal) * eVariationOn (d.lam u) (Ioi u) := by
      have hm : (d.lam u * fun x => q x - d.rawFields.phi u x) =
          (fun x => d.lam u x * (q x - d.rawFields.phi u x)) := by
        funext x
        exact Pi.mul_apply _ _ x
      have hn : q - d.rawFields.phi u = (fun x => q x - d.rawFields.phi u x) := by
        funext x
        exact Pi.sub_apply _ _ x
      simpa only [ENNReal.ofReal_one, one_mul, hm, hn] using hprod
    _ ≤ _ := add_le_add hsub
      (mul_le_mul_of_nonneg_left ((expansions_limit h d).1 u hu) bot_le)

/-- Uniform variation of θ and ζ (frozen item 5) survives the incoming
changes. Its constants depend only on D and universal coefficients. -/
theorem incoming_right_fields_item5
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ K : ℝ,
      (∀ u, eVariationOn (d.incomingRightFields.theta u)
        {v | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K) ∧
      ∀ v, eVariationOn (fun u => d.incomingRightFields.zeta u v)
        {u | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K := by
  let V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)
  let W := s4UniversalC * D ^ 2
  let K := (V + V) + ENNReal.ofReal (24 * D.toReal) * W
  have hW : W ≠ ∞ := ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  have hK : K ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW⟩
  refine ⟨K.toReal, ?_⟩
  rw [ENNReal.ofReal_toReal hK]
  exact section_bounds (fun _ hu => raw_theta_variation h d hu)
    (bv_invariant_variation h hD d).2

end ChristodoulouBV

end
