module

public import ChristodoulouBV.Existence.BVStieltjesCalculus
public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Log
import Mathlib.Tactic

/-!
# Local logarithmic calculus before BV solution assembly

Only the reduced null primitives and the already proved geometry are used.
No axis-variation clause or full `IsBVSolution` premise is needed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem log_gap_calculus
    {r m N Z : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hm : AbsolutelyContinuousOnInterval m a b)
    (hrd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv r t = N t)
    (hmd : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv m t = (1 - 2 * m t / r t) * Z t ^ 2 / (2 * N t))
    (hrc : ∀ t ∈ Icc a b, c ≤ r t)
    (hgap : ∀ t ∈ Icc a b, (2 / 3 : ℝ) ≤ 1 - 2 * m t / r t)
    (hN : ∀ t ∈ Icc a b, N t ≠ 0) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (1 - 2 * m t / r t)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => Real.log (1 - 2 * m s / r s)) t =
          (2 * m t / r t) * N t / ((1 - 2 * m t / r t) * r t) -
            Z t ^ 2 / (r t * N t) := by
  have hq := hm.div_and_ae_deriv hr hc (by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (hrc t ht).trans (le_abs_self _))
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hg : AbsolutelyContinuousOnInterval (fun t => 1 - 2 * (m t / r t)) a b :=
    hconst.fun_sub (hq.1.const_mul 2)
  have hlog := hg.log_and_ae_deriv (by norm_num : (0 : ℝ) < 2 / 3) (by
    intro t ht
    rw [uIcc_of_le hab] at ht
    simpa only [mul_div_assoc] using hgap t ht)
  refine ⟨by simpa only [mul_div_assoc] using hlog.1, ?_⟩
  filter_upwards [hlog.2, hq.2, hrd, hmd]
    with t hlt hqt hrt hmt ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  have hr0 : r t ≠ 0 := (hc.trans_le (hrc t ht)).ne'
  have hg0 : 1 - 2 * m t / r t ≠ 0 := by linarith only [hgap t ht]
  have hg' : r t - 2 * m t ≠ 0 := by
    intro hh
    apply hg0
    have heq : 2 * m t / r t = 1 := (div_eq_one_iff_eq hr0).mpr (by linarith only [hh])
    rw [heq, sub_self]
  have hnd := hN t ht
  have he : (fun s => Real.log (1 - 2 * m s / r s)) =
      fun s => Real.log (1 - 2 * (m s / r s)) := by
    funext s
    rw [mul_div_assoc]
  rw [he, hlt htu, deriv_const_sub, deriv_const_mul_field, hqt htu, hrt ht, hmt ht]
  field_simp [hr0, hnd, hg0, hg']
  ring

/-- The canonical outgoing logarithmic mass gap is AC and has the
usual derivative on every compact section, without a full BV-solution premise. -/
theorem bv_log_mass_gap_out
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    AbsolutelyContinuousOnInterval
      (fun t => Real.log (1 - 2 * S.m u t / S.r u t)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => Real.log (1 - 2 * S.m u s / S.r u s)) t =
          (2 * S.m u t / S.r u t) * S.lam u t /
            ((1 - 2 * S.m u t / S.r u t) * S.r u t) -
              S.theta u t ^ 2 / (S.r u t * S.lam u t) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hr := H.radius_out_ac_ae hab hs
  have hm := H.mass_out_ac_ae hab hs
  have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  apply log_gap_calculus hab (c := (a - u) / 3)
    (div_pos (sub_pos.mpr hp.2) (by norm_num)) hr.1 hm.1 hr.2 hm.2
  · intro t ht
    exact (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 u) (by norm_num)).trans
      (d.radius_lower h (p := (u, t)) (hs ⟨rfl, ht⟩))
  · intro t ht
    exact (scalar_right_fields_geometry h hD d (u, t) (hs ⟨rfl, ht⟩)).2.2.2.2.1
  · intro t ht
    exact (H.lam_pos (u, t) (hs ⟨rfl, ht⟩)).ne'

/-- The symmetric incoming logarithmic mass-gap calculus, using only
the reduced solution, canonical geometry and mass primitives. -/
theorem bv_log_mass_gap_in
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    AbsolutelyContinuousOnInterval
      (fun t => Real.log (1 - 2 * S.m t v / S.r t v)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => Real.log (1 - 2 * S.m s v / S.r s v)) t =
          (2 * S.m t v / S.r t v) * S.nu t v /
            ((1 - 2 * S.m t v / S.r t v) * S.r t v) -
              S.zeta t v ^ 2 / (S.r t v * S.nu t v) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hr := H.radius_in_ac_ae hab hs
  have hm := H.mass_in_ac_ae hab hs
  have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
  apply log_gap_calculus hab (c := (v - b) / 3)
    (div_pos (sub_pos.mpr hp.2) (by norm_num)) hr.1 hm.1 hr.2 hm.2
  · intro t ht
    exact (div_le_div_of_nonneg_right (sub_le_sub_left ht.2 v) (by norm_num)).trans
      (d.radius_lower h (p := (t, v)) (hs ⟨ht, rfl⟩))
  · intro t ht
    exact (scalar_right_fields_geometry h hD d (t, v) (hs ⟨ht, rfl⟩)).2.2.2.2.1
  · intro t ht
    exact (limit_signs_conformal h hD d (t, v) (hs ⟨ht, rfl⟩)).2.2.1.ne

/-- The normalized outgoing expansion has an incoming logarithmic
primitive before any axis-variation conclusion is established. -/
theorem bv_log_normalized_lam_in
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    IntervalPrimitive (fun t => Real.log (S.lam t v) -
      Real.log (1 - 2 * S.m t v / S.r t v))
        (fun t => S.zeta t v ^ 2 / (S.r t v * S.nu t v)) a b := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hl := H.lam_in_ac_ae hab hs
  have hlog := hl.1.log_and_ae_deriv (by norm_num : (0 : ℝ) < 1 / 3) (by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (scalar_right_fields_geometry h hD d (t, v) (hs ⟨ht, rfl⟩)).1)
  have hg := bv_log_mass_gap_in h hD d hab hs
  apply IntervalPrimitive.of_ac_ae hab (hlog.1.fun_sub hg.1)
  filter_upwards [hlog.2, hl.2, hg.2, hlog.1.ae_differentiableAt,
    hg.1.ae_differentiableAt] with t hlt hld hgd hldiff hgdiff ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  have hp : (t, v) ∈ globalDomain := hs ⟨ht, rfl⟩
  have hr0 := (H.radius_pos (t, v) hp).ne'
  have hl0 := (H.lam_pos (t, v) hp).ne'
  have hn0 := (limit_signs_conformal h hD d (t, v) hp).2.2.1.ne
  have hgap := (scalar_right_fields_geometry h hD d (t, v) hp).2.2.2.2.1
  have hg0 : 1 - 2 * S.m t v / S.r t v ≠ 0 := by linarith only [hgap]
  rw [deriv_fun_sub (hldiff htu) (hgdiff htu), hlt htu, hld ht, hgd ht]
  dsimp only [IsBVSolution.radiusCoeff]
  field_simp [hr0, hl0, hn0, hg0]
  ring

/-- The symmetric normalized incoming expansion has an outgoing
logarithmic primitive, with its canonical negative expansion sign. -/
theorem bv_log_normalized_nu_out
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    IntervalPrimitive (fun t => Real.log (-S.nu u t) -
      Real.log (1 - 2 * S.m u t / S.r u t))
        (fun t => S.theta u t ^ 2 / (S.r u t * S.lam u t)) a b := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hn := H.nu_out_ac_ae hab hs
  have hlog := hn.1.neg.log_and_ae_deriv (by norm_num : (0 : ℝ) < 1 / 3) (by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (scalar_right_fields_geometry h hD d (u, t) (hs ⟨rfl, ht⟩)).2.2.1)
  have hg := bv_log_mass_gap_out h hD d hab hs
  apply IntervalPrimitive.of_ac_ae hab (hlog.1.fun_sub hg.1)
  filter_upwards [hlog.2, hn.2, hg.2, hlog.1.ae_differentiableAt,
    hg.1.ae_differentiableAt] with t hnt hnd hgd hndiff hgdiff ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  have hp : (u, t) ∈ globalDomain := hs ⟨rfl, ht⟩
  have hr0 := (H.radius_pos (u, t) hp).ne'
  have hl0 := (H.lam_pos (u, t) hp).ne'
  have hn0 := (limit_signs_conformal h hD d (u, t) hp).2.2.1.ne
  have hgap := (scalar_right_fields_geometry h hD d (u, t) hp).2.2.2.2.1
  have hg0 : 1 - 2 * S.m u t / S.r u t ≠ 0 := by linarith only [hgap]
  rw [deriv_fun_sub (hndiff htu) (hgdiff htu), hnt htu, deriv.neg, hnd ht, hgd ht]
  simp only [Pi.neg_apply]
  dsimp only [IsBVSolution.radiusCoeff]
  field_simp [hr0, hl0, hn0, hg0]
  ring

end ChristodoulouBV

end
