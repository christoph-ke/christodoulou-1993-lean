module

public import ChristodoulouBV.Existence.RepresentativesPrimitives
public import ChristodoulouBV.Existence.BVStieltjesInitial
public import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation
import Mathlib.Tactic

/-!
# Compatibility with the canonical quantitative witness

The initial gauge fixes the raw λ representative. Uniqueness of its
incoming linear equation identifies it with canonical λ at every point.
For right-continuous data the α equation then identifies raw and canonical
α as well. Thus the incoming representative witness itself has all four
canonical right-continuity clauses; a second existential witness is unnecessary.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem raw_initial_lam_eq_half
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {v : ℝ} (hv : 0 < v) : d.lam 0 v = 1 / 2 := by
  have hs (n : ℕ) : (T (d.subsequence n)).lam 0 v = 1 / 2 := by
    apply initial_lam_eq_of_gauge ((h (d.subsequence n)).finite (v + 1) (by linarith))
      (fun w hw => ((h (d.subsequence n)).initial_data w hw.1).1)
    exact ⟨hv, lt_add_one v⟩
  have he : Tendsto (fun n => (T (d.subsequence n)).lam 0 v) atTop (𝓝 (1 / 2)) := by
    simp_rw [hs]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (d.lam_limit (0, v) ⟨le_rfl, hv⟩) he

/-- The prescribed radius gauge and incoming transport force raw λ to
equal its canonical right-v representative at every domain point. -/
theorem raw_lam_eq_right_lam
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    d.lam p.1 p.2 = d.rightLam p.1 p.2 := by
  let S := d.incomingRightFields
  let R := d.scalarRightFields
  have hS := representative_stability h hD d
  have hR := transport_limit_is_solution h hD d
  have hs : inSeg p.2 0 p.1 ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨hx, rfl⟩
    exact ⟨hx.1, hx.2.trans_lt hp.2⟩
  have hs' (x : ℝ) (hx : x ∈ Icc 0 p.1) : (x, p.2) ∈ globalDomain := hs ⟨hx, rfl⟩
  let k := fun x => IsBVSolution.radiusCoeff R x p.2 / R.lam x p.2
  have hln (x : ℝ) (hx : x ∈ Icc 0 p.1) : R.lam x p.2 ≠ 0 :=
    (hR.lam_pos (x, p.2) (hs' x hx)).ne'
  have hc := (hR.lam_in_ac_ae hp.1 hs).1.continuousOn
  have hk : IntervalIntegrable k volume 0 p.1 := by
    apply (hR.lam_in p.2 0 p.1 hp.1 hs).1.mul_continuousOn
      (hc.inv₀ (fun x hx => hln x (uIcc_of_le hp.1 ▸ hx))) |>.congr
    intro x _
    exact (div_eq_mul_inv _ _).symm
  have heR (x : ℝ) (hx : x ∈ Icc 0 p.1) :
      k x * R.lam x p.2 = IsBVSolution.radiusCoeff R x p.2 :=
    div_mul_cancel₀ _ (hln x hx)
  have heS (x : ℝ) (hx : x ∈ Icc 0 p.1) :
      k x * S.lam x p.2 = IsBVSolution.radiusCoeff S x p.2 := by
    dsimp only [k, R, S, IsBVSolution.radiusCoeff, RadiusLimitData.scalarRightFields,
      RadiusLimitData.rightFields, RadiusLimitData.incomingRightFields, RadiusLimitData.rawFields]
    have hl : d.rightLam x p.2 ≠ 0 := hln x hx
    field_simp [hl]
  have hky : IntervalIntegrable (fun x => k x * S.lam x p.2) volume 0 p.1 := by
    apply (hS.lam_in p.2 0 p.1 hp.1 hs).1.congr
    intro x hx
    exact (heS x (uIcc_of_le hp.1 ▸ uIoc_subset_uIcc hx)).symm
  have hkz : IntervalIntegrable (fun x => k x * R.lam x p.2) volume 0 p.1 := by
    apply (hR.lam_in p.2 0 p.1 hp.1 hs).1.congr
    intro x hx
    exact (heR x (uIcc_of_le hp.1 ▸ uIoc_subset_uIcc hx)).symm
  have hy (t : ℝ) (ht : t ∈ Icc 0 p.1) :
      S.lam t p.2 - S.lam 0 p.2 = ∫ x in 0..t, k x * S.lam x p.2 + 0 := by
    rw [(hS.lam_in p.2 0 t ht.1 ((inSeg_subsegment le_rfl ht.1 ht.2).trans hs)).2]
    apply intervalIntegral.integral_congr
    intro x hx
    change IsBVSolution.radiusCoeff S x p.2 = k x * S.lam x p.2 + 0
    rw [add_zero, heS x ⟨(show x ∈ Icc 0 t from uIcc_of_le ht.1 ▸ hx).1,
      (show x ∈ Icc 0 t from uIcc_of_le ht.1 ▸ hx).2.trans ht.2⟩]
  have hz (t : ℝ) (ht : t ∈ Icc 0 p.1) :
      R.lam t p.2 - R.lam 0 p.2 = ∫ x in 0..t, k x * R.lam x p.2 + 0 := by
    rw [(hR.lam_in p.2 0 t ht.1 ((inSeg_subsegment le_rfl ht.1 ht.2).trans hs)).2]
    apply intervalIntegral.integral_congr
    intro x hx
    change IsBVSolution.radiusCoeff R x p.2 = k x * R.lam x p.2 + 0
    rw [add_zero, heR x ⟨(show x ∈ Icc 0 t from uIcc_of_le ht.1 ▸ hx).1,
      (show x ∈ Icc 0 t from uIcc_of_le ht.1 ▸ hx).2.trans ht.2⟩]
  have hzero : S.lam 0 p.2 = R.lam 0 p.2 := by
    exact (raw_initial_lam_eq_half h d (hp.1.trans_lt hp.2)).trans
      (bv_initial_lam_eq_half h d (hp.1.trans_lt hp.2)).symm
  exact intervalIntegral.eq_on_of_integral_eq hp.1 hk intervalIntegrable_const hky hkz
    hy hz hzero ⟨hp.1, le_rfl⟩

/-- The two records have identical mixed radius coefficients everywhere
on the carrier, independently of any regularity of the initial α datum. -/
theorem incoming_right_fields_radius_coeff_eq
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    IsBVSolution.radiusCoeff d.incomingRightFields p.1 p.2 =
      IsBVSolution.radiusCoeff d.scalarRightFields p.1 p.2 := by
  dsimp only [IsBVSolution.radiusCoeff, RadiusLimitData.incomingRightFields,
    RadiusLimitData.scalarRightFields, RadiusLimitData.rightFields, RadiusLimitData.rawFields]
  rw [raw_lam_eq_right_lam h hD d hp]

/-- The only possible outgoing scalar discrepancy is transported
literally from the initial datum. This also records the representative
defect needed to transfer canonical axis estimates for arbitrary data. -/
theorem incoming_right_alpha_defect
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    d.incomingRightFields.alpha p.1 p.2 - d.scalarRightFields.alpha p.1 p.2 =
      d.incomingRightFields.alpha 0 p.2 - d.scalarRightFields.alpha 0 p.2 := by
  have hs : inSeg p.2 0 p.1 ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨hx, rfl⟩
    exact ⟨hx.1, hx.2.trans_lt hp.2⟩
  have hS := (representative_stability h hD d).alpha_in p.2 0 p.1 hp.1 hs
  have hR := (transport_limit_is_solution h hD d).alpha_in p.2 0 p.1 hp.1 hs
  have he : (∫ x in 0..p.1, IsBVSolution.radiusCoeff d.incomingRightFields x p.2 *
      d.incomingRightFields.phi x p.2) =
      ∫ x in 0..p.1, IsBVSolution.radiusCoeff d.scalarRightFields x p.2 *
        d.scalarRightFields.phi x p.2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [incoming_right_fields_radius_coeff_eq h hD d (p := (x, p.2))
      (hs ⟨uIcc_of_le hp.1 ▸ hx, rfl⟩)]
    rfl
  have hSe : d.incomingRightFields.alpha p.1 p.2 - d.incomingRightFields.alpha 0 p.2 =
      ∫ x in 0..p.1, IsBVSolution.radiusCoeff d.incomingRightFields x p.2 *
        d.incomingRightFields.phi x p.2 := hS.2
  have hRe : d.scalarRightFields.alpha p.1 p.2 - d.scalarRightFields.alpha 0 p.2 =
      ∫ x in 0..p.1, IsBVSolution.radiusCoeff d.scalarRightFields x p.2 *
        d.scalarRightFields.phi x p.2 := hR.2
  linarith only [hSe, hRe, he]

/-- For right-continuous data the incoming representative witness equals
the canonical quantitative witness in all seven fields at every domain point. -/
theorem incoming_right_fields_eq_canonical_of_right_continuous
    {alpha₀ : ℝ → ℝ} {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a₀ n v) atTop (𝓝 (alpha₀ v)))
    (hrc : ∀ v, 0 < v → ContinuousWithinAt alpha₀ (Ici v) v)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain, d.incomingRightFields.alpha p.1 p.2 =
      d.scalarRightFields.alpha p.1 p.2 ∧
      d.incomingRightFields.lam p.1 p.2 = d.scalarRightFields.lam p.1 p.2 := by
  intro p hp
  refine ⟨?_, raw_lam_eq_right_lam h hD d hp⟩
  have he := incoming_right_alpha_defect h hD d hp
  have hdata := (incoming_right_fields_data_trace h hpoint d p.2 (hp.1.trans_lt hp.2)).2
  have hdataR := (data_trace_limit_of_right_continuous h hpoint hrc d p.2
    (hp.1.trans_lt hp.2)).2
  linarith only [he, hdata, hdataR]

/-- All four canonical right-continuity clauses hold for the very same incoming
representative witness when the prescribed datum is right continuous. -/
theorem incoming_right_fields_rightBV_of_right_continuous
    {alpha₀ : ℝ → ℝ} {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a₀ n v) atTop (𝓝 (alpha₀ v)))
    (hrc : ∀ v, 0 < v → ContinuousWithinAt alpha₀ (Ici v) v)
    (d : RadiusLimitData T) : RightBVFields globalDomain d.incomingRightFields := by
  have hc := scalar_right_fields_rightBV h hD d
  have he := incoming_right_fields_eq_canonical_of_right_continuous h hD hpoint hrc d
  have hθ (p : ℝ × ℝ) (hp : p ∈ globalDomain) :
      d.incomingRightFields.theta p.1 p.2 = d.scalarRightFields.theta p.1 p.2 := by
    dsimp only [Fields.theta]
    rw [(he p hp).1, (he p hp).2]
    rfl
  refine ⟨?_, ?_, hc.2.2.1, hc.2.2.2⟩
  · intro p hp
    exact (hc.1 p hp).congr_of_mem (fun w hw => (he (p.1, w) hw.2).2) ⟨le_rfl, hp⟩
  · intro p hp
    exact (hc.2.1 p hp).congr_of_mem (fun w hw => hθ (p.1, w) hw.2) ⟨le_rfl, hp⟩

end ChristodoulouBV

end
