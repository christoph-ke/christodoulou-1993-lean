module

public import ChristodoulouBV.Uniqueness.RadiusScalarBase

/-!
# Outgoing scalar quotient identity

The quotient products in (3.6a) are integrable on the full axis-to-point
characteristic, so the source's two-integral decomposition is literal.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Exact outgoing scalar difference decomposition (3.6a). The quotient
integrands are integrable without preliminary variation smallness. -/
theorem ComparisonData.phi_diff_outgoing_identity (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.phi u v - D.S₂.phi u v =
      (∫ t in u..v, D.S₁.lam u t *
        (D.S₁.alpha u t / D.S₁.lam u t -
          D.S₂.alpha u t / D.S₂.lam u t)) / D.S₁.r u v +
      (∫ t in u..v,
        (D.S₂.alpha u t / D.S₂.lam u t) *
          (D.S₁.lam u t - D.S₂.lam u t)) / D.S₁.r u v -
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) *
        D.S₂.phi u v := by
  let f : ℝ → ℝ := fun t => D.S₁.lam u t *
    (D.S₁.alpha u t / D.S₁.lam u t -
      D.S₂.alpha u t / D.S₂.lam u t)
  let g : ℝ → ℝ := fun t =>
    (D.S₂.alpha u t / D.S₂.lam u t) *
      (D.S₁.lam u t - D.S₂.lam u t)
  have hp := D.hT huv
  have hα₁ := alpha_integrable_outgoing_axis D.h₁ hp.1
  have hα₂ := alpha_integrable_outgoing_axis D.h₂ hp.2
  have hlam₁ := D.h₁.lam_integrable_outgoing_axis hp.1
  have hlam₂ := D.h₂.lam_integrable_outgoing_axis hp.2
  have hab : u ≤ v := huv.2.1.le
  have hα₁on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hα₁
  have hα₂on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hα₂
  have hlam₁on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hlam₁
  have hlam₂on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hlam₂
  have hq₁ae : AEStronglyMeasurable
      (fun t => D.S₁.alpha u t / D.S₁.lam u t)
      (volume.restrict (Ioc u v)) :=
    hα₁on.aestronglyMeasurable.div₀ hlam₁on.aestronglyMeasurable
  have hq₂ae : AEStronglyMeasurable
      (fun t => D.S₂.alpha u t / D.S₂.lam u t)
      (volume.restrict (Ioc u v)) :=
    hα₂on.aestronglyMeasurable.div₀ hlam₂on.aestronglyMeasurable
  have hfae : AEStronglyMeasurable f
      (volume.restrict (Ioc u v)) := by
    have hh := hlam₁on.aestronglyMeasurable.mul (hq₁ae.sub hq₂ae)
    convert hh using 1
  have hgae : AEStronglyMeasurable g
      (volume.restrict (Ioc u v)) := by
    have hh := hq₂ae.mul
      (hlam₁on.aestronglyMeasurable.sub hlam₂on.aestronglyMeasurable)
    convert hh using 1
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) = D.S₂.phi 0 (1 / 2 : ℝ) := by
    have hh := (D.hdata (1 / 2 : ℝ) (by rw [ha, hb]; constructor <;> norm_num)).2
    simpa only [ha] using hh
  obtain ⟨c, C, hc, hC, hcoeff⟩ :=
    D.h₁.preloc_coefficient_bounds D.h₂ href hdatum
  let K := C + C * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let Q := K / c
  have hQ : 0 ≤ Q := div_nonneg hK hc.le
  have hfield (t : ℝ) (ht : t ∈ Ioc u v)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D.a D.b u t D.hT
      ((mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩) S hS
  have hqbound (t : ℝ) (ht : t ∈ Ioc u v)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      |S.alpha u t / S.lam u t| ≤ Q := by
    rcases hfield t ht S hS with
      ⟨hlamLo, hlamHi, _, _, hphi, htheta, _⟩
    have halpha : |S.alpha u t| ≤ K := by
      have heq : S.alpha u t = S.theta u t + S.lam u t * S.phi u t := by
        dsimp [Fields.theta]; ring
      rw [heq]
      calc
        |S.theta u t + S.lam u t * S.phi u t| ≤
            |S.theta u t| + |S.lam u t| * |S.phi u t| := by
          simpa only [abs_mul] using
            (abs_add_le (S.theta u t) (S.lam u t * S.phi u t))
        _ ≤ C + C * C := by
          have hpos := D.h₁.solution.lam_pos (u,t)
            (D.hT ((mem_triangle).2
              ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩)).1
          rcases hS with rfl | rfl
          · rw [abs_of_pos hpos]
            exact add_le_add htheta
              ((mul_le_mul_of_nonneg_right hlamHi (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hphi hC))
          · have hpos₂ := D.h₂.solution.lam_pos (u,t)
              (D.hT ((mem_triangle).2
                ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩)).2
            rw [abs_of_pos hpos₂]
            exact add_le_add htheta
              ((mul_le_mul_of_nonneg_right hlamHi (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hphi hC))
        _ = K := rfl
    have hlamPos : 0 < S.lam u t := hc.trans_le hlamLo
    rw [abs_div, abs_of_pos hlamPos]
    apply (div_le_div_iff₀ hlamPos hc).2
    exact (mul_le_mul_of_nonneg_right halpha hc.le).trans
      (mul_le_mul_of_nonneg_left hlamLo hK)
  have hfgbound (t : ℝ) (ht : t ∈ Ioc u v) :
      |f t| ≤ 2 * C * Q ∧ |g t| ≤ 2 * C * Q := by
    have hlam₁ := (hfield t ht D.S₁ (Or.inl rfl)).2.1
    have hlam₂ := (hfield t ht D.S₂ (Or.inr rfl)).2.1
    have hq₁ := hqbound t ht D.S₁ (Or.inl rfl)
    have hq₂ := hqbound t ht D.S₂ (Or.inr rfl)
    have hqdiff : |D.S₁.alpha u t / D.S₁.lam u t -
        D.S₂.alpha u t / D.S₂.lam u t| ≤ 2 * Q := by
      calc
        _ ≤ |D.S₁.alpha u t / D.S₁.lam u t| +
            |D.S₂.alpha u t / D.S₂.lam u t| := abs_sub _ _
        _ ≤ Q + Q := add_le_add hq₁ hq₂
        _ = 2 * Q := by ring
    have hlamdiff : |D.S₁.lam u t - D.S₂.lam u t| ≤ 2 * C := by
      have hp₁ := D.h₁.solution.lam_pos (u,t)
        (D.hT ((mem_triangle).2
          ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩)).1
      have hp₂ := D.h₂.solution.lam_pos (u,t)
        (D.hT ((mem_triangle).2
          ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩)).2
      calc
        _ ≤ |D.S₁.lam u t| + |D.S₂.lam u t| := abs_sub _ _
        _ ≤ C + C := by
          rw [abs_of_pos hp₁, abs_of_pos hp₂]
          exact add_le_add hlam₁ hlam₂
        _ = 2 * C := by ring
    constructor
    · dsimp [f]
      rw [abs_mul]
      have hp₁ := D.h₁.solution.lam_pos (u,t)
        (D.hT ((mem_triangle).2
          ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩)).1
      rw [abs_of_pos hp₁]
      exact (mul_le_mul_of_nonneg_left hqdiff hp₁.le).trans
        (by nlinarith [mul_nonneg hC hQ])
    · dsimp [g]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hlamdiff (abs_nonneg _)).trans
        (by nlinarith [mul_nonneg hC hQ])
  have hmeasure : volume (Ioc u v) < ⊤ :=
    (measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  have hfon : IntegrableOn f (Ioc u v) volume := by
    apply IntegrableOn.of_bound hmeasure hfae (2 * C * Q)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using (hfgbound t ht).1
  have hgon : IntegrableOn g (Ioc u v) volume := by
    apply IntegrableOn.of_bound hmeasure hgae (2 * C * Q)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using (hfgbound t ht).2
  have hfint : IntervalIntegrable f volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hfon
  have hgint : IntervalIntegrable g volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hgon
  have hpoint (t : ℝ) (ht : t ∈ Ioc u v) :
      D.S₁.alpha u t - D.S₂.alpha u t = f t + g t := by
    have heq := D.alpha_diff_quotient_identity
      ((mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩)
    simpa only [f, g] using heq
  have hsum : (∫ t in u..v, D.S₁.alpha u t - D.S₂.alpha u t) =
      (∫ t in u..v, f t) + (∫ t in u..v, g t) := by
    calc
      (∫ t in u..v, D.S₁.alpha u t - D.S₂.alpha u t) =
          ∫ t in u..v, f t + g t := by
        apply intervalIntegral.integral_congr_ae'
        · exact Filter.Eventually.of_forall (fun t ht => hpoint t ht)
        · exact Filter.Eventually.of_forall (fun t ht =>
            (not_lt_of_ge hab (ht.1.trans_le ht.2)).elim)
      _ = (∫ t in u..v, f t) + (∫ t in u..v, g t) :=
        intervalIntegral.integral_add hfint hgint
  rw [D.phi_diff_outgoing_density_identity huv, hsum]
  ring

end ChristodoulouBV.Uniqueness

end
