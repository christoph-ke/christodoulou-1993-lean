module

public import ChristodoulouBV.Existence.BVStieltjesOutgoing
import Mathlib.Tactic

/-!
# Initial-edge scalar residual and the prescribed datum

The initial radius gauge fixes λ to one half. Consequently the scalar
Stieltjes residual has exactly the canonical α variation. Taking right
limits can only decrease the variation of the prescribed raw datum.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The canonical initial expansion has the exact gauge value. -/
theorem bv_initial_lam_eq_half
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {v : ℝ} (hv : 0 < v) : d.scalarRightFields.lam 0 v = 1 / 2 := by
  have hraw (t : ℝ) (ht : 0 < t) : d.lam 0 t = 1 / 2 := by
    have hs (n : ℕ) : (T (d.subsequence n)).lam 0 t = 1 / 2 := by
      apply initial_lam_eq_of_gauge ((h (d.subsequence n)).finite (t + 1) (by linarith))
        (fun w hw => ((h (d.subsequence n)).initial_data w hw.1).1)
      exact ⟨ht, lt_add_one t⟩
    have he : Tendsto (fun n => (T (d.subsequence n)).lam 0 t) atTop (𝓝 (1 / 2)) := by
      simp_rw [hs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (d.lam_limit (0, t) ⟨le_rfl, ht⟩) he
  apply rightLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hraw t (hv.trans ht)).symm

/-- On the initial edge the outgoing scalar residual differs from
canonical α by a constant, including every canonical jump value. -/
theorem bv_initial_scalar_residual_eq
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {x b : ℝ} (hx : 0 < x) (hxb : x ≤ b) :
    bvOutgoingScalarResidual d.scalarRightFields 0 b x =
      d.scalarRightFields.alpha 0 x - (1 / 2 : ℝ) * d.scalarRightFields.phi 0 b := by
  let S := d.scalarRightFields
  have hs : outSeg 0 x b ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨le_rfl, hx.trans_le ht.1⟩
  have hp := IntervalPrimitive.of_ac_ae hxb
    ((scalar_limit_absolute_continuity h hD d).1 0 x b hxb hs)
    (bv_ae_deriv_phi_out h hD d hxb hs)
  change IntervalPrimitive (S.phi 0) (fun t => S.theta 0 t / S.r 0 t) x b at hp
  have he : (∫ t in x..b, S.lam 0 t * (S.theta 0 t / S.r 0 t)) =
      (1 / 2 : ℝ) * (S.phi 0 b - S.phi 0 x) := by
    calc
      _ = ∫ t in x..b, (1 / 2 : ℝ) * (S.theta 0 t / S.r 0 t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change S.lam 0 t * (S.theta 0 t / S.r 0 t) = _
        rw [show S.lam 0 t = 1 / 2 from bv_initial_lam_eq_half h d
          (hx.trans_le (show x ≤ t from (uIcc_of_le hxb ▸ ht).1))]
      _ = _ := by rw [intervalIntegral.integral_const_mul, ← hp.2]
  dsimp only [bvOutgoingScalarResidual]
  rw [intervalIntegral.integral_symm, he]
  change S.alpha 0 x - S.lam 0 x * S.phi 0 x -
    (1 / 2 : ℝ) * (S.phi 0 b - S.phi 0 x) = _
  rw [show S.lam 0 x = 1 / 2 from bv_initial_lam_eq_half h d hx]
  ring

/-- The initial canonical residual variation is bounded by the variation
of the prescribed datum, without a continuity assumption on that datum. -/
theorem bv_initial_scalar_residual_variation_le
    {alpha₀ : ℝ → ℝ} {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a₀ n v) atTop (𝓝 (alpha₀ v)))
    (d : RadiusLimitData T) {a b : ℝ} (ha : 0 ≤ a) :
    eVariationOn (bvOutgoingScalarResidual d.scalarRightFields 0 b) (Ioo a b) ≤
      eVariationOn alpha₀ (Ioo a b) := by
  have he : EqOn (bvOutgoingScalarResidual d.scalarRightFields 0 b)
      (fun t => d.scalarRightFields.alpha 0 t - (1 / 2 : ℝ) *
        d.scalarRightFields.phi 0 b) (Ioo a b) := by
    intro t ht
    exact bv_initial_scalar_residual_eq h hD d (ha.trans_lt ht.1) ht.2.le
  rw [eVariationOn.eq_of_eqOn he]
  simp_rw [sub_eq_add_neg]
  rw [eVariationOn.add_const]
  change eVariationOn (d.alpha 0).rightLim (Ioo a b) ≤ _
  refine (eVariationOn.rightLim_Ioo_le a b).trans ?_
  exact le_of_eq (eVariationOn.eq_of_eqOn fun t ht =>
    (data_trace_limit h hpoint d t (ha.trans_lt ht.1)).2)

/-- The outgoing scalar Stieltjes inequality (6.7a), with the actual
initial datum and the actual λ--φ analytic area. -/
theorem eq6_7a
    {alpha₀ : ℝ → ℝ} {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a₀ n v) atTop (𝓝 (alpha₀ v)))
    (d : RadiusLimitData T) {u a : ℝ} (hu : 0 < u) (hua : u < a) :
    eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u a) (Ioo u a) ≤
      eVariationOn alpha₀ (Ioo u a) +
        bvAnalyticArea h hD d .lamPhi (Ioo 0 u ×ˢ Ioo u a) :=
  (bv_outgoing_scalar_transport h hD d (u₀ := 0) le_rfl hu.le hua).trans
    (add_le_add (bv_initial_scalar_residual_variation_le h hD hpoint d hu.le) le_rfl)

end ChristodoulouBV

end
