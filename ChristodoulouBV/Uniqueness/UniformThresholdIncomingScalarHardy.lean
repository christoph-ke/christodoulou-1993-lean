module

public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingMassNorm
public import ChristodoulouBV.Uniqueness.IncomingHardyEndpoint

/-!
# Incoming scalar Hardy estimate from a shared package

The radius upper bound is selected before the normalized comparison data.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem abs_div_distance_le
    {z r d K : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hrK : r ≤ K * d) : |z| / d ≤ K * |z / r| := by
  have hK : 0 ≤ K := by nlinarith [hrK]
  have hratio : r / d ≤ K := (div_le_iff₀ hd).2 (by
    simpa only [mul_comm] using hrK)
  have hnonneg : 0 ≤ |z| / r := div_nonneg (abs_nonneg _) hr.le
  calc
    |z| / d = (r / d) * (|z| / r) := by field_simp
    _ ≤ K * (|z| / r) := mul_le_mul_of_nonneg_right hratio hnonneg
    _ = K * |z / r| := by rw [abs_div, abs_of_pos hr]

/-- The terminal-distance weighted incoming amplitude retains the local
incoming variation bound, with a geometric constant fixed globally. -/
theorem UniformThresholdBounds.zeta_abs_div_distance_integral_le_local_variation
    (P : UniformThresholdBounds) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ u v L, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ L →
            (∫ s in u..v, |S.zeta s v| / (v - s)) ≤ K * L := by
  let K := max P.radiusUpper 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K, hK, ?_⟩
  intro D ha hb hP u v L huv S hS hvar
  have hboundOne (U : Set (ℝ × ℝ)) (h : IsBVSolution U S)
      (hT : triangle D.a D.b ⊆ U) :
      (∫ s in u..v, |S.zeta s v| / (v - s)) ≤ K * L := by
    have hInt := zeta_abs_div_distance_integrable h hT huv
    have hInt' : IntegrableOn (fun s => |S.zeta s v| / (v - s))
        (Ioo u v) volume := by
      change Integrable _ (volume.restrict (Ioo u v))
      rw [restrict_Ioo_eq_restrict_Ioc]
      exact hInt
    have haccess := IsBVSolution.incoming_axis_access_of_triangle hT huv
    have hderiv : IntegrableOn (fun s => K * |deriv (fun t => S.phi t v) s|)
        (Ioo u v) volume := by
      change Integrable _ (volume.restrict (Ioo u v))
      rw [restrict_Ioo_eq_restrict_Ioc]
      exact ((h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess).abs).const_mul K
    have hae : (fun s => |S.zeta s v| / (v - s)) ≤ᵐ[volume.restrict (Ioo u v)]
        (fun s => K * |deriv (fun t => S.phi t v) s|) := by
      apply (ae_restrict_iff' measurableSet_Ioo).mpr
      filter_upwards [h.scalar_ae_deriv_in_on_half_open_access
        huv.2.1 haccess] with s hφ hs
      have hsco : s ∈ Ico u v := ⟨hs.1.le, hs.2⟩
      have hsU := haccess s hsco
      have hr := h.solution.radius_pos (s, v) hsU
      have hd : 0 < v - s := sub_pos.mpr hsco.2
      have hspt : (s, v) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1.trans hsco.1, hsco.2, huv.2.2⟩
      have hspt' : (s, v) ∈ triangle 0 1 := by
        simpa only [ha, hb] using hspt
      have hrhi := (hP s v hspt' S hS).2.2.2.2.2.2.2.2
      have hrK : S.r s v ≤ K * (v - s) :=
        hrhi.trans (mul_le_mul_of_nonneg_right
          (le_max_left P.radiusUpper 0) hd.le)
      have hh := abs_div_distance_le hr hd hrK (z := S.zeta s v)
      rw [← hφ hsco] at hh
      exact hh
    have hle := integral_mono_ae hInt' hderiv hae
    change (∫ s in Ioo u v, |S.zeta s v| / (v - s)) ≤
      (∫ s in Ioo u v, K * |deriv (fun t => S.phi t v) s|) at hle
    rw [restrict_Ioo_eq_restrict_Ioc] at hle
    rw [← intervalIntegral.integral_of_le huv.2.1.le,
      ← intervalIntegral.integral_of_le huv.2.1.le,
      intervalIntegral.integral_const_mul] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left
      (scalar_deriv_integral_le_local_variation_in h hT huv hvar) hK)
  rcases hS with rfl | rfl
  · exact hboundOne D.U₁ D.h₁ (fun p hp => (D.hT hp).1)
  · exact hboundOne D.U₂ D.h₂ (fun p hp => (D.hT hp).2)

end ChristodoulouBV.Uniqueness

end
