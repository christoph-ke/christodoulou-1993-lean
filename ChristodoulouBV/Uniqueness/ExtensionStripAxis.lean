module

public import ChristodoulouBV.Uniqueness.ExtensionStripIntegralI1
import ChristodoulouBV.BVSolution.AxisIntegrals

/-!
# Local outgoing axis identity

The scalar-radius primitive and the regular-axis trace give the identity
used before (5.16), on the complete outgoing ray of any C¹ development.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The radius equals the integral of its outgoing expansion from the
regular axis on any C¹ development. -/
theorem radius_eq_outgoing_lam_integral_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    S.r u v = ∫ t in u..v, S.lam u t := by
  have huv : u < v := (H.solution.development.1 hp).2
  have haxisMem : (u, u) ∈ closure U :=
    H.solution.development.axis_mem hp
  have hmap (t : ℝ) (ht : t ∈ Icc u v) : (u, t) ∈ closure U := by
    rcases eq_or_lt_of_le ht.1 with heq | hlt
    · subst t
      exact haxisMem
    · exact subset_closure
        (H.solution.development.outgoing_mem hp hlt ht.2)
  have hlam : ContinuousOn (S.lam u) (Icc u v) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hInt : IntervalIntegrable (S.lam u) volume u v :=
    hlam.intervalIntegrable_of_Icc huv.le
  have htrace : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq hp] using
      H.solution.radius_axis u (H.solution.development.axis_mem hp)
  have hprim : ∀ x ∈ Ioo u v,
      IntervalPrimitive (S.r u) (S.lam u) x v := by
    intro x hx
    exact H.solution.radius_out u x v hx.2.le
      (H.solution.development.out_seg_subset hp hx.1 hx.2.le le_rfl)
  exact IsBVSolution.primitive_eq_integral_of_left_trace
    huv hInt hprim htrace

/-- The scalar field equals the outgoing `α` integral divided by radius,
on any C¹ development. -/
theorem phi_eq_outgoing_alpha_integral_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    S.phi u v = (∫ t in u..v, S.alpha u t) / S.r u v := by
  have huv : u < v := (H.solution.development.1 hp).2
  have haxisMem : (u, u) ∈ closure U :=
    H.solution.development.axis_mem hp
  have hmap (t : ℝ) (ht : t ∈ Icc u v) : (u, t) ∈ closure U := by
    rcases eq_or_lt_of_le ht.1 with heq | hlt
    · subst t
      exact haxisMem
    · exact subset_closure
        (H.solution.development.outgoing_mem hp hlt ht.2)
  have hα : ContinuousOn (S.alpha u) (Icc u v) :=
    (alpha_contDiffOn_closure H).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hInt : IntervalIntegrable (S.alpha u) volume u v :=
    hα.intervalIntegrable_of_Icc huv.le
  have hRaxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq hp] using
      H.solution.radius_axis u (H.solution.development.axis_mem hp)
  have hpair : Tendsto (fun t : ℝ => (u, t))
      (𝓝[>] u) (𝓝 (u, u)) :=
    ((show Continuous (fun t : ℝ => (u, t)) by fun_prop).tendsto u).mono_left
      inf_le_left
  have hnear : ∀ᶠ t in 𝓝[>] u, (u, t) ∈ closure U := by
    filter_upwards [Ioo_mem_nhdsGT huv] with t ht
    exact subset_closure
      (H.solution.development.outgoing_mem hp ht.1 ht.2.le)
  have hmapAxis : Tendsto (fun t : ℝ => (u, t))
      (𝓝[>] u) (𝓝[closure U] (u, u)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpair, hnear⟩
  have hφaxis : Tendsto (S.phi u) (𝓝[>] u) (𝓝 (S.phi u u)) := by
    exact ((H.phi_c1.continuousOn (u, u) haxisMem).tendsto).comp hmapAxis
  have htrace : Tendsto (fun t => S.r u t * S.phi u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa using hRaxis.mul hφaxis
  have hprim : ∀ x ∈ Ioo u v,
      IntervalPrimitive (fun t => S.r u t * S.phi u t) (S.alpha u) x v := by
    intro x hx
    exact H.solution.scalar_radius_out u x v hx.2.le
      (H.solution.development.out_seg_subset hp hx.1 hx.2.le le_rfl)
  have heq := IsBVSolution.primitive_eq_integral_of_left_trace
    huv hInt hprim htrace
  exact (eq_div_iff (ne_of_gt (H.solution.radius_pos (u, v) hp))).2
    (by simpa only [mul_comm] using heq)

/-- The exact axis identity used in (5.16), valid on the enlarged domain
without a triangle cutoff. -/
theorem theta_ratio_axis_identity_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    S.theta u v / S.lam u v =
      S.alpha u v / S.lam u v -
        (∫ t in u..v, S.alpha u t) / S.r u v := by
  have hφ := phi_eq_outgoing_alpha_integral_of_c1_domain H hp
  have hlam : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v) hp)
  dsimp [Fields.theta]
  rw [hφ]
  field_simp [hlam]

end ChristodoulouBV.Uniqueness

end
