module

public import ChristodoulouBV.AreaEstimates.SourceInputsWeakLogIn

/-!
# Open-segment source bounds without BV axis clauses

The source majorants and their endpoint integrability use explicit reduced
solution, scalar AC/BV, invariant BV and pointwise geometry premises.
The original full-BV statements are recovered in `SourceInputsWeakCorollaries`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.SourceInputsWeak

open IsBVSolution

/-- A pointwise upper expansion bound integrates from the excluded axis. -/
theorem radius_upper_of_lam_le {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S) {K u v : ℝ}
    (hlam : ∀ p ∈ U, S.lam p.1 p.2 ≤ K) (huv : (u, v) ∈ U) :
    S.r u v ≤ K * (v - u) := by
  let hD := h.development
  have hlt : u < v := (hD.wedge huv).2
  have haxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      h.radius_axis u (hD.axis_mem huv)
  have hlimK : Tendsto (fun a : ℝ => K * (v - a)) (𝓝[>] u)
      (𝓝 (K * (v - u))) :=
    ((show Continuous (fun a : ℝ => K * (v - a)) by fun_prop).tendsto u).mono_left
      inf_le_left
  have hlim : Tendsto (fun a : ℝ => S.r u a + K * (v - a))
      (𝓝[>] u) (𝓝 (K * (v - u))) := by
    simpa using haxis.add hlimK
  have hbound : ∀ᶠ a in 𝓝[>] u, S.r u v ≤ S.r u a + K * (v - a) := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with a ha
    have hseg := hD.out_seg_subset huv ha.1 ha.2.le le_rfl
    obtain ⟨hint, heq⟩ := h.radius_out u a v ha.2.le hseg
    have hcint : IntervalIntegrable (fun _ : ℝ => K) volume a v :=
      intervalIntegrable_const
    have hmono : (∫ t in a..v, S.lam u t) ≤ ∫ _ in a..v, K := by
      apply intervalIntegral.integral_mono_on ha.2.le hint hcint
      intro t ht
      exact hlam (u, t) (hD.outgoing_mem huv (ha.1.trans_le ht.1) ht.2)
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    linarith
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- The value at the terminal point of an outgoing BV scalar slice contributes
no extra variation: the frozen local absolute-continuity clause fixes its
left trace. -/
theorem outgoing_scalar_variation_Ioc_eq_Ioo
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsSolution U S)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    eVariationOn (S.phi u) (Ioc u v) =
      eVariationOn (S.phi u) (Ioo u v) := by
  have hlt : u < v := (h.development.wedge huv).2
  let a : ℝ := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hseg : outSeg u a v ⊆ U :=
    h.development.out_seg_subset huv hua hav.le le_rfl
  have hAC := hACOut u a v hav.le hseg
  have hcont : ContinuousOn (S.phi u) (Icc a v) := by
    simpa only [uIcc_of_le hav.le] using hAC.continuousOn
  have hleft : ContinuousWithinAt (S.phi u) (Iic v) v :=
    (continuousWithinAt_Icc_iff_Iic hav).mp
      (hcont.continuousWithinAt ⟨hav.le, le_rfl⟩)
  exact eVariationOn.Ioc_eq_Ioo_of_continuousWithinAt hlt hleft

/-- The value at the initial point of an incoming BV scalar slice contributes
no extra variation on an accessible characteristic. -/
theorem incoming_scalar_variation_Ico_eq_Ioo
    {U : Set (ℝ × ℝ)} {S : Fields} (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    eVariationOn (fun s => S.phi s v) (Ico u v) =
      eVariationOn (fun s => S.phi s v) (Ioo u v) := by
  let b : ℝ := (u + v) / 2
  have hub : u < b := by dsimp [b]; linarith
  have hbv : b < v := by dsimp [b]; linarith
  have hseg : inSeg v u b ⊆ U := by
    intro p hp
    rcases p with ⟨s, t⟩
    have hst : s ∈ Icc u b ∧ t = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
    rcases hst with ⟨hs, rfl⟩
    exact haccess s ⟨hs.1, hs.2.trans_lt hbv⟩
  have hAC := hACIn v u b hub.le hseg
  have hcont : ContinuousOn (fun s => S.phi s v) (Icc u b) := by
    simpa only [uIcc_of_le hub.le] using hAC.continuousOn
  have hright : ContinuousWithinAt (fun s => S.phi s v) (Ici u) u :=
    (continuousWithinAt_Icc_iff_Ici hub).mp
      (hcont.continuousWithinAt ⟨le_rfl, hub.le⟩)
  exact eVariationOn.Ico_eq_Ioo_of_continuousWithinAt huv hright

/-- Outgoing source mass-ratio majorant under the displayed weak premises. -/
theorem source_mass_ratio_out_majorant
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (hPhiBVOut : ∀ u, BoundedVariationOn (S.phi u) {v | (u, v) ∈ U})
    (hThetaBV : ∀ u, BoundedVariationOn (S.theta u) {v | (u, v) ∈ U})
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ p ∈ U, |S.theta p.1 p.2 / S.lam p.1 p.2| ≤ M) :
    (∫ t in u..v,
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) ≤
      M * (eVariationOn (S.phi u) (Ioo u v)).toReal := by
  rw [← outgoing_scalar_variation_Ioc_eq_Ioo h hACOut huv]
  exact eq3_1a h hc hlam hR hmu hACOut hPhiBVOut hThetaBV huv
    (fun t ht => hM (u, t) (h.development.outgoing_mem huv ht.1 ht.2))

/-- Incoming source mass-ratio majorant on an accessible half-open ray. -/
theorem source_mass_ratio_in_majorant_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (hPhiBVIn : ∀ v, BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U})
    (hZetaBV : ∀ v, BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U})
    {u v M : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U)
    (hM : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ M) :
    -(∫ s in u..v,
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) ≤
      M * (eVariationOn (fun s => S.phi s v) (Ioo u v)).toReal := by
  rw [← incoming_scalar_variation_Ico_eq_Ioo hACIn huv haccess]
  exact eq3_1b h hc hlam hnu hR hmu hACIn hPhiBVIn hZetaBV huv haccess hM

/-- Incoming source mass-ratio majorant on an accessible triangle. -/
theorem source_mass_ratio_in_majorant
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (hPhiBVIn : ∀ v, BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U})
    (hZetaBV : ∀ v, BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U})
    {a b u v M : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b)
    (hM : ∀ p ∈ Uniqueness.triangle a b, |S.zeta p.1 p.2 / S.nu p.1 p.2| ≤ M) :
    -(∫ s in u..v,
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) ≤
      M * (eVariationOn (fun s => S.phi s v) (Ioo u v)).toReal := by
  exact source_mass_ratio_in_majorant_of_half_open_access h hc hlam hnu hR hmu
    hACIn hPhiBVIn hZetaBV huv.2.1 (incoming_axis_access_of_triangle hT huv)
    (fun s hs => hM (s, v) (Uniqueness.mem_triangle.mpr
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩))

/-- Outgoing printed mass-ratio coefficient is integrable up to the axis. -/
theorem source_mass_ratio_out_interval_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (hPhiBVOut : ∀ u, BoundedVariationOn (S.phi u) {v | (u, v) ∈ U})
    (hThetaBV : ∀ u, BoundedVariationOn (S.theta u) {v | (u, v) ∈ U})
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M) :
    IntervalIntegrable (fun t =>
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) volume u v := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (h.development.wedge huv).2.le).2
      (nu_coeff_integrable_axis h hc hlam hR hmu hACOut hPhiBVOut hThetaBV huv hM)
  apply hi.congr_uIoo
  intro t ht
  rw [uIoo_of_le (h.development.wedge huv).2.le] at ht
  exact nuCoeff_eq_mass_ratio_coefficient_out h hmu
    (h.development.outgoing_mem huv ht.1 ht.2.le)

/-- Incoming printed mass-ratio coefficient is integrable up to the axis. -/
theorem source_mass_ratio_in_interval_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (hPhiBVIn : ∀ v, BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U})
    (hZetaBV : ∀ v, BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U})
    {u v M : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U)
    (hM : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ M) :
    IntervalIntegrable (fun s =>
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) volume u v := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).2
    (incomingCoeff_integrable_axis h hc hlam hnu hR hmu hACIn hPhiBVIn hZetaBV
      huv haccess hM)

end ChristodoulouBV.SourceInputsWeak

end
