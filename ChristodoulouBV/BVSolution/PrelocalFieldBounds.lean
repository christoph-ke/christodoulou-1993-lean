module

public import ChristodoulouBV.BVSolution.AxisExponential
public import ChristodoulouBV.BVSolution.IncomingAxis
public import ChristodoulouBV.Uniqueness.Triangle

/-!
# Bounds fixed before local comparison

The BV constants control the scalar from one initial reference value. Axis
traces then anchor both scalar amplitudes on complete comparison triangles.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The scalar at any development point is controlled by its value at one
fixed initial point and twice the global scalar variation. The limit from
strictly lower outgoing coordinates handles an included terminal top. -/
theorem phi_abs_le_reference_variation
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {w u v : ℝ} (href : (0, w) ∈ U) (huv : (u, v) ∈ U) :
    |S.phi u v| ≤ |S.phi 0 w| +
      2 * max h.item3_variation.choose 0 := by
  let hD := h.solution.development
  let C := h.item3_variation.choose
  have hvarOut := h.item3_variation.choose_spec.1
  have hvarIn := h.item3_variation.choose_spec.2
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hvarOut' (s : ℝ) :
      (eVariationOn (S.phi s) {t | (s, t) ∈ U}).toReal ≤ max C 0 :=
    ENNReal.toReal_le_of_le_ofReal hC
      ((hvarOut s).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hvarIn' (t : ℝ) :
      (eVariationOn (fun s => S.phi s t) {s | (s, t) ∈ U}).toReal ≤ max C 0 :=
    ENNReal.toReal_le_of_le_ofReal hC
      ((hvarIn t).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hBVout : BoundedVariationOn (S.phi 0) {t | (0, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvarOut 0)
  let t₀ : ℝ := (u + v) / 2
  have hut₀ : u < t₀ := by
    dsimp [t₀]
    linarith [(hD.wedge huv).2]
  have ht₀v : t₀ < v := by
    dsimp [t₀]
    linarith [(hD.wedge huv).2]
  have hseg := hD.out_seg_subset huv hut₀ ht₀v.le le_rfl
  have hcont : ContinuousOn (S.phi u) (Icc t₀ v) := by
    simpa only [uIcc_of_le ht₀v.le] using
      (h.item3_ac_out u t₀ v ht₀v.le hseg).continuousOn
  have hleft : Tendsto (fun t : ℝ => t) (𝓝[<] v) (𝓝[Icc t₀ v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT ht₀v)
        (fun t ht => ⟨ht.1.le, ht.2.le⟩)⟩
  have hphi : Tendsto (S.phi u) (𝓝[<] v) (𝓝 (S.phi u v)) :=
    (hcont.continuousWithinAt
      (show v ∈ Icc t₀ v from ⟨ht₀v.le, le_rfl⟩)).tendsto.comp hleft
  have hbound : ∀ᶠ t in 𝓝[<] v,
      |S.phi u t| ≤ |S.phi 0 w| + 2 * max C 0 := by
    filter_upwards [Ioo_mem_nhdsLT ht₀v] with t ht
    have hut : u < t := hut₀.trans ht.1
    have h0t : (0, t) ∈ U :=
      hD.past_mem huv le_rfl (hD.wedge huv).1
        ((hD.wedge huv).1.trans_lt hut) ht.2
    have hutU : (u, t) ∈ U := hD.outgoing_mem huv hut ht.2.le
    have hBVIn : BoundedVariationOn (fun s => S.phi s t)
        {s | (s, t) ∈ U} :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvarIn t)
    have h₁ := hBVout.abs_sub_le_variation h0t href
    have h₂ := hBVIn.abs_sub_le_variation hutU h0t
    have h₁' := hvarOut' 0
    have h₂' := hvarIn' t
    have htri₁ : |S.phi u t| ≤
        |S.phi u t - S.phi 0 t| + |S.phi 0 t| := by
      calc
        |S.phi u t| = |(S.phi u t - S.phi 0 t) + S.phi 0 t| := by
          rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
    have htri₂ : |S.phi 0 t| ≤
        |S.phi 0 t - S.phi 0 w| + |S.phi 0 w| := by
      calc
        |S.phi 0 t| = |(S.phi 0 t - S.phi 0 w) + S.phi 0 w| := by
          rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
    linarith
  have hlim : Tendsto (fun t => |S.phi u t|) (𝓝[<] v)
      (𝓝 |S.phi u v|) := hphi.abs
  have hres := le_of_tendsto hlim hbound
  exact hres

/-- The zero outgoing axis trace anchors the global variation bound for
`θ`, uniformly on every development point. -/
theorem theta_abs_le_global_variation
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    |S.theta u v| ≤ max h.item5.choose 0 := by
  let C := h.item5.choose
  have hvar := h.item5.choose_spec.1 u
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hTV : (eVariationOn (S.theta u) {t | (u, t) ∈ U}).toReal ≤
      max C 0 := ENNReal.toReal_le_of_le_ofReal hC
        (hvar.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hBV : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have hlt := (h.solution.development.wedge huv).2
  have hbound : ∀ᶠ t in 𝓝[>] u,
      |S.theta u v| ≤ |S.theta u t| + max C 0 := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2.le
    have hd := hBV.abs_sub_le_variation huv htU
    have htri : |S.theta u v| ≤
        |S.theta u v - S.theta u t| + |S.theta u t| := by
      calc
        |S.theta u v| =
            |(S.theta u v - S.theta u t) + S.theta u t| := by
          rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
    linarith
  have hlim : Tendsto (fun t => |S.theta u t| + max C 0)
      (𝓝[>] u) (𝓝 (max C 0)) := by
    simpa only [abs_zero, zero_add] using
      (h.theta_tendsto_zero_axis_out huv).abs.add_const (max C 0)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- The zero incoming axis trace anchors the global incoming variation on
each full augmented comparison triangle. -/
theorem zeta_abs_le_global_variation_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    |S.zeta u v| ≤ max h.item5.choose 0 := by
  let C := h.item5.choose
  have hvar := h.item5.choose_spec.2 v
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hTV : (eVariationOn (fun s => S.zeta s v)
      {s | (s, v) ∈ U}).toReal ≤ max C 0 :=
    ENNReal.toReal_le_of_le_ofReal hC
      (hvar.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hBV : BoundedVariationOn (fun s => S.zeta s v)
      {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U := by
    intro s hs
    exact hT ((Uniqueness.mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  have hbound : ∀ᶠ s in 𝓝[<] v,
      |S.zeta u v| ≤ |S.zeta s v| + max C 0 := by
    filter_upwards [Ioo_mem_nhdsLT huv.2.1] with s hs
    have hsU := haccess s ⟨hs.1.le, hs.2⟩
    have hd := hBV.abs_sub_le_variation (hT huv) hsU
    have htri : |S.zeta u v| ≤
        |S.zeta u v - S.zeta s v| + |S.zeta s v| := by
      calc
        |S.zeta u v| =
            |(S.zeta u v - S.zeta s v) + S.zeta s v| := by
          rw [sub_add_cancel]
        _ ≤ _ := abs_add_le _ _
    linarith
  have hlim : Tendsto (fun s => |S.zeta s v| + max C 0)
      (𝓝[<] v) (𝓝 (max C 0)) := by
    simpa only [abs_zero, zero_add] using
      (h.zeta_tendsto_zero_axis_in_of_half_open_access huv.2.1 haccess).abs.add_const
        (max C 0)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- One solution has constants fixed from its global BV bounds and a single
initial scalar reference value. They work on every full comparison triangle,
independently of its top and width. -/
theorem exists_preloc_field_bounds
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {w : ℝ} (href : (0, w) ∈ U) :
    ∃ c C₀ : ℝ, 0 < c ∧ 0 ≤ C₀ ∧
      ∀ a b u v, Uniqueness.triangle a b ⊆ U →
        (u, v) ∈ Uniqueness.triangle a b →
        c ≤ S.lam u v ∧ S.lam u v ≤ C₀ ∧
        c ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₀ ∧
        |S.phi u v| ≤ C₀ ∧ |S.theta u v| ≤ C₀ ∧
        |S.zeta u v| ≤ C₀ := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  obtain ⟨K, hK, _⟩ := h.exists_uniform_radius_upper
  obtain ⟨N, hN⟩ := h.nu_bounded_below
  let P := |S.phi 0 w| + 2 * max h.item3_variation.choose 0
  let T := max h.item5.choose 0
  let C₀ := max K (max N (max P T))
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀, T]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨c, C₀, hc, hC₀, ?_⟩
  intro a b u v hT huv
  have huU := hT huv
  have hnneg : S.nu u v < 0 :=
    (h.nu_le_neg_lower hc hlam huU).trans_lt (neg_lt_zero.mpr hc)
  have hK' : K ≤ C₀ := le_max_left _ _
  have hN' : N ≤ C₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hP' : P ≤ C₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hT' : T ≤ C₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hnlow := h.nu_le_neg_lower hc hlam huU
  have hnup := hN (u, v) huU
  have hphi := h.phi_abs_le_reference_variation href huU
  have htheta := h.theta_abs_le_global_variation huU
  have hzeta := h.zeta_abs_le_global_variation_of_triangle hT huv
  dsimp [P, T] at hP' hT'
  rw [abs_of_neg hnneg]
  exact ⟨hlam (u, v) huU, (hK (u, v) huU).trans hK',
    by linarith, hnup.trans hN', hphi.trans hP',
    htheta.trans hT', hzeta.trans hT'⟩

/-- A fixed pair sharing an initial scalar reference has one pair of
prelocal constants, chosen before any comparison triangle or smallness
parameter. -/
theorem exists_pair_preloc_field_bounds
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w : ℝ} (href : (0, w) ∈ U₁ ∩ U₂)
    (hdata : S₁.phi 0 w = S₂.phi 0 w) :
    ∃ c C₀ : ℝ, 0 < c ∧ 0 ≤ C₀ ∧
      ∀ a b u v, Uniqueness.triangle a b ⊆ U₁ ∩ U₂ →
        (u, v) ∈ Uniqueness.triangle a b →
        ∀ S : Fields, (S = S₁ ∨ S = S₂) →
          c ≤ S.lam u v ∧ S.lam u v ≤ C₀ ∧
          c ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₀ ∧
          |S.phi u v| ≤ C₀ ∧ |S.theta u v| ≤ C₀ ∧
          |S.zeta u v| ≤ C₀ := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hbound₁⟩ :=
    h₁.exists_preloc_field_bounds href.1
  obtain ⟨c₂, C₂, hc₂, hC₂, hbound₂⟩ :=
    h₂.exists_preloc_field_bounds href.2
  have _hshared : |S₂.phi 0 w| = |S₁.phi 0 w| := by rw [← hdata]
  refine ⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂,
    hC₁.trans (le_max_left _ _), ?_⟩
  intro a b u v hT huv S hS
  rcases hS with rfl | rfl
  · have hT₁ : Uniqueness.triangle a b ⊆ U₁ := fun p hp => (hT hp).1
    obtain ⟨hlamLo, hlamHi, hnuLo, hnuHi, hphi, htheta, hzeta⟩ :=
      hbound₁ a b u v hT₁ huv
    exact ⟨(min_le_left _ _).trans hlamLo,
      hlamHi.trans (le_max_left _ _), (min_le_left _ _).trans hnuLo,
      hnuHi.trans (le_max_left _ _), hphi.trans (le_max_left _ _),
      htheta.trans (le_max_left _ _), hzeta.trans (le_max_left _ _)⟩
  · have hT₂ : Uniqueness.triangle a b ⊆ U₂ := fun p hp => (hT hp).2
    obtain ⟨hlamLo, hlamHi, hnuLo, hnuHi, hphi, htheta, hzeta⟩ :=
      hbound₂ a b u v hT₂ huv
    exact ⟨(min_le_right _ _).trans hlamLo,
      hlamHi.trans (le_max_right _ _), (min_le_right _ _).trans hnuLo,
      hnuHi.trans (le_max_right _ _), hphi.trans (le_max_right _ _),
      htheta.trans (le_max_right _ _), hzeta.trans (le_max_right _ _)⟩

end ChristodoulouBV.IsBVSolution

end
