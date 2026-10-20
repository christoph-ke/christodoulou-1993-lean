module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesIncomingRadius

/-!
# Incoming scalar-radius primitive at a mixed terminal segment

The outgoing beta equation and a uniform coefficient bound dominate beta near
the terminal level by its integrable value at one lower level.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming scalar-radius density has bounded variation on each source
segment, as the sum of zeta and the product of nu with the scalar. -/
theorem source_beta_bv_on_compact_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hseg : inSeg v a b ⊆ U) :
    BoundedVariationOn (fun s => S.beta s v) (Icc a b) := by
  have hsub : Icc a b ⊆ {s | (s, v) ∈ U} := by
    intro s hs
    exact hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs, rfl⟩)
  have hNu : BoundedVariationOn (fun s => S.nu s v) (Icc a b) :=
    bv_on_compact_of_variation_bound (h.item1.choose_spec.2 v) hsub
  have hPhi : BoundedVariationOn (fun s => S.phi s v) (Icc a b) :=
    bv_on_compact_of_variation_bound (h.item3_variation.choose_spec.2 v) hsub
  have hZeta : BoundedVariationOn (fun s => S.zeta s v) (Icc a b) :=
    bv_on_compact_of_variation_bound (h.item5.choose_spec.2 v) hsub
  have hbeta : (fun s => S.beta s v) =
      (fun s => S.zeta s v) +
        (fun s => S.nu s v) * (fun s => S.phi s v) := by
    funext s
    simp only [Pi.add_apply, Pi.mul_apply, Fields.zeta]
    ring
  rw [hbeta]
  exact hZeta.add (hNu.mul hPhi)

/-- The first source's incoming scalar density has a single integrable
dominator on a strip below a mixed terminal segment. -/
theorem first_source_beta_dominated_below_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    ∃ g : ℝ → ℝ, IntervalIntegrable g volume a b ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Icc a b, g s ≤ B) ∧
      ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b, |S₁.beta s t| ≤ g s := by
  obtain ⟨C, hC, hcoefEv⟩ :=
    first_source_incoming_coefficients_uniform_below_top
      h₁ h₂ hdata hab hseg hb
  obtain ⟨t₀, ht₀v, ht₀⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).1 hcoefEv
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  let tbase := (max t₀ b + v) / 2
  have ht₀base : t₀ < tbase := by
    dsimp [tbase]
    have := le_max_left t₀ b
    have := max_lt ht₀v hbv
    linarith
  have hbbase : b < tbase := by
    dsimp [tbase]
    have := le_max_right t₀ b
    have := max_lt ht₀v hbv
    linarith
  have hbasev : tbase < v := by
    dsimp [tbase]
    have := max_lt ht₀v hbv
    linarith
  have hbaseBound := ht₀ (show tbase ∈ Ioo t₀ v from ⟨ht₀base, hbasev⟩)
  have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have ha0 : 0 ≤ a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  have hbaseSeg : inSeg tbase a b ⊆ U₁ :=
    h₁.solution.development.in_seg_subset hb ha0 hab le_rfl
      hbbase hbasev
  have hbetaBaseInt : IntervalIntegrable (fun s => S₁.beta s tbase)
      volume a b :=
    (h₁.solution.scalar_radius_in tbase a b hab hbaseSeg).1
  obtain ⟨Bβ, hBβ, hbetaBaseBound⟩ :=
    (source_beta_bv_on_compact_in h₁ hbaseSeg).exists_bound_on
  let D := C * (v - tbase)
  let g : ℝ → ℝ := fun s => |S₁.beta s tbase| + D
  have hgInt : IntervalIntegrable g volume a b :=
    hbetaBaseInt.abs.add intervalIntegrable_const
  refine ⟨g, hgInt, ⟨Bβ + max D 0, by positivity, ?_⟩, ?_⟩
  · intro s hs
    dsimp [g]
    exact add_le_add (hbetaBaseBound s hs) (le_max_left D 0)
  filter_upwards [Ioo_mem_nhdsLT hbasev] with t ht s hs
  have hst : (s, t) ∈ U₁ :=
    h₁.solution.development.past_mem hb
      (ha0.trans hs.1) hs.2 (lt_of_le_of_lt hs.2 (hbbase.trans ht.1)) ht.2
  have hprim : IntervalPrimitive (S₁.beta s)
      (fun q => IsBVSolution.radiusCoeff S₁ s q * S₁.phi s q)
      tbase t := by
    have hseg' := h₁.solution.development.out_seg_subset hst
      (lt_of_le_of_lt hs.2 hbbase) ht.1.le le_rfl
    simpa only [IsBVSolution.radiusCoeff] using
      h₁.solution.beta_out s tbase t ht.1.le hseg'
  have hcoefBound : ∀ q ∈ Ι tbase t,
      ‖IsBVSolution.radiusCoeff S₁ s q * S₁.phi s q‖ ≤ C := by
    intro q hq
    rw [uIoc_of_le ht.1.le] at hq
    rw [Real.norm_eq_abs]
    exact (ht₀ ⟨ht₀base.trans hq.1, hq.2.trans_lt ht.2⟩).2 s hs |>.2
  have hIntBound : |∫ q in tbase..t,
      IsBVSolution.radiusCoeff S₁ s q * S₁.phi s q| ≤
      C * (t - tbase) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const hcoefBound
    rwa [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.1)] at this
  have hD : C * (t - tbase) ≤ D := by
    dsimp [D]
    gcongr
    exact ht.2.le
  have htri : |S₁.beta s t| ≤
      |S₁.beta s tbase| + |S₁.beta s t - S₁.beta s tbase| := by
    have h := abs_add_le (S₁.beta s tbase) (S₁.beta s t - S₁.beta s tbase)
    have heq : S₁.beta s tbase + (S₁.beta s t - S₁.beta s tbase) =
        S₁.beta s t := by ring
    rwa [heq] at h
  calc
    |S₁.beta s t| ≤ |S₁.beta s tbase| +
      |S₁.beta s t - S₁.beta s tbase| := htri
    _ = |S₁.beta s tbase| +
      |∫ q in tbase..t,
        IsBVSolution.radiusCoeff S₁ s q * S₁.phi s q| := by rw [hprim.2]
    _ ≤ |S₁.beta s tbase| + D := by linarith only [hIntBound, hD]

/-- The selected scalar radius and incoming scalar density satisfy the
incoming primitive when the terminal endpoint belongs to the first source. -/
theorem first_source_scalar_radius_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).r s v *
        (gluedFields U₁ S₁ S₂).phi s v)
      (fun s => (gluedFields U₁ S₁ S₂).beta s v) a b := by
  let G := gluedFields U₁ S₁ S₂
  have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have ha0 : 0 ≤ a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  have hstrip : ∀ᶠ t in 𝓝[<] v, inSeg t a b ⊆ U₁ := by
    filter_upwards [Ioo_mem_nhdsLT hbv] with t ht
    exact h₁.solution.development.in_seg_subset hb ha0 hab le_rfl ht.1 ht.2
  have hsource : ∀ᶠ t in 𝓝[<] v,
      IntervalPrimitive (fun s => S₁.r s t * S₁.phi s t)
        (fun s => S₁.beta s t) a b :=
    hstrip.mono (fun t ht => h₁.solution.scalar_radius_in t a b hab ht)
  obtain ⟨g, hgInt, _, hbound⟩ :=
    first_source_beta_dominated_below_mixed_top h₁ h₂ hdata hab hseg hb
  have hLim (s : ℝ) (hs : s ∈ Icc a b) :=
    first_source_fields_tendsto_mixed_top h₁ h₂ hdata hab hseg hb hs
  obtain ⟨hTargetInt, hIntegralLimit⟩ :=
    intervalIntegrable_and_tendsto_integral_of_eventually_dominated
      hab (hsource.mono (fun _ ht => ht.1)) hgInt hbound
      (fun s hs => (hLim s hs).2.2.2.2)
  have hA := ((hLim a ⟨le_rfl, hab⟩).1.mul
    (hLim a ⟨le_rfl, hab⟩).2.1)
  have hB := ((hLim b ⟨hab, le_rfl⟩).1.mul
    (hLim b ⟨hab, le_rfl⟩).2.1)
  have hEqEv : ∀ᶠ t in 𝓝[<] v,
      S₁.r b t * S₁.phi b t - S₁.r a t * S₁.phi a t =
        ∫ s in a..b, S₁.beta s t :=
    hsource.mono (fun _ ht => ht.2)
  have hEq : G.r b v * G.phi b v - G.r a v * G.phi a v =
      ∫ s in a..b, G.beta s v := by
    have hleft := hB.sub hA
    have hright := hIntegralLimit.congr' (hEqEv.mono fun _ ht => ht.symm)
    exact tendsto_nhds_unique hleft hright
  exact ⟨hTargetInt, hEq⟩

end ChristodoulouBV.Uniqueness

end
