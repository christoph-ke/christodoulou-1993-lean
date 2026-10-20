module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesDominated

/-!
# Incoming transport across a mixed terminal edge

The incoming `λ` and `α` equations pass from lower outgoing levels to the
canonical left traces on a mixed terminal segment.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- If the first source contains the upper incoming endpoint, the canonical
left-trace densities satisfy both incoming transport primitives on the whole
mixed terminal segment. -/
theorem first_source_lam_alpha_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).lam s v)
      (fun s => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v) a b ∧
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).alpha s v)
      (fun s => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v *
        (gluedFields U₁ S₁ S₂).phi s v) a b := by
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
  have hLamSource : ∀ᶠ t in 𝓝[<] v,
      IntervalPrimitive (fun s => S₁.lam s t)
        (fun s => IsBVSolution.radiusCoeff S₁ s t) a b := by
    filter_upwards [hstrip] with t ht
    simpa only [IsBVSolution.radiusCoeff] using
      h₁.solution.lam_in t a b hab ht
  have hAlphaSource : ∀ᶠ t in 𝓝[<] v,
      IntervalPrimitive (fun s => S₁.alpha s t)
        (fun s => IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t) a b := by
    filter_upwards [hstrip] with t ht
    simpa only [IsBVSolution.radiusCoeff] using
      h₁.solution.alpha_in t a b hab ht
  obtain ⟨C, hC, hbound⟩ :=
    first_source_incoming_coefficients_uniform_below_top
      h₁ h₂ hdata hab hseg hb
  have hLamInt : ∀ᶠ t in 𝓝[<] v,
      IntervalIntegrable (fun s => IsBVSolution.radiusCoeff S₁ s t)
        volume a b := hLamSource.mono (fun _ ht => ht.1)
  have hAlphaInt : ∀ᶠ t in 𝓝[<] v,
      IntervalIntegrable
        (fun s => IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t)
        volume a b := hAlphaSource.mono (fun _ ht => ht.1)
  have hLamBound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b,
        |IsBVSolution.radiusCoeff S₁ s t| ≤ C := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with t ht s hs
    exact (ht.2 s hs).1
  have hAlphaBound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b,
        |IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t| ≤ C := by
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with t ht s hs
    exact (ht.2 s hs).2
  have hCoeffLimit (s : ℝ) (hs : s ∈ Icc a b) :=
    first_source_radiusCoeff_tendsto_mixed_top
      h₁ h₂ hdata hab hseg hb hs
  obtain ⟨hLamTargetInt, hLamIntegralLimit⟩ :=
    intervalIntegrable_and_tendsto_integral_of_eventually_bounded
      hab hLamInt hLamBound (fun s hs => (hCoeffLimit s hs).1)
  obtain ⟨hAlphaTargetInt, hAlphaIntegralLimit⟩ :=
    intervalIntegrable_and_tendsto_integral_of_eventually_bounded
      hab hAlphaInt hAlphaBound (fun s hs => (hCoeffLimit s hs).2)
  have hLamA := (first_source_lam_alpha_tendsto_mixed_top
    h₁ h₂ hdata hab hseg hb (show a ∈ Icc a b from ⟨le_rfl, hab⟩)).1
  have hLamB := (first_source_lam_alpha_tendsto_mixed_top
    h₁ h₂ hdata hab hseg hb (show b ∈ Icc a b from ⟨hab, le_rfl⟩)).1
  have hAlphaA := (first_source_lam_alpha_tendsto_mixed_top
    h₁ h₂ hdata hab hseg hb (show a ∈ Icc a b from ⟨le_rfl, hab⟩)).2
  have hAlphaB := (first_source_lam_alpha_tendsto_mixed_top
    h₁ h₂ hdata hab hseg hb (show b ∈ Icc a b from ⟨hab, le_rfl⟩)).2
  have hLamEqEv : ∀ᶠ t in 𝓝[<] v,
      S₁.lam b t - S₁.lam a t =
        ∫ s in a..b, IsBVSolution.radiusCoeff S₁ s t :=
    hLamSource.mono (fun _ ht => ht.2)
  have hAlphaEqEv : ∀ᶠ t in 𝓝[<] v,
      S₁.alpha b t - S₁.alpha a t =
        ∫ s in a..b, IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t :=
    hAlphaSource.mono (fun _ ht => ht.2)
  have hLamTopEq : G.lam b v - G.lam a v =
      ∫ s in a..b, IsBVSolution.radiusCoeff G s v := by
    have hleft := hLamB.sub hLamA
    have hright := hLamIntegralLimit.congr'
      (hLamEqEv.mono fun _ ht => ht.symm)
    exact tendsto_nhds_unique hleft hright
  have hAlphaTopEq : G.alpha b v - G.alpha a v =
      ∫ s in a..b, IsBVSolution.radiusCoeff G s v * G.phi s v := by
    have hleft := hAlphaB.sub hAlphaA
    have hright := hAlphaIntegralLimit.congr'
      (hAlphaEqEv.mono fun _ ht => ht.symm)
    exact tendsto_nhds_unique hleft hright
  exact ⟨⟨hLamTargetInt, hLamTopEq⟩,
    ⟨hAlphaTargetInt, hAlphaTopEq⟩⟩

end ChristodoulouBV.Uniqueness

end
