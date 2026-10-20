module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesFields
import ChristodoulouBV.BVSolution.PrimitiveCalculus

/-!
# Outgoing limits at mixed incoming terminal points

The five fields that are pointwise common on overlaps approach the selected
top values from lower outgoing levels, even if the first source does not
contain the top point.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Absolute continuity on a closed outgoing interval gives its left
endpoint limit at the upper endpoint. -/
theorem tendsto_left_of_absolutelyContinuousOnInterval
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    Tendsto f (𝓝[<] b) (𝓝 (f b)) := by
  have hcont : ContinuousOn f (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hf.continuousOn
  have hleft : Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT hab)
        (fun t ht => ⟨ht.1.le, ht.2.le⟩)⟩
  exact (hcont.continuousWithinAt
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)).tendsto.comp hleft

/-- Radius, scalar, mass, incoming expansion, and incoming scalar density
are continuous from below in the outgoing coordinate at every source point. -/
theorem source_fields_tendsto_outgoing_top
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    Tendsto (S.r u) (𝓝[<] v) (𝓝 (S.r u v)) ∧
      Tendsto (S.phi u) (𝓝[<] v) (𝓝 (S.phi u v)) ∧
      Tendsto (S.m u) (𝓝[<] v) (𝓝 (S.m u v)) ∧
      Tendsto (S.nu u) (𝓝[<] v) (𝓝 (S.nu u v)) ∧
      Tendsto (S.beta u) (𝓝[<] v) (𝓝 (S.beta u v)) := by
  have huv := (h.solution.development.wedge hp).2
  let t₀ := (u + v) / 2
  have hut₀ : u < t₀ := by dsimp [t₀]; linarith only [huv]
  have ht₀v : t₀ < v := by dsimp [t₀]; linarith only [huv]
  have hseg := h.solution.development.out_seg_subset hp hut₀ ht₀v.le le_rfl
  have hr := (h.solution.radius_out_ac_ae ht₀v.le hseg).1
  have hphi := h.item3_ac_out u t₀ v ht₀v.le hseg
  have hm := (h.solution.mass_out_ac_ae ht₀v.le hseg).1
  have hnu := (h.solution.nu_out_ac_ae ht₀v.le hseg).1
  have hbeta := (h.solution.beta_out_ac_ae ht₀v.le hseg).1
  exact ⟨tendsto_left_of_absolutelyContinuousOnInterval ht₀v hr,
    tendsto_left_of_absolutelyContinuousOnInterval ht₀v hphi,
    tendsto_left_of_absolutelyContinuousOnInterval ht₀v hm,
    tendsto_left_of_absolutelyContinuousOnInterval ht₀v hnu,
    tendsto_left_of_absolutelyContinuousOnInterval ht₀v hbeta⟩

/-- At every point of a mixed terminal incoming segment, the source
containing its upper endpoint approaches the five canonical top values from
strictly lower outgoing levels. -/
theorem first_source_fields_tendsto_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b s : ℝ} (_hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁)
    (hs : s ∈ Icc a b) :
    Tendsto (S₁.r s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).r s v)) ∧
    Tendsto (S₁.phi s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).phi s v)) ∧
    Tendsto (S₁.m s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).m s v)) ∧
    Tendsto (S₁.nu s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).nu s v)) ∧
    Tendsto (S₁.beta s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).beta s v)) := by
  have htop : (s, v) ∈ U₁ ∪ U₂ := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  rcases htop with ht₁ | ht₂
  · obtain ⟨hr, hphi, hm, hnu, hbeta⟩ :=
      source_fields_tendsto_outgoing_top h₁ ht₁
    obtain ⟨hrEq, hphiEq, hmEq, hnuEq, hbetaEq⟩ :=
      gluedFields_eq_first ht₁
    rw [hrEq, hphiEq, hmEq, hnuEq, hbetaEq]
    exact ⟨hr, hphi, hm, hnu, hbeta⟩
  · obtain ⟨hr, hphi, hm, hnu, hbeta⟩ :=
      source_fields_tendsto_outgoing_top h₂ ht₂
    have hs0 := (h₂.solution.development.wedge ht₂).1
    have hsv := (h₂.solution.development.wedge ht₂).2
    have heq : ∀ᶠ t in 𝓝[<] v,
        S₁.r s t = S₂.r s t ∧ S₁.phi s t = S₂.phi s t ∧
        S₁.m s t = S₂.m s t ∧ S₁.nu s t = S₂.nu s t ∧
        S₁.beta s t = S₂.beta s t := by
      filter_upwards [Ioo_mem_nhdsLT hsv] with t ht
      have ht₁' : (s, t) ∈ U₁ :=
        h₁.solution.development.past_mem hb hs0 hs.2 ht.1 ht.2
      have ht₂' : (s, t) ∈ U₂ :=
        h₂.solution.development.outgoing_mem ht₂ ht.1 ht.2.le
      obtain ⟨hrEq, hphiEq, hmEq⟩ :=
        theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata
          (s, t) ⟨ht₁', ht₂'⟩
      have hnuEq := source_nu_eq_on_overlap h₁ h₂ hdata
        (show (s, t) ∈ U₁ ∩ U₂ from ⟨ht₁', ht₂'⟩)
      have hbetaEq := source_beta_eq_on_overlap h₁ h₂ hdata
        (show (s, t) ∈ U₁ ∩ U₂ from ⟨ht₁', ht₂'⟩)
      exact ⟨hrEq, hphiEq, hmEq, hnuEq, hbetaEq⟩
    obtain ⟨hrEq, hphiEq, hmEq, hnuEq, hbetaEq⟩ :=
      gluedFields_eq_second h₁ h₂ hdata ht₂
    rw [hrEq, hphiEq, hmEq, hnuEq, hbetaEq]
    refine ⟨hr.congr' ?_, hphi.congr' ?_, hm.congr' ?_,
      hnu.congr' ?_, hbeta.congr' ?_⟩
    · exact heq.mono (fun _ h => h.1.symm)
    · exact heq.mono (fun _ h => h.2.1.symm)
    · exact heq.mono (fun _ h => h.2.2.1.symm)
    · exact heq.mono (fun _ h => h.2.2.2.1.symm)
    · exact heq.mono (fun _ h => h.2.2.2.2.symm)

/-- The outgoing densities of the source containing the upper incoming
endpoint converge to their canonical left-trace values at every point of the
mixed segment. -/
theorem first_source_lam_alpha_tendsto_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b s : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁)
    (hs : s ∈ Icc a b) :
    Tendsto (S₁.lam s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).lam s v)) ∧
    Tendsto (S₁.alpha s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).alpha s v)) := by
  have htop : (s, v) ∈ U₁ ∪ U₂ := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hs0 : 0 ≤ s := by
    rcases htop with ht₁ | ht₂
    · exact (h₁.solution.development.wedge ht₁).1
    · exact (h₂.solution.development.wedge ht₂).1
  have hsv : s < v := by
    rcases htop with ht₁ | ht₂
    · exact (h₁.solution.development.wedge ht₁).2
    · exact (h₂.solution.development.wedge ht₂).2
  have hnear : Ioo s v ⊆ {t | (s, t) ∈ U₁} := by
    intro t ht
    exact h₁.solution.development.past_mem hb hs0 hs.2 ht.1 ht.2
  have hLamBV : BoundedVariationOn (S₁.lam s) {t | (s, t) ∈ U₁} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₁.item1.choose_spec.1 s)
  obtain ⟨L, hL⟩ :=
    exists_left_trace_of_bv_punctured_slice hsv hLamBV hnear
  obtain ⟨A, hA⟩ :=
    exists_left_trace_of_bv_punctured_slice hsv
      (source_alpha_bv_on_slice h₁ s) hnear
  have htraces := common_lam_alpha_on_incoming_segment_of_first_top
    h₁ h₂ hdata hab hseg hb s hs
  change Tendsto (S₁.lam s) (𝓝[<] v)
      (𝓝 (commonLam U₁ S₁ S₂ s v)) ∧
    Tendsto (S₁.alpha s) (𝓝[<] v)
      (𝓝 (commonAlpha U₁ S₁ S₂ s v))
  rw [htraces.1, htraces.2]
  exact ⟨by rwa [leftLim_eq_of_tendsto hL],
    by rwa [leftLim_eq_of_tendsto hA]⟩

end ChristodoulouBV.Uniqueness

end
