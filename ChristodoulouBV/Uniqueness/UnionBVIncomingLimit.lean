module

public import ChristodoulouBV.Uniqueness.UnionEquations
public import ChristodoulouBV.ForMathlib.BoundedVariation.PointwiseLimit

/-!
# Pointwise limits on terminal incoming slices

The source containing the largest selected incoming point controls all
smaller selected points from levels strictly below the terminal level.
No interval of terminal points is assumed to lie in either source.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Below a terminal point of the first source, every selected point has
the same five field limits as that source. -/
theorem first_source_fields_tendsto_incoming_terminal
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v b s : ℝ} (hb : (b, v) ∈ U₁) (hs : (s, v) ∈ U₁ ∪ U₂)
    (hsb : s ≤ b) :
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
  rcases hs with ht₁ | ht₂
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
        h₁.solution.development.past_mem hb hs0 hsb ht.1 ht.2
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

/-- The same terminal control applies to the canonical outgoing densities. -/
theorem first_source_lam_alpha_tendsto_incoming_terminal
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v b s : ℝ} (hb : (b, v) ∈ U₁) (hs : (s, v) ∈ U₁ ∪ U₂)
    (hsb : s ≤ b) :
    Tendsto (S₁.lam s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).lam s v)) ∧
    Tendsto (S₁.alpha s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).alpha s v)) := by
  have hs0 : 0 ≤ s := by
    rcases hs with ht₁ | ht₂
    · exact (h₁.solution.development.wedge ht₁).1
    · exact (h₂.solution.development.wedge ht₂).1
  have hsv : s < v := by
    rcases hs with ht₁ | ht₂
    · exact (h₁.solution.development.wedge ht₁).2
    · exact (h₂.solution.development.wedge ht₂).2
  have hnear : Ioo s v ⊆ {t | (s, t) ∈ U₁} := by
    intro t ht
    exact h₁.solution.development.past_mem hb hs0 hsb ht.1 ht.2
  have hLamBV : BoundedVariationOn (S₁.lam s) {t | (s, t) ∈ U₁} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₁.item1.choose_spec.1 s)
  obtain ⟨L, hL⟩ :=
    exists_left_trace_of_bv_punctured_slice hsv hLamBV hnear
  obtain ⟨A, hA⟩ :=
    exists_left_trace_of_bv_punctured_slice hsv
      (source_alpha_bv_on_slice h₁ s) hnear
  have htraces :
      commonLam U₁ S₁ S₂ s v = (S₁.lam s).leftLim v ∧
      commonAlpha U₁ S₁ S₂ s v = (S₁.alpha s).leftLim v := by
    by_cases ht₁ : (s, v) ∈ U₁
    · exact common_lam_alpha_eq_first ht₁
    · have ht₂ : (s, v) ∈ U₂ := hs.resolve_left ht₁
      have hcommon : ∀ t ∈ Ioo s v, (s, t) ∈ U₁ ∩ U₂ := by
        intro t ht
        exact ⟨hnear ht,
          h₂.solution.development.outgoing_mem ht₂ ht.1 ht.2.le⟩
      obtain ⟨hLam, hAlpha⟩ :=
        source_lam_alpha_leftLim_eq_of_punctured_overlap
          h₁ h₂ hdata hsv hcommon
      classical
      simp only [commonLam, commonAlpha, ht₁, ↓reduceIte]
      exact ⟨hLam.symm, hAlpha.symm⟩
  change Tendsto (S₁.lam s) (𝓝[<] v)
      (𝓝 (commonLam U₁ S₁ S₂ s v)) ∧
    Tendsto (S₁.alpha s) (𝓝[<] v)
      (𝓝 (commonAlpha U₁ S₁ S₂ s v))
  rw [htraces.1, htraces.2]
  exact ⟨by rwa [leftLim_eq_of_tendsto hL],
    by rwa [leftLim_eq_of_tendsto hA]⟩

/-- The second source also controls selected values below its terminal
incoming point. -/
theorem second_source_fields_tendsto_incoming_terminal
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v b s : ℝ} (hb : (b, v) ∈ U₂) (hs : (s, v) ∈ U₁ ∪ U₂)
    (hsb : s ≤ b) :
    Tendsto (S₂.r s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).r s v)) ∧
    Tendsto (S₂.phi s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).phi s v)) ∧
    Tendsto (S₂.m s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).m s v)) ∧
    Tendsto (S₂.nu s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).nu s v)) ∧
    Tendsto (S₂.beta s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).beta s v)) := by
  have h := first_source_fields_tendsto_incoming_terminal h₂ h₁
    (swapped_initial_agreement hdata) hb hs.symm hsb
  obtain ⟨hr, hphi, hm, _, hnu, _, hbeta⟩ :=
    gluedFields_swap_eq_on_union h₁ h₂ hdata hs
  rwa [hr, hphi, hm, hnu, hbeta] at h

/-- The selected outgoing densities have the analogous second-source
terminal limits. -/
theorem second_source_lam_alpha_tendsto_incoming_terminal
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v b s : ℝ} (hb : (b, v) ∈ U₂) (hs : (s, v) ∈ U₁ ∪ U₂)
    (hsb : s ≤ b) :
    Tendsto (S₂.lam s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).lam s v)) ∧
    Tendsto (S₂.alpha s) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).alpha s v)) := by
  have h := first_source_lam_alpha_tendsto_incoming_terminal h₂ h₁
    (swapped_initial_agreement hdata) hb hs.symm hsb
  obtain ⟨_, _, _, hlam, _, halpha, _⟩ :=
    gluedFields_swap_eq_on_union h₁ h₂ hdata hs
  rwa [hlam, halpha] at h

/-- The incoming scalar amplitudes converge to the selected value from
either source containing a higher terminal point. -/
theorem source_zeta_tendsto_incoming_terminal
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v b s : ℝ} (hs : (s, v) ∈ U₁ ∪ U₂) (hsb : s ≤ b) :
    ((b, v) ∈ U₁ → Tendsto (fun t => S₁.zeta s t) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).zeta s v))) ∧
    ((b, v) ∈ U₂ → Tendsto (fun t => S₂.zeta s t) (𝓝[<] v)
      (𝓝 ((gluedFields U₁ S₁ S₂).zeta s v))) := by
  constructor
  · intro hb
    obtain ⟨_, hphi, _, hnu, hbeta⟩ :=
      first_source_fields_tendsto_incoming_terminal h₁ h₂ hdata hb hs hsb
    simpa only [Fields.zeta] using hbeta.sub (hnu.mul hphi)
  · intro hb
    obtain ⟨_, hphi, _, hnu, hbeta⟩ :=
      second_source_fields_tendsto_incoming_terminal h₁ h₂ hdata hb hs hsb
    simpa only [Fields.zeta] using hbeta.sub (hnu.mul hphi)

end ChristodoulouBV.Uniqueness

end
