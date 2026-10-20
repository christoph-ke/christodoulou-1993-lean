module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesIncoming
public import ChristodoulouBV.BVSolution.CoefficientClosure

/-!
# Incoming mass gap control near a terminal segment

The signed quotient equation makes `λ/(1−μ)` nonincreasing in the incoming
coordinate. Its left-endpoint value controls the mass gap on the whole
segment using the global upper and lower bounds for `λ`.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The positive quotient `λ/(1−μ)` is nonincreasing along every complete
incoming segment of a BV solution. -/
theorem incoming_lam_quotient_le_left
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b s : ℝ} (_hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) (hs : s ∈ Icc a b) :
    S.lam s v / (1 - IsBVSolution.mu S s v) ≤
      S.lam a v / (1 - IsBVSolution.mu S a v) := by
  have hsub : inSeg v a s ⊆ U := by
    intro p hp
    have hmem : p.1 ∈ Icc a s ∧ p.2 = v := by
      simpa [inSeg] using hp
    apply hseg
    change p.1 ∈ Icc a b ∧ p.2 = v
    exact ⟨⟨hmem.1.1, hmem.1.2.trans hs.2⟩, hmem.2⟩
  have htrans := h.quotient_transport_in hs.1 (hs.2.trans_lt hbv) hsub
  let q : ℝ → ℝ := fun x => S.lam x v / (1 - IsBVSolution.mu S x v)
  have hnonpos : ∀ᵐ x ∂volume, x ∈ Icc a s → deriv q x ≤ 0 := by
    filter_upwards [htrans.2] with x hx hxs
    have hxU : (x, v) ∈ U := hsub (by
      change x ∈ Icc a s ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hxs, rfl⟩)
    have hr : 0 < S.r x v := h.solution.radius_pos (x, v) hxU
    obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
    have hn : S.nu x v < 0 :=
      (h.nu_le_neg_lower hc hlam hxU).trans_lt (neg_lt_zero.mpr hc)
    have hg : 0 < 1 - IsBVSolution.mu S x v := by
      have hm := (h.mass_ratio_bounds hxU).2
      dsimp [IsBVSolution.mu]
      linarith
    have hq : 0 ≤ q x := div_nonneg
      (h.solution.lam_pos (x, v) hxU).le hg.le
    have hcoeff : S.zeta x v ^ 2 / (S.r x v * S.nu x v) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (mul_nonpos_of_nonneg_of_nonpos hr.le hn.le)
    rw [hx hxs]
    exact mul_nonpos_of_nonpos_of_nonneg hcoeff hq
  have hle : (∫ x in a..s, deriv q x) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hs.1]
    apply integral_nonpos_of_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hnonpos] with x hx hmem
    exact hx ⟨hmem.1.le, hmem.2⟩
  have heq : (∫ x in a..s, deriv q x) = q s - q a :=
    htrans.1.integral_deriv_eq_sub
  dsimp [q] at heq ⊢
  linarith only [hle, heq]

/-- A positive mass gap at the left endpoint controls the gap everywhere on
the same incoming segment. The constants are the global expansion bounds of
the source solution. -/
theorem incoming_mass_gap_ge_left
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b s c K : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) (hs : s ∈ Icc a b)
    (_hc : 0 < c) (hlow : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hupper : ∀ p ∈ U, S.lam p.1 p.2 ≤ K) :
    c * (1 - IsBVSolution.mu S a v) ≤
      K * (1 - IsBVSolution.mu S s v) := by
  have haU : (a, v) ∈ U := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have hsU : (s, v) ∈ U := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hga : 0 < 1 - IsBVSolution.mu S a v := by
    have hm := (h.mass_ratio_bounds haU).2
    dsimp [IsBVSolution.mu]
    linarith
  have hgs : 0 < 1 - IsBVSolution.mu S s v := by
    have hm := (h.mass_ratio_bounds hsU).2
    dsimp [IsBVSolution.mu]
    linarith
  have hquot := incoming_lam_quotient_le_left h hab hbv hseg hs
  have hcross : S.lam s v * (1 - IsBVSolution.mu S a v) ≤
      S.lam a v * (1 - IsBVSolution.mu S s v) :=
    (div_le_div_iff₀ hgs hga).mp hquot
  calc
    c * (1 - IsBVSolution.mu S a v) ≤
        S.lam s v * (1 - IsBVSolution.mu S a v) :=
      mul_le_mul_of_nonneg_right (hlow (s, v) hsU) hga.le
    _ ≤ S.lam a v * (1 - IsBVSolution.mu S s v) := hcross
    _ ≤ K * (1 - IsBVSolution.mu S s v) :=
      mul_le_mul_of_nonneg_right (hupper (a, v) haU) hgs.le

/-- At a source top point, the mass gap has its expected outgoing left
limit. This also applies when the top is absent from the other source. -/
theorem source_mass_gap_tendsto_top
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun t => 1 - IsBVSolution.mu S u t) (𝓝[<] v)
      (𝓝 (1 - IsBVSolution.mu S u v)) := by
  have huv' := (h.solution.development.wedge huv).2
  let t₀ := (u + v) / 2
  have hut₀ : u < t₀ := by dsimp [t₀]; linarith only [huv']
  have ht₀v : t₀ < v := by dsimp [t₀]; linarith only [huv']
  have hAC := h.mass_div_radius_ac_out huv hut₀ ht₀v.le le_rfl
  have hcont : ContinuousOn (fun t => S.m u t / S.r u t) (Icc t₀ v) := by
    simpa only [uIcc_of_le ht₀v.le] using hAC.continuousOn
  have hleft : Tendsto (fun t : ℝ => t) (𝓝[<] v) (𝓝[Icc t₀ v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT ht₀v)
        (fun t ht => ⟨ht.1.le, ht.2.le⟩)⟩
  have hratio : Tendsto (fun t => S.m u t / S.r u t) (𝓝[<] v)
      (𝓝 (S.m u v / S.r u v)) :=
    (hcont.continuousWithinAt
      (show v ∈ Icc t₀ v from ⟨ht₀v.le, le_rfl⟩)).tendsto.comp hleft
  have hfun : (fun t => 1 - IsBVSolution.mu S u t) =
      (fun t => 1 - (2 : ℝ) * (S.m u t / S.r u t)) := by
    funext t
    dsimp [IsBVSolution.mu]
    ring
  have hval : 1 - IsBVSolution.mu S u v =
      1 - (2 : ℝ) * (S.m u v / S.r u v) := by
    dsimp [IsBVSolution.mu]
    ring
  rw [hfun, hval]
  exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hratio)

/-- The mass gap of the source containing the upper incoming endpoint stays
uniformly positive on the whole compact segment as the outgoing level rises
to the mixed terminal edge. -/
theorem first_source_mass_gap_uniform_below_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    ∃ d : ℝ, 0 < d ∧
      ∀ᶠ t in 𝓝[<] v,
        b < t ∧ ∀ s ∈ Icc a b,
          d ≤ 1 - IsBVSolution.mu S₁ s t := by
  have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have ha0 : 0 ≤ a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  obtain ⟨c, hc, hlow⟩ := h₁.lam_bounded_below
  obtain ⟨K, hupper, _⟩ := h₁.exists_uniform_radius_upper
  have hK : 0 < K := by
    have hc' := hlow (b, v) hb
    have hK' := hupper (b, v) hb
    linarith
  have hleft : ∃ g : ℝ, 0 < g ∧
      ∀ᶠ t in 𝓝[<] v,
        b < t ∧ g ≤ 1 - IsBVSolution.mu S₁ a t := by
    rcases ha with ha₁ | ha₂
    · let g := (1 - IsBVSolution.mu S₁ a v) / 2
      have hg : 0 < g := by
        have hm := (h₁.mass_ratio_bounds ha₁).2
        dsimp [g, IsBVSolution.mu]
        linarith
      have hlim := source_mass_gap_tendsto_top h₁ ha₁
      have hhalf : g < 1 - IsBVSolution.mu S₁ a v := by
        dsimp [g] at hg ⊢
        linarith
      have hev : ∀ᶠ t in 𝓝[<] v,
          g < 1 - IsBVSolution.mu S₁ a t :=
        hlim.eventually (eventually_gt_nhds hhalf)
      refine ⟨g, hg, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hbv, hev] with t ht hgt
      exact ⟨ht.1, hgt.le⟩
    · let g := (1 - IsBVSolution.mu S₂ a v) / 2
      have hg : 0 < g := by
        have hm := (h₂.mass_ratio_bounds ha₂).2
        dsimp [g, IsBVSolution.mu]
        linarith
      have hlim := source_mass_gap_tendsto_top h₂ ha₂
      have hhalf : g < 1 - IsBVSolution.mu S₂ a v := by
        dsimp [g] at hg ⊢
        linarith
      have hev : ∀ᶠ t in 𝓝[<] v,
          g < 1 - IsBVSolution.mu S₂ a t :=
        hlim.eventually (eventually_gt_nhds hhalf)
      refine ⟨g, hg, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hbv, hev] with t ht hgt
      have hat : a < t := hab.trans_lt ht.1
      have ht₁ : (a, t) ∈ U₁ :=
        h₁.solution.development.past_mem hb ha0 hab hat ht.2
      have ht₂ : (a, t) ∈ U₂ :=
        h₂.solution.development.outgoing_mem ha₂ hat ht.2.le
      obtain ⟨hr, _, hm⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata
        (a, t) ⟨ht₁, ht₂⟩
      have hgapEq : 1 - IsBVSolution.mu S₁ a t =
          1 - IsBVSolution.mu S₂ a t := by
        simp only [IsBVSolution.mu, hr, hm]
      exact ⟨ht.1, by rw [hgapEq]; exact hgt.le⟩
  obtain ⟨g, hg, hgev⟩ := hleft
  refine ⟨c * g / K, div_pos (mul_pos hc hg) hK, ?_⟩
  filter_upwards [hgev, Ioo_mem_nhdsLT hbv] with t ht htv
  have hstrip : inSeg t a b ⊆ U₁ :=
    h₁.solution.development.in_seg_subset hb ha0 hab le_rfl ht.1 htv.2
  refine ⟨ht.1, ?_⟩
  intro s hs
  have hbound := incoming_mass_gap_ge_left h₁ hab ht.1 hstrip hs hc hlow hupper
  apply (div_le_iff₀ hK).2
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left ht.2 hc.le).trans hbound

/-- The same uniform gap estimate when the second source contains the upper
incoming endpoint. -/
theorem second_source_mass_gap_uniform_below_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₂) :
    ∃ d : ℝ, 0 < d ∧
      ∀ᶠ t in 𝓝[<] v,
        b < t ∧ ∀ s ∈ Icc a b,
          d ≤ 1 - IsBVSolution.mu S₂ s t := by
  have hdata' : ∀ w, (0, w) ∈ U₂ ∩ U₁ →
      S₂.r 0 w = S₁.r 0 w ∧ S₂.phi 0 w = S₁.phi 0 w := by
    intro w hw
    obtain ⟨hr, hphi⟩ := hdata w ⟨hw.2, hw.1⟩
    exact ⟨hr.symm, hphi.symm⟩
  have hseg' : inSeg v a b ⊆ U₂ ∪ U₁ := by
    intro p hp
    exact (hseg hp).symm
  exact first_source_mass_gap_uniform_below_top h₂ h₁ hdata' hab hseg' hb

end ChristodoulouBV.Uniqueness

end
