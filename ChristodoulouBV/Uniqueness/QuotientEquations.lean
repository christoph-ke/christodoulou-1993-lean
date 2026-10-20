module

public import ChristodoulouBV.Uniqueness.QuotientMassAbsorption
public import ChristodoulouBV.BVSolution.PrimitiveCalculus

/-!
# A.e. scalar quotient equations

The frozen mixed primitives and the absolutely continuous quotient rule give
the incoming `α/λ` and outgoing `β/ν` transport equations on compact
off-axis characteristic segments.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace ChristodoulouBV.IsBVSolution

/-- Incoming transport of the outgoing scalar quotient. The displayed form
retains the frozen mixed coefficient; replacing it by its mass-ratio formula
is a pointwise algebra step. -/
theorem alpha_div_lam_transport_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (_hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval
        (fun s => S.alpha s v / S.lam s v) a b ∧
      ∀ᵐ s ∂volume, s ∈ Icc a b →
        deriv (fun t => S.alpha t v / S.lam t v) s =
          -radiusCoeff S s v * S.theta s v / S.lam s v ^ 2 := by
  have hα := h.solution.alpha_in_ac_ae hab hseg
  have hLam := h.solution.lam_in_ac_ae hab hseg
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hbound : ∀ s ∈ uIcc a b, c ≤ |S.lam s v| := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsU : (s, v) ∈ U := hseg ⟨hs, rfl⟩
    have hpos := h.solution.lam_pos (s, v) hsU
    rw [abs_of_pos hpos]
    exact hlam (s, v) hsU
  have hq := hα.1.div_and_ae_deriv hLam.1 hc hbound
  refine ⟨hq.1, ?_⟩
  filter_upwards [hq.2, hα.2, hLam.2] with s hqs hαs hLams hs
  rw [uIcc_of_le hab] at hqs
  rw [hqs hs, hαs hs, hLams hs]
  dsimp [Fields.theta]
  ring

/-- Outgoing transport of the incoming scalar quotient. The BV sign bridge
keeps `ν` uniformly separated from zero on the segment. -/
theorem beta_div_nu_transport_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u a b : ℝ} (hab : a ≤ b) (_hua : u < a)
    (hseg : outSeg u a b ⊆ U) :
    AbsolutelyContinuousOnInterval
        (fun t => S.beta u t / S.nu u t) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => S.beta u s / S.nu u s) t =
          -radiusCoeff S u t * S.zeta u t / S.nu u t ^ 2 := by
  have hβ := h.solution.beta_out_ac_ae hab hseg
  have hNu := h.solution.nu_out_ac_ae hab hseg
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hbound : ∀ t ∈ uIcc a b, c ≤ |S.nu u t| := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htU : (u, t) ∈ U := hseg ⟨rfl, ht⟩
    have hneg := h.nu_le_neg_lower hc hlam htU
    rw [abs_of_neg (hneg.trans_lt (neg_lt_zero.mpr hc))]
    linarith
  have hq := hβ.1.div_and_ae_deriv hNu.1 hc hbound
  refine ⟨hq.1, ?_⟩
  filter_upwards [hq.2, hβ.2, hNu.2] with t hqt hβt hNut ht
  rw [uIcc_of_le hab] at hqt
  rw [hqt ht, hβt ht, hNut ht]
  dsimp [Fields.zeta]
  ring

end ChristodoulouBV.IsBVSolution

namespace ChristodoulouBV.Uniqueness

/-- A.e. incoming equation for the difference of `α/λ` on a compact
comparison segment. Both quotients are absolutely continuous there. -/
theorem ComparisonData.alpha_ratio_difference_ae (D : ComparisonData)
    {v a b : ℝ} (hav : D.a ≤ a) (hab : a ≤ b)
    (hbv : b < v) (hvb : v < D.b) :
    AbsolutelyContinuousOnInterval
      (fun s => D.S₁.alpha s v / D.S₁.lam s v -
        D.S₂.alpha s v / D.S₂.lam s v) a b ∧
      ∀ᵐ s ∂volume, s ∈ Icc a b →
        deriv (fun t => D.S₁.alpha t v / D.S₁.lam t v -
          D.S₂.alpha t v / D.S₂.lam t v) s =
          -IsBVSolution.radiusCoeff D.S₁ s v * D.S₁.theta s v /
              D.S₁.lam s v ^ 2 +
            IsBVSolution.radiusCoeff D.S₂ s v * D.S₂.theta s v /
              D.S₂.lam s v ^ 2 := by
  have hseg : inSeg v a b ⊆ D.U₁ ∩ D.U₂ := by
    intro p hp
    change p.1 ∈ Icc a b ∧ p.2 ∈ ({v} : Set ℝ) at hp
    obtain ⟨hpa, hpv⟩ := hp
    have hpt : (p.1, p.2) ∈ triangle D.a D.b := by
      rw [show p.2 = v from hpv]
      exact (mem_triangle).2 ⟨hav.trans hpa.1, hpa.2.trans_lt hbv, hvb⟩
    exact D.hT hpt
  have h₁ := D.h₁.alpha_div_lam_transport_in hab hbv
    (fun p hp => (hseg hp).1)
  have h₂ := D.h₂.alpha_div_lam_transport_in hab hbv
    (fun p hp => (hseg hp).2)
  constructor
  · exact h₁.1.sub h₂.1
  filter_upwards [h₁.1.ae_differentiableAt, h₂.1.ae_differentiableAt,
    h₁.2, h₂.2] with s hd₁ hd₂ hder₁ hder₂ hs
  have hsI : s ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hs
  change deriv ((fun t => D.S₁.alpha t v / D.S₁.lam t v) -
    (fun t => D.S₂.alpha t v / D.S₂.lam t v)) s = _
  rw [deriv_sub (hd₁ hsI) (hd₂ hsI), hder₁ hs, hder₂ hs]
  ring

/-- A.e. outgoing equation for the difference of `β/ν` on a compact
comparison segment. Both quotients are absolutely continuous there. -/
theorem ComparisonData.beta_ratio_difference_ae (D : ComparisonData)
    {u a b : ℝ} (hau : D.a ≤ u) (hua : u < a)
    (hab : a ≤ b) (hbb : b < D.b) :
    AbsolutelyContinuousOnInterval
      (fun t => D.S₁.beta u t / D.S₁.nu u t -
        D.S₂.beta u t / D.S₂.nu u t) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => D.S₁.beta u s / D.S₁.nu u s -
          D.S₂.beta u s / D.S₂.nu u s) t =
          -IsBVSolution.radiusCoeff D.S₁ u t * D.S₁.zeta u t /
              D.S₁.nu u t ^ 2 +
            IsBVSolution.radiusCoeff D.S₂ u t * D.S₂.zeta u t /
              D.S₂.nu u t ^ 2 := by
  have hseg : outSeg u a b ⊆ D.U₁ ∩ D.U₂ := by
    intro p hp
    change p.1 ∈ ({u} : Set ℝ) ∧ p.2 ∈ Icc a b at hp
    obtain ⟨hpu, hpb⟩ := hp
    have hpt : (p.1, p.2) ∈ triangle D.a D.b := by
      rw [show p.1 = u from hpu]
      exact (mem_triangle).2 ⟨hau, hua.trans_le hpb.1, hpb.2.trans_lt hbb⟩
    exact D.hT hpt
  have h₁ := D.h₁.beta_div_nu_transport_out hab hua
    (fun p hp => (hseg hp).1)
  have h₂ := D.h₂.beta_div_nu_transport_out hab hua
    (fun p hp => (hseg hp).2)
  constructor
  · exact h₁.1.sub h₂.1
  filter_upwards [h₁.1.ae_differentiableAt, h₂.1.ae_differentiableAt,
    h₁.2, h₂.2] with t hd₁ hd₂ hder₁ hder₂ ht
  have htI : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  change deriv ((fun s => D.S₁.beta u s / D.S₁.nu u s) -
    (fun s => D.S₂.beta u s / D.S₂.nu u s)) t = _
  rw [deriv_sub (hd₁ htI) (hd₂ htI), hder₁ ht, hder₂ ht]
  ring

end ChristodoulouBV.Uniqueness

end
