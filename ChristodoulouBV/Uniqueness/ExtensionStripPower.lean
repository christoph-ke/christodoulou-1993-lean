module

public import ChristodoulouBV.Uniqueness.ExtensionStripIntegrals
import ChristodoulouBV.C1Solution.ExtractionMass

/-!
# Incoming radius-power integral in the enlarged domain

This is the elementary change of variable behind the factors two in
equations (5.15) and (5.17).
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming radius-power integral is bounded by its terminal value. -/
theorem incoming_radius_power_integral_le_local
    {R N : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hR : ContinuousOn R (Icc a b)) (hN : ContinuousOn N (Icc a b))
    (hRpos : ∀ s ∈ Icc a b, 0 < R s)
    (hD : ∀ s ∈ Icc a b, HasDerivAt R (N s) s) :
    IntervalIntegrable (fun s => (-N s) / R s * (R s)^(-δ)) volume a b ∧
      (∫ s in a..b, (-N s) / R s * (R s)^(-δ)) ≤ (R b)^(-δ) / δ := by
  let F : ℝ → ℝ := fun s => (R s)^(-δ) / δ
  let G : ℝ → ℝ := fun s => (-N s) / R s * (R s)^(-δ)
  have hpow : ContinuousOn (fun s => (R s)^(-δ)) (Icc a b) :=
    hR.rpow_const (fun s hs => Or.inl (ne_of_gt (hRpos s hs)))
  have hG : ContinuousOn G (Icc a b) :=
    (hN.neg.div hR (fun s hs => ne_of_gt (hRpos s hs))).mul hpow
  have hGI : IntervalIntegrable G volume a b :=
    hG.intervalIntegrable_of_Icc hab
  have hderiv : ∀ s ∈ Icc a b, HasDerivAt F (G s) s := by
    intro s hs
    have hspos := hRpos s hs
    have h := (Real.hasDerivAt_rpow_const
      (p := -δ) (Or.inl (ne_of_gt hspos))).comp s (hD s hs)
    have h' := h.div_const δ
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have heq : (-δ * (R s)^(-δ-1) * N s) / δ = G s := by
      dsimp [G]
      rw [show -δ - 1 = -δ + (-1 : ℝ) by ring,
        Real.rpow_add hspos, Real.rpow_neg_one]
      field_simp
    simpa only [F, G, Function.comp_apply, heq] using h'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le hab] using hderiv) hGI
  have hFa : 0 ≤ F a :=
    div_nonneg (Real.rpow_nonneg (hRpos a (left_mem_Icc.mpr hab)).le _) hδ.le
  dsimp [F] at hFa
  change (∫ s in a..b, G s) = F b - F a at hFTC
  constructor
  · exact hGI
  · rw [hFTC]
    dsimp [F]
    linarith only [hFa]

/-- The same integral bound for a segment inside the actual enlarged
working domain, where the radius derivative equals `ν`. -/
theorem incoming_radius_power_integral_le_workingDomain
    {u₁ top : ℝ} {S : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) S)
    {u₀ u v δ : ℝ} (hu₀ : 0 < u₀) (hu₀u : u₀ ≤ u) (hδ : 0 < δ)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ extensionWorkingDomain u₁ top) :
    IntervalIntegrable
      (fun s => (-S.nu s v) / S.r s v * (S.r s v)^(-δ)) volume u₀ u ∧
    (∫ s in u₀..u, (-S.nu s v) / S.r s v * (S.r s v)^(-δ)) ≤
      (S.r u v)^(-δ) / δ := by
  have hr : ContinuousOn (fun s => S.r s v) (Icc u₀ u) := by
    refine intervalPrimitive_continuousOn_of_subintervals
      (g := fun s => S.nu s v) hu₀u ?_
    intro t ht
    apply H.solution.radius_in v u₀ t ht.1
    intro p hp
    rcases p with ⟨x, y⟩
    obtain ⟨hx, rfl⟩ : x ∈ Icc u₀ t ∧ y = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
    exact hseg x ⟨hx.1, hx.2.trans ht.2⟩
  have hnu : ContinuousOn (fun s => S.nu s v) (Icc u₀ u) :=
    H.nu_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => subset_closure (hseg s hs))
  exact incoming_radius_power_integral_le_local hu₀u hδ hr hnu
    (fun s hs => H.solution.radius_pos (s, v) (hseg s hs))
    (fun s hs => radius_hasDerivAt_u_of_c1_interior H
      (extensionWorkingDomain_mem_interior
        (hu₀.trans_le hs.1) (hseg s hs).2.1
        (hseg s hs).2.2.1 (hseg s hs).2.2.2))

end ChristodoulouBV.Uniqueness

end
