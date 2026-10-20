module

public import ChristodoulouBV.Uniqueness.UnionBVIncoming
public import ChristodoulouBV.ForMathlib.BoundedVariation.FiniteGlue

/-!
# Outgoing variation of the selected fields

Every finite ordered set on an outgoing union slice lies in the source
containing its largest point. The left-trace convention costs no variation.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- A full outgoing source slice inherits a variation bound from all its
included initial intervals. -/
theorem outgoing_variation_le_of_initial_intervals
    {U : Set (ℝ × ℝ)} {f : ℝ → ℝ} {u : ℝ} {C : ℝ≥0∞}
    (hdev : IsDomainOfDevelopment U)
    (hbound : ∀ v, (u, v) ∈ U → eVariationOn f (Ioc u v) ≤ C) :
    eVariationOn f {v | (u, v) ∈ U} ≤ C := by
  apply iSup_le
  rintro ⟨n, ⟨w, hw, hws⟩⟩
  have hmem (i : ℕ) (hi : i ≤ n) : w i ∈ Ioc u (w n) :=
    ⟨(hdev.wedge (hws i)).2, hw hi⟩
  exact (eVariationOn.sum_le_of_monotoneOn_Iic
    (hw.monotoneOn _) hmem).trans (hbound (w n) (hws n))

/-- The left trace of the radius density has the original uniform outgoing
variation bound on every complete source slice. -/
theorem source_lam_leftLim_variation_full_le
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (u : ℝ) :
    eVariationOn (S.lam u).leftLim {v | (u, v) ∈ U} ≤
      eVariationOn (S.lam u) {v | (u, v) ∈ U} := by
  exact outgoing_variation_le_of_initial_intervals h.solution.development
    (fun v hv => source_lam_leftLim_variation_outgoing_le h hv)

/-- The same full-slice estimate holds for the scalar amplitude's left
trace. -/
theorem source_theta_leftLim_variation_full_le
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (u : ℝ) :
    eVariationOn (S.theta u).leftLim {v | (u, v) ∈ U} ≤
      eVariationOn (S.theta u) {v | (u, v) ∈ U} := by
  exact outgoing_variation_le_of_initial_intervals h.solution.development
    (fun v hv => source_theta_leftLim_variation_outgoing_le h hv)

/-- At a source point, its canonical scalar amplitude is the left trace
of the source scalar amplitude. -/
theorem glued_theta_eq_first_leftLim
    {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁)
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    (gluedFields U₁ S₁ S₂).theta u v = (S₁.theta u).leftLim v := by
  have huv : u < v := (h₁.solution.development.wedge hp).2
  have hslice : Ioc u v ⊆ {t | (u, t) ∈ U₁} :=
    fun t ht => h₁.solution.development.outgoing_mem hp ht.1 ht.2
  have hLamFull : BoundedVariationOn (S₁.lam u) {t | (u, t) ∈ U₁} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₁.item1.choose_spec.1 u)
  have hLamBV : BoundedVariationOn (S₁.lam u) (Ioc u v) :=
    hLamFull.mono hslice
  have hAlphaBV : BoundedVariationOn (S₁.alpha u) (Ioc u v) :=
    (source_alpha_bv_on_slice h₁ u).mono hslice
  have hL := leftLim_tendsto_of_bv_Ioc huv hLamBV
  have hA := leftLim_tendsto_of_bv_Ioc huv hAlphaBV
  have hPhi := (source_fields_tendsto_outgoing_top h₁ hp).2.1
  have hTheta : Tendsto (S₁.theta u) (𝓝[<] v)
      (𝓝 ((S₁.alpha u).leftLim v -
        (S₁.lam u).leftLim v * S₁.phi u v)) := by
    change Tendsto (fun t => S₁.alpha u t - S₁.lam u t * S₁.phi u t)
      (𝓝[<] v) _
    exact hA.sub (hL.mul hPhi)
  have hEq := leftLim_eq_of_tendsto hTheta
  obtain ⟨_, hPhiEq, _, _, _⟩ := gluedFields_eq_first hp
  obtain ⟨hLamEq, hAlphaEq⟩ := gluedFields_lam_alpha_eq_first hp
  change (gluedFields U₁ S₁ S₂).alpha u v -
    (gluedFields U₁ S₁ S₂).lam u v *
      (gluedFields U₁ S₁ S₂).phi u v = _
  rw [hAlphaEq, hLamEq, hPhiEq]
  exact hEq.symm

/-- The analogous selected amplitude agrees with the second source's left
trace on that source. -/
theorem glued_theta_eq_second_leftLim
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    (gluedFields U₁ S₁ S₂).theta u v = (S₂.theta u).leftLim v := by
  have hswap := glued_theta_eq_first_leftLim (S₂ := S₁) h₂ hp
  have heq := gluedFields_swap_eq_on_union h₁ h₂ hdata (Or.inr hp)
  obtain ⟨_, hPhiEq, _, hLamEq, _, hAlphaEq, _⟩ := heq
  change (gluedFields U₁ S₁ S₂).alpha u v -
    (gluedFields U₁ S₁ S₂).lam u v *
      (gluedFields U₁ S₁ S₂).phi u v = _
  rw [← hPhiEq, ← hLamEq, ← hAlphaEq]
  exact hswap

/-- The three outgoing BV quantities have one global bound each on the
union. -/
theorem glued_outgoing_variation_bounds
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (u : ℝ) :
    eVariationOn ((gluedFields U₁ S₁ S₂).lam u)
      {v | (u, v) ∈ U₁ ∪ U₂} ≤
      max (ENNReal.ofReal h₁.item1.choose) (ENNReal.ofReal h₂.item1.choose) ∧
    eVariationOn ((gluedFields U₁ S₁ S₂).phi u)
      {v | (u, v) ∈ U₁ ∪ U₂} ≤
      max (ENNReal.ofReal h₁.item3_variation.choose)
        (ENNReal.ofReal h₂.item3_variation.choose) ∧
    eVariationOn ((gluedFields U₁ S₁ S₂).theta u)
      {v | (u, v) ∈ U₁ ∪ U₂} ≤
      max (ENNReal.ofReal h₁.item5.choose) (ENNReal.ofReal h₂.item5.choose) := by
  have hselect {F F₁ F₂ : ℝ → ℝ → ℝ}
      (heq₁ : ∀ v, (u, v) ∈ U₁ → F u v = F₁ u v)
      (heq₂ : ∀ v, (u, v) ∈ U₂ → F u v = F₂ u v) :
      eVariationOn (F u) {v | (u, v) ∈ U₁ ∪ U₂} ≤
        max (eVariationOn (F₁ u) {v | (u, v) ∈ U₁})
          (eVariationOn (F₂ u) {v | (u, v) ∈ U₂}) := by
    apply eVariationOn.le_max_of_finite_partition_source
    intro n w hw hws
    have htop : (u, w n) ∈ U₁ ∪ U₂ := hws n
    rcases htop with ht₁ | ht₂
    · left
      intro i hi
      have hmem : (u, w i) ∈ U₁ := by
        have hlt : u < w i := by
          rcases hws i with h | h
          · exact (h₁.solution.development.wedge h).2
          · exact (h₂.solution.development.wedge h).2
        exact h₁.solution.development.outgoing_mem ht₁ hlt (hw hi)
      exact ⟨hmem, heq₁ (w i) hmem⟩
    · right
      intro i hi
      have hmem : (u, w i) ∈ U₂ := by
        have hlt : u < w i := by
          rcases hws i with h | h
          · exact (h₁.solution.development.wedge h).2
          · exact (h₂.solution.development.wedge h).2
        exact h₂.solution.development.outgoing_mem ht₂ hlt (hw hi)
      exact ⟨hmem, heq₂ (w i) hmem⟩
  refine ⟨?_, ?_, ?_⟩
  · have hglue := hselect
        (F := fun x y => (gluedFields U₁ S₁ S₂).lam x y)
        (F₁ := fun x y => (S₁.lam x).leftLim y)
        (F₂ := fun x y => (S₂.lam x).leftLim y)
        (fun v hp => (gluedFields_lam_alpha_eq_first (S₂ := S₂) hp).1)
        (fun v hp => (gluedFields_lam_alpha_eq_second h₁ h₂ hdata hp).1)
    exact hglue.trans (max_le_max
      ((source_lam_leftLim_variation_full_le h₁ u).trans
        (h₁.item1.choose_spec.1 u))
      ((source_lam_leftLim_variation_full_le h₂ u).trans
        (h₂.item1.choose_spec.1 u)))
  · have hglue := hselect
        (F := fun x y => (gluedFields U₁ S₁ S₂).phi x y)
        (F₁ := S₁.phi) (F₂ := S₂.phi)
        (fun v hp => (gluedFields_eq_first (S₂ := S₂) hp).2.1)
        (fun v hp => (gluedFields_eq_second h₁ h₂ hdata hp).2.1)
    exact hglue.trans (max_le_max
      (h₁.item3_variation.choose_spec.1 u)
      (h₂.item3_variation.choose_spec.1 u))
  · have hglue := hselect
        (F := fun x y => (gluedFields U₁ S₁ S₂).theta x y)
        (F₁ := fun x y => (S₁.theta x).leftLim y)
        (F₂ := fun x y => (S₂.theta x).leftLim y)
        (fun v hp => glued_theta_eq_first_leftLim h₁ hp)
        (fun v hp => glued_theta_eq_second_leftLim h₁ h₂ hdata hp)
    exact hglue.trans (max_le_max
      ((source_theta_leftLim_variation_full_le h₁ u).trans
        (h₁.item5.choose_spec.1 u))
      ((source_theta_leftLim_variation_full_le h₂ u).trans
        (h₂.item5.choose_spec.1 u)))

end ChristodoulouBV.Uniqueness

end
