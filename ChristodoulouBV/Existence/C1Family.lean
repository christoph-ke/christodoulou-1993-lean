module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceInitial
public import ChristodoulouBV.C1Solution.UniquenessTheorem
public import ChristodoulouBV.C1Solution.AxisTranslationFrozen
public import ChristodoulouBV.Existence.C1FamilyBootstrap
public import ChristodoulouBV.Existence.C1FamilyExitFinal
public import ChristodoulouBV.AreaEstimates.SmallData
import Mathlib.Tactic

/-!
# Compatible finite C¹ developments

Finite developments with the same radius gauge and prescribed outgoing
scalar data agree in every field on their common development. This is the
compatibility required before taking the maximal existence parameter in
Section 6.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- A finite C¹ development of prescribed characteristic data. The positive
endpoint is part of the predicate, excluding vacuous empty developments. -/
@[expose] def C1InitialDevelopment (alpha₀ : ℝ → ℝ) (b : ℝ) : Prop :=
  0 < b ∧ ∃ S : Fields,
    IsC1Solution (developmentWithInitialEdge b) S ∧
    ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v

/-- The maximal C¹ existence parameter as an extended nonnegative real.
It can equal infinity without an artificial a priori upper cutoff. -/
@[expose] noncomputable def c1MaximalParameter (alpha₀ : ℝ → ℝ) : ℝ≥0∞ :=
  sSup ((fun b : ℝ => ENNReal.ofReal b) ''
    {b : ℝ | C1InitialDevelopment alpha₀ b})

/-- Local C¹ existence makes the set of positive finite developments
nonempty for every C¹ initial datum. -/
theorem exists_c1_initial_development (alpha₀ : ℝ → ℝ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0)) :
    ∃ b : ℝ, C1InitialDevelopment alpha₀ b := by
  obtain ⟨b, hb, S, H, hdata⟩ :=
    C1Solution.exists_local_c1_solution alpha₀ hα
  exact ⟨b, hb, S, H, hdata⟩

/-- A prescribed finite C¹ development restricts to each smaller positive
cutoff with the exact initial data. -/
theorem c1_initial_development_restrict {alpha₀ : ℝ → ℝ}
    {b c : ℝ} (H : C1InitialDevelopment alpha₀ b)
    (hc : 0 < c) (hcb : c ≤ b) :
    C1InitialDevelopment alpha₀ c := by
  obtain ⟨_, S, HS, hdata⟩ := H
  refine ⟨hc, S, C1Solution.isC1Solution_restrict_initialEdge HS hcb, ?_⟩
  intro v hv
  exact hdata v ⟨hv.1, hv.2.trans_le hcb⟩

/-- Every positive cutoff strictly below the maximal parameter carries a
C¹ solution with the prescribed data. -/
theorem c1_development_below_maximal (alpha₀ : ℝ → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hmax : ENNReal.ofReal b < c1MaximalParameter alpha₀) :
    C1InitialDevelopment alpha₀ b := by
  obtain ⟨x, hx, hbx⟩ := (lt_sSup_iff.mp hmax)
  obtain ⟨c, hc, rfl⟩ := hx
  exact c1_initial_development_restrict hc hb
    ((ENNReal.ofReal_lt_ofReal_iff hc.1).mp hbx).le

/-- Two finite C¹ developments with the same prescribed initial `r` and
`alpha` agree in all nine fields, including on the initial edge. This gives full-field compatibility of the finite family. -/
theorem c1_developments_agree {alpha₀ : ℝ → ℝ} {b₁ b₂ : ℝ}
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hdata₁ : ∀ v ∈ Ioo (0 : ℝ) b₁,
      S₁.r 0 v = v / 2 ∧ S₁.alpha 0 v = alpha₀ v)
    (hdata₂ : ∀ v ∈ Ioo (0 : ℝ) b₂,
      S₂.r 0 v = v / 2 ∧ S₂.alpha 0 v = alpha₀ v)
    {u v : ℝ}
    (hp₁ : (u, v) ∈ developmentWithInitialEdge b₁)
    (hp₂ : (u, v) ∈ developmentWithInitialEdge b₂) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v ∧ S₁.theta u v = S₂.theta u v ∧
    S₁.zeta u v = S₂.zeta u v := by
  have hr₁ : ∀ w ∈ Ioo (0 : ℝ) b₁, S₁.r 0 w = w / 2 :=
    fun w hw => (hdata₁ w hw).1
  have hr₂ : ∀ w ∈ Ioo (0 : ℝ) b₂, S₂.r 0 w = w / 2 :=
    fun w hw => (hdata₂ w hw).1
  have hα : ∀ w ∈ Ioo (0 : ℝ) (min b₁ b₂),
      S₁.alpha 0 w = S₂.alpha 0 w := by
    intro w hw
    rw [(hdata₁ w ⟨hw.1, hw.2.trans_le (min_le_left _ _)⟩).2,
      (hdata₂ w ⟨hw.1, hw.2.trans_le (min_le_right _ _)⟩).2]
  have hphi := initial_phi_eq_of_radius_alpha_data H₁ H₂ hr₁ hr₂ hα
  apply C1Solution.c1_solution_unique_on_common_development H₁ H₂
  · intro w hw
    have hw₁ : w ∈ Ioo (0 : ℝ) b₁ := ⟨hw.1.2.1, hw.1.2.2⟩
    have hw₂ : w ∈ Ioo (0 : ℝ) b₂ := ⟨hw.2.2.1, hw.2.2.2⟩
    have hwm : w ∈ Ioo (0 : ℝ) (min b₁ b₂) :=
      ⟨hw₁.1, lt_min hw₁.2 hw₂.2⟩
    exact ⟨(hr₁ w hw₁).trans (hr₂ w hw₂).symm, hphi w hwm⟩
  · exact hp₁
  · exact hp₂

/-- A choice of C¹ fields at every positive finite cutoff below the maximal
existence parameter. Choice is harmless because all such fields agree on
overlaps by `c1_developments_agree`. -/
@[expose] noncomputable def c1FamilyField (alpha₀ : ℝ → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hmax : ENNReal.ofReal b < c1MaximalParameter alpha₀) : Fields :=
  Classical.choose (c1_development_below_maximal alpha₀ hb hmax).2

/-- The selected field at a finite cutoff solves the C¹ equations and
retains both exact initial traces. -/
theorem c1FamilyField_spec (alpha₀ : ℝ → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hmax : ENNReal.ofReal b < c1MaximalParameter alpha₀) :
    IsC1Solution (developmentWithInitialEdge b)
      (c1FamilyField alpha₀ b hb hmax) ∧
    ∀ v ∈ Ioo (0 : ℝ) b,
      (c1FamilyField alpha₀ b hb hmax).r 0 v = v / 2 ∧
      (c1FamilyField alpha₀ b hb hmax).alpha 0 v = alpha₀ v :=
  Classical.choose_spec (c1_development_below_maximal alpha₀ hb hmax).2

/-- Local existence makes the maximal C¹ parameter strictly positive. -/
theorem c1MaximalParameter_pos (alpha₀ : ℝ → ℝ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0)) :
    0 < c1MaximalParameter alpha₀ := by
  obtain ⟨b, hb⟩ := exists_c1_initial_development alpha₀ hα
  have hmem : ENNReal.ofReal b ∈
      (fun c : ℝ => ENNReal.ofReal c) ''
        {c : ℝ | C1InitialDevelopment alpha₀ c} :=
    ⟨b, hb, rfl⟩
  exact (ENNReal.ofReal_pos.mpr hb.1).trans_le (le_sSup hmem)

/-- The maximal-parameter family is compatible in every field on every
common development, including the characteristic initial edge. This supplies the compatible finite family. -/
theorem c1_compatible_family (alpha₀ : ℝ → ℝ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0)) :
    0 < c1MaximalParameter alpha₀ ∧
    (∀ b : ℝ, ∀ hb : 0 < b,
      ∀ hmax : ENNReal.ofReal b < c1MaximalParameter alpha₀,
      IsC1Solution (developmentWithInitialEdge b)
        (c1FamilyField alpha₀ b hb hmax) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (c1FamilyField alpha₀ b hb hmax).r 0 v = v / 2 ∧
        (c1FamilyField alpha₀ b hb hmax).alpha 0 v = alpha₀ v) ∧
    (∀ b₁ b₂ : ℝ, ∀ hb₁ : 0 < b₁, ∀ hb₂ : 0 < b₂,
      ∀ hm₁ : ENNReal.ofReal b₁ < c1MaximalParameter alpha₀,
      ∀ hm₂ : ENNReal.ofReal b₂ < c1MaximalParameter alpha₀,
      ∀ u v : ℝ,
      (u, v) ∈ developmentWithInitialEdge b₁ →
      (u, v) ∈ developmentWithInitialEdge b₂ →
      let S₁ := c1FamilyField alpha₀ b₁ hb₁ hm₁
      let S₂ := c1FamilyField alpha₀ b₂ hb₂ hm₂
      S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
      S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
      S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
      S₁.beta u v = S₂.beta u v ∧ S₁.theta u v = S₂.theta u v ∧
      S₁.zeta u v = S₂.zeta u v) := by
  refine ⟨c1MaximalParameter_pos alpha₀ hα, ?_, ?_⟩
  · intro b hb hmax
    exact c1FamilyField_spec alpha₀ hb hmax
  · intro b₁ b₂ hb₁ hb₂ hm₁ hm₂ u v hp₁ hp₂
    let S₁ := c1FamilyField alpha₀ b₁ hb₁ hm₁
    let S₂ := c1FamilyField alpha₀ b₂ hb₂ hm₂
    have h₁ := c1FamilyField_spec alpha₀ hb₁ hm₁
    have h₂ := c1FamilyField_spec alpha₀ hb₂ hm₂
    exact c1_developments_agree h₁.1 h₂.1 h₁.2 h₂.2 hp₁ hp₂

end ChristodoulouBV

end
