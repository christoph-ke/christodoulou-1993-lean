module

public import ChristodoulouBV.BVSolution.C1InitialCompatibility
public import ChristodoulouBV.Frozen.OpenDevelopment
import ChristodoulouBV.Frozen.Theorem3_1Unique
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Compatibility and tail mass ratio for the extension family

The family in the frozen Theorem 5.1 has common initial radius and scalar-radius
density. Theorem 3.1 and the C¹ reconstruction lemmas identify its members on
their common developments, including the initial edge. The mass-ratio supremum
uses every family member only where that member is defined.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Any two members of the frozen extension family have equal seven fields at
each point of their common development, including the initial edge. This gives the family compatibility used in Theorem 5.1. -/
theorem family_fields_eq_on_common_development
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {S : ℝ → Fields}
    (hfamily : ∀ v₀ ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge v₀) (S v₀) ∧
      (∀ v ∈ Ioo (0 : ℝ) v₀,
        (S v₀).r 0 v = v / 2 ∧ (S v₀).alpha 0 v = alpha₀ v))
    {b₁ b₂ : ℝ} (hb₁ : b₁ ∈ Ioo (0 : ℝ) vStar)
    (hb₂ : b₂ ∈ Ioo (0 : ℝ) vStar)
    {p : ℝ × ℝ}
    (hp : p ∈ developmentWithInitialEdge b₁ ∩
      developmentWithInitialEdge b₂) :
    (S b₁).r p.1 p.2 = (S b₂).r p.1 p.2 ∧
    (S b₁).phi p.1 p.2 = (S b₂).phi p.1 p.2 ∧
    (S b₁).m p.1 p.2 = (S b₂).m p.1 p.2 ∧
    (S b₁).lam p.1 p.2 = (S b₂).lam p.1 p.2 ∧
    (S b₁).nu p.1 p.2 = (S b₂).nu p.1 p.2 ∧
    (S b₁).alpha p.1 p.2 = (S b₂).alpha p.1 p.2 ∧
    (S b₁).beta p.1 p.2 = (S b₂).beta p.1 p.2 := by
  obtain ⟨H₁, hdata₁⟩ := hfamily b₁ hb₁
  obtain ⟨H₂, hdata₂⟩ := hfamily b₂ hb₂
  have hinitial : ∀ v, (0, v) ∈ developmentWithInitialEdge b₁ ∩
      developmentWithInitialEdge b₂ →
      (S b₁).r 0 v = (S b₂).r 0 v ∧
      (S b₁).phi 0 v = (S b₂).phi 0 v := by
    intro v hv
    have hv₁ : v ∈ Ioo (0 : ℝ) b₁ := ⟨hv.1.2.1, hv.1.2.2⟩
    have hv₂ : v ∈ Ioo (0 : ℝ) b₂ := ⟨hv.2.2.1, hv.2.2.2⟩
    have hα : ∀ w ∈ Ioo (0 : ℝ) (min b₁ b₂),
        (S b₁).alpha 0 w = (S b₂).alpha 0 w := by
      intro w hw
      rw [(hdata₁ w ⟨hw.1, hw.2.trans_le (min_le_left _ _)⟩).2,
        (hdata₂ w ⟨hw.1, hw.2.trans_le (min_le_right _ _)⟩).2]
    constructor
    · rw [(hdata₁ v hv₁).1, (hdata₂ v hv₂).1]
    · exact initial_phi_eq_of_radius_alpha_data H₁ H₂
        (fun w hw => (hdata₁ w hw).1)
        (fun w hw => (hdata₂ w hw).1) hα v
        ⟨hv₁.1, lt_min hv₁.2 hv₂.2⟩
  have hprimary : ∀ q ∈ developmentWithInitialEdge b₁ ∩
      developmentWithInitialEdge b₂,
      (S b₁).r q.1 q.2 = (S b₂).r q.1 q.2 ∧
      (S b₁).phi q.1 q.2 = (S b₂).phi q.1 q.2 ∧
      (S b₁).m q.1 q.2 = (S b₂).m q.1 q.2 :=
    ChristodoulouBV.theorem3_1_unique
      (developmentWithInitialEdge b₁) (developmentWithInitialEdge b₂)
      (S b₁) (S b₂)
      (H₁.isBVSolution_development hb₁.1)
      (H₂.isBVSolution_development hb₂.1) hinitial
  have hopen : ∀ q ∈ openDevelopment 0 (min b₁ b₂),
      (S b₁).r q.1 q.2 = (S b₂).r q.1 q.2 ∧
      (S b₁).phi q.1 q.2 = (S b₂).phi q.1 q.2 ∧
      (S b₁).m q.1 q.2 = (S b₂).m q.1 q.2 := by
    intro q hq
    have hq₁ : q ∈ developmentWithInitialEdge b₁ :=
      ⟨hq.1.1.le, hq.2.1, hq.2.2.trans_le (min_le_left _ _)⟩
    have hq₂ : q ∈ developmentWithInitialEdge b₂ :=
      ⟨hq.1.1.le, hq.2.1, hq.2.2.trans_le (min_le_right _ _)⟩
    exact hprimary q ⟨hq₁, hq₂⟩
  have haux : (S b₁).lam p.1 p.2 = (S b₂).lam p.1 p.2 ∧
      (S b₁).nu p.1 p.2 = (S b₂).nu p.1 p.2 ∧
      (S b₁).alpha p.1 p.2 = (S b₂).alpha p.1 p.2 ∧
      (S b₁).beta p.1 p.2 = (S b₂).beta p.1 p.2 := by
    by_cases hp0 : p.1 = 0
    · let B : ℝ := (p.2 + min b₁ b₂) / 2
      have hpv : 0 < p.2 := by rw [← hp0]; exact hp.1.2.1
      have hpmin : p.2 < min b₁ b₂ := lt_min hp.1.2.2 hp.2.2.2
      have hB : 0 < B := by dsimp [B]; linarith
      have hBb₁ : B < b₁ := by dsimp [B]; have := min_le_left b₁ b₂; linarith
      have hBb₂ : B < b₂ := by dsimp [B]; have := min_le_right b₁ b₂; linarith
      have hpB : p ∈ closedCoordTriangle 0 B := by
        refine ⟨hp.1.1, hp.1.2.1.le, ?_⟩
        dsimp [B]
        linarith
      have hjets := c1_field_jets_eq_on_compact_closure_of_r_phi_m_eq
        hB hBb₁ hBb₂ H₁ H₂ hopen hpB
      rcases hjets with ⟨_, _, _, _, _, _, _, hlam, hnu, halpha,
        hbeta, _, _, _⟩
      exact ⟨hlam, hnu, halpha, hbeta⟩
    · have hpOpen : p ∈ openDevelopment 0 (min b₁ b₂) :=
        ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hp0),
          hp.1.2.1.trans (lt_min hp.1.2.2 hp.2.2.2)⟩,
          ⟨hp.1.2.1, lt_min hp.1.2.2 hp.2.2.2⟩⟩
      rcases fields_eq_on_open_overlap_of_r_phi_m_eq H₁ H₂ hopen p hpOpen with
        ⟨hlam, hnu, halpha, hbeta, _, _⟩
      exact ⟨hlam, hnu, halpha, hbeta⟩
  exact ⟨(hprimary p hp).1, (hprimary p hp).2.1,
    (hprimary p hp).2.2, haux.1, haux.2.1, haux.2.2.1, haux.2.2.2⟩

/-- The mass ratio has a single value at a point shared by two family members. -/
theorem family_mass_ratio_eq_on_common_development
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {S : ℝ → Fields}
    (hfamily : ∀ v₀ ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge v₀) (S v₀) ∧
      (∀ v ∈ Ioo (0 : ℝ) v₀,
        (S v₀).r 0 v = v / 2 ∧ (S v₀).alpha 0 v = alpha₀ v))
    {b₁ b₂ : ℝ} (hb₁ : b₁ ∈ Ioo (0 : ℝ) vStar)
    (hb₂ : b₂ ∈ Ioo (0 : ℝ) vStar)
    {p : ℝ × ℝ}
    (hp : p ∈ developmentWithInitialEdge b₁ ∩
      developmentWithInitialEdge b₂) :
    2 * (S b₁).m p.1 p.2 / (S b₁).r p.1 p.2 =
      2 * (S b₂).m p.1 p.2 / (S b₂).r p.1 p.2 := by
  have hfields := family_fields_eq_on_common_development hfamily hb₁ hb₂ hp
  rw [hfields.1, hfields.2.2.1]

/-- The in-domain mass-ratio values on the tail, sampled across the entire
frozen extension family. Compatibility makes each point's value independent
of the member used there. -/
@[expose] def tailMassRatioValues (u₀ vStar : ℝ) (S : ℝ → Fields) : Set ℝ :=
  {x | ∃ b ∈ Ioo (0 : ℝ) vStar,
    ∃ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
      x = 2 * (S b).m p.1 p.2 / (S b).r p.1 p.2}

/-- The supremum in (5.1), taken over every in-domain member on the tail. -/
@[expose] noncomputable def tailMassRatioSup (u₀ vStar : ℝ) (S : ℝ → Fields) : ℝ :=
  sSup (tailMassRatioValues u₀ vStar S)

/-- The uniform frozen family tail premise makes the compatible mass-ratio
supremum finite and places it below `η < ε₁`. Every sampled value is bounded
by that same supremum. -/
theorem tail_mass_ratio_bound
    {alpha₀ : ℝ → ℝ} {vStar u₀ η ε₁ : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hfamily : ∀ v₀ ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge v₀) (S v₀) ∧
      (∀ v ∈ Ioo (0 : ℝ) v₀,
        (S v₀).r 0 v = v / 2 ∧ (S v₀).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ η)
    (hη : η < ε₁) :
    0 ≤ tailMassRatioSup u₀ vStar S ∧
    tailMassRatioSup u₀ vStar S ≤ η ∧
    tailMassRatioSup u₀ vStar S < ε₁ ∧
    ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤
          tailMassRatioSup u₀ vStar S := by
  let u : ℝ := (u₀ + vStar) / 2
  let v : ℝ := (u + vStar) / 2
  let b : ℝ := (v + vStar) / 2
  have hsample : (u, v) ∈ openDevelopment u₀ vStar ∩
      developmentWithInitialEdge b := by
    dsimp [openDevelopment, developmentWithInitialEdge, u, v, b]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo]
    constructor
    · constructor
      · constructor <;> linarith [hu₀.1, hu₀.2]
      · constructor <;> linarith [hu₀.1, hu₀.2]
    · constructor
      · linarith [hu₀.1, hu₀.2]
      · constructor <;> linarith [hu₀.1, hu₀.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b, v, u]
    constructor <;> linarith [hu₀.1, hu₀.2]
  have hne : (tailMassRatioValues u₀ vStar S).Nonempty := by
    refine ⟨2 * (S b).m u v / (S b).r u v, b, hb, (u, v), hsample, rfl⟩
  have hupper : BddAbove (tailMassRatioValues u₀ vStar S) := by
    refine ⟨η, ?_⟩
    rintro x ⟨b', hb', p, hp, rfl⟩
    exact htail b' hb' p hp
  have hnonneg : 0 ≤ tailMassRatioSup u₀ vStar S := by
    have hmem : 2 * (S b).m u v / (S b).r u v ∈
        tailMassRatioValues u₀ vStar S := ⟨b, hb, (u, v), hsample, rfl⟩
    exact ((hfamily b hb).1.mass_ratio_nonneg_of_c1 hsample.2).trans
      (le_csSup hupper hmem)
  have hle : tailMassRatioSup u₀ vStar S ≤ η :=
    csSup_le hne (by
      rintro x ⟨b', hb', p, hp, rfl⟩
      exact htail b' hb' p hp)
  refine ⟨hnonneg, hle, hle.trans_lt hη, ?_⟩
  intro b' hb' p hp
  exact le_csSup hupper ⟨b', hb', p, hp, rfl⟩

end ChristodoulouBV.Uniqueness

end
