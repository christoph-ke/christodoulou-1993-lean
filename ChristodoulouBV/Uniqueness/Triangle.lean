module

public import ChristodoulouBV.BVSolution.Geometry
public import ChristodoulouBV.Frozen.OpenDevelopment
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge

/-!
# Triangles in common developments

The local comparison carrier includes its initial outgoing edge and has an open
upper `v` endpoint. Past closure places it in both developments below any
strictly future common witness.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The supremum of the `u` coordinates in a common development, including
the possible unbounded case. -/
noncomputable def overlapCoordinateSup (U₁ U₂ : Set (ℝ × ℝ)) : EReal :=
  sSup ((fun p : ℝ × ℝ => (p.1 : EReal)) '' (U₁ ∩ U₂))

/-- The local triangle, including its initial outgoing characteristic. -/
def triangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < b}

/-- Membership in the augmented local triangle. -/
theorem mem_triangle {a b u v : ℝ} :
    (u, v) ∈ triangle a b ↔ a ≤ u ∧ u < v ∧ v < b := Iff.rfl

/-- The printed open triangle is the strict interior of the augmented one. -/
theorem mem_openDevelopment {a b u v : ℝ} :
    (u, v) ∈ openDevelopment a b ↔ a < u ∧ u < v ∧ v < b := by
  simp only [openDevelopment, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨hau, _⟩, huv, hvb⟩
    exact ⟨hau, huv, hvb⟩
  · rintro ⟨hau, huv, hvb⟩
    exact ⟨⟨hau, huv.trans hvb⟩, huv, hvb⟩

/-- The printed open triangle lies in the augmented triangle. -/
theorem openDevelopment_subset_triangle (a b : ℝ) :
    openDevelopment a b ⊆ triangle a b := by
  intro p hp
  rcases p with ⟨u, v⟩
  exact ⟨(mem_openDevelopment.mp hp).1.le,
    (mem_openDevelopment.mp hp).2.1, (mem_openDevelopment.mp hp).2.2⟩

/-- The augmented triangle at the initial axis is the frozen initial-edge development. -/
theorem triangle_zero_eq_developmentWithInitialEdge (b : ℝ) :
    triangle 0 b = developmentWithInitialEdge b := rfl

/-- The normalized augmented triangle is a domain of development. -/
theorem triangle_zero_isDomainOfDevelopment (b : ℝ) :
    IsDomainOfDevelopment (triangle 0 b) := by
  constructor
  · intro p hp
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp q hq
    exact ⟨hq.1.1, hq.2.1, lt_trans hq.2.2 hp.2.2⟩

/-- The initial characteristic edge belongs to the augmented triangle exactly
below its open top. -/
theorem initial_edge_of_triangle {a b v : ℝ} (hav : a < v) (hvb : v < b) :
    (a, v) ∈ triangle a b := ⟨le_rfl, hav, hvb⟩

/-- The augmented triangle is the printed open triangle together with its
initial characteristic edge. -/
theorem triangle_eq_open_union_initial (a b : ℝ) :
    triangle a b = openDevelopment a b ∪
      {p : ℝ × ℝ | p.1 = a ∧ a < p.2 ∧ p.2 < b} := by
  ext p
  rcases p with ⟨u, v⟩
  constructor
  · intro hp
    rcases lt_or_eq_of_le hp.1 with hau | rfl
    · exact Or.inl ((mem_openDevelopment).2 ⟨hau, hp.2.1, hp.2.2⟩)
    · exact Or.inr ⟨rfl, hp.2.1, hp.2.2⟩
  · rintro (hp | hp)
    · exact openDevelopment_subset_triangle a b hp
    · rcases hp with ⟨rfl, hav, hvb⟩
      exact initial_edge_of_triangle hav hvb

/-- A common point supplies its whole strict causal past in both developments. -/
theorem strict_past_common
    {U₁ U₂ : Set (ℝ × ℝ)}
    (h₁ : IsDomainOfDevelopment U₁) (h₂ : IsDomainOfDevelopment U₂)
    {A V a b : ℝ} (hp : (A, V) ∈ U₁ ∩ U₂)
    (ha : 0 ≤ a) (hb : b ≤ V) :
    {p | a ≤ p.1 ∧ p.1 ≤ A ∧ p.1 < p.2 ∧ p.2 < b} ⊆ U₁ ∩ U₂ := by
  intro p hpt
  rcases p with ⟨u, v⟩
  have hmem {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
      (hpoint : (A, V) ∈ U) : (u, v) ∈ U :=
    h.past_mem hpoint (ha.trans hpt.1) hpt.2.1 hpt.2.2.1
      (hpt.2.2.2.trans_le hb)
  exact ⟨hmem h₁ hp.1, hmem h₂ hp.2⟩

/-- Any triangle strictly below the future witness and with left edge before
its `u` coordinate lies in the common development. -/
theorem common_triangle
    {U₁ U₂ : Set (ℝ × ℝ)}
    (h₁ : IsDomainOfDevelopment U₁) (h₂ : IsDomainOfDevelopment U₂)
    {A V a b : ℝ} (hp : (A, V) ∈ U₁ ∩ U₂)
    (ha : 0 ≤ a) (hA : b ≤ A) (hV : b ≤ V) :
    triangle a b ⊆ U₁ ∩ U₂ := by
  intro p hpt
  exact strict_past_common h₁ h₂ hp ha hV
    ⟨hpt.1, (le_of_lt hpt.2.1).trans ((le_of_lt hpt.2.2).trans hA),
      hpt.2.1, hpt.2.2⟩

/-- A future common witness yields an entire family of common triangles,
including each initial edge. The top remains strict. -/
theorem common_strict_past_triangle_of_witness
    {U₁ U₂ : Set (ℝ × ℝ)}
    (h₁ : IsDomainOfDevelopment U₁) (h₂ : IsDomainOfDevelopment U₂)
    {A V a : ℝ} (hp : (A, V) ∈ U₁ ∩ U₂)
    (ha : 0 ≤ a) (haA : a < A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      triangle a (a + 2 * δ) ⊆ U₁ ∩ U₂ := by
  have hAV : A < V := (h₁.wedge hp.1).2
  let δ₀ : ℝ := (A - a) / 2
  refine ⟨δ₀, by dsimp [δ₀]; linarith, ?_⟩
  intro δ hδ hδ₀
  apply common_triangle h₁ h₂ hp ha
  · dsimp [δ₀] at hδ₀
    linarith
  · dsimp [δ₀] at hδ₀
    linarith

/-- If `a` is below the supremum of common `u` coordinates, every sufficiently
small future triangle and its initial edge lie in both developments. -/
theorem common_strict_past_triangle
    {U₁ U₂ : Set (ℝ × ℝ)}
    (h₁ : IsDomainOfDevelopment U₁) (h₂ : IsDomainOfDevelopment U₂)
    {a : ℝ} (ha : 0 ≤ a)
    (hbelow : (a : EReal) < overlapCoordinateSup U₁ U₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      triangle a (a + 2 * δ) ⊆ U₁ ∩ U₂ := by
  obtain ⟨x, ⟨⟨A, V⟩, hp, rfl⟩, hax⟩ :=
    (lt_sSup_iff.mp hbelow)
  change (a : EReal) < (A : EReal) at hax
  have haA : a < A := by exact_mod_cast hax
  exact common_strict_past_triangle_of_witness h₁ h₂ hp ha haA

/-- Every closed outgoing subsegment of a local triangle is contained in it. -/
theorem outSeg_subset_triangle {a b u s t : ℝ}
    (hau : a ≤ u) (hus : u < s) (_hst : s ≤ t) (htb : t < b) :
    outSeg u s t ⊆ triangle a b := by
  intro p hp
  rcases p with ⟨x, v⟩
  have ⟨hx, hv⟩ : x = u ∧ v ∈ Icc s t := by
    simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
  subst x
  exact ⟨hau, hus.trans_le hv.1, hv.2.trans_lt htb⟩

/-- Every closed incoming subsegment strictly below the axis is contained in
the local triangle. No terminal incoming axis point is asserted. -/
theorem inSeg_subset_triangle {a b v s t : ℝ}
    (has : a ≤ s) (_hst : s ≤ t) (htv : t < v) (hvb : v < b) :
    inSeg v s t ⊆ triangle a b := by
  intro p hp
  rcases p with ⟨u, w⟩
  have ⟨hu, hw⟩ : u ∈ Icc s t ∧ w = v := by
    simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
  subst w
  exact ⟨has.trans hu.1, hu.2.trans_lt htv, hvb⟩

/-- A common triangle gives access to each of its closed outgoing subsegments. -/
theorem common_outSeg_subset
    {U₁ U₂ : Set (ℝ × ℝ)} {a b u s t : ℝ}
    (hT : triangle a b ⊆ U₁ ∩ U₂)
    (hau : a ≤ u) (hus : u < s) (hst : s ≤ t) (htb : t < b) :
    outSeg u s t ⊆ U₁ ∩ U₂ :=
  (outSeg_subset_triangle hau hus hst htb).trans hT

/-- A common triangle gives access to each closed incoming subsegment
strictly before its axis endpoint. -/
theorem common_inSeg_subset
    {U₁ U₂ : Set (ℝ × ℝ)} {a b v s t : ℝ}
    (hT : triangle a b ⊆ U₁ ∩ U₂)
    (has : a ≤ s) (hst : s ≤ t) (htv : t < v) (hvb : v < b) :
    inSeg v s t ⊆ U₁ ∩ U₂ :=
  (inSeg_subset_triangle has hst htv hvb).trans hT

end ChristodoulouBV.Uniqueness

end
