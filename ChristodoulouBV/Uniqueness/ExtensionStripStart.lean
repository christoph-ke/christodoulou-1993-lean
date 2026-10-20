module

public import ChristodoulouBV.Uniqueness.ExtensionCutoff
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The adjacent extension strip

The new strip includes its lower outgoing seam at `vStar` and excludes its
incoming sides. The weighted suprema are real `sSup` values; their boundedness
is a separate assertion about an actual C¹ extension.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The adjacent strip `U_η(u₁) = (u₀,u₁) × [vStar,vStar+η)` on p. 1177. -/
def extensionStrip (u₀ u₁ vStar η : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo u₀ u₁ ∧ p.2 ∈ Ico vStar (vStar + η)}

/-- Weighted `α′` values of one C¹ field on the adjacent strip. -/
def stripWeightedAlphaPrimeValues (u₀ u₁ vStar η : ℝ) (T : Fields) : Set ℝ :=
  {x | ∃ p : AlphaPrimeDomain T,
    (p : ℝ × ℝ) ∈ extensionStrip u₀ u₁ vStar η ∧
    x = T.r p.1.1 p.1.2 ^ ((1 : ℝ) / 2) * |alphaPrime T p|}

/-- The strip supremum `Ā′_η(u₁)` in Christodoulou (1993), p. 1177. -/
noncomputable def stripWeightedAlphaPrimeSup
    (u₀ u₁ vStar η : ℝ) (T : Fields) : ℝ :=
  sSup (stripWeightedAlphaPrimeValues u₀ u₁ vStar η T)

/-- Weighted `α′` values on the incoming edge `u=u₀` above `vStar`. -/
def incomingStripWeightedValues (u₀ vStar η : ℝ) (T : Fields) : Set ℝ :=
  {x | ∃ p : AlphaPrimeDomain T,
    p.1.1 = u₀ ∧ p.1.2 ∈ Ico vStar (vStar + η) ∧
    x = T.r p.1.1 p.1.2 ^ ((1 : ℝ) / 2) * |alphaPrime T p|}

/-- The incoming edge supremum `D̄′_η(u₀)` on p. 1177. -/
noncomputable def incomingStripWeightedSup (u₀ vStar η : ℝ) (T : Fields) : ℝ :=
  sSup (incomingStripWeightedValues u₀ vStar η T)

/-- The old truncated region excludes `u=u₁`, including when `u₁=vStar`. -/
theorem mem_truncatedDevelopment_iff_of_le
    {u₀ u₁ vStar : ℝ} (_hu₁Star : u₁ ≤ vStar) {p : ℝ × ℝ} :
    p ∈ truncatedDevelopment u₀ u₁ vStar ↔
      u₀ < p.1 ∧ p.1 < u₁ ∧ p.1 < p.2 ∧ p.2 < vStar := by
  constructor
  · intro hp
    have hdev := hp.1
    have hfst : p.1 < u₁ := by
      by_contra hn
      have hu₁ : u₁ ≤ p.1 := le_of_not_gt hn
      have hu₁Strict : u₁ < vStar := hu₁.trans_lt hdev.1.2
      have hcl : p ∈ closure (openDevelopment u₁ vStar) := by
        have hEq : openDevelopment u₁ vStar =
            openCoordTriangle u₁ vStar := by
          ext q
          constructor
          · intro h
            exact ⟨h.1.1, h.2.1, h.2.2⟩
          · intro h
            exact ⟨⟨h.1, h.2.1.trans h.2.2⟩,
              ⟨h.2.1, h.2.2⟩⟩
        rw [hEq, closure_openCoordTriangle hu₁Strict]
        exact ⟨hu₁, hdev.2.1.le, hdev.2.2.le⟩
      exact hp.2 hcl
    exact ⟨hdev.1.1, hfst, hdev.2.1, hdev.2.2⟩
  · rintro ⟨hu₀, hu₁, huv, hv⟩
    refine ⟨⟨⟨hu₀, huv.trans hv⟩, ⟨huv, hv⟩⟩, ?_⟩
    have hsub : openDevelopment u₁ vStar ⊆
        {q : ℝ × ℝ | u₁ ≤ q.1} := by
      intro q hq
      exact hq.1.1.le
    have hclosed : IsClosed {q : ℝ × ℝ | u₁ ≤ q.1} :=
      isClosed_le continuous_const continuous_fst
    intro hcl
    exact (not_le_of_gt hu₁) (closure_minimal hsub hclosed hcl)

/-- The literal old-region/strip union on p. 1177. The old side has `v<vStar`,
the strip has `vStar≤v`, and both sides exclude `u=u₁`. -/
theorem truncated_union_strip {u₀ u₁ vStar η : ℝ}
    (_hu₀u₁ : u₀ < u₁) (hu₁Star : u₁ ≤ vStar) (hη : 0 < η) :
    truncatedDevelopment u₀ u₁ vStar ∪ extensionStrip u₀ u₁ vStar η =
      truncatedDevelopment u₀ u₁ (vStar + η) := by
  have hu₁Top : u₁ < vStar + η := lt_of_le_of_lt hu₁Star (lt_add_of_pos_right _ hη)
  ext p
  rw [mem_union, mem_truncatedDevelopment_iff_of_le hu₁Star,
    mem_truncatedDevelopment_iff_of_le hu₁Top.le]
  change (u₀ < p.1 ∧ p.1 < u₁ ∧ p.1 < p.2 ∧ p.2 < vStar) ∨
    (p.1 ∈ Ioo u₀ u₁ ∧ p.2 ∈ Ico vStar (vStar + η)) ↔
    u₀ < p.1 ∧ p.1 < u₁ ∧ p.1 < p.2 ∧ p.2 < vStar + η
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (lt_add_of_pos_right _ hη)⟩
    · exact ⟨h.1.1, h.1.2, h.1.2.trans_le (hu₁Star.trans h.2.1), h.2.2⟩
  · rintro ⟨hu₀, hu₁, huv, hvTop⟩
    rcases lt_or_ge p.2 vStar with hvOld | hvStrip
    · exact Or.inl ⟨hu₀, hu₁, huv, hvOld⟩
    · exact Or.inr ⟨⟨hu₀, hu₁⟩, ⟨hvStrip, hvTop⟩⟩

end ChristodoulouBV.Uniqueness

end
