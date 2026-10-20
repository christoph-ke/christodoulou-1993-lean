module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Closed coordinate triangles in the real plane

The triangle with `a ≤ u ≤ v ≤ b` is a compact convex set whose interior is
specified by the three strict inequalities.
-/

public section

open Set

/-- The closed coordinate triangle between the diagonal points `(a,a)` and `(b,b)`. -/
def closedCoordTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}

/-- The strict coordinate triangle between the diagonal points `(a,a)` and `(b,b)`. -/
def openCoordTriangle (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a < p.1 ∧ p.1 < p.2 ∧ p.2 < b}

private def coordGap : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun p := p.2 - p.1
  map_add' := by intro p q; dsimp; ring
  map_smul' := by intro c p; dsimp; ring

private theorem coordGap_surjective : Function.Surjective coordGap := by
  intro y
  exact ⟨(0, y), by simp [coordGap]⟩

/-- The closed coordinate triangle is closed. -/
theorem isClosed_closedCoordTriangle (a b : ℝ) : IsClosed (closedCoordTriangle a b) := by
  have h₁ : IsClosed {p : ℝ × ℝ | a ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have h₂ : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} :=
    isClosed_le continuous_fst continuous_snd
  have h₃ : IsClosed {p : ℝ × ℝ | p.2 ≤ b} :=
    isClosed_le continuous_snd continuous_const
  simpa [closedCoordTriangle, ofPred_and, inter_assoc] using h₁.inter (h₂.inter h₃)

/-- The closed coordinate triangle is convex. -/
theorem convex_closedCoordTriangle (a b : ℝ) : Convex ℝ (closedCoordTriangle a b) := by
  intro p hp q hq s t hs ht hst
  change a ≤ (s • p + t • q).1 ∧
    (s • p + t • q).1 ≤ (s • p + t • q).2 ∧
    (s • p + t • q).2 ≤ b
  change a ≤ s * p.1 + t * q.1 ∧
    s * p.1 + t * q.1 ≤ s * p.2 + t * q.2 ∧
    s * p.2 + t * q.2 ≤ b
  change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
  change a ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ b at hq
  constructor
  · calc
      a = (s + t) * a := by rw [hst]; ring
      _ = s * a + t * a := by ring
      _ ≤ s * p.1 + t * q.1 := add_le_add
        (mul_le_mul_of_nonneg_left hp.1 hs)
        (mul_le_mul_of_nonneg_left hq.1 ht)
  constructor
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr hp.2.1),
      mul_nonneg ht (sub_nonneg.mpr hq.2.1)]
  · calc
      s * p.2 + t * q.2 ≤ s * b + t * b := add_le_add
        (mul_le_mul_of_nonneg_left hp.2.2 hs)
        (mul_le_mul_of_nonneg_left hq.2.2 ht)
      _ = (s + t) * b := by ring
      _ = b := by rw [hst]; ring

/-- The closed coordinate triangle is compact. -/
theorem isCompact_closedCoordTriangle (a b : ℝ) : IsCompact (closedCoordTriangle a b) := by
  apply ((isCompact_Icc : IsCompact (Icc a b)).prod
    (isCompact_Icc : IsCompact (Icc a b))).of_isClosed_subset
    (isClosed_closedCoordTriangle a b)
  intro p hp
  change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
  exact ⟨⟨hp.1, hp.2.1.trans hp.2.2⟩,
    ⟨hp.1.trans hp.2.1, hp.2.2⟩⟩

/-- The interior of the closed coordinate triangle consists of the strict inequalities. -/
theorem interior_closedCoordTriangle (a b : ℝ) :
    interior (closedCoordTriangle a b) = openCoordTriangle a b := by
  have hfst : interior {p : ℝ × ℝ | a ≤ p.1} = {p | a < p.1} := by
    change interior ((fun p : ℝ × ℝ => p.1) ⁻¹' Ici a) = _
    rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst]
    ext p
    simp
  have hsnd : interior {p : ℝ × ℝ | p.2 ≤ b} = {p | p.2 < b} := by
    change interior ((fun p : ℝ × ℝ => p.2) ⁻¹' Iic b) = _
    rw [← isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd]
    ext p
    simp
  have hgap : interior {p : ℝ × ℝ | p.1 ≤ p.2} = {p | p.1 < p.2} := by
    have hopen : IsOpenMap coordGap :=
      LinearMap.isOpenMap_of_finiteDimensional coordGap coordGap_surjective
    have hcont : Continuous coordGap :=
      (LinearMap.toContinuousLinearMap coordGap).continuous
    have hset : {p : ℝ × ℝ | p.1 ≤ p.2} = coordGap ⁻¹' Ici 0 := by
      ext p
      simp [coordGap, sub_nonneg]
    rw [hset, ← hopen.preimage_interior_eq_interior_preimage hcont]
    ext p
    simp [coordGap, sub_pos]
  simp only [closedCoordTriangle, openCoordTriangle, ofPred_and, interior_inter,
    hfst, hgap, hsnd]

/-- A nondegenerate strict coordinate triangle has an interior point. -/
theorem openCoordTriangle_nonempty {a b : ℝ} (hab : a < b) :
    (openCoordTriangle a b).Nonempty := by
  let u := (2 * a + b) / 3
  let v := (a + 2 * b) / 3
  refine ⟨(u, v), ?_⟩
  change a < u ∧ u < v ∧ v < b
  dsimp [u, v]
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The strict coordinate triangle is dense in the closed one. -/
theorem closure_openCoordTriangle {a b : ℝ} (hab : a < b) :
    closure (openCoordTriangle a b) = closedCoordTriangle a b := by
  rw [← interior_closedCoordTriangle]
  rw [(convex_closedCoordTriangle a b).closure_interior_eq_closure_of_nonempty_interior]
  · exact (isClosed_closedCoordTriangle a b).closure_eq
  · rw [interior_closedCoordTriangle]
    exact openCoordTriangle_nonempty hab

/-- Every point of a nondegenerate closed coordinate triangle is approached from its interior. -/
theorem closedCoordTriangle_subset_closure_open {a b : ℝ} (hab : a < b) :
    closedCoordTriangle a b ⊆ closure (openCoordTriangle a b) := by
  rw [closure_openCoordTriangle hab]

/-- The region with a closed initial edge and strict remaining inequalities is dense
in the corresponding closed triangle. -/
theorem closure_initialEdgeTriangle {b : ℝ} (hb : 0 < b) :
    closure {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < b} =
      closedCoordTriangle 0 b := by
  apply Subset.antisymm
  · apply (isClosed_closedCoordTriangle 0 b).closure_subset_iff.mpr
    intro p hp
    exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  · rw [← closure_openCoordTriangle hb]
    apply closure_mono
    intro p hp
    exact ⟨hp.1.le, hp.2.1, hp.2.2⟩

end
