module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldGeometry
public import ChristodoulouBV.Uniqueness.RouteBGluingFields
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Closed-jet gluing inside the clipped old region

The finite old triangle and the terminal rectangle are closed convex sets.
Matching seven values and full relative first jets on their horizontal
intersection yield a single C¹ seven-field state on the clipped old region.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Two scalar fields with matching values and full relative first jets
glue on the clipped old region. -/
theorem exists_routeB_old_scalar_glue
    {a vBar vStar : ℝ} (ha : 0 < a) (haBar : a < vBar)
    (hBarStar : vBar < vStar)
    (fBottom fTop : ℝ × ℝ → ℝ)
    (hBottom : ContDiffOn ℝ 1 fBottom (routeBOldRegion a vBar))
    (hTop : ContDiffOn ℝ 1 fTop (routeBLowerRegion a vBar vStar))
    (hValue : EqOn fBottom fTop
      (routeBOldRegion a vBar ∩ routeBLowerRegion a vBar vStar))
    (hJet : EqOn
      (fderivWithin ℝ fBottom (routeBOldRegion a vBar))
      (fderivWithin ℝ fTop (routeBLowerRegion a vBar vStar))
      (routeBOldRegion a vBar ∩ routeBLowerRegion a vBar vStar)) :
    ∃ f : ℝ × ℝ → ℝ,
      ContDiffOn ℝ 1 f (routeBOldRegion a vStar) ∧
      EqOn f fBottom (routeBOldRegion a vBar) ∧
      EqOn f fTop (routeBLowerRegion a vBar vStar) := by
  let K : Bool → Set (ℝ × ℝ)
    | false => routeBOldRegion a vBar
    | true => routeBLowerRegion a vBar vStar
  let f : Bool → ℝ × ℝ → ℝ
    | false => fBottom
    | true => fTop
  let G : Bool → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
    fun i => fderivWithin ℝ (f i) (K i)
  have hconv : ∀ i ∈ (Finset.univ : Finset Bool), Convex ℝ (K i) := by
    intro i _
    cases i
    · exact (routeBOldRegion_closed_convex a vBar).2
    · exact (routeBLowerRegion_closed_convex a vBar vStar).2
  have hclosed : ∀ i ∈ (Finset.univ : Finset Bool), IsClosed (K i) := by
    intro i _
    cases i
    · exact (routeBOldRegion_closed_convex a vBar).1
    · exact (routeBLowerRegion_closed_convex a vBar vStar).1
  have hinterior : ∀ i ∈ (Finset.univ : Finset Bool),
      (interior (K i)).Nonempty := by
    intro i _
    cases i
    · exact routeBOldRegion_interior_nonempty ha haBar
    · exact routeBLowerRegion_interior_nonempty ha hBarStar
  have hC1 : ∀ i ∈ (Finset.univ : Finset Bool),
      ContDiffOn ℝ 1 (f i) (K i) := by
    intro i _
    cases i <;> assumption
  have hf : ∀ i ∈ (Finset.univ : Finset Bool),
      ContinuousOn (f i) (K i) := by
    intro i hi
    exact (hC1 i hi).continuousOn
  have hG : ∀ i ∈ (Finset.univ : Finset Bool),
      ContinuousOn (G i) (K i) := by
    intro i hi
    exact (hC1 i hi).continuousOn_fderivWithin
      (uniqueDiffOn_convex (hconv i hi) (hinterior i hi)) (by norm_num)
  have hdiff : ∀ i ∈ (Finset.univ : Finset Bool),
      DifferentiableOn ℝ (f i) (interior (K i)) := by
    intro i hi
    exact ((hC1 i hi).differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ i ∈ (Finset.univ : Finset Bool),
      ∀ p ∈ interior (K i), fderiv ℝ (f i) p = G i p := by
    intro i _ p hp
    have hmem : K i ∈ 𝓝 p :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hp) interior_subset
    exact (fderivWithin_of_mem_nhds (f := f i) (s := K i) hmem).symm
  have hvalue : ∀ i ∈ (Finset.univ : Finset Bool),
      ∀ j ∈ (Finset.univ : Finset Bool),
      EqOn (f i) (f j) (K i ∩ K j) := by
    intro i _ j _
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact hValue
    · intro p hp; exact (hValue ⟨hp.2, hp.1⟩).symm
    · exact fun _ _ => rfl
  have hjet : ∀ i ∈ (Finset.univ : Finset Bool),
      ∀ j ∈ (Finset.univ : Finset Bool),
      EqOn (G i) (G j) (K i ∩ K j) := by
    intro i _ j _
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact hJet
    · intro p hp; exact (hJet ⟨hp.2, hp.1⟩).symm
    · exact fun _ _ => rfl
  obtain ⟨fglue, _, hglue, hmatch, _⟩ :=
    Convex.exists_contDiffOn_one_finset_glue
      (Finset.univ : Finset Bool) K hconv hclosed hinterior
      f G hf hG hdiff hderiv hvalue hjet
  have hcover : (⋃ i ∈ (Finset.univ : Finset Bool), K i) =
      routeBOldRegion a vStar := by
    rw [← routeB_old_triangle_terminal_cover ha.le haBar.le hBarStar.le]
    ext p
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hp | hp)
      · exact ⟨false, hp⟩
      · exact ⟨true, hp⟩
  refine ⟨fglue, hcover ▸ hglue, ?_, ?_⟩
  · exact hmatch false (Finset.mem_univ _)
  · exact hmatch true (Finset.mem_univ _)

/-- Seven closed-jet glues form one C¹ old field on the clipped region. -/
theorem exists_routeB_old_fields_c1_glue
    {a vBar vStar : ℝ} (ha : 0 < a) (haBar : a < vBar)
    (hBarStar : vBar < vStar)
    (SBottom STop : Fields)
    (hBottom : RouteBFieldsC1On SBottom (routeBOldRegion a vBar))
    (hTop : RouteBFieldsC1On STop (routeBLowerRegion a vBar vStar))
    (hValue : RouteBFieldsEqOn SBottom STop
      (routeBOldRegion a vBar ∩ routeBLowerRegion a vBar vStar))
    (hJet : RouteBFieldsJetEqOn SBottom STop
      (routeBOldRegion a vBar) (routeBLowerRegion a vBar vStar)) :
    ∃ SOld : Fields,
      RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
      RouteBFieldsEqOn SOld SBottom (routeBOldRegion a vBar) ∧
      RouteBFieldsEqOn SOld STop (routeBLowerRegion a vBar vStar) := by
  have hglue (c : RouteBField) :
      ∃ f : ℝ × ℝ → ℝ,
        ContDiffOn ℝ 1 f (routeBOldRegion a vStar) ∧
        EqOn f (routeBField SBottom c) (routeBOldRegion a vBar) ∧
        EqOn f (routeBField STop c) (routeBLowerRegion a vBar vStar) :=
    exists_routeB_old_scalar_glue ha haBar hBarStar
      (routeBField SBottom c) (routeBField STop c)
      (hBottom c) (hTop c) (hValue c) (hJet c)
  let f : RouteBField → ℝ × ℝ → ℝ := fun c => Classical.choose (hglue c)
  let SOld := routeBFieldsOfComponents f
  refine ⟨SOld, ?_, ?_, ?_⟩
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).1
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).2.1
  · intro c
    rw [routeBField_ofComponents]
    exact (Classical.choose_spec (hglue c)).2.2

end ChristodoulouBV.Uniqueness

end
