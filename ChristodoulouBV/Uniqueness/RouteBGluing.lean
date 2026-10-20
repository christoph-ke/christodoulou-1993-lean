module

public import ChristodoulouBV.Uniqueness.RouteBGluingGeometry
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Three-region closed-jet gluing

This is the scalar C¹ gluing step for Route B. Its old input is a genuine
closed-triangle representative with canonical radius and mass on the axis,
not a raw family member defined only below the terminal parameter.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Labels for the three closed regions of the Route B construction. -/
inductive RouteBPiece where
  | old | lower | axis
  deriving DecidableEq

/-- The three Route B piece labels form a finite type. -/
instance : Fintype RouteBPiece where
  elems := {.old, .lower, .axis}
  complete := by
    intro i
    cases i <;> simp

/-- The closed region belonging to a Route B piece. -/
@[expose] def routeBRegion (a vStar b : ℝ) : RouteBPiece → Set (ℝ × ℝ)
  | .old => closedCoordTriangle 0 vStar
  | .lower => routeBLowerRegion a vStar b
  | .axis => closedCoordTriangle a b

/-- Three scalar fields with matching values and relative full jets on every
pairwise intersection glue to one C¹ field on the enlarged triangle. The
old scalar must be the closed-region C¹ extension supplied by the terminal
trace construction; the raw old family has no value at `v = vStar`. -/
theorem exists_routeB_scalar_glue
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (fOld fLow fAx : ℝ × ℝ → ℝ)
    (hOld : ContDiffOn ℝ 1 fOld (closedCoordTriangle 0 vStar))
    (hLow : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hAx : ContDiffOn ℝ 1 fAx (closedCoordTriangle a b))
    (hOldLow : EqOn fOld fLow
      (closedCoordTriangle 0 vStar ∩ routeBLowerRegion a vStar b))
    (hOldAx : EqOn fOld fAx
      (closedCoordTriangle 0 vStar ∩ closedCoordTriangle a b))
    (hLowAx : EqOn fLow fAx
      (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b))
    (hJetOldLow : EqOn
      (fderivWithin ℝ fOld (closedCoordTriangle 0 vStar))
      (fderivWithin ℝ fLow (routeBLowerRegion a vStar b))
      (closedCoordTriangle 0 vStar ∩ routeBLowerRegion a vStar b))
    (hJetOldAx : EqOn
      (fderivWithin ℝ fOld (closedCoordTriangle 0 vStar))
      (fderivWithin ℝ fAx (closedCoordTriangle a b))
      (closedCoordTriangle 0 vStar ∩ closedCoordTriangle a b))
    (hJetLowAx : EqOn
      (fderivWithin ℝ fLow (routeBLowerRegion a vStar b))
      (fderivWithin ℝ fAx (closedCoordTriangle a b))
      (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b)) :
    ∃ f : ℝ × ℝ → ℝ,
      ContDiffOn ℝ 1 f (closedCoordTriangle 0 b) ∧
      EqOn f fOld (closedCoordTriangle 0 vStar) ∧
      EqOn f fLow (routeBLowerRegion a vStar b) ∧
      EqOn f fAx (closedCoordTriangle a b) := by
  let K := routeBRegion a vStar b
  let f : RouteBPiece → ℝ × ℝ → ℝ
    | .old => fOld
    | .lower => fLow
    | .axis => fAx
  let G : RouteBPiece → ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
    fun i => fderivWithin ℝ (f i) (K i)
  have hconv : ∀ i ∈ (Finset.univ : Finset RouteBPiece), Convex ℝ (K i) := by
    intro i _
    cases i
    · exact convex_closedCoordTriangle 0 vStar
    · exact (routeBLowerRegion_closed_convex a vStar b).2
    · exact convex_closedCoordTriangle a b
  have hclosed : ∀ i ∈ (Finset.univ : Finset RouteBPiece), IsClosed (K i) := by
    intro i _
    cases i
    · exact isClosed_closedCoordTriangle 0 vStar
    · exact (routeBLowerRegion_closed_convex a vStar b).1
    · exact isClosed_closedCoordTriangle a b
  have hinterior : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      (interior (K i)).Nonempty := by
    intro i _
    cases i
    · change (interior (closedCoordTriangle 0 vStar)).Nonempty
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (ha.trans haStar)
    · exact routeBLowerRegion_interior_nonempty ha hStarb
    · change (interior (closedCoordTriangle a b)).Nonempty
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb)
  have hC1 : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      ContDiffOn ℝ 1 (f i) (K i) := by
    intro i _
    cases i <;> assumption
  have hf : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      ContinuousOn (f i) (K i) := by
    intro i hi
    exact (hC1 i hi).continuousOn
  have hG : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      ContinuousOn (G i) (K i) := by
    intro i hi
    exact (hC1 i hi).continuousOn_fderivWithin
      (uniqueDiffOn_convex (hconv i hi) (hinterior i hi)) (by norm_num)
  have hdiff : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      DifferentiableOn ℝ (f i) (interior (K i)) := by
    intro i hi
    exact ((hC1 i hi).differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      ∀ p ∈ interior (K i), fderiv ℝ (f i) p = G i p := by
    intro i _ p hp
    have hmem : K i ∈ 𝓝 p :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hp) interior_subset
    exact (fderivWithin_of_mem_nhds (f := f i) (s := K i) hmem).symm
  have hvalue : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      ∀ j ∈ (Finset.univ : Finset RouteBPiece),
      EqOn (f i) (f j) (K i ∩ K j) := by
    intro i _ j _
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact hOldLow
    · exact hOldAx
    · intro p hp; exact (hOldLow ⟨hp.2, hp.1⟩).symm
    · exact fun _ _ => rfl
    · exact hLowAx
    · intro p hp; exact (hOldAx ⟨hp.2, hp.1⟩).symm
    · intro p hp; exact (hLowAx ⟨hp.2, hp.1⟩).symm
    · exact fun _ _ => rfl
  have hjet : ∀ i ∈ (Finset.univ : Finset RouteBPiece),
      ∀ j ∈ (Finset.univ : Finset RouteBPiece),
      EqOn (G i) (G j) (K i ∩ K j) := by
    intro i _ j _
    cases i <;> cases j
    · exact fun _ _ => rfl
    · exact hJetOldLow
    · exact hJetOldAx
    · intro p hp; exact (hJetOldLow ⟨hp.2, hp.1⟩).symm
    · exact fun _ _ => rfl
    · exact hJetLowAx
    · intro p hp; exact (hJetOldAx ⟨hp.2, hp.1⟩).symm
    · intro p hp; exact (hJetLowAx ⟨hp.2, hp.1⟩).symm
    · exact fun _ _ => rfl
  obtain ⟨fglue, _, hglue, hmatch, _⟩ :=
    Convex.exists_contDiffOn_one_finset_glue
      (Finset.univ : Finset RouteBPiece) K hconv hclosed hinterior
      f G hf hG hdiff hderiv hvalue hjet
  have hcover : (⋃ i ∈ (Finset.univ : Finset RouteBPiece), K i) =
      closedCoordTriangle 0 b := by
    rw [← routeB_three_region_cover ha.le haStar.le hStarb.le]
    ext p
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | old => exact Or.inl (Or.inl hi)
      | lower => exact Or.inl (Or.inr hi)
      | axis => exact Or.inr hi
    · intro hp
      rcases hp with (hOld | hLow) | hAx
      · exact ⟨.old, hOld⟩
      · exact ⟨.lower, hLow⟩
      · exact ⟨.axis, hAx⟩
  refine ⟨fglue, hcover ▸ hglue, ?_, ?_, ?_⟩
  · exact hmatch .old (Finset.mem_univ _)
  · exact hmatch .lower (Finset.mem_univ _)
  · exact hmatch .axis (Finset.mem_univ _)

end ChristodoulouBV.Uniqueness

end
