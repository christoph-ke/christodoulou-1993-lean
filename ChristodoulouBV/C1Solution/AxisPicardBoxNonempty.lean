module

public import ChristodoulouBV.C1Solution.AxisPicardBox
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Initial point of the axis Picard box

The product jet induced by the two edge traces is the initial point for the
axis Picard iteration. The derivatives of its fields are coordinate lifts of
the one-dimensional edge derivatives.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Global `C¹` representatives of the two edge traces, with the local bounds
used to initialize the axis Picard box. -/
structure EdgeData (a b M : ℝ) (g hEdge : ℝ → ℝ) where
  /-- Outgoing edge regularity. -/
  g_c1 : ContDiff ℝ 1 g
  /-- Scalar edge regularity. -/
  h_c1 : ContDiff ℝ 1 hEdge
  /-- Lower outgoing edge bound. -/
  g_lower : ∀ v ∈ Icc a b, 3 / 8 ≤ g v
  /-- Upper outgoing edge bound. -/
  g_upper : ∀ v ∈ Icc a b, g v ≤ 5 / 8
  /-- Outgoing edge derivative bound. -/
  g_deriv_bound : ∀ v ∈ Icc a b, |deriv g v| ≤ M
  /-- Scalar edge value bound. -/
  h_bound : ∀ v ∈ Icc a b, |hEdge v| ≤ M
  /-- Scalar edge derivative bound. -/
  h_deriv_bound : ∀ v ∈ Icc a b, |deriv hEdge v| ≤ M

/-- The three uniterated fields determined by the prescribed edge traces. -/
@[expose] def EdgeData.baseTriple {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (_D : EdgeData a b M g hEdge) : Triple :=
  { lam := fun p => g p.2, nu := fun p => -g p.1, h := fun p => hEdge p.2 }

/-- The base outgoing field is `C¹` on the triangle. -/
theorem EdgeData.base_lam_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) :
    ContDiffOn ℝ 1 D.baseTriple.lam (closedCoordTriangle a b) := by
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => g p.2) :=
    D.g_c1.comp contDiff_snd
  exact h.contDiffOn

/-- The base incoming field is `C¹` on the triangle. -/
theorem EdgeData.base_nu_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) :
    ContDiffOn ℝ 1 D.baseTriple.nu (closedCoordTriangle a b) := by
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => -g p.1) :=
    (D.g_c1.comp contDiff_fst).neg
  exact h.contDiffOn

/-- The base scalar field is `C¹` on the triangle. -/
theorem EdgeData.base_h_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) :
    ContDiffOn ℝ 1 D.baseTriple.h (closedCoordTriangle a b) := by
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => hEdge p.2) :=
    D.h_c1.comp contDiff_snd
  exact h.contDiffOn

/-- The relative first jet of a function lifted along the upper coordinate. -/
theorem fderivWithin_upper_lift {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => g q.2)
      (closedCoordTriangle a b) p) e =
      (fderiv ℝ g p.2) e.2 := by
  have hunique : UniqueDiffWithinAt ℝ (closedCoordTriangle a b) p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)) p hp
  have houter : HasFDerivAt g (fderiv ℝ g p.2) p.2 :=
    (hg p.2).hasFDerivAt
  have hinner : HasFDerivAt (fun q : ℝ × ℝ => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hcomp := houter.comp p hinner
  have heq := hcomp.hasFDerivWithinAt.fderivWithin hunique
  simpa [Function.comp_def] using congrArg (fun L => L e) heq

/-- The relative first jet of the negative lower-coordinate lift. -/
theorem fderivWithin_neg_lower_lift {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => -g q.1)
      (closedCoordTriangle a b) p) e =
      -(fderiv ℝ g p.1) e.1 := by
  have hunique : UniqueDiffWithinAt ℝ (closedCoordTriangle a b) p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)) p hp
  have houter : HasFDerivAt g (fderiv ℝ g p.1) p.1 :=
    (hg p.1).hasFDerivAt
  have hinner : HasFDerivAt (fun q : ℝ × ℝ => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hcomp := (houter.comp p hinner).neg
  have heq := hcomp.hasFDerivWithinAt.fderivWithin hunique
  have hfun : (-g ∘ Prod.fst : ℝ × ℝ → ℝ) =
      (fun q : ℝ × ℝ => -g q.1) := by
    funext q
    rfl
  rw [hfun] at heq
  simpa [Function.comp_def] using
    congrArg (fun L => L e) heq

/-- A one-dimensional derivative bound controls both coordinate components
of its upper-coordinate lift. -/
theorem upper_lift_coordinate_bound {a b M : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hM : 0 ≤ M) (hderiv : |deriv g p.2| ≤ M) (i : Fin 2) :
    |(fderivWithin ℝ (fun q : ℝ × ℝ => g q.2)
      (closedCoordTriangle a b) p) (coordinateDirection i)| ≤ M := by
  rw [fderivWithin_upper_lift hab hg hp]
  fin_cases i
  · simp [coordinateDirection, hM]
  · simpa [coordinateDirection, fderiv_eq_deriv_mul] using hderiv

/-- The negative lower-coordinate lift has the same coordinate bound. -/
theorem neg_lower_lift_coordinate_bound {a b M : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hM : 0 ≤ M) (hderiv : |deriv g p.1| ≤ M) (i : Fin 2) :
    |(fderivWithin ℝ (fun q : ℝ × ℝ => -g q.1)
      (closedCoordTriangle a b) p) (coordinateDirection i)| ≤ M := by
  rw [fderivWithin_neg_lower_lift hab hg hp]
  fin_cases i
  · simpa [coordinateDirection, fderiv_eq_deriv_mul] using hderiv
  · simp [coordinateDirection, hM]

/-- The base fields as elements of the complete triple-jet space. -/
@[expose] def EdgeData.baseJets {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b) : TripleJet a b :=
  (ScalarJet.ofContDiffOn hab D.baseTriple.lam D.base_lam_c1,
    ScalarJet.ofContDiffOn hab D.baseTriple.nu D.base_nu_c1,
    ScalarJet.ofContDiffOn hab D.baseTriple.h D.base_h_c1)

/-- The base outgoing jet stores the prescribed upper-coordinate trace. -/
@[simp] theorem EdgeData.baseJets_lam_value {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b)
    (p : closedCoordTriangle a b) :
    (D.baseJets hab).1.1.1 p = g p.1.2 := by
  exact ScalarJet.ofContDiffOn_value hab D.baseTriple.lam D.base_lam_c1 p

/-- The base incoming jet stores the negative lower-coordinate trace. -/
@[simp] theorem EdgeData.baseJets_nu_value {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b)
    (p : closedCoordTriangle a b) :
    (D.baseJets hab).2.1.1.1 p = -g p.1.1 := by
  exact ScalarJet.ofContDiffOn_value hab D.baseTriple.nu D.base_nu_c1 p

/-- The base scalar jet stores the prescribed upper-coordinate trace. -/
@[simp] theorem EdgeData.baseJets_h_value {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b)
    (p : closedCoordTriangle a b) :
    (D.baseJets hab).2.2.1.1 p = hEdge p.1.2 := by
  exact ScalarJet.ofContDiffOn_value hab D.baseTriple.h D.base_h_c1 p

/-- Both coordinate components of the base outgoing jet obey the box bound. -/
theorem EdgeData.baseJets_lam_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 0 ≤ M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(D.baseJets hab).1.1.2 p (coordinateDirection i)| ≤ 2 * M := by
  have hp : p.1 ∈ closedCoordTriangle a b := p.2
  have hv : p.1.2 ∈ Icc a b := by
    change a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ b at hp
    exact ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hb := upper_lift_coordinate_bound hab
    (D.g_c1.differentiable (by norm_num)) p.2 hM (D.g_deriv_bound _ hv) i
  change |(ScalarJet.ofContDiffOn hab D.baseTriple.lam D.base_lam_c1).1.2 p
    (coordinateDirection i)| ≤ 2 * M
  rw [ScalarJet.ofContDiffOn_derivative]
  exact hb.trans (by linarith)

/-- Both coordinate components of the base incoming jet obey the box bound. -/
theorem EdgeData.baseJets_nu_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 0 ≤ M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(D.baseJets hab).2.1.1.2 p (coordinateDirection i)| ≤ 2 * M := by
  have hp : p.1 ∈ closedCoordTriangle a b := p.2
  have hu : p.1.1 ∈ Icc a b := by
    change a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ b at hp
    exact ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hb := neg_lower_lift_coordinate_bound hab
    (D.g_c1.differentiable (by norm_num)) p.2 hM (D.g_deriv_bound _ hu) i
  change |(ScalarJet.ofContDiffOn hab D.baseTriple.nu D.base_nu_c1).1.2 p
    (coordinateDirection i)| ≤ 2 * M
  rw [ScalarJet.ofContDiffOn_derivative]
  exact hb.trans (by linarith)

/-- Both coordinate components of the base scalar jet obey the box bound. -/
theorem EdgeData.baseJets_h_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 0 ≤ M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(D.baseJets hab).2.2.1.2 p (coordinateDirection i)| ≤ 2 * M := by
  have hp : p.1 ∈ closedCoordTriangle a b := p.2
  have hv : p.1.2 ∈ Icc a b := by
    change a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ b at hp
    exact ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hb := upper_lift_coordinate_bound hab
    (D.h_c1.differentiable (by norm_num)) p.2 hM (D.h_deriv_bound _ hv) i
  change |(ScalarJet.ofContDiffOn hab D.baseTriple.h D.base_h_c1).1.2 p
    (coordinateDirection i)| ≤ 2 * M
  rw [ScalarJet.ofContDiffOn_derivative]
  exact hb.trans (by linarith)

/-- The uniterated trace fields satisfy every physical Picard-box
constraint, including both coordinate jet bounds. -/
theorem EdgeData.baseJets_isInBox {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b) (hM : 1 ≤ M) :
    IsInBox a b M g hEdge (D.baseJets hab) := by
  unfold IsInBox
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    have hp : a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ b := p.2
    have hu : p.1.1 ∈ Icc a b := ⟨hp.1, hp.2.1.trans hp.2.2⟩
    have hv : p.1.2 ∈ Icc a b := ⟨hp.1.trans hp.2.1, hp.2.2⟩
    have hgl := D.g_lower _ hv
    have hgu := D.g_upper _ hv
    have hgu' := D.g_upper _ hu
    have hgl' := D.g_lower _ hu
    have hh := D.h_bound _ hv
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [D.baseJets_lam_value hab p]
      linarith
    · rw [D.baseJets_lam_value hab p]
      linarith
    · rw [D.baseJets_nu_value hab p, abs_neg, abs_of_nonneg (by linarith : 0 ≤ g p.1.1)]
      linarith
    · rw [D.baseJets_h_value hab p]
      linarith
    · intro i
      exact ⟨D.baseJets_lam_coordinate_bound hab (by linarith) p i,
        D.baseJets_nu_coordinate_bound hab (by linarith) p i,
        D.baseJets_h_coordinate_bound hab (by linarith) p i⟩
  · intro v
    simpa only [D.baseJets_lam_value hab (edgePoint v)] using
      (show g (edgePoint v).1.2 = g v.1 from rfl)
  · intro v
    simpa only [D.baseJets_h_value hab (edgePoint v)] using
      (show hEdge (edgePoint v).1.2 = hEdge v.1 from rfl)
  · intro u
    rw [D.baseJets_nu_value hab (diagonalPoint u),
      D.baseJets_lam_value hab (diagonalPoint u)]
    rfl

/-- The base triple also satisfies the public segment identities. -/
theorem EdgeData.baseJets_isAdmissible {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M) :
    IsAdmissible a b M g hEdge (D.baseJets hab) := by
  unfold IsAdmissible
  exact ⟨D.baseJets_isInBox hab hM,
    ScalarJet.ofContDiffOn_explicit hab D.baseTriple.lam D.base_lam_c1,
    ScalarJet.ofContDiffOn_explicit hab D.baseTriple.nu D.base_nu_c1,
    ScalarJet.ofContDiffOn_explicit hab D.baseTriple.h D.base_h_c1⟩

/-- Globally `C¹` edge representatives with the prescribed local bounds
give an explicit starting point in the complete Picard box. -/
theorem EdgeData.nonempty_box {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (hab : a < b) (hM : 1 ≤ M) :
    Nonempty (Box a b M g hEdge) :=
  ⟨⟨D.baseJets hab, D.baseJets_isAdmissible hab hM⟩⟩

end ChristodoulouBV.AxisPicard

end
