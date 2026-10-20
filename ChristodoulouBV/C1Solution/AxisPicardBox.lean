module

public import ChristodoulouBV.C1Solution.AxisPicard
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.SegmentJetDeriv
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanIntegral
import Mathlib.Tactic

/-!
# The closed axis Picard box

The box records the edge traces, the regular-axis relation, the value
intervals, and the bounds on both coordinate components of all three jets.
Its closedness follows from continuity of evaluation in the uniform jet norm.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The two coordinate directions of the axis triangle. -/
@[expose] def coordinateDirection (i : Fin 2) : ℝ × ℝ :=
  if i = 0 then (1, 0) else (0, 1)

/-- A point of the outgoing edge, regarded as a point of the closed triangle. -/
@[expose] def edgePoint {a b : ℝ} (v : Icc a b) : closedCoordTriangle a b :=
  ⟨(a, v.1), by
    change a ≤ a ∧ a ≤ v.1 ∧ v.1 ≤ b
    exact ⟨le_refl _, v.2.1, v.2.2⟩⟩

/-- A point of the regular axis, regarded as a point of the closed triangle. -/
@[expose] def diagonalPoint {a b : ℝ} (u : Icc a b) : closedCoordTriangle a b :=
  ⟨(u.1, u.1), by
    change a ≤ u.1 ∧ u.1 ≤ u.1 ∧ u.1 ≤ b
    exact ⟨u.2.1, le_refl _, u.2.2⟩⟩

/-- The closed Picard box for the three value and derivative fields. -/
@[expose] def IsInBox (a b M : ℝ) (g hEdge : ℝ → ℝ)
    (x : TripleJet a b) : Prop :=
  (∀ p : closedCoordTriangle a b,
      (1 / 4 : ℝ) ≤ x.1.1.1 p ∧ x.1.1.1 p ≤ 3 / 4 ∧
      |x.2.1.1.1 p| ≤ 3 / 4 ∧ |x.2.2.1.1 p| ≤ 2 * M ∧
      ∀ i : Fin 2,
        |x.1.1.2 p (coordinateDirection i)| ≤ 2 * M ∧
        |x.2.1.1.2 p (coordinateDirection i)| ≤ 2 * M ∧
        |x.2.2.1.2 p (coordinateDirection i)| ≤ 2 * M) ∧
    (∀ v : Icc a b, x.1.1.1 (edgePoint v) = g v.1) ∧
    (∀ v : Icc a b, x.2.2.1.1 (edgePoint v) = hEdge v.1) ∧
    (∀ u : Icc a b,
      x.2.1.1.1 (diagonalPoint u) = -x.1.1.1 (diagonalPoint u))

/-- Membership in the Picard box is closed in the complete product jet space. -/
theorem isClosed_isInBox (a b M : ℝ) (g hEdge : ℝ → ℝ) :
    IsClosed {x : TripleJet a b | IsInBox a b M g hEdge x} := by
  have hpoint (p : closedCoordTriangle a b) :
      IsClosed {x : TripleJet a b |
        (1 / 4 : ℝ) ≤ x.1.1.1 p ∧ x.1.1.1 p ≤ 3 / 4 ∧
        |x.2.1.1.1 p| ≤ 3 / 4 ∧ |x.2.2.1.1 p| ≤ 2 * M ∧
        ∀ i : Fin 2,
          |x.1.1.2 p (coordinateDirection i)| ≤ 2 * M ∧
          |x.2.1.1.2 p (coordinateDirection i)| ≤ 2 * M ∧
          |x.2.2.1.2 p (coordinateDirection i)| ≤ 2 * M} := by
    simp only [ofPred_and, ofPred_forall]
    repeat' apply IsClosed.inter
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_le (by fun_prop) continuous_const
    · apply isClosed_iInter
      intro i
      repeat' apply IsClosed.inter
      · exact isClosed_le (by fun_prop) continuous_const
      · exact isClosed_le (by fun_prop) continuous_const
      · exact isClosed_le (by fun_prop) continuous_const
  have hedgeLam (v : Icc a b) :
      IsClosed {x : TripleJet a b | x.1.1.1 (edgePoint v) = g v.1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hedgeH (v : Icc a b) :
      IsClosed {x : TripleJet a b | x.2.2.1.1 (edgePoint v) = hEdge v.1} :=
    isClosed_eq (by fun_prop) continuous_const
  have haxis (u : Icc a b) :
      IsClosed {x : TripleJet a b |
        x.2.1.1.1 (diagonalPoint u) = -x.1.1.1 (diagonalPoint u)} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  change IsClosed {x : TripleJet a b |
    (∀ p : closedCoordTriangle a b,
      (1 / 4 : ℝ) ≤ x.1.1.1 p ∧ x.1.1.1 p ≤ 3 / 4 ∧
      |x.2.1.1.1 p| ≤ 3 / 4 ∧ |x.2.2.1.1 p| ≤ 2 * M ∧
      ∀ i : Fin 2,
        |x.1.1.2 p (coordinateDirection i)| ≤ 2 * M ∧
        |x.2.1.1.2 p (coordinateDirection i)| ≤ 2 * M ∧
        |x.2.2.1.2 p (coordinateDirection i)| ≤ 2 * M) ∧
    (∀ v : Icc a b, x.1.1.1 (edgePoint v) = g v.1) ∧
    (∀ v : Icc a b, x.2.2.1.1 (edgePoint v) = hEdge v.1) ∧
    (∀ u : Icc a b,
      x.2.1.1.1 (diagonalPoint u) = -x.1.1.1 (diagonalPoint u))}
  simpa only [ofPred_and, ofPred_forall] using
    ((isClosed_iInter hpoint).inter
      ((isClosed_iInter hedgeLam).inter
        ((isClosed_iInter hedgeH).inter (isClosed_iInter haxis))))

/-- The physical box constraints together with the public segment identities
needed for relative `C¹` calculus. -/
@[expose] def IsAdmissible (a b M : ℝ) (g hEdge : ℝ → ℝ)
    (x : TripleJet a b) : Prop :=
  IsInBox a b M g hEdge x ∧
    (convex_closedCoordTriangle a b).IsExplicitSegmentJet x.1.1 ∧
    (convex_closedCoordTriangle a b).IsExplicitSegmentJet x.2.1.1 ∧
    (convex_closedCoordTriangle a b).IsExplicitSegmentJet x.2.2.1

/-- The box with its explicit segment identities is closed. -/
theorem isClosed_isAdmissible (a b M : ℝ) (g hEdge : ℝ → ℝ) :
    IsClosed {x : TripleJet a b | IsAdmissible a b M g hEdge x} := by
  let hK := convex_closedCoordTriangle a b
  have hlam : IsClosed {x : TripleJet a b |
      hK.IsExplicitSegmentJet x.1.1} :=
    hK.isClosed_isExplicitSegmentJet.preimage (by fun_prop)
  have hnu : IsClosed {x : TripleJet a b |
      hK.IsExplicitSegmentJet x.2.1.1} :=
    hK.isClosed_isExplicitSegmentJet.preimage (by fun_prop)
  have hh : IsClosed {x : TripleJet a b |
      hK.IsExplicitSegmentJet x.2.2.1} :=
    hK.isClosed_isExplicitSegmentJet.preimage (by fun_prop)
  change IsClosed {x : TripleJet a b |
    IsInBox a b M g hEdge x ∧ hK.IsExplicitSegmentJet x.1.1 ∧
    hK.IsExplicitSegmentJet x.2.1.1 ∧ hK.IsExplicitSegmentJet x.2.2.1}
  simpa only [ofPred_and] using
    (isClosed_isInBox a b M g hEdge).inter (hlam.inter (hnu.inter hh))

/-- The complete closed box used by the axis Picard iteration. -/
abbrev Box (a b M : ℝ) (g hEdge : ℝ → ℝ) :=
  {x : TripleJet a b // IsAdmissible a b M g hEdge x}

/-- The closed Picard box is complete. -/
instance boxComplete (a b M : ℝ) (g hEdge : ℝ → ℝ) :
    CompleteSpace (Box a b M g hEdge) :=
  ((isClosed_isAdmissible a b M g hEdge).isComplete).completeSpace_coe

/-- A total derivative representative of a scalar triangle jet, using zero
outside the triangle. -/
@[expose] def ScalarJet.extendDerivative {a b : ℝ} (f : ScalarJet a b)
    (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ := by
  classical
  exact if hp : p ∈ closedCoordTriangle a b then f.1.2 ⟨p, hp⟩ else 0

/-- On the triangle, the total derivative representative is the stored jet. -/
theorem ScalarJet.extendDerivative_eq {a b : ℝ} (f : ScalarJet a b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    f.extendDerivative p = f.1.2 ⟨p, hp⟩ := by
  simp [ScalarJet.extendDerivative, hp]

/-- An explicit scalar segment jet has the stored derivative at every point
of the closed triangle. -/
theorem ScalarJet.hasFDerivWithinAt_of_explicit {a b : ℝ}
    (f : ScalarJet a b)
    (hexplicit : (convex_closedCoordTriangle a b).IsExplicitSegmentJet f.1)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    HasFDerivWithinAt f.extendValue (f.extendDerivative p)
      (closedCoordTriangle a b) p :=
  (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_explicitSegmentJet
    f.1 hexplicit
    (fun x => (f.extendValue_eq x.2))
    (fun x => (f.extendDerivative_eq x.2)) hp

/-- An explicit scalar segment jet is relatively `C¹` on the whole triangle. -/
theorem ScalarJet.contDiffOn_of_explicit {a b : ℝ}
    (f : ScalarJet a b)
    (hexplicit : (convex_closedCoordTriangle a b).IsExplicitSegmentJet f.1) :
    ContDiffOn ℝ 1 f.extendValue (closedCoordTriangle a b) :=
  (convex_closedCoordTriangle a b).contDiffOn_one_of_explicitSegmentJet
    f.1 hexplicit
    (fun x => f.extendValue_eq x.2)
    (fun x => f.extendDerivative_eq x.2)

/-- The outgoing derivative field of a boxed triple has continuous full
first jets on the closed axis triangle. -/
theorem Box.lam_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) :
    ContDiffOn ℝ 1 x.1.1.extendValue (closedCoordTriangle a b) :=
  x.1.1.contDiffOn_of_explicit x.2.2.1

/-- The incoming derivative field of a boxed triple has continuous full
first jets on the closed axis triangle. -/
theorem Box.nu_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) :
    ContDiffOn ℝ 1 x.1.2.1.extendValue (closedCoordTriangle a b) :=
  x.1.2.1.contDiffOn_of_explicit x.2.2.2.1

/-- The normalized scalar field of a boxed triple has continuous full
first jets on the closed axis triangle. -/
theorem Box.h_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) :
    ContDiffOn ℝ 1 x.1.2.2.extendValue (closedCoordTriangle a b) :=
  x.1.2.2.contDiffOn_of_explicit x.2.2.2.2

/-- A horizontal component bound for a continuous triangle jet controls
variation from the outgoing edge at fixed upper coordinate. -/
theorem norm_sub_horizontal_le_of_jet {a b B : ℝ} {f : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (G p) (closedCoordTriangle a b) p)
    (hbound : ∀ p ∈ closedCoordTriangle a b, ‖G p (1, 0)‖ ≤ B)
    {u v : ℝ} (ha : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    ‖f (u, v) - f (a, v)‖ ≤ B * (u - a) := by
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc a u)
      (closedCoordTriangle a b) := by
    intro t ht
    change a ≤ t ∧ t ≤ v ∧ v ≤ b
    exact ⟨ht.1, ht.2.trans huv, hv⟩
  have hderiv : ∀ t ∈ Icc a u,
      HasDerivWithinAt (fun t : ℝ => f (t, v)) (G (t, v) (1, 0))
        (Icc a u) t := by
    intro t ht
    have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) t := by
      exact (hasDerivAt_id' t).prodMk (hasDerivAt_const t v)
    simpa only [Function.comp_def] using
      (hjet (t, v) (hmap ht)).comp_hasDerivWithinAt t
        hpair.hasDerivWithinAt hmap
  have hb : ∀ t ∈ Icc a u, ‖G (t, v) (1, 0)‖ ≤ B := by
    intro t ht
    exact hbound (t, v) (hmap ht)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hb
    (convex_Icc a u) ⟨le_refl a, ha⟩ ⟨ha, le_refl u⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha)] using h

/-- The outgoing field has the box's two coordinate derivative bounds. -/
theorem Box.lam_coordinate_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (i : Fin 2) :
    |(x.1.1.extendDerivative p) (coordinateDirection i)| ≤ 2 * M := by
  have hbox := x.2.1
  unfold IsInBox at hbox
  have h := ((hbox.1 ⟨p, hp⟩).2.2.2.2 i).1
  simpa only [x.1.1.extendDerivative_eq hp] using h

/-- The incoming field has the box's two coordinate derivative bounds. -/
theorem Box.nu_coordinate_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (i : Fin 2) :
    |(x.1.2.1.extendDerivative p) (coordinateDirection i)| ≤ 2 * M := by
  have hbox := x.2.1
  unfold IsInBox at hbox
  have h := ((hbox.1 ⟨p, hp⟩).2.2.2.2 i).2.1
  simpa only [x.1.2.1.extendDerivative_eq hp] using h

/-- The outgoing field takes its prescribed value on the initial edge. -/
theorem Box.lam_edge {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (v : Icc a b) :
    x.1.1.extendValue (a, v.1) = g v.1 := by
  have hbox := x.2.1
  unfold IsInBox at hbox
  calc
    x.1.1.extendValue (a, v.1) = x.1.1.extendValue (edgePoint v).1 := rfl
    _ = x.1.1.1.1 (edgePoint v) := x.1.1.extendValue_eq (edgePoint v).2
    _ = g v.1 := hbox.2.1 v

/-- The incoming field is the negative outgoing field on the axis. -/
theorem Box.nu_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (u : Icc a b) :
    x.1.2.1.extendValue (u.1, u.1) =
      -x.1.1.extendValue (u.1, u.1) := by
  have hbox := x.2.1
  unfold IsInBox at hbox
  calc
    x.1.2.1.extendValue (u.1, u.1) =
        x.1.2.1.1.1 (diagonalPoint u) :=
      x.1.2.1.extendValue_eq (diagonalPoint u).2
    _ = -x.1.1.1.1 (diagonalPoint u) := hbox.2.2.2 u
    _ = -x.1.1.extendValue (u.1, u.1) :=
      congrArg Neg.neg (x.1.1.extendValue_eq (diagonalPoint u).2).symm

/-- The edge trace and both coordinate jet bounds force the incoming field
below `-1/4` throughout the input box at the explicit lifetime. -/
theorem Box.nu_le_neg_quarter {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    x.1.2.1.extendValue p ≤ -(1 / 4 : ℝ) := by
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  let u : Icc a b := ⟨p.1, hcoord.1, hcoord.2.1.trans hcoord.2.2⟩
  have hlamJet : ∀ q ∈ closedCoordTriangle a b,
      HasFDerivWithinAt x.1.1.extendValue (x.1.1.extendDerivative q)
        (closedCoordTriangle a b) q := by
    intro q hq
    exact x.1.1.hasFDerivWithinAt_of_explicit x.2.2.1 hq
  have hnuJet : ∀ q ∈ closedCoordTriangle a b,
      HasFDerivWithinAt x.1.2.1.extendValue (x.1.2.1.extendDerivative q)
        (closedCoordTriangle a b) q := by
    intro q hq
    exact x.1.2.1.hasFDerivWithinAt_of_explicit x.2.2.2.1 hq
  have hlamBound : ∀ q ∈ closedCoordTriangle a b,
      ‖(x.1.1.extendDerivative q) (1, 0)‖ ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection, Real.norm_eq_abs] using
      x.lam_coordinate_bound hq (0 : Fin 2)
  have hnuBound : ∀ q ∈ closedCoordTriangle a b,
      ‖(x.1.2.1.extendDerivative q) (0, 1)‖ ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection, Real.norm_eq_abs] using
      x.nu_coordinate_bound hq (1 : Fin 2)
  have hlam := norm_sub_horizontal_le_of_jet hlamJet hlamBound
    hcoord.1 (le_refl p.1) (hcoord.2.1.trans hcoord.2.2)
  have hnu := intervalIntegral.norm_sub_vertical_le_of_jet hnuJet hnuBound
    hcoord.1 (le_refl p.1) hcoord.2.1 hcoord.2.2
  have hlamAbs : |x.1.1.extendValue (p.1, p.1) - g p.1| ≤
      2 * M * (p.1 - a) := by
    rw [x.lam_edge u] at hlam
    simpa only [Real.norm_eq_abs] using hlam
  have hnuAbs : |x.1.2.1.extendValue p +
      x.1.1.extendValue (p.1, p.1)| ≤ 2 * M * (p.2 - p.1) := by
    rw [x.nu_axis u] at hnu
    simpa only [Real.norm_eq_abs, sub_neg_eq_add] using hnu
  have hvariation : x.1.2.1.extendValue p + g p.1 ≤
      2 * M * (b - a) := by
    have h₁ := (abs_le.mp hnuAbs).2
    have h₂ := (abs_le.mp hlamAbs).1
    calc
      x.1.2.1.extendValue p + g p.1 =
          (x.1.2.1.extendValue p + x.1.1.extendValue (p.1, p.1)) +
            (g p.1 - x.1.1.extendValue (p.1, p.1)) := by ring
      _ ≤ 2 * M * (p.2 - p.1) + 2 * M * (p.1 - a) := by linarith
      _ = 2 * M * (p.2 - a) := by ring
      _ ≤ 2 * M * (b - a) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  exact input_nu_le_neg_quarter hM (sub_pos.mpr hab) hsmall
    (hg p.1 u.2) hvariation

/-- Restricting a relatively `C¹` scalar field and its relative derivative
produces a bounded continuous segment jet on the compact triangle. -/
@[expose] noncomputable def ScalarJet.ofContDiffOn {a b : ℝ} (hab : a < b)
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b)) :
    ScalarJet a b := by
  let K := closedCoordTriangle a b
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedCoordTriangle a b)
  have hK := convex_closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex hK (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty hab)
  have hG : ContinuousOn (fderivWithin ℝ f K) K :=
    hf.continuousOn_fderivWithin hunique (by norm_num)
  let fBCF : BoundedContinuousFunction K ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun p : K => f p.1, continuousOn_iff_continuous_domRestrict.mp hf.continuousOn⟩
  let GBCF : BoundedContinuousFunction K ((ℝ × ℝ) →L[ℝ] ℝ) :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun p : K => fderivWithin ℝ f K p.1,
        continuousOn_iff_continuous_domRestrict.mp hG⟩
  have hderiv : ∀ p ∈ interior K,
      fderiv ℝ f p = fderivWithin ℝ f K p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  refine ⟨(fBCF, GBCF), ?_⟩
  exact hK.isContinuousSegmentJet_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hf.continuousOn hG
    (hf.differentiableOn_one.mono interior_subset) hderiv (fBCF, GBCF)
    (by intro p; rfl) (by intro p; rfl)

/-- The restricted `C¹` jet also satisfies the public explicit segment
identity used by the Picard box. -/
theorem ScalarJet.ofContDiffOn_explicit {a b : ℝ} (hab : a < b)
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b)) :
    (convex_closedCoordTriangle a b).IsExplicitSegmentJet
      (ScalarJet.ofContDiffOn hab f hf).1 := by
  let K := closedCoordTriangle a b
  let hK := convex_closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex hK (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty hab)
  have hG : ContinuousOn (fderivWithin ℝ f K) K :=
    hf.continuousOn_fderivWithin hunique (by norm_num)
  intro x y
  have hsegment := hK.sub_eq_integral_fderivWithin hf.continuousOn hG
    (fun p hp => (hf.differentiableOn_one p hp).hasFDerivWithinAt) x.2 y.2
  change f y.1 - f x.1 =
    ∫ t in (0 : ℝ)..1,
      (fderivWithin ℝ f K)
        (hK.clampedSegmentPoint x y t) (y.1 - x.1)
  rw [hsegment]
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  change (fderivWithin ℝ f K (x.1 + t • (y.1 - x.1))) (y.1 - x.1) =
    (fderivWithin ℝ f K (hK.clampedSegmentPoint x y t)) (y.1 - x.1)
  rw [hK.clampedSegmentPoint_val_of_mem x y htI]

/-- The value component of the restricted jet is the original field. -/
@[simp] theorem ScalarJet.ofContDiffOn_value {a b : ℝ} (hab : a < b)
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (p : closedCoordTriangle a b) :
    (ScalarJet.ofContDiffOn hab f hf).1.1 p = f p.1 := by
  rfl

/-- The derivative component of the restricted jet is the relative
Fréchet derivative of the original field. -/
@[simp] theorem ScalarJet.ofContDiffOn_derivative {a b : ℝ} (hab : a < b)
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (p : closedCoordTriangle a b) :
    (ScalarJet.ofContDiffOn hab f hf).1.2 p =
      fderivWithin ℝ f (closedCoordTriangle a b) p.1 := by
  rfl

end ChristodoulouBV.AxisPicard

end
