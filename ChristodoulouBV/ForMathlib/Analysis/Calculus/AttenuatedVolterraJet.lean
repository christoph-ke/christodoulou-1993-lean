module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterra
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraRadiusJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Continuous first jets of attenuated Volterra integrals

The integrating-factor representation reduces the two-coordinate calculus
to the closed-triangle primitive theorem. The formulas include the diagonal
and the two vertices.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The integral of the attenuation kernel from the diagonal. -/
@[expose] noncomputable def attenuatedVolterraPotential
    (k : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  weightedDiagonalRadius k p

/-- The source after multiplication by the integrating factor. -/
@[expose] noncomputable def attenuatedVolterraWeightedSource
    (j k : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  j p * Real.exp (attenuatedVolterraPotential k p)

/-- The attenuation from `s` to `v` is the difference of the potentials
at `v` and `s`. -/
theorem integral_attenuation_eq_potential_sub
    {a b u s v : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b) :
    (∫ t in s..v, k (u, t)) =
      attenuatedVolterraPotential k (u, v) -
        attenuatedVolterraPotential k (u, s) := by
  have hi₁ : IntervalIntegrable (fun t => k (u, t)) volume u s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hus
    exact hk.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro t ht
      exact ⟨hu, ht.1, ht.2.trans (hsv.trans hv)⟩)
  have hi₂ : IntervalIntegrable (fun t => k (u, t)) volume s v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hsv
    exact hk.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro t ht
      exact ⟨hu, hus.trans ht.1, ht.2.trans hv⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  simp only [attenuatedVolterraPotential, weightedDiagonalRadius]
  linarith only [hadd]

/-- Integrating-factor representation of the attenuated Volterra integral. -/
theorem attenuatedVolterraIntegral_eq_exp_mul_radius
    {a b u v : ℝ} {j k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    attenuatedVolterraIntegral j k u v =
      Real.exp (-attenuatedVolterraPotential k (u, v)) *
        weightedDiagonalRadius (attenuatedVolterraWeightedSource j k) (u, v) := by
  let Q := attenuatedVolterraPotential k
  have hfactor (s : ℝ) (hs : s ∈ Icc u v) :
      Real.exp (-(∫ t in s..v, k (u, t))) =
        Real.exp (-Q (u, v)) * Real.exp (Q (u, s)) := by
    rw [integral_attenuation_eq_potential_sub hk hu hs.1 hs.2 hv]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [attenuatedVolterraIntegral, weightedDiagonalRadius,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc u v := by
    simpa only [uIcc_of_le huv] using hs
  change j (u, s) * Real.exp (-(∫ t in s..v, k (u, t))) =
    Real.exp (-Q (u, v)) *
      (j (u, s) * Real.exp (Q (u, s)))
  rw [hfactor s hs']
  ring

/-- The diagonal potential is continuously differentiable when its kernel
has a continuous first jet on the closed triangle. -/
theorem contDiffOn_attenuatedVolterraPotential
    {a b : ℝ} (hab : a < b) {k : ℝ × ℝ → ℝ}
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b)) :
    ContDiffOn ℝ 1 (attenuatedVolterraPotential k)
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG := hk.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ k (interior K) :=
    (hk.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K, fderiv ℝ k p = fderivWithin ℝ k K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv
      (hunique p (interior_subset hp))
      ((hdiff p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  change ContDiffOn ℝ 1 (weightedDiagonalRadius k) K
  exact contDiffOn_weightedDiagonalRadius hab hk.continuousOn hG hdiff hderiv

/-- The source multiplied by the integrating factor has a continuous first
jet on the same closed triangle. -/
theorem contDiffOn_attenuatedVolterraWeightedSource
    {a b : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b)) :
    ContDiffOn ℝ 1 (attenuatedVolterraWeightedSource j k)
      (closedCoordTriangle a b) := by
  have hQ := contDiffOn_attenuatedVolterraPotential hab hk
  change ContDiffOn ℝ 1
    (fun p => j p * Real.exp (attenuatedVolterraPotential k p))
    (closedCoordTriangle a b)
  exact hj.mul (Real.contDiff_exp.contDiffOn.comp hQ (Set.mapsTo_univ _ _))

/-- An attenuated Volterra integral has a continuous first jet on a
nondegenerate closed coordinate triangle. -/
theorem contDiffOn_attenuatedVolterraIntegral
    {a b : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      attenuatedVolterraIntegral j k p.1 p.2) (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let F := attenuatedVolterraWeightedSource j k
  have hF := contDiffOn_attenuatedVolterraWeightedSource hab hj hk
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG := hF.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ F (interior K) :=
    (hF.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K, fderiv ℝ F p = fderivWithin ℝ F K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv
      (hunique p (interior_subset hp))
      ((hdiff p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hP := contDiffOn_weightedDiagonalRadius hab hF.continuousOn hG hdiff hderiv
  have hQ := contDiffOn_attenuatedVolterraPotential hab hk
  have hproduct : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      Real.exp (-attenuatedVolterraPotential k p) *
        weightedDiagonalRadius F p) K :=
    (Real.contDiff_exp.contDiffOn.comp hQ.neg (Set.mapsTo_univ _ _)).mul hP
  apply hproduct.congr
  intro p hp
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  exact attenuatedVolterraIntegral_eq_exp_mul_radius (j := j) hk.continuousOn
    hcoord.1 hcoord.2.1 hcoord.2.2

/-- The vertical jet formula for a primitive of a closed-triangle `C¹` function. -/
theorem radius_vertical_jet_of_contDiffOn
    {a b : ℝ} (hab : a < b) {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalRadius f) (closedCoordTriangle a b) p) (0, 1) =
      f p := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG := hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) :=
    (hf.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K, fderiv ℝ f p = fderivWithin ℝ f K p := by
    intro q hq
    exact (fderivWithin_eq_fderiv
      (hunique q (interior_subset hq))
      ((hdiff q hq).differentiableAt (isOpen_interior.mem_nhds hq))).symm
  exact (fderivWithin_weightedDiagonalRadius_apply hab hf.continuousOn hG
    hdiff hderiv hp).2

/-- The horizontal jet formula for a primitive of a closed-triangle `C¹` function. -/
theorem radius_horizontal_jet_of_contDiffOn
    {a b : ℝ} (hab : a < b) {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalRadius f) (closedCoordTriangle a b) p) (1, 0) =
      -f (p.1, p.1) +
        ∫ s in p.1..p.2,
          (fderivWithin ℝ f (closedCoordTriangle a b) (p.1, s)) (1, 0) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG := hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) :=
    (hf.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ q ∈ interior K, fderiv ℝ f q = fderivWithin ℝ f K q := by
    intro q hq
    exact (fderivWithin_eq_fderiv
      (hunique q (interior_subset hq))
      ((hdiff q hq).differentiableAt (isOpen_interior.mem_nhds hq))).symm
  exact (fderivWithin_weightedDiagonalRadius_apply hab hf.continuousOn hG
    hdiff hderiv hp).1

/-- The vertical first jet of the attenuated integral satisfies the linear
Volterra differential equation, including the diagonal and triangle corners. -/
theorem fderivWithin_attenuatedVolterraIntegral_vertical
    {a b : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (fun z : ℝ × ℝ =>
      attenuatedVolterraIntegral j k z.1 z.2)
      (closedCoordTriangle a b) p) (0, 1) =
      j p - k p * attenuatedVolterraIntegral j k p.1 p.2 := by
  let K := closedCoordTriangle a b
  let Q := attenuatedVolterraPotential k
  let F := attenuatedVolterraWeightedSource j k
  let P := weightedDiagonalRadius F
  let E : ℝ × ℝ → ℝ := fun z => Real.exp (-Q z)
  let J : ℝ × ℝ → ℝ := fun z => attenuatedVolterraIntegral j k z.1 z.2
  have hQ := contDiffOn_attenuatedVolterraPotential hab hk
  have hF := contDiffOn_attenuatedVolterraWeightedSource hab hj hk
  have hJ := contDiffOn_attenuatedVolterraIntegral hab hj hk
  have hP : ContDiffOn ℝ 1 P K := by
    let G := fderivWithin ℝ F K
    have hunique : UniqueDiffOn ℝ K :=
      uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    have hG := hF.continuousOn_fderivWithin hunique (by norm_num)
    have hdiff : DifferentiableOn ℝ F (interior K) :=
      (hF.differentiableOn (by norm_num)).mono interior_subset
    have hderiv : ∀ q ∈ interior K, fderiv ℝ F q = G q := by
      intro q hq
      exact (fderivWithin_eq_fderiv
        (hunique q (interior_subset hq))
        ((hdiff q hq).differentiableAt (isOpen_interior.mem_nhds hq))).symm
    exact contDiffOn_weightedDiagonalRadius hab hF.continuousOn hG hdiff hderiv
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hQdiff : DifferentiableWithinAt ℝ Q K p :=
    hQ.differentiableOn (by norm_num) p hp
  have hPdiff : DifferentiableWithinAt ℝ P K p :=
    hP.differentiableOn (by norm_num) p hp
  have hEdiff : DifferentiableWithinAt ℝ E K p := hQdiff.neg.exp
  have hEq : EqOn J (fun z => E z * P z) K := by
    intro z hz
    have hz' : a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := hz
    exact attenuatedVolterraIntegral_eq_exp_mul_radius (j := j) hk.continuousOn
      hz'.1 hz'.2.1 hz'.2.2
  have hJderiv : fderivWithin ℝ J K p = fderivWithin ℝ (fun z => E z * P z) K p :=
    fderivWithin_congr' hEq hp
  have hEderiv : fderivWithin ℝ E K p =
      Real.exp (-Q p) • -(fderivWithin ℝ Q K p) := by
    simpa only [E, Pi.neg_apply] using
      (fderivWithin_exp hQdiff.neg hunique).trans
        (by rw [fderivWithin_neg hunique]; rfl)
  have hPv : (fderivWithin ℝ P K p) (0, 1) = F p :=
    radius_vertical_jet_of_contDiffOn hab hF hp
  have hQv : (fderivWithin ℝ Q K p) (0, 1) = k p :=
    radius_vertical_jet_of_contDiffOn hab hk hp
  have hJval : J p = E p * P p := hEq hp
  have hFval : F p = j p * Real.exp (Q p) := rfl
  have hExp : Real.exp (-Q p) * Real.exp (Q p) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hJderiv]
  change (fderivWithin ℝ (E * P) K p) (0, 1) = _
  rw [fderivWithin_mul hunique hEdiff hPdiff, hEderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [neg_apply]
  rw [hPv, hQv]
  simp only [hFval]
  rw [show attenuatedVolterraIntegral j k p.1 p.2 = E p * P p from hJval]
  dsimp [E]
  calc
    _ = j p * (Real.exp (-Q p) * Real.exp (Q p)) -
          k p * (Real.exp (-Q p) * P p) := by ring
    _ = _ := by rw [hExp]; ring

/-- The horizontal first jet in integrating-factor form. This formula
holds on the entire closed triangle without a vanishing-diagonal premise. -/
theorem fderivWithin_attenuatedVolterraIntegral_horizontal_factor
    {a b : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (fun z : ℝ × ℝ =>
      attenuatedVolterraIntegral j k z.1 z.2)
      (closedCoordTriangle a b) p) (1, 0) =
      Real.exp (-attenuatedVolterraPotential k p) *
        (-attenuatedVolterraWeightedSource j k (p.1, p.1) +
          ∫ s in p.1..p.2,
            (fderivWithin ℝ (attenuatedVolterraWeightedSource j k)
              (closedCoordTriangle a b) (p.1, s)) (1, 0)) -
      Real.exp (-attenuatedVolterraPotential k p) *
        (-k (p.1, p.1) +
          ∫ s in p.1..p.2,
            (fderivWithin ℝ k (closedCoordTriangle a b) (p.1, s)) (1, 0)) *
        weightedDiagonalRadius (attenuatedVolterraWeightedSource j k) p := by
  let K := closedCoordTriangle a b
  let Q := attenuatedVolterraPotential k
  let F := attenuatedVolterraWeightedSource j k
  let P := weightedDiagonalRadius F
  let E : ℝ × ℝ → ℝ := fun z => Real.exp (-Q z)
  let J : ℝ × ℝ → ℝ := fun z => attenuatedVolterraIntegral j k z.1 z.2
  have hQ := contDiffOn_attenuatedVolterraPotential hab hk
  have hF := contDiffOn_attenuatedVolterraWeightedSource hab hj hk
  have hP : ContDiffOn ℝ 1 P K := by
    let G := fderivWithin ℝ F K
    have hunique : UniqueDiffOn ℝ K :=
      uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    have hG := hF.continuousOn_fderivWithin hunique (by norm_num)
    have hdiff : DifferentiableOn ℝ F (interior K) :=
      (hF.differentiableOn (by norm_num)).mono interior_subset
    have hderiv : ∀ q ∈ interior K, fderiv ℝ F q = G q := by
      intro q hq
      exact (fderivWithin_eq_fderiv
        (hunique q (interior_subset hq))
        ((hdiff q hq).differentiableAt (isOpen_interior.mem_nhds hq))).symm
    exact contDiffOn_weightedDiagonalRadius hab hF.continuousOn hG hdiff hderiv
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hQdiff : DifferentiableWithinAt ℝ Q K p :=
    hQ.differentiableOn (by norm_num) p hp
  have hPdiff : DifferentiableWithinAt ℝ P K p :=
    hP.differentiableOn (by norm_num) p hp
  have hEdiff : DifferentiableWithinAt ℝ E K p := hQdiff.neg.exp
  have hEq : EqOn J (fun z => E z * P z) K := by
    intro z hz
    have hz' : a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := hz
    exact attenuatedVolterraIntegral_eq_exp_mul_radius (j := j) hk.continuousOn
      hz'.1 hz'.2.1 hz'.2.2
  have hEderiv : fderivWithin ℝ E K p =
      Real.exp (-Q p) • -(fderivWithin ℝ Q K p) := by
    simpa only [E, Pi.neg_apply] using
      (fderivWithin_exp hQdiff.neg hunique).trans
        (by rw [fderivWithin_neg hunique]; rfl)
  have hPu := radius_horizontal_jet_of_contDiffOn hab hF hp
  have hQu := radius_horizontal_jet_of_contDiffOn hab hk hp
  have hQu' : (fderivWithin ℝ Q K p) (1, 0) =
      -k (p.1, p.1) +
        ∫ s in p.1..p.2, (fderivWithin ℝ k K (p.1, s)) (1, 0) := by
    exact hQu
  rw [show fderivWithin ℝ J K p =
      fderivWithin ℝ (fun z => E z * P z) K p from
        fderivWithin_congr' hEq hp]
  change (fderivWithin ℝ (E * P) K p) (1, 0) = _
  rw [fderivWithin_mul hunique hEdiff hPdiff, hEderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply]
  rw [hPu]
  rw [hQu']
  dsimp only [E, P, F]
  ring

end intervalIntegral

end
