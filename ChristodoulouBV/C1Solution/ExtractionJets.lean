module

public import ChristodoulouBV.C1Solution.ExtractionCoefficient
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Axis jets from the frozen characteristic primitives

The mixed coefficient is represented by its canonical continuous extension.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

private theorem intervalPrimitive_congr_density
    {f g h : ℝ → ℝ} {a z : ℝ} (haz : a ≤ z)
    (hp : IntervalPrimitive f g a z)
    (heq : ∀ t ∈ Icc a z, g t = h t) :
    IntervalPrimitive f h a z := by
  have hint : IntervalIntegrable h volume a z := by
    apply hp.1.congr_uIoo
    intro t ht
    rw [uIoo_of_le haz] at ht
    exact heq t ⟨ht.1.le, ht.2.le⟩
  refine ⟨hint, ?_⟩
  rw [hp.2]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le haz] at ht
  exact heq t ht

private theorem horizontal_jet_of_incoming_primitive {B : ℝ} (hB : 0 < B)
    {F g : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hg : ContinuousOn g (closedCoordTriangle 0 B))
    (hprim : ∀ v a t, 0 ≤ a → a ≤ t → t < v → v ≤ B →
      IntervalPrimitive (fun s => F (s, v)) (fun s => g (s, v)) a t)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = g p := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hjetcont : ContinuousOn
      (fun q => (fderivWithin ℝ F K q) (1, 0)) K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hopen : ∀ q ∈ openCoordTriangle 0 B,
      (fderivWithin ℝ F K q) (1, 0) = g q := by
    rintro ⟨u, v⟩ hq
    have hqi : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hq
    have hparts : 0 < u ∧ u < v ∧ v < B := hq
    have hdiff : DifferentiableAt ℝ F (u, v) :=
      ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hqi).differentiableAt
        (isOpen_interior.mem_nhds hqi)
    have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hqi)) hdiff
    let a := u / 2
    let c := (u + v) / 2
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hau : a < u := by dsimp [a]; linarith
    have huc : u < c := by dsimp [c]; linarith
    have hcv : c < v := by dsimp [c]; linarith
    have hmap (s : ℝ) (hs : s ∈ Icc a c) : (s, v) ∈ K :=
      ⟨ha.trans hs.1, hs.2.trans hcv.le, hparts.2.2.le⟩
    have hgline : ContinuousOn (fun s => g (s, v)) (Icc a c) :=
      hg.comp (continuous_id.prodMk continuous_const).continuousOn hmap
    have hlocal (t : ℝ) (ht : t ∈ Ioo a c) :
        IntervalPrimitive (fun s => F (s, v)) (fun s => g (s, v)) a t :=
      hprim v a t ha ht.1.le (ht.2.trans hcv) hparts.2.2.le
    have hderiv := hasDerivAt_of_intervalPrimitive_local hau huc hgline hlocal
    have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    have hcomp : HasDerivAt (fun s => F (s, v))
        (fderiv ℝ F (u, v) (1, 0)) u := by
      simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
    rw [hwithin]
    exact hcomp.unique hderiv
  have hEq : EqOn (fun q => (fderivWithin ℝ F K q) (1, 0)) g K :=
    (show EqOn (fun q => (fderivWithin ℝ F K q) (1, 0)) g
      (openCoordTriangle 0 B) from hopen).of_subset_closure
      hjetcont hg
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hB])
  exact hEq hp

private theorem vertical_jet_of_outgoing_primitive {B : ℝ} (hB : 0 < B)
    {F g : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hg : ContinuousOn g (closedCoordTriangle 0 B))
    (hprim : ∀ u a t, 0 ≤ u → u < a → a ≤ t → t ≤ B →
      IntervalPrimitive (fun s => F (u, s)) (fun s => g (u, s)) a t)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (0, 1) = g p := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hjetcont : ContinuousOn
      (fun q => (fderivWithin ℝ F K q) (0, 1)) K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hopen : ∀ q ∈ openCoordTriangle 0 B,
      (fderivWithin ℝ F K q) (0, 1) = g q := by
    rintro ⟨u, v⟩ hq
    have hqi : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hq
    have hparts : 0 < u ∧ u < v ∧ v < B := hq
    have hdiff : DifferentiableAt ℝ F (u, v) :=
      ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hqi).differentiableAt
        (isOpen_interior.mem_nhds hqi)
    have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hqi)) hdiff
    let a := (u + v) / 2
    let c := (v + B) / 2
    have hua : u < a := by dsimp [a]; linarith
    have hav : a < v := by dsimp [a]; linarith
    have hvc : v < c := by dsimp [c]; linarith
    have hcB : c < B := by dsimp [c]; linarith
    have hmap (s : ℝ) (hs : s ∈ Icc a c) : (u, s) ∈ K :=
      ⟨hparts.1.le, hua.le.trans hs.1, hs.2.trans hcB.le⟩
    have hgline : ContinuousOn (fun s => g (u, s)) (Icc a c) :=
      hg.comp (continuous_const.prodMk continuous_id).continuousOn hmap
    have hlocal (t : ℝ) (ht : t ∈ Ioo a c) :
        IntervalPrimitive (fun s => F (u, s)) (fun s => g (u, s)) a t :=
      hprim u a t hparts.1.le hua ht.1.le (ht.2.trans hcB).le
    have hderiv := hasDerivAt_of_intervalPrimitive_local hav hvc hgline hlocal
    have hpair : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hcomp : HasDerivAt (fun s => F (u, s))
        (fderiv ℝ F (u, v) (0, 1)) v := by
      simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt v hpair
    rw [hwithin]
    exact hcomp.unique hderiv
  have hEq : EqOn (fun q => (fderivWithin ℝ F K q) (0, 1)) g K :=
    (show EqOn (fun q => (fderivWithin ℝ F K q) (0, 1)) g
      (openCoordTriangle 0 B) from hopen).of_subset_closure
      hjetcont hg
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hB])
  exact hEq hp

/-- The four frozen mixed primitives identify the continuous coordinate jets
with the canonical removable coefficient on the whole closed triangle. -/
theorem four_mixed_coordinate_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
      (closedCoordTriangle 0 B) p) (1, 0) = canonicalMixedCoefficient b S p ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1) = canonicalMixedCoefficient b S p ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.alpha q.1 q.2)
      (closedCoordTriangle 0 B) p) (1, 0) =
        canonicalMixedCoefficient b S p * S.phi p.1 p.2 ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1) =
        canonicalMixedCoefficient b S p * S.phi p.1 p.2 := by
  let K := closedCoordTriangle 0 B
  let g := canonicalMixedCoefficient b S
  let gphi : ℝ × ℝ → ℝ := fun q => g q * S.phi q.1 q.2
  have hg : ContinuousOn g K := canonicalMixedCoefficient_continuousOn hB hBb H
  have hphi := (five_fields_contDiffOn hB hBb H).2.2.1
  have hgphi : ContinuousOn gphi K := hg.mul hphi.continuousOn
  have hInSeg (v a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t)
      (htv : t < v) (hvB : v ≤ B) :
      inSeg v a t ⊆ developmentWithInitialEdge b := by
    intro q hq
    rcases q with ⟨s, w⟩
    have hsw : s ∈ Icc a t ∧ w = v := by simpa [inSeg] using hq
    rcases hsw with ⟨hs, rfl⟩
    exact ⟨ha.trans hs.1, hs.2.trans_lt htv, hvB.trans_lt hBb⟩
  have hOutSeg (u a t : ℝ) (hu : 0 ≤ u) (hua : u < a)
      (hat : a ≤ t) (htB : t ≤ B) :
      outSeg u a t ⊆ developmentWithInitialEdge b := by
    intro q hq
    rcases q with ⟨s, w⟩
    have hsw : s = u ∧ w ∈ Icc a t := by simpa [outSeg] using hq
    rcases hsw with ⟨rfl, hw⟩
    exact ⟨hu, hua.trans_le hw.1, (hw.2.trans htB).trans_lt hBb⟩
  have hprimLam (v a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t)
      (htv : t < v) (hvB : v ≤ B) :
      IntervalPrimitive (fun s => S.lam s v) (fun s => g (s, v)) a t := by
    apply intervalPrimitive_congr_density hat
      (H.solution.lam_in v a t hat (hInSeg v a t ha hat htv hvB))
    intro s hs
    exact (canonicalMixedCoefficient_eq_frozen hB hBb H
      (ha.trans hs.1) (hs.2.trans_lt htv) hvB).symm
  have hprimNu (u a t : ℝ) (hu : 0 ≤ u) (hua : u < a)
      (hat : a ≤ t) (htB : t ≤ B) :
      IntervalPrimitive (S.nu u) (fun s => g (u, s)) a t := by
    apply intervalPrimitive_congr_density hat
      (H.solution.nu_out u a t hat (hOutSeg u a t hu hua hat htB))
    intro s hs
    exact (canonicalMixedCoefficient_eq_frozen hB hBb H
      hu (hua.trans_le hs.1) (hs.2.trans htB)).symm
  have hprimAlpha (v a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t)
      (htv : t < v) (hvB : v ≤ B) :
      IntervalPrimitive (fun s => S.alpha s v) (fun s => gphi (s, v)) a t := by
    apply intervalPrimitive_congr_density hat
      (H.solution.alpha_in v a t hat (hInSeg v a t ha hat htv hvB))
    intro s hs
    change _ * S.phi s v = canonicalMixedCoefficient b S (s, v) * S.phi s v
    rw [canonicalMixedCoefficient_eq_frozen hB hBb H
      (ha.trans hs.1) (hs.2.trans_lt htv) hvB]
  have hprimBeta (u a t : ℝ) (hu : 0 ≤ u) (hua : u < a)
      (hat : a ≤ t) (htB : t ≤ B) :
      IntervalPrimitive (S.beta u) (fun s => gphi (u, s)) a t := by
    apply intervalPrimitive_congr_density hat
      (H.solution.beta_out u a t hat (hOutSeg u a t hu hua hat htB))
    intro s hs
    change _ * S.phi u s = canonicalMixedCoefficient b S (u, s) * S.phi u s
    rw [canonicalMixedCoefficient_eq_frozen hB hBb H
      hu (hua.trans_le hs.1) (hs.2.trans htB)]
  obtain ⟨hlam, hnu, _, _, _⟩ := five_fields_contDiffOn hB hBb H
  exact ⟨horizontal_jet_of_incoming_primitive hB hlam hg hprimLam hp,
    vertical_jet_of_outgoing_primitive hB hnu hg hprimNu hp,
    horizontal_jet_of_incoming_primitive hB (alpha_contDiffOn hB hBb H)
      hgphi hprimAlpha hp,
    vertical_jet_of_outgoing_primitive hB (beta_contDiffOn hB hBb H)
      hgphi hprimBeta hp⟩

/-- The four mixed coordinate jets vanish on the regular axis. -/
theorem four_mixed_axis_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) = 0 ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.alpha q.1 q.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) = 0 := by
  have hp : (u, u) ∈ closedCoordTriangle 0 B := ⟨hu.1, le_rfl, hu.2⟩
  obtain ⟨hlamJet, hnuJet, halphaJet, hbetaJet⟩ :=
    four_mixed_coordinate_jets hB hBb H hp
  rw [hlamJet, hnuJet, halphaJet, hbetaJet, canonicalMixedCoefficient_axis]
  simp

/-- The outgoing quotient has zero incoming axis jet, and the scalar's two
coordinate jets agree there. -/
theorem outgoingQuotient_and_phi_axis_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (outgoingQuotient S)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) := by
  let K := closedCoordTriangle 0 B
  let lam : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let alpha : ℝ × ℝ → ℝ := fun p => S.alpha p.1 p.2
  let h := outgoingQuotient S
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  obtain ⟨hlam, _, halpha, _⟩ := four_mixed_axis_jets hB hBb H hu
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hlpos : 0 < lam (u, u) := hc.trans_le (hcl (u, u) hp)
  have hunique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, u) hp
  have hlamDiff : DifferentiableWithinAt ℝ lam K (u, u) :=
    ((five_fields_contDiffOn hB hBb H).1.differentiableOn (by norm_num)) (u, u) hp
  have hhDiff : DifferentiableWithinAt ℝ h K (u, u) :=
    ((alpha_div_lam_contDiffOn hB hBb H).differentiableOn (by norm_num))
      (u, u) hp
  have hEq : EqOn alpha (lam * h) K := by
    intro p hpK
    have hne : lam p ≠ 0 := ne_of_gt (hc.trans_le (hcl p hpK))
    change S.alpha p.1 p.2 = S.lam p.1 p.2 *
      (S.alpha p.1 p.2 / S.lam p.1 p.2)
    field_simp [show S.lam p.1 p.2 ≠ 0 from hne]
  have hprod :
      (fderivWithin ℝ alpha K (u, u)) (1, 0) =
        lam (u, u) * (fderivWithin ℝ h K (u, u)) (1, 0) +
        h (u, u) * (fderivWithin ℝ lam K (u, u)) (1, 0) := by
    rw [fderivWithin_congr' hEq hp]
    rw [fderivWithin_mul hunique hlamDiff hhDiff]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hhzero : (fderivWithin ℝ h K (u, u)) (1, 0) = 0 := by
    dsimp [lam, alpha] at hprod
    rw [halpha, hlam] at hprod
    nlinarith only [hprod, hlpos]
  have hphi := phi_axis_jets hB hBb H hu
  refine ⟨hhzero, ?_⟩
  rw [hphi.2, hphi.1, hhzero]
  ring

end ChristodoulouBV.C1Solution

end
