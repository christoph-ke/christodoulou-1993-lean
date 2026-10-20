module

public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import ChristodoulouBV.ForMathlib.Gronwall.Integral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Moving outgoing slices for C¹ uniqueness

Compact outgoing maxima are continuous even where the slice collapses to the
top vertex. The zero-data integral inequality then forces the maximum to
vanish.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- The maximum of a continuous summand on the outgoing segment from
`(u,u)` to `(u,B)`, parametrized by the fixed compact interval `[0,1]`. -/
@[expose] noncomputable def movingSliceSup (B : ℝ) (f : ℝ × ℝ → ℝ)
    (u : Icc (0 : ℝ) B) : ℝ :=
  sSup ((fun t : Icc (0 : ℝ) 1 =>
    f (u.1, u.1 + (B - u.1) * t.1)) '' Set.univ)

/-- The outgoing maximum varies continuously with its moving lower endpoint,
including when the segment collapses at `u=B`. -/
theorem continuous_movingSliceSup {B : ℝ} (_hB : 0 ≤ B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B)) :
    Continuous (movingSliceSup B f) := by
  let T : Set ℝ := Icc 0 1
  let U : Set ℝ := Icc 0 B
  let Φ : U × T → ℝ × ℝ := fun q =>
    (q.1.1, q.1.1 + (B - q.1.1) * q.2.1)
  have hΦcont : Continuous Φ := by
    dsimp [Φ]
    fun_prop
  have hΦmap : Set.MapsTo Φ Set.univ (closedCoordTriangle 0 B) := by
    intro q _
    have hu := q.1.2
    have ht := q.2.2
    have hgap : 0 ≤ B - q.1.1 := sub_nonneg.mpr hu.2
    have hfirst : 0 ≤ (B - q.1.1) * q.2.1 := mul_nonneg hgap ht.1
    have hlast : 0 ≤ (B - q.1.1) * (1 - q.2.1) :=
      mul_nonneg hgap (sub_nonneg.mpr ht.2)
    change 0 ≤ q.1.1 ∧
      q.1.1 ≤ q.1.1 + (B - q.1.1) * q.2.1 ∧
      q.1.1 + (B - q.1.1) * q.2.1 ≤ B
    constructor
    · exact hu.1
    constructor
    · linarith only [hfirst]
    · nlinarith only [hlast]
  have hF : Continuous (fun q : U × T => f (Φ q)) := by
    exact continuousOn_univ.mp (hf.comp hΦcont.continuousOn hΦmap)
  have hSup : Continuous (fun u : U =>
      sSup ((fun t : T => f (Φ (u, t))) '' Set.univ)) :=
    (isCompact_univ : IsCompact (Set.univ : Set T)).continuous_sSup hF
  change Continuous (fun u : U =>
    sSup ((fun t : T => f (u.1, u.1 + (B - u.1) * t.1)) '' Set.univ))
  exact hSup

/-- The continuous moving-slice summand has a bounded range. -/
theorem movingSliceSup_bddAbove {B : ℝ} (_hB : 0 ≤ B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B))
    (u : Icc (0 : ℝ) B) :
    BddAbove ((fun t : Icc (0 : ℝ) 1 =>
      f (u.1, u.1 + (B - u.1) * t.1)) '' Set.univ) := by
  let T : Set ℝ := Icc 0 1
  let Φ : T → ℝ × ℝ := fun t =>
    (u.1, u.1 + (B - u.1) * t.1)
  have hΦcont : Continuous Φ := by dsimp [Φ]; fun_prop
  have hΦmap : Set.MapsTo Φ Set.univ (closedCoordTriangle 0 B) := by
    intro t _
    have hgap : 0 ≤ B - u.1 := sub_nonneg.mpr u.2.2
    have hfirst : 0 ≤ (B - u.1) * t.1 := mul_nonneg hgap t.2.1
    have hlast : 0 ≤ (B - u.1) * (1 - t.1) :=
      mul_nonneg hgap (sub_nonneg.mpr t.2.2)
    change 0 ≤ u.1 ∧
      u.1 ≤ u.1 + (B - u.1) * t.1 ∧
      u.1 + (B - u.1) * t.1 ≤ B
    constructor
    · exact u.2.1
    constructor
    · linarith only [hfirst]
    · nlinarith only [hlast]
  have hcont : Continuous (fun t : T => f (Φ t)) :=
    continuousOn_univ.mp (hf.comp hΦcont.continuousOn hΦmap)
  exact ((isCompact_univ : IsCompact (Set.univ : Set T)).image hcont).bddAbove

/-- A nonnegative continuous summand has a nonnegative moving maximum. -/
theorem movingSliceSup_nonneg {B : ℝ} (hB : 0 ≤ B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B))
    (hf0 : ∀ p ∈ closedCoordTriangle 0 B, 0 ≤ f p)
    (u : Icc (0 : ℝ) B) : 0 ≤ movingSliceSup B f u := by
  have hp : (u.1, u.1) ∈ closedCoordTriangle 0 B :=
    ⟨u.2.1, le_rfl, u.2.2⟩
  have hmem : f (u.1, u.1) ∈
      ((fun t : Icc (0 : ℝ) 1 =>
        f (u.1, u.1 + (B - u.1) * t.1)) '' Set.univ) := by
    refine ⟨⟨0, by norm_num⟩, Set.mem_univ _, ?_⟩
    simp
  exact (hf0 (u.1, u.1) hp).trans
    (le_csSup (movingSliceSup_bddAbove hB hf u) hmem)

/-- Every point of the closed triangle is bounded by the maximum on its
outgoing slice. -/
theorem le_movingSliceSup {B : ℝ} (hB : 0 ≤ B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    f (u, v) ≤ movingSliceSup B f ⟨u, ⟨hu, huv.trans hv⟩⟩ := by
  have huB : u ≤ B := huv.trans hv
  obtain ⟨t, ht, heq⟩ : ∃ t : ℝ, t ∈ Icc 0 1 ∧
      u + (B - u) * t = v := by
    rcases lt_or_eq_of_le huB with huB' | huB'
    · have hden : 0 < B - u := sub_pos.mpr huB'
      refine ⟨(v - u) / (B - u), ?_, ?_⟩
      constructor
      · exact div_nonneg (sub_nonneg.mpr huv) hden.le
      · apply (div_le_iff₀ hden).2
        linarith
      · field_simp [hden.ne']
        ring
    · subst B
      have hvu : v = u := le_antisymm hv huv
      subst v
      exact ⟨0, by norm_num, by ring⟩
  have hmem : f (u, v) ∈
      ((fun t : Icc (0 : ℝ) 1 =>
        f (u, u + (B - u) * t.1)) '' Set.univ) := by
    refine ⟨⟨t, ht⟩, Set.mem_univ _, ?_⟩
    exact congrArg (fun z => f (u, z)) heq
  exact le_csSup (movingSliceSup_bddAbove hB hf
    ⟨u, ⟨hu, huB⟩⟩) hmem

/-- A real-valued extension of the moving maximum, obtained by projecting
the first coordinate onto `[0,B]`. -/
@[expose] noncomputable def movingSliceSupReal (B : ℝ) (hB : 0 ≤ B)
    (f : ℝ × ℝ → ℝ) (u : ℝ) : ℝ :=
  movingSliceSup B f (Set.projIcc 0 B hB u)

/-- The projected moving maximum is continuous on the real line. -/
theorem continuous_movingSliceSupReal {B : ℝ} (hB : 0 ≤ B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B)) :
    Continuous (movingSliceSupReal B hB f) := by
  change Continuous (fun u => movingSliceSup B f (Set.projIcc 0 B hB u))
  exact (continuous_movingSliceSup hB hf).comp continuous_projIcc

/-- The scalar zero-data Gronwall step used after the moving-slice estimate
(U). Continuity supplies the required interval integrability. -/
theorem eq_zero_of_moving_slice_integral_bound {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) {D : ℝ → ℝ}
    (hDcont : ContinuousOn D (Icc 0 B))
    (hDnonneg : ∀ u ∈ Icc 0 B, 0 ≤ D u)
    (hineq : ∀ u ∈ Icc 0 B,
      D u ≤ A * ∫ s in (0 : ℝ)..u, D s) :
    ∀ u ∈ Icc 0 B, D u = 0 := by
  have hDint : IntervalIntegrable D volume 0 B :=
    hDcont.intervalIntegrable_of_Icc hB
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 B :=
    intervalIntegrable_const
  have hprod : IntervalIntegrable (fun s : ℝ => (1 : ℝ) * D s) volume 0 B := by
    simpa only [one_mul] using hDint
  have hbound := intervalIntegral.le_mul_exp_integral_of_le_integral_const_mul
    (a := (0 : ℝ)) (b := B) (A := (0 : ℝ)) (B := A)
    (k := fun _ => (1 : ℝ)) (h := D) hB hA hconst hprod
    (fun _ _ => by norm_num)
    (fun u hu => by simpa only [zero_add, one_mul] using hineq u hu)
  intro u hu
  have hle : D u ≤ 0 := by simpa only [zero_mul] using hbound u hu
  exact le_antisymm hle (hDnonneg u hu)

/-- If the moving maximum obeys the zero-data Volterra inequality (U),
then its nonnegative summand vanishes on the whole closed triangle. -/
theorem eq_zero_of_movingSliceSup_integral_bound {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A)
    {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 B))
    (hf0 : ∀ p ∈ closedCoordTriangle 0 B, 0 ≤ f p)
    (hU : ∀ u ∈ Icc 0 B,
      movingSliceSupReal B hB f u ≤
        A * ∫ s in (0 : ℝ)..u, movingSliceSupReal B hB f s) :
    EqOn f (fun _ => 0) (closedCoordTriangle 0 B) := by
  let D := movingSliceSupReal B hB f
  have hDcont : ContinuousOn D (Icc 0 B) :=
    (continuous_movingSliceSupReal hB hf).continuousOn
  have hDnonneg : ∀ u ∈ Icc 0 B, 0 ≤ D u := by
    intro u hu
    change 0 ≤ movingSliceSup B f (Set.projIcc 0 B hB u)
    exact movingSliceSup_nonneg hB hf hf0 (Set.projIcc 0 B hB u)
  have hzero := eq_zero_of_moving_slice_integral_bound hB hA
    hDcont hDnonneg hU
  intro p hp
  rcases p with ⟨u, v⟩
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  have huB : u ∈ Icc 0 B := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hbound := le_movingSliceSup hB hf hp.1 hp.2.1 hp.2.2
  have heq : D u = movingSliceSup B f ⟨u, huB⟩ := by
    change movingSliceSup B f (Set.projIcc 0 B hB u) = _
    rw [Set.projIcc_of_mem hB huB]
  rw [← heq, hzero u huB] at hbound
  exact le_antisymm hbound (hf0 (u, v) hp)


end ChristodoulouBV.C1Solution

end
