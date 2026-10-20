module

public import Mathlib

/-!
# First-order extension of initial characteristic data

A function that is `C¹` on the nonnegative half-line has a global `C¹`
representative obtained by continuing its value and right derivative linearly
to negative arguments.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- Continue a right-half-line function to the left by its first-order Taylor
polynomial at zero. -/
@[expose] def initialEdgeExtension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then f x else f 0 + derivWithin f (Ici 0) 0 * x

/-- The first-order extension preserves the original half-line values. -/
theorem initialEdgeExtension_eq {f : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) :
    initialEdgeExtension f x = f x := by
  simp [initialEdgeExtension, hx]

/-- The first-order extension is globally `C¹`. -/
theorem initialEdgeExtension_c1 {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) :
    ContDiff ℝ 1 (initialEdgeExtension f) := by
  let d := derivWithin f (Ici 0) 0
  have hpositive : ∀ x ∈ Ici (0 : ℝ),
      initialEdgeExtension f x = f x :=
    fun _ hx => initialEdgeExtension_eq hx
  have hnegative : ∀ x ∈ Iic (0 : ℝ),
      initialEdgeExtension f x = f 0 + d * x := by
    intro x hx
    by_cases hzero : x = 0
    · subst x
      simp [initialEdgeExtension, d]
    · have hx' : ¬ 0 ≤ x := by exact not_le.mpr (lt_of_le_of_ne hx hzero)
      simp [initialEdgeExtension, hx', d]
  have hzero : HasDerivAt (initialEdgeExtension f) d 0 := by
    have hright : HasDerivWithinAt f d (Ici 0) 0 :=
      ((hf.differentiableOn (by norm_num) 0 le_rfl).hasDerivWithinAt)
    have hleft : HasDerivWithinAt (fun x : ℝ => f 0 + d * x) d (Iic 0) 0 := by
      convert (((hasDerivAt_const 0 (f 0)).add
        ((hasDerivAt_id' 0).const_mul d)).hasDerivWithinAt) using 1; ring
    have hright' : HasDerivWithinAt (initialEdgeExtension f) d (Ici 0) 0 :=
      hright.congr_of_mem hpositive le_rfl
    have hleft' : HasDerivWithinAt (initialEdgeExtension f) d (Iic 0) 0 :=
      hleft.congr_of_mem hnegative le_rfl
    have h := hleft'.union hright'
    rw [Iic_union_Ici] at h
    exact hasDerivWithinAt_univ.mp h
  have hderiv_positive : ∀ x ∈ Ici (0 : ℝ),
      deriv (initialEdgeExtension f) x = derivWithin f (Ici 0) x := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx'
    · exact hzero.deriv
    · have hmem : Ici (0 : ℝ) ∈ 𝓝 x := Ici_mem_nhds hx'
      have hf' : HasDerivAt f (derivWithin f (Ici 0) x) x :=
        (((hf.differentiableOn (by norm_num) x hx).hasDerivWithinAt).hasDerivAt hmem)
      have heq : initialEdgeExtension f =ᶠ[𝓝 x] f :=
        by filter_upwards [hmem] with y hy; exact hpositive y hy
      exact (hf'.congr_of_eventuallyEq heq).deriv
  have hderiv_negative : ∀ x ∈ Iic (0 : ℝ),
      deriv (initialEdgeExtension f) x = d := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx'
    · exact hzero.deriv
    · have hmem : Iic (0 : ℝ) ∈ 𝓝 x := Iic_mem_nhds hx'
      have hlin : HasDerivAt (fun t : ℝ => f 0 + d * t) d x := by
        convert (hasDerivAt_const x (f 0)).add ((hasDerivAt_id' x).const_mul d) using 1; ring
      have heq : initialEdgeExtension f =ᶠ[𝓝 x] fun t => f 0 + d * t :=
        by filter_upwards [hmem] with y hy; exact hnegative y hy
      exact (hlin.congr_of_eventuallyEq heq).deriv
  have hdiff : Differentiable ℝ (initialEdgeExtension f) := by
    intro x
    rcases le_total 0 x with hx | hx
    · rcases eq_or_lt_of_le hx with rfl | hx'
      · exact hzero.differentiableAt
      · have hf' : DifferentiableAt ℝ f x :=
          (hf.contDiffAt (Ici_mem_nhds hx')).differentiableAt (by norm_num)
        have heq : initialEdgeExtension f =ᶠ[𝓝 x] f :=
          by filter_upwards [Ici_mem_nhds hx'] with y hy; exact hpositive y hy
        exact hf'.congr_of_eventuallyEq heq
    · rcases eq_or_lt_of_le hx with rfl | hx'
      · exact hzero.differentiableAt
      · have hmem : Iic (0 : ℝ) ∈ 𝓝 x := Iic_mem_nhds hx'
        have hlin : DifferentiableAt ℝ (fun t : ℝ => f 0 + d * t) x := by fun_prop
        exact hlin.congr_of_eventuallyEq
          (by filter_upwards [hmem] with y hy; exact hnegative y hy)
  have hdcont : ContinuousOn (derivWithin f (Ici 0)) (Ici 0) :=
    (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici 0)).mp hf |>.2
  have hposcont : ContinuousOn (deriv (initialEdgeExtension f)) (Ici 0) :=
    hdcont.congr hderiv_positive
  have hnegcont : ContinuousOn (deriv (initialEdgeExtension f)) (Iic 0) :=
    continuousOn_const.congr hderiv_negative
  have hcont : Continuous (deriv (initialEdgeExtension f)) := by
    rw [← continuousOn_univ, ← Iic_union_Ici]
    exact hnegcont.union_of_isClosed hposcont isClosed_Iic isClosed_Ici
  exact contDiff_one_iff_deriv.mpr ⟨hdiff, hcont⟩

/-- A positive C¹ outgoing expansion can be normalized into the numerical
Picard interval on a short right-hand edge by a positive physical scale. -/
theorem exists_normalized_positive_edge {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {a : ℝ} (hga : 0 < g a) :
    ∃ k L : ℝ, 0 < k ∧ 0 < L ∧ k * g a = 1 / 2 ∧
      ∀ v ∈ Icc a (a + L), 3 / 8 ≤ k * g v ∧ k * g v ≤ 5 / 8 := by
  let k : ℝ := 1 / (2 * g a)
  have hk : 0 < k := by positivity
  have hka : k * g a = 1 / 2 := by
    dsimp [k]
    field_simp [ne_of_gt hga]
  let s : Set ℝ := {v | 3 / 8 < k * g v ∧ k * g v < 5 / 8}
  have hsopen : IsOpen s := by
    have hcont : Continuous (fun v => k * g v) :=
      continuous_const.mul hg.continuous
    exact (isOpen_Ioi.preimage hcont).inter (isOpen_Iio.preimage hcont)
  have has : a ∈ s := by
    change 3 / 8 < k * g a ∧ k * g a < 5 / 8
    rw [hka]
    constructor <;> norm_num
  obtain ⟨b, hab, hsub⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (nhdsWithin_le_nhds (hsopen.mem_nhds has))
  refine ⟨k, b - a, hk, by linarith only [hab], hka, ?_⟩
  intro v hv
  have hv' : v ∈ Icc a b := by
    simpa only [show a + (b - a) = b by ring] using hv
  exact ⟨(hsub hv').1.le, (hsub hv').2.le⟩

end ChristodoulouBV.AxisPicard

end
