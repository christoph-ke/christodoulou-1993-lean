module

public import Mathlib

/-!
# First-order extension from a compact interval

A real function that is `C¹` on a nondegenerate closed interval is continued
by its endpoint tangent lines. The values and endpoint derivatives agree.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

/-- Continue a function on `[a,c]` using its one-sided first-order Taylor
polynomials at the endpoints. -/
@[expose] def intervalC1Extension (f : ℝ → ℝ) (a c x : ℝ) : ℝ :=
  if x < a then f a + derivWithin f (Icc a c) a * (x - a)
  else if x ≤ c then f x
  else f c + derivWithin f (Icc a c) c * (x - c)

/-- The extension preserves the prescribed interval values. -/
theorem intervalC1Extension_eq {f : ℝ → ℝ} {a c x : ℝ}
    (hx : x ∈ Icc a c) : intervalC1Extension f a c x = f x := by
  simp [intervalC1Extension, not_lt.mpr hx.1, hx.2]

/-- The first-order interval extension is globally `C¹`. -/
theorem intervalC1Extension_c1 {f : ℝ → ℝ} {a c : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c)) :
    ContDiff ℝ 1 (intervalC1Extension f a c) := by
  let F := intervalC1Extension f a c
  let da := derivWithin f (Icc a c) a
  let dc := derivWithin f (Icc a c) c
  have hleft : ∀ x ∈ Iic a, F x = f a + da * (x - a) := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx'
    · simp [F, intervalC1Extension, da, hac.le]
    · simp [F, intervalC1Extension, hx', da]
  have hmiddle : ∀ x ∈ Icc a c, F x = f x := by
    intro x hx
    exact intervalC1Extension_eq hx
  have hright : ∀ x ∈ Ici c, F x = f c + dc * (x - c) := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx'
    · simp [F, intervalC1Extension, hac.le, dc]
    · have hxa : ¬ x < a := not_lt.mpr (hac.le.trans hx)
      simp [F, intervalC1Extension, hxa, not_le.mpr hx', dc]
  have hderivA : HasDerivAt F da a := by
    have hleft' : HasDerivWithinAt F da (Iic a) a := by
      have hlin : HasDerivAt (fun x : ℝ => f a + da * (x - a)) da a := by
        convert (hasDerivAt_const a (f a)).add
          (((hasDerivAt_id' a).sub_const a).const_mul da) using 1; ring
      exact hlin.hasDerivWithinAt.congr_of_mem hleft le_rfl
    have hmid' : HasDerivWithinAt F da (Icc a c) a :=
      ((hf.differentiableOn (by norm_num) a ⟨le_rfl, hac.le⟩).hasDerivWithinAt).congr_of_mem
        hmiddle ⟨le_rfl, hac.le⟩
    have h := hleft'.union hmid'
    rw [Iic_union_Icc_eq_Iic hac.le] at h
    exact h.hasDerivAt (Iic_mem_nhds hac)
  have hderivC : HasDerivAt F dc c := by
    have hmid' : HasDerivWithinAt F dc (Icc a c) c :=
      ((hf.differentiableOn (by norm_num) c ⟨hac.le, le_rfl⟩).hasDerivWithinAt).congr_of_mem
        hmiddle ⟨hac.le, le_rfl⟩
    have hright' : HasDerivWithinAt F dc (Ici c) c := by
      have hlin : HasDerivAt (fun x : ℝ => f c + dc * (x - c)) dc c := by
        convert (hasDerivAt_const c (f c)).add
          (((hasDerivAt_id' c).sub_const c).const_mul dc) using 1; ring
      exact hlin.hasDerivWithinAt.congr_of_mem hright le_rfl
    have h := hmid'.union hright'
    rw [Icc_union_Ici_eq_Ici hac.le] at h
    exact h.hasDerivAt (Ici_mem_nhds hac)
  have hderivLeft : ∀ x ∈ Iic a, deriv F x = da := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx'
    · exact hderivA.deriv
    · have hlin : HasDerivAt (fun t : ℝ => f a + da * (t - a)) da x := by
        convert (hasDerivAt_const x (f a)).add
          (((hasDerivAt_id' x).sub_const a).const_mul da) using 1; ring
      exact (hlin.congr_of_eventuallyEq (by
        filter_upwards [Iic_mem_nhds hx'] with y hy
        exact hleft y hy)).deriv
  have hderivMid : ∀ x ∈ Icc a c,
      deriv F x = derivWithin f (Icc a c) x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact hderivA.deriv
    rcases eq_or_lt_of_le hx.2 with rfl | hxc
    · exact hderivC.deriv
    · have hf' : HasDerivAt f (derivWithin f (Icc a c) x) x :=
        ((hf.differentiableOn (by norm_num) x hx).hasDerivWithinAt).hasDerivAt
          (Icc_mem_nhds hax hxc)
      exact (hf'.congr_of_eventuallyEq (by
        filter_upwards [Icc_mem_nhds hax hxc] with y hy
        exact hmiddle y hy)).deriv
  have hderivRight : ∀ x ∈ Ici c, deriv F x = dc := by
    intro x hx
    rcases eq_or_lt_of_le hx with rfl | hx'
    · exact hderivC.deriv
    · have hlin : HasDerivAt (fun t : ℝ => f c + dc * (t - c)) dc x := by
        convert (hasDerivAt_const x (f c)).add
          (((hasDerivAt_id' x).sub_const c).const_mul dc) using 1; ring
      exact (hlin.congr_of_eventuallyEq (by
        filter_upwards [Ici_mem_nhds hx'] with y hy
        exact hright y hy)).deriv
  have hdiff : Differentiable ℝ F := by
    intro x
    rcases lt_trichotomy x a with hxa | rfl | hax
    · have hlin : DifferentiableAt ℝ (fun t : ℝ => f a + da * (t - a)) x := by
        fun_prop
      exact hlin.congr_of_eventuallyEq (by
        filter_upwards [Iic_mem_nhds hxa] with y hy
        exact hleft y hy)
    · exact hderivA.differentiableAt
    · rcases lt_trichotomy x c with hxc | rfl | hcx
      · have hf' : DifferentiableAt ℝ f x :=
          (hf.contDiffAt (Icc_mem_nhds hax hxc)).differentiableAt (by norm_num)
        exact hf'.congr_of_eventuallyEq (by
          filter_upwards [Icc_mem_nhds hax hxc] with y hy
          exact hmiddle y hy)
      · exact hderivC.differentiableAt
      · have hlin : DifferentiableAt ℝ (fun t : ℝ => f c + dc * (t - c)) x := by
          fun_prop
        exact hlin.congr_of_eventuallyEq (by
          filter_upwards [Ici_mem_nhds hcx] with y hy
          exact hright y hy)
  have hdcont : ContinuousOn (derivWithin f (Icc a c)) (Icc a c) :=
    (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hac)).mp hf |>.2
  have hleftCont : ContinuousOn (deriv F) (Iic a) :=
    continuousOn_const.congr hderivLeft
  have hmidCont : ContinuousOn (deriv F) (Icc a c) :=
    hdcont.congr hderivMid
  have hrightCont : ContinuousOn (deriv F) (Ici c) :=
    continuousOn_const.congr hderivRight
  have hcont : Continuous (deriv F) := by
    rw [← continuousOn_univ, ← Iic_union_Ici (a := a),
      ← Icc_union_Ici_eq_Ici hac.le]
    exact hleftCont.union_of_isClosed
      (hmidCont.union_of_isClosed hrightCont isClosed_Icc isClosed_Ici)
      isClosed_Iic (isClosed_Icc.union isClosed_Ici)
  exact contDiff_one_iff_deriv.mpr ⟨hdiff, hcont⟩

end ChristodoulouBV

end
