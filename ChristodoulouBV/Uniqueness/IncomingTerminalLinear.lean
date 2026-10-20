module

public import ChristodoulouBV.Uniqueness.IncomingMassEquation
public import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation

/-!
# Terminal variation of constants on a half-open incoming ray

The value at the diagonal is only a limit. This lemma applies compact
variation of constants and then takes that limit using full-ray integrability.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A linear equation on every compact part of a half-open ray, with zero
terminal trace, has the decaying terminal integrating factor. -/
theorem terminal_integral_formula_of_ae_hasDerivAt
    {u v : ℝ} (huv : u < v) {k g y : ℝ → ℝ}
    (hk : IntervalIntegrable k volume u v)
    (hg : IntervalIntegrable g volume u v)
    (hyAC : ∀ w, u ≤ w → w < v → AbsolutelyContinuousOnInterval y u w)
    (hy' : ∀ w, u ≤ w → w < v →
      ∀ᵐ s ∂volume, s ∈ uIcc u w →
        HasDerivAt y (k s * y s + g s) s)
    (hlim : Tendsto y (𝓝[<] v) (𝓝 (0 : ℝ))) :
    y u = -(∫ s in u..v,
      Real.exp (-(∫ t in u..s, k t)) * g s) := by
  let K : ℝ → ℝ := fun s => ∫ t in u..s, k t
  let E : ℝ → ℝ := fun s => Real.exp (-K s)
  let H : ℝ → ℝ := fun s => ∫ t in u..s, E t * g t
  have hK : AbsolutelyContinuousOnInterval K u v :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE : AbsolutelyContinuousOnInterval E u v := hK.neg.exp
  have hEg : IntervalIntegrable (fun s => E s * g s) volume u v :=
    hg.continuousOn_mul hE.continuousOn
  have hH : AbsolutelyContinuousOnInterval H u v :=
    hEg.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hcont : ContinuousOn
      (fun w => Real.exp (K w) * (y u + H w)) (Icc u v) := by
    have hKcont : ContinuousOn K (Icc u v) := by
      simpa only [uIcc_of_le huv.le] using hK.continuousOn
    have hHcont : ContinuousOn H (Icc u v) := by
      simpa only [uIcc_of_le huv.le] using hH.continuousOn
    exact (Real.continuous_exp.comp_continuousOn hKcont).mul
      (continuousOn_const.add hHcont)
  have hleft : Tendsto (fun w : ℝ => w) (𝓝[<] v) (𝓝[Icc u v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT huv)
        (fun w hw => ⟨hw.1.le, hw.2.le⟩)⟩
  have hformula : ∀ᶠ w in 𝓝[<] v,
      y w = Real.exp (K w) * (y u + H w) := by
    filter_upwards [Ioo_mem_nhdsLT huv] with w hw
    have huw : u ≤ w := hw.1.le
    have hsub : uIcc u w ⊆ uIcc u v := by
      rw [uIcc_of_le huw, uIcc_of_le huv.le]
      exact Icc_subset_Icc_right hw.2.le
    have hkw : IntervalIntegrable k volume u w := hk.mono_set hsub
    have hgw : IntervalIntegrable g volume u w := hg.mono_set hsub
    have hrepr := intervalIntegral.eq_exp_mul_add_integral_of_ae_hasDerivAt
      huw hkw hgw (hyAC w huw hw.2) (hy' w huw hw.2)
      (show w ∈ Icc u w from ⟨huw, le_rfl⟩)
    exact hrepr
  have hRHS : Tendsto
      (fun w => Real.exp (K w) * (y u + H w))
      (𝓝[<] v) (𝓝 (Real.exp (K v) * (y u + H v))) :=
    (hcont.continuousWithinAt ⟨huv.le, le_rfl⟩).tendsto.comp hleft
  have hzero : Real.exp (K v) * (y u + H v) = 0 := by
    have hconv : Tendsto y (𝓝[<] v)
        (𝓝 (Real.exp (K v) * (y u + H v))) :=
      hRHS.congr' (hformula.mono fun _ h => h.symm)
    exact tendsto_nhds_unique hconv hlim
  have hsum : y u + H v = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (Real.exp_ne_zero _)
  dsimp [H, E, K] at hsum ⊢
  linarith only [hsum]

end ChristodoulouBV.Uniqueness

end
