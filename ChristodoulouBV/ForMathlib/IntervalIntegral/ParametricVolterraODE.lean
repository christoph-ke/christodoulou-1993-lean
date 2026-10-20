module

public import ChristodoulouBV.ForMathlib.IntervalIntegral.ParametricVolterra

/-!
# Terminal continuity for parameter-dependent linear ODEs

The fundamental theorem converts a pointwise incoming ODE to the integral
form used by the terminal Volterra extension theorem.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace intervalIntegral

/-- A continuous solution of a linear incoming ODE extends jointly to the
terminal parameter edge when its coefficients and initial value do. -/
theorem exists_continuousOn_closed_rectangle_of_linear_ode
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ < v₁)
    {a b : ℝ × ℝ → ℝ} {y₀ : ℝ → ℝ} {y : ℝ × ℝ → ℝ}
    (ha : ContinuousOn a (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hb : ContinuousOn b (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hy₀ : ContinuousOn y₀ (Icc v₀ v₁))
    (hy : ∀ v ∈ Ico v₀ v₁,
      ContinuousOn (fun u => y (u, v)) (Icc u₀ u₁))
    (hyinit : ∀ v ∈ Ico v₀ v₁, y (u₀, v) = y₀ v)
    (hderiv : ∀ v ∈ Ico v₀ v₁, ∀ u ∈ Ioo u₀ u₁,
      HasDerivAt (fun s => y (s, v))
        (a (u, v) * y (u, v) + b (u, v)) u) :
    ∃ Y : ℝ × ℝ → ℝ,
      ContinuousOn Y (Icc u₀ u₁ ×ˢ Icc v₀ v₁) ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ico v₀ v₁, Y (u, v) = y (u, v) := by
  apply exists_continuousOn_closed_rectangle_of_linear_volterra
    hu hv ha hb hy₀ hy hyinit
  intro v hv' u hu'
  have hvClosed : v ∈ Icc v₀ v₁ := ⟨hv'.1, hv'.2.le⟩
  have hA : ContinuousOn (fun s => a (s, v)) (Icc u₀ u₁) :=
    ha.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hvClosed⟩)
  have hB : ContinuousOn (fun s => b (s, v)) (Icc u₀ u₁) :=
    hb.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hvClosed⟩)
  have hsource : ContinuousOn
      (fun s => a (s, v) * y (s, v) + b (s, v)) (Icc u₀ u) :=
    ((hA.mul (hy v hv')).add hB).mono
      (fun s hs => ⟨hs.1, hs.2.trans hu'.2⟩)
  have hint : IntervalIntegrable
      (fun s => a (s, v) * y (s, v) + b (s, v)) volume u₀ u :=
    hsource.intervalIntegrable_of_Icc hu'.1
  have hresult := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hu'.1 ((hy v hv').mono (fun s hs => ⟨hs.1, hs.2.trans hu'.2⟩))
    (by
      intro s hs
      exact hderiv v hv' s ⟨hs.1, hs.2.trans_le hu'.2⟩)
    hint
  exact hresult.symm

end intervalIntegral

end
