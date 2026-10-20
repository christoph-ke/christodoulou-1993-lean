module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A terminal value from a bounded derivative

Uniform bounds on the ordinary derivative over a half-open interval give a
Lipschitz extension through its missing right endpoint.
-/

public section

open Set
open scoped NNReal

/-- A real function with uniformly bounded derivative before a finite
endpoint agrees there with a globally Lipschitz function. -/
theorem exists_lipschitz_extension_of_deriv_bound_on_Ico
    {a b M : ℝ} {f : ℝ → ℝ} (_hab : a < b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Ico a b, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ Ico a b, |deriv f x| ≤ M) :
    ∃ F : ℝ → ℝ,
      LipschitzWith ⟨M, hM⟩ F ∧ EqOn f F (Ico a b) := by
  have hbound' : ∀ x ∈ Ico a b,
      ‖deriv f x‖₊ ≤ (⟨M, hM⟩ : ℝ≥0) := by
    intro x hx
    apply NNReal.coe_le_coe.mp
    change ‖deriv f x‖ ≤ M
    simpa only [Real.norm_eq_abs] using hbound x hx
  exact ((convex_Ico a b).lipschitzOnWith_of_nnnorm_deriv_le hf hbound').extend_real

/-- A bounded derivative yields a continuous extension on the closed
interval, preserving all values below the right endpoint. -/
theorem exists_continuousOn_Icc_of_deriv_bound_on_Ico
    {a b M : ℝ} {f : ℝ → ℝ} (hab : a < b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Ico a b, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ Ico a b, |deriv f x| ≤ M) :
    ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc a b) ∧ EqOn f F (Ico a b) := by
  obtain ⟨F, hF, hEq⟩ :=
    exists_lipschitz_extension_of_deriv_bound_on_Ico hab hM hf hbound
  exact ⟨F, hF.continuous.continuousOn, hEq⟩

/-- Continuity at both endpoints upgrades an interior derivative bound to
a Lipschitz bound on the entire closed interval. -/
theorem lipschitzOnWith_Icc_of_continuousOn_deriv_bound_Ioo
    {a b M : ℝ} {f : ℝ → ℝ} (hab : a < b) (hM : 0 ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ Ioo a b, |deriv f x| ≤ M) :
    LipschitzOnWith ⟨M, hM⟩ f (Icc a b) := by
  have hbound' : ∀ x ∈ Ioo a b,
      ‖deriv f x‖₊ ≤ (⟨M, hM⟩ : ℝ≥0) := by
    intro x hx
    apply NNReal.coe_le_coe.mp
    change ‖deriv f x‖ ≤ M
    simpa only [Real.norm_eq_abs] using hbound x hx
  have hOpen :=
    (convex_Ioo a b).lipschitzOnWith_of_nnnorm_deriv_le hdiff hbound'
  have hclosure : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  rw [← hclosure] at hcont ⊢
  exact hOpen.closure hcont

end
