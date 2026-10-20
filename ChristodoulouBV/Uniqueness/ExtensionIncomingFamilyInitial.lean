module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingInitialGap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Initial-edge bounds shared by the extension family

The prescribed scalar data are bounded on the compact interval ending at
`vStar`. The same bound controls the initial scalar amplitude in every
finite member, independently of its cutoff.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The common initial data bound both `α` and `θ` on every member before
`vStar`. This supplies the scalar-data bound for the incoming strip. -/
theorem exists_initial_scalar_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {S : ℝ → Fields}
    (hvStar : 0 < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ v ∈ Ioo (0 : ℝ) b,
          |(S b).alpha 0 v| ≤ A ∧ |(S b).theta 0 v| ≤ 2 * A := by
  have hcont : ContinuousOn alpha₀ (Icc 0 vStar) :=
    hα.continuousOn.mono (fun _ hw => hw.1)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hA0 : 0 ≤ A := by
    have hzero := hA 0 ⟨le_refl 0, hvStar.le⟩
    exact (norm_nonneg (alpha₀ 0)).trans hzero
  refine ⟨A, hA0, ?_⟩
  intro b hb v hv
  obtain ⟨H, hdata⟩ := hfamily b hb
  have hmember (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) b) :
      |(S b).alpha 0 w| ≤ A := by
    rw [(hdata w hw).2]
    simpa only [Real.norm_eq_abs] using
      hA w ⟨hw.1.le, hw.2.trans hb.2 |>.le⟩
  exact ⟨hmember v hv,
    initial_theta_abs_le_of_alpha_bound H
      (fun w hw => (hdata w hw).1) hv hmember⟩

end ChristodoulouBV.Uniqueness

end
