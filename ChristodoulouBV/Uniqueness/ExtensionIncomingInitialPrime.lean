module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyTailGap
public import ChristodoulouBV.Uniqueness.ExtensionTransportEquation
import ChristodoulouBV.BVSolution.InitialData
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The outgoing quotient jet on the initial edge

The gauge `r(0,v)=v/2` gives `λ(0,v)=1/2`, so the continuous initial
value of the coordinate expression for `α′` is `4α₀′(v)`.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The outgoing derivative expression at `u = 0` equals four times the
prescribed initial derivative. This is an edge value of the coordinate
expression; the subtype-valued `alphaPrime` has domain `u > 0`. -/
theorem initial_alphaPrime_formula
    {b : ℝ} {S : Fields} {alpha₀ : ℝ → ℝ}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) :
    deriv (fun t => S.alpha 0 t / S.lam 0 t) v / S.lam 0 v =
      4 * deriv alpha₀ v := by
  have hlam (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) b) :
      S.lam 0 w = 1 / 2 :=
    initial_lam_eq_of_gauge H (fun t ht => (hdata t ht).1) hw
  have heq : (fun t => S.alpha 0 t / S.lam 0 t) =ᶠ[𝓝 v]
      (fun t => 2 * alpha₀ t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    rw [(hdata t ht).2, hlam t ht]
    ring
  rw [heq.deriv_eq, hlam v hv]
  have hdiff : DifferentiableAt ℝ alpha₀ v :=
    ((hα.mono (fun _ h => le_of_lt h)).differentiableOn (by norm_num)
      v hv.1).differentiableAt (isOpen_Ioi.mem_nhds hv.1)
  have hder : deriv (fun t => 2 * alpha₀ t) v = 2 * deriv alpha₀ v :=
    (hdiff.hasDerivAt.const_mul 2).deriv
  rw [hder]
  ring

/-- The initial values of the outgoing derivative expression have one
bound for all finite members before `vStar`. -/
theorem exists_initial_alphaPrime_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar vBar : ℝ} {S : ℝ → Fields}
    (hvBar : 0 < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ v : ℝ, vBar ≤ v → v < b →
          |deriv (fun t => (S b).alpha 0 t / (S b).lam 0 t) v /
            (S b).lam 0 v| ≤ M := by
  have hαopen : ContDiffOn ℝ 1 alpha₀ (Ioi 0) :=
    hα.mono (fun v hv => hv.le)
  have hderiv : ContinuousOn (deriv alpha₀) (Icc vBar vStar) :=
    (hαopen.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun v hv => hvBar.trans_le hv.1)
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hderiv
  have hA0 : 0 ≤ A := by
    have h := hA vBar ⟨le_rfl, hvBarStar.le⟩
    exact (norm_nonneg _).trans h
  refine ⟨4 * A, by positivity, ?_⟩
  intro b hb v hvBarv hvb
  have hv : v ∈ Ioo (0 : ℝ) b := ⟨hvBar.trans_le hvBarv, hvb⟩
  rw [initial_alphaPrime_formula (hfamily b hb).1 hα (hfamily b hb).2 hv]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using
      hA v ⟨hvBarv, (hvb.trans hb.2).le⟩) (by norm_num)

end ChristodoulouBV.Uniqueness

end
