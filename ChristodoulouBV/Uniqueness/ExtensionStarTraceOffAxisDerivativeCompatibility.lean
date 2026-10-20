module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisAlphaPrimeVolterra
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisLambdaVVolterra
import Mathlib.Tactic.Linarith

/-!
# Compatibility of terminal derivative traces with every old cutoff

Agreement of compatible values on an open overlap gives agreement of their
ordinary outgoing derivatives.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Two finite cutoffs have the same outgoing derivative at a common point
when both agree locally with one canonical value trace. -/
theorem deriv_eq_of_common_terminal_value_trace
    {vStar vBar v b₁ b₂ : ℝ} {F : ℝ → ℝ → ℝ} {G : ℝ → ℝ}
    (hmatch : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ w ∈ Ico vBar b, G w = F b w)
    (hb₁ : b₁ ∈ Ioo (0 : ℝ) vStar)
    (hb₂ : b₂ ∈ Ioo (0 : ℝ) vStar)
    (hv : v ∈ Ioo vBar (min b₁ b₂)) :
    deriv (F b₁) v = deriv (F b₂) v := by
  have heq : F b₁ =ᶠ[𝓝 v] F b₂ := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
    have hw₁ : w ∈ Ico vBar b₁ :=
      ⟨hw.1.le, hw.2.trans_le (min_le_left _ _)⟩
    have hw₂ : w ∈ Ico vBar b₂ :=
      ⟨hw.1.le, hw.2.trans_le (min_le_right _ _)⟩
    exact (hmatch b₁ hb₁ w hw₁).symm.trans (hmatch b₂ hb₂ w hw₂)
  exact heq.deriv_eq

/-- The parametric Volterra trace of `α′` agrees with the outgoing derivative
expression on every finite family member below `vStar`. -/
theorem alphaPrime_terminal_trace_eq_old
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (haBar : a < vBar)
    (T : OffAxisTerminalTraces a vBar vStar S)
    {P : ℝ × ℝ → ℝ}
    (hP : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
      P (u, v) =
        deriv (fun t =>
          (S ((v + vStar) / 2)).alpha u t /
            (S ((v + vStar) / 2)).lam u t) v /
          (S ((v + vStar) / 2)).lam u v)
    {b u v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar b) :
    P (u, v) =
      deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
        (S b).lam u v := by
  let b₀ : ℝ := (v + vStar) / 2
  have hvStar : v < vStar := hv.2.trans hb.2
  have hbc : b₀ ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b₀]
    constructor <;> linarith only [ha, haBar, hv.1, hvStar]
  have hvb₀ : v < b₀ := by dsimp [b₀]; linarith only [hvStar]
  have hv₀ : v ∈ Ico vBar vStar := ⟨hv.1.le, hvStar⟩
  have hderiv := deriv_eq_of_common_terminal_value_trace
    (F := fun b w => (S b).alpha u w / (S b).lam u w)
    (G := fun w => T.quotient (u, w))
    (by
      intro c hc w hw
      exact (T.match_old c hc u hu w hw).2.2.2.2.2.2.2.2)
    hbc hb ⟨hv.1, lt_min hvb₀ hv.2⟩
  have hlam₀ := (T.match_old b₀ hbc u hu v ⟨hv.1.le, hvb₀⟩).2.2.1
  have hlam := (T.match_old b hb u hu v ⟨hv.1.le, hv.2⟩).2.2.1
  rw [hP u hu v hv₀, hderiv, ← hlam, hlam₀]

/-- The parametric Volterra trace of `λᵥ` agrees with every finite family
member below the terminal edge. -/
theorem lambdaV_terminal_trace_eq_old
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (haBar : a < vBar)
    (T : OffAxisTerminalTraces a vBar vStar S)
    {L : ℝ × ℝ → ℝ}
    (hL : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
      L (u, v) = deriv ((S ((v + vStar) / 2)).lam u) v)
    {b u v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar b) :
    L (u, v) = deriv ((S b).lam u) v := by
  let b₀ : ℝ := (v + vStar) / 2
  have hvStar : v < vStar := hv.2.trans hb.2
  have hbc : b₀ ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b₀]
    constructor <;> linarith only [ha, haBar, hv.1, hvStar]
  have hvb₀ : v < b₀ := by dsimp [b₀]; linarith only [hvStar]
  have hderiv := deriv_eq_of_common_terminal_value_trace
    (F := fun b w => (S b).lam u w)
    (G := fun w => T.lam (u, w))
    (by
      intro c hc w hw
      exact (T.match_old c hc u hu w hw).2.2.1)
    hbc hb ⟨hv.1, lt_min hvb₀ hv.2⟩
  rw [hL u hu v ⟨hv.1.le, hvStar⟩, hderiv]

end ChristodoulouBV.Uniqueness

end
