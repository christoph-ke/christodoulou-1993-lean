module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseCharacteristic
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Stability of linearized transverse Goursat jets

The linearized transverse recursion is a short Volterra contraction. If its
full derivative field and its known characteristic jet converge uniformly,
then its unknown transverse jet converges uniformly to a solution of the
limiting equation.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform convergence of a first transverse jet sequence satisfying the
full linearized recursion, relative to any limiting Volterra solution. -/
theorem tendsto_first_transverse_of_linearized_recursion
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (d : ℝ → E) (κ : NNReal)
    (D : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (R : ℕ → C(rectangle u₀ u₁ v₀ v₁, F))
    (P : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (D_lim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (R_lim : C(rectangle u₀ u₁ v₀ v₁, F))
    (P_lim : C(rectangle u₀ u₁ v₀ v₁, E))
    (hD : Tendsto D atTop (𝓝 D_lim))
    (hR : Tendsto R atTop (𝓝 R_lim))
    (hκ : ∀ n p (x : E),
      ‖D n p ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖)
    (hsmall : (κ : ℝ) * (u₁ - u₀) < 1)
    (hrec : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      P (n + 1) p = d p.1.2 + ∫ s in u₀..p.1.1,
        D n (clippedPoint hu hv (s, p.1.2))
          ((0, 1),
            (P n (clippedPoint hu hv (s, p.1.2)),
             R n (clippedPoint hu hv (s, p.1.2)))))
    (hlim : ∀ p : rectangle u₀ u₁ v₀ v₁,
      P_lim p = d p.1.2 + ∫ s in u₀..p.1.1,
        D_lim (clippedPoint hu hv (s, p.1.2))
          ((0, 1),
            (P_lim (clippedPoint hu hv (s, p.1.2)),
             R_lim (clippedPoint hu hv (s, p.1.2))))) :
    Tendsto P atTop (𝓝 P_lim) := by
  let A : ℕ → C(rectangle u₀ u₁ v₀ v₁, E →L[ℝ] E) :=
    fun n => firstLinearCoefficient (D n)
  let J : ℕ → C(rectangle u₀ u₁ v₀ v₁, E) :=
    fun n => firstLinearSource (D n) (R n)
  let A_lim := firstLinearCoefficient D_lim
  let J_lim := firstLinearSource D_lim R_lim
  have hA : Tendsto A atTop (𝓝 A_lim) :=
    tendsto_firstLinearCoefficient D D_lim hD
  have hJ : Tendsto J atTop (𝓝 J_lim) :=
    tendsto_firstLinearSource D R D_lim R_lim hD hR
  have hAbound : ∀ n p, ‖A n p‖ ≤ (κ : ℝ) := by
    intro n p
    exact norm_firstLinearCoefficient_le (D n) κ κ.coe_nonneg (hκ n) p
  have hrec' : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      P (n + 1) p = d p.1.2 + ∫ s in u₀..p.1.1,
        A n (clippedPoint hu hv (s, p.1.2))
          (P n (clippedPoint hu hv (s, p.1.2))) +
        J n (clippedPoint hu hv (s, p.1.2)) := by
    intro n p
    rw [hrec n p]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact first_linearized_split
      (D n (clippedPoint hu hv (s, p.1.2)))
      (P n (clippedPoint hu hv (s, p.1.2)))
      (R n (clippedPoint hu hv (s, p.1.2)))
  have hlim' : ∀ p : rectangle u₀ u₁ v₀ v₁,
      P_lim p = d p.1.2 + ∫ s in u₀..p.1.1,
        A_lim (clippedPoint hu hv (s, p.1.2))
          (P_lim (clippedPoint hu hv (s, p.1.2))) +
        J_lim (clippedPoint hu hv (s, p.1.2)) := by
    intro p
    rw [hlim p]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    exact first_linearized_split
      (D_lim (clippedPoint hu hv (s, p.1.2)))
      (P_lim (clippedPoint hu hv (s, p.1.2)))
      (R_lim (clippedPoint hu hv (s, p.1.2)))
  exact tendsto_of_linear_horizontal_volterra_recursion hu hv d κ
    A J P A_lim J_lim P_lim hAbound hJ hsmall hrec' hlim' hA


/-- Uniform convergence of a second transverse jet sequence satisfying the
full linearized recursion, relative to any limiting Volterra solution. -/
theorem tendsto_second_transverse_of_linearized_recursion
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (d : ℝ → F) (κ : NNReal)
    (D : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (S : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (Q : ℕ → C(rectangle u₀ u₁ v₀ v₁, F))
    (D_lim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (S_lim : C(rectangle u₀ u₁ v₀ v₁, E))
    (Q_lim : C(rectangle u₀ u₁ v₀ v₁, F))
    (hD : Tendsto D atTop (𝓝 D_lim))
    (hS : Tendsto S atTop (𝓝 S_lim))
    (hκ : ∀ n p (y : F),
      ‖D n p ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖)
    (hsmall : (κ : ℝ) * (v₁ - v₀) < 1)
    (hrec : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      Q (n + 1) p = d p.1.1 + ∫ t in v₀..p.1.2,
        D n (clippedPoint hu hv (p.1.1, t))
          ((1, 0),
            (S n (clippedPoint hu hv (p.1.1, t)),
             Q n (clippedPoint hu hv (p.1.1, t)))))
    (hlim : ∀ p : rectangle u₀ u₁ v₀ v₁,
      Q_lim p = d p.1.1 + ∫ t in v₀..p.1.2,
        D_lim (clippedPoint hu hv (p.1.1, t))
          ((1, 0),
            (S_lim (clippedPoint hu hv (p.1.1, t)),
             Q_lim (clippedPoint hu hv (p.1.1, t))))) :
    Tendsto Q atTop (𝓝 Q_lim) := by
  let A : ℕ → C(rectangle u₀ u₁ v₀ v₁, F →L[ℝ] F) :=
    fun n => secondLinearCoefficient (D n)
  let J : ℕ → C(rectangle u₀ u₁ v₀ v₁, F) :=
    fun n => secondLinearSource (D n) (S n)
  let A_lim := secondLinearCoefficient D_lim
  let J_lim := secondLinearSource D_lim S_lim
  have hA : Tendsto A atTop (𝓝 A_lim) :=
    tendsto_secondLinearCoefficient D D_lim hD
  have hJ : Tendsto J atTop (𝓝 J_lim) :=
    tendsto_secondLinearSource D S D_lim S_lim hD hS
  have hAbound : ∀ n p, ‖A n p‖ ≤ (κ : ℝ) := by
    intro n p
    exact norm_secondLinearCoefficient_le (D n) κ κ.coe_nonneg (hκ n) p
  have hrec' : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      Q (n + 1) p = d p.1.1 + ∫ t in v₀..p.1.2,
        A n (clippedPoint hu hv (p.1.1, t))
          (Q n (clippedPoint hu hv (p.1.1, t))) +
        J n (clippedPoint hu hv (p.1.1, t)) := by
    intro n p
    rw [hrec n p]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact second_linearized_split
      (D n (clippedPoint hu hv (p.1.1, t)))
      (S n (clippedPoint hu hv (p.1.1, t)))
      (Q n (clippedPoint hu hv (p.1.1, t)))
  have hlim' : ∀ p : rectangle u₀ u₁ v₀ v₁,
      Q_lim p = d p.1.1 + ∫ t in v₀..p.1.2,
        A_lim (clippedPoint hu hv (p.1.1, t))
          (Q_lim (clippedPoint hu hv (p.1.1, t))) +
        J_lim (clippedPoint hu hv (p.1.1, t)) := by
    intro p
    rw [hlim p]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact second_linearized_split
      (D_lim (clippedPoint hu hv (p.1.1, t)))
      (S_lim (clippedPoint hu hv (p.1.1, t)))
      (Q_lim (clippedPoint hu hv (p.1.1, t)))
  let σ : C(rectangle v₀ v₁ u₀ u₁, rectangle u₀ u₁ v₀ v₁) :=
    ⟨fun p => ⟨(p.1.2, p.1.1), by
      have hp := p.2
      simpa only [rectangle, mem_prod] using And.symm hp⟩,
      Continuous.subtype_mk
        (continuous_swap.comp continuous_subtype_val)
        (fun p => by
          have hp := p.2
          simpa only [rectangle, mem_prod, Function.comp_def, Prod.swap]
            using And.symm hp)⟩
  let As : ℕ → C(rectangle v₀ v₁ u₀ u₁, F →L[ℝ] F) :=
    fun n => (A n).comp σ
  let Js : ℕ → C(rectangle v₀ v₁ u₀ u₁, F) :=
    fun n => (J n).comp σ
  let Qs : ℕ → C(rectangle v₀ v₁ u₀ u₁, F) :=
    fun n => (Q n).comp σ
  have hAs : Tendsto As atTop (𝓝 (A_lim.comp σ)) := by
    exact ((ContinuousMap.continuous_precomp σ).tendsto A_lim).comp hA
  have hJs : Tendsto Js atTop (𝓝 (J_lim.comp σ)) := by
    exact ((ContinuousMap.continuous_precomp σ).tendsto J_lim).comp hJ
  have hQs : Tendsto Qs atTop (𝓝 (Q_lim.comp σ)) := by
    apply tendsto_of_linear_horizontal_volterra_recursion hv hu d κ
      As Js Qs (A_lim.comp σ) (J_lim.comp σ) (Q_lim.comp σ)
      (by intro n p; exact hAbound n (σ p)) hJs hsmall
    · intro n p
      have h := hrec' n (σ p)
      exact h
    · intro p
      exact hlim' (σ p)
    · exact hAs
  let hσ : C(rectangle u₀ u₁ v₀ v₁, rectangle v₀ v₁ u₀ u₁) :=
    ⟨fun p => ⟨(p.1.2, p.1.1), by
      have hp := p.2
      simpa only [rectangle, mem_prod] using And.symm hp⟩,
      Continuous.subtype_mk
        (continuous_swap.comp continuous_subtype_val)
        (fun p => by
          have hp := p.2
          simpa only [rectangle, mem_prod, Function.comp_def, Prod.swap]
            using And.symm hp)⟩
  have hback := ((ContinuousMap.continuous_precomp hσ).tendsto
    (Q_lim.comp σ)).comp hQs
  have hσσ (p : rectangle u₀ u₁ v₀ v₁) : σ (hσ p) = p := by
    apply Subtype.ext
    dsimp [σ, hσ]
  convert hback using 1
  · funext n
    ext p
    change Q n p = Q n (σ (hσ p))
    rw [hσσ p]
  · congr 1

end Goursat

end
