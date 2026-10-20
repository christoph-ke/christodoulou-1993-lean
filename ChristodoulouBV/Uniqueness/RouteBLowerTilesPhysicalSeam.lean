module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesCoverState
import Mathlib.Tactic

/-!
# Physical fields from matching seven-state jets

Each primary physical field is a smooth coordinate of a safe rectangle
state. The scalar field is the quotient of scalar radius by radius.
-/

@[expose] public section

noncomputable section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Read a primary physical field directly from a seven-state value. -/
def lowerRectangleSelector (c : RouteBField)
    (z : C1Solution.RectangleState) : ℝ :=
  match c with
  | .radius => C1Solution.stateRadius z
  | .scalar => C1Solution.statePhi z
  | .mass => C1Solution.stateMass z
  | .expansion => C1Solution.stateLam z
  | .contraction => C1Solution.stateNu z
  | .outgoing => C1Solution.stateAlpha z
  | .incoming => C1Solution.stateBeta z

/-- The reconstructed physical field is selector evaluation on the state. -/
theorem routeBField_rectangleStateFields_eq
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (c : RouteBField) (p : ℝ × ℝ) :
    routeBField (rectangleStateFields Z) c p =
      lowerRectangleSelector c (Z p) := by
  cases c <;> rfl

/-- Every primary selector is differentiable at a safe state. -/
theorem lowerRectangleSelector_differentiableAt
    (c : RouteBField) {z : C1Solution.RectangleState}
    (hz : C1Solution.IsSafeRectangleState z) :
    DifferentiableAt ℝ (lowerRectangleSelector c) z := by
  cases c with
  | radius =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState => w.2.2.2.2.1) z
      fun_prop
  | scalar =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState =>
          w.2.2.2.2.2 / w.2.2.2.2.1) z
      have hψ : ContDiffAt ℝ 1
          (fun w : C1Solution.RectangleState => w.2.2.2.2.2) z := by
        fun_prop
      have hr : ContDiffAt ℝ 1
          (fun w : C1Solution.RectangleState => w.2.2.2.2.1) z := by
        fun_prop
      exact (hψ.div hr (ne_of_gt hz.1)).differentiableAt (by norm_num)
  | mass =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState => w.2.2.2.1) z
      fun_prop
  | expansion =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState => w.1.1) z
      fun_prop
  | contraction =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState => w.2.1) z
      fun_prop
  | outgoing =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState => w.1.2) z
      fun_prop
  | incoming =>
      change DifferentiableAt ℝ
        (fun w : C1Solution.RectangleState => w.2.2.1) z
      fun_prop

/-- Equal safe seven-state values and full jets give equal full jets of all
seven reconstructed physical fields. -/
theorem routeBFieldsJetEqOn_rectangleStateFields
    {K₁ K₂ : Set (ℝ × ℝ)}
    (hunique₁ : UniqueDiffOn ℝ K₁) (hunique₂ : UniqueDiffOn ℝ K₂)
    (Z₁ Z₂ : ℝ × ℝ → C1Solution.RectangleState)
    (hZ₁ : ContDiffOn ℝ 1 Z₁ K₁)
    (hZ₂ : ContDiffOn ℝ 1 Z₂ K₂)
    (hsafe₁ : ∀ p ∈ K₁, C1Solution.IsSafeRectangleState (Z₁ p))
    (hvalue : EqOn Z₁ Z₂ (K₁ ∩ K₂))
    (hjet : EqOn (fderivWithin ℝ Z₁ K₁)
      (fderivWithin ℝ Z₂ K₂) (K₁ ∩ K₂)) :
    RouteBFieldsJetEqOn
      (rectangleStateFields Z₁) (rectangleStateFields Z₂) K₁ K₂ := by
  intro c p hp
  have hp₁ : p ∈ K₁ := hp.1
  have hp₂ : p ∈ K₂ := hp.2
  let F := lowerRectangleSelector c
  have hF : DifferentiableAt ℝ F (Z₁ p) :=
    lowerRectangleSelector_differentiableAt c (hsafe₁ p hp₁)
  have hZ₁diff : DifferentiableWithinAt ℝ Z₁ K₁ p :=
    (hZ₁.differentiableOn (by norm_num)) p hp₁
  have hZ₂diff : DifferentiableWithinAt ℝ Z₂ K₂ p :=
    (hZ₂.differentiableOn (by norm_num)) p hp₂
  have hF₂ : DifferentiableAt ℝ F (Z₂ p) :=
    (hvalue hp).symm ▸ hF
  have hcomp₁ := hF.hasFDerivAt.comp_hasFDerivWithinAt p
    hZ₁diff.hasFDerivWithinAt
  have hcomp₂ := hF₂.hasFDerivAt.comp_hasFDerivWithinAt p
    hZ₂diff.hasFDerivWithinAt
  have hderiv₁ := hcomp₁.fderivWithin (hunique₁ p hp₁)
  have hderiv₂ := hcomp₂.fderivWithin (hunique₂ p hp₂)
  have hfield₁ : routeBField (rectangleStateFields Z₁) c = F ∘ Z₁ := by
    funext q
    exact routeBField_rectangleStateFields_eq Z₁ c q
  have hfield₂ : routeBField (rectangleStateFields Z₂) c = F ∘ Z₂ := by
    funext q
    exact routeBField_rectangleStateFields_eq Z₂ c q
  rw [hfield₁, hfield₂]
  rw [hderiv₁, hderiv₂, ← hvalue hp, hjet hp]

end ChristodoulouBV.Uniqueness

end
