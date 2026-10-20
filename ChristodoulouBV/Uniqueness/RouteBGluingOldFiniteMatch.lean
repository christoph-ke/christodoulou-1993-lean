module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldConstruction
public import ChristodoulouBV.Uniqueness.ExtensionFamily
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Independence of the old finite cutoff

Canonical old representatives agree on any smaller closed triangle. In the
interior this is the compatible-family theorem; continuity closes the axis
and finite top edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Two canonical old members agree on every common strict closed cutoff,
including the diagonal where their frozen radius and mass are unspecified. -/
theorem routeBCanonicalOldFields_eq_on_closed_triangle
    {alpha₀ : ℝ → ℝ} {vStar B d₁ d₂ : ℝ} {S : ℝ → Fields}
    (hB : 0 < B) (hd₁ : d₁ ∈ Ioo B vStar)
    (hd₂ : d₂ ∈ Ioo B vStar)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v)) :
    RouteBFieldsEqOn (routeBCanonicalOldFields d₁ (S d₁))
      (routeBCanonicalOldFields d₂ (S d₂))
      (closedCoordTriangle 0 B) := by
  have hd₁' : d₁ ∈ Ioo (0 : ℝ) vStar := ⟨hB.trans hd₁.1, hd₁.2⟩
  have hd₂' : d₂ ∈ Ioo (0 : ℝ) vStar := ⟨hB.trans hd₂.1, hd₂.2⟩
  let F₁ := routeBCanonicalOldFields d₁ (S d₁)
  let F₂ := routeBCanonicalOldFields d₂ (S d₂)
  have hC1₁ : RouteBFieldsC1On F₁ (closedCoordTriangle 0 B) :=
    routeBCanonicalOldFields_c1 hB hd₁.1 (hfamily d₁ hd₁').1
  have hC1₂ : RouteBFieldsC1On F₂ (closedCoordTriangle 0 B) :=
    routeBCanonicalOldFields_c1 hB hd₂.1 (hfamily d₂ hd₂').1
  intro c
  have hOpen : EqOn (routeBField F₁ c) (routeBField F₂ c)
      (openCoordTriangle 0 B) := by
    intro p hp
    have hp₁ : p ∈ developmentWithInitialEdge d₁ :=
      ⟨hp.1.le, hp.2.1, hp.2.2.trans hd₁.1⟩
    have hp₂ : p ∈ developmentWithInitialEdge d₂ :=
      ⟨hp.1.le, hp.2.1, hp.2.2.trans hd₂.1⟩
    have hEq := family_fields_eq_on_common_development
      hfamily hd₁' hd₂' ⟨hp₁, hp₂⟩
    cases c
    · have hr₁ := C1Solution.canonicalRadius_eq_radius
        hB hd₁.1 (hfamily d₁ hd₁').1 hp.1.le hp.2.1 hp.2.2.le
      have hr₂ := C1Solution.canonicalRadius_eq_radius
        hB hd₂.1 (hfamily d₂ hd₂').1 hp.1.le hp.2.1 hp.2.2.le
      exact hr₁.trans (hEq.1.trans hr₂.symm)
    · exact hEq.2.1
    · change C1Solution.canonicalMass d₁ (S d₁) p =
        C1Solution.canonicalMass d₂ (S d₂) p
      rw [C1Solution.canonicalMass_eq_mass hp₁,
        C1Solution.canonicalMass_eq_mass hp₂]
      exact hEq.2.2.1
    · exact hEq.2.2.2.1
    · exact hEq.2.2.2.2.1
    · exact hEq.2.2.2.2.2.1
    · exact hEq.2.2.2.2.2.2
  exact hOpen.of_subset_closure (hC1₁ c).continuousOn
    (hC1₂ c).continuousOn
    (by intro p hp; exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
    (by rw [closure_openCoordTriangle hB])

end ChristodoulouBV.Uniqueness

end
