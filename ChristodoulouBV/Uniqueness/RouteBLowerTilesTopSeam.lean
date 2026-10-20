module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesSeamCorner
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Full seven-state jets at the top of the old base

The old and new states have one terminal trace and one initial gauge. The
pointwise safe horizontal seam theorem identifies both incoming and outgoing
full relative first jets at every point of their shared edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The canonical old base and any safe classical lower strip with its
prescribed gauge have matching full first jets along `v = vStar`. -/
theorem RouteBTerminalBaseJets.full_jets_eq_lower_strip_on_top
    {a vBar vStar c η b : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c) (hη : 0 < η) (hTop : vStar + η < b)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ t ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge t) (S t) ∧
      (∀ v ∈ Ioo (0 : ℝ) t,
        (S t).r 0 v = v / 2 ∧ (S t).alpha 0 v = alpha₀ v))
    (hfloor : ∀ t ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < t → c ≤ (S t).lam u v)
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hZ : ContDiffOn ℝ 1 Z
      (Goursat.rectangle 0 a vStar (vStar + η)))
    (hsafe : ∀ p ∈ Goursat.rectangle 0 a vStar (vStar + η),
      C1Solution.IsSafeRectangleState (Z p))
    (hclassical : RouteBClassicalJetOn b
      (Goursat.rectangle 0 a vStar (vStar + η))
      (rectangleStateFields Z))
    (htrace : ∀ u ∈ Icc 0 a,
      Z (u, vStar) = P.state.rectangleState (u, vStar))
    (hinit : ∀ v ∈ Icc vStar (vStar + η),
      (Z (0, v)).1 = (1 / 2, alpha₀ v)) :
    ∀ u ∈ Icc 0 a,
      fderivWithin ℝ (fun p => (P.state.rectangleState p).1)
        (Goursat.rectangle 0 a vBar vStar) (u, vStar) =
        fderivWithin ℝ (fun p => (Z p).1)
          (Goursat.rectangle 0 a vStar (vStar + η)) (u, vStar) ∧
      fderivWithin ℝ (fun p => (P.state.rectangleState p).2)
        (Goursat.rectangle 0 a vBar vStar) (u, vStar) =
        fderivWithin ℝ (fun p => (Z p).2)
          (Goursat.rectangle 0 a vStar (vStar + η)) (u, vStar) := by
  have hStar : 0 < vStar := ha.trans (haBar.trans hBarStar)
  have hOldC1 : ContDiffOn ℝ 1
      P.state.rectangleState (Goursat.rectangle 0 a vBar vStar) := by
    simpa only [Goursat.rectangle] using J.state_c1
  have hOldSafe : ∀ p ∈ Goursat.rectangle 0 a vBar vStar,
      C1Solution.IsSafeRectangleState (P.state.rectangleState p) := by
    intro p hp
    exact P.safe_on_closed_base ha haBar hBarStar hc hfamily hfloor
      hp.1 hp.2
  have hOldJet : ∀ u ∈ Icc 0 a, ∀ v ∈ Icc vBar vStar,
      HasDerivWithinAt
        (fun s => (P.state.rectangleState (s, v)).1)
        (C1Solution.rectangleF (P.state.rectangleState (u, v)))
        (Icc 0 a) u ∧
      HasDerivWithinAt
        (fun t => (P.state.rectangleState (u, t)).2)
        (C1Solution.rectangleG (P.state.rectangleState (u, v)))
        (Icc vBar vStar) v := by
    intro u hu v hv
    exact J.characteristic_jets ha haBar hBarStar hu hv
  have hNewJet := characteristic_jets_of_classical_strip
    ha (haBar.trans hBarStar) hη hTop Z hZ hsafe hclassical
  have hOldGauge : ∀ v ∈ Icc vBar vStar,
      (P.state.rectangleState (0, v)).1 = (1 / 2, alpha₀ v) := by
    intro v hv
    obtain ⟨hLam, hAlpha⟩ :=
      P.initial_terminal_gauge ha haBar hBarStar hα hfamily hv
    change (P.state.lam (0, v), P.state.alpha (0, v)) = _
    rw [hLam, hAlpha]
  have hCornerOld := hasDerivWithinAt_incoming_gauge_at
    (X := fun p => (P.state.rectangleState p).1)
    hStar hBarStar.le le_rfl hα hOldGauge
  have hCornerNew := hasDerivWithinAt_incoming_gauge_at
    (X := fun p => (Z p).1)
    hStar le_rfl (le_add_of_nonneg_right hη.le) hα hinit
  apply C1Solution.full_first_jets_eq_on_horizontal_seam_of_corner_data_safe
    ha hBarStar (by linarith only [hη])
    (fun p => (P.state.rectangleState p).1)
    (fun p => (P.state.rectangleState p).2)
    (fun p => (Z p).1) (fun p => (Z p).2)
    hOldC1.fst hOldC1.snd hZ.fst hZ.snd
    hOldSafe hsafe hOldJet hNewJet
    (fun u hu => (htrace u hu).symm)
    (0, deriv alpha₀ vStar) hCornerOld hCornerNew

end ChristodoulouBV.Uniqueness

end
