module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesBaseData
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Global representatives of the prescribed initial gauge

Clipping a C¹ prescribed scalar amplitude to the proposed initial edge
supplies continuous global characteristic data and continuous relative
derivatives on that edge.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The clipped initial incoming pair prescribed by the gauge. -/
@[expose] noncomputable def lowerInitialIncoming
    (vStar L : ℝ) (alpha₀ : ℝ → ℝ) (v : ℝ) :
    C1Solution.IncomingState :=
  (1 / 2, alpha₀ (Goursat.clip vStar (vStar + L) v))

/-- A global representative of the relative initial incoming derivative. -/
@[expose] noncomputable def lowerInitialIncomingPrime
    (vStar L : ℝ) (alpha₀ : ℝ → ℝ) (v : ℝ) :
    C1Solution.IncomingState :=
  (0, derivWithin alpha₀ (Icc vStar (vStar + L))
    (Goursat.clip vStar (vStar + L) v))

/-- Gauge data from a prescribed C¹ scalar amplitude satisfy the
continuity and relative derivative requirements of the tile interface. -/
theorem lowerInitialIncoming_regular
    {vStar L : ℝ} {alpha₀ : ℝ → ℝ}
    (hvStar : 0 ≤ vStar) (hL : 0 < L)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0)) :
    Continuous (lowerInitialIncoming vStar L alpha₀) ∧
    ContinuousOn (lowerInitialIncomingPrime vStar L alpha₀)
      (Icc vStar (vStar + L)) ∧
    (∀ v ∈ Icc vStar (vStar + L),
      HasDerivWithinAt (lowerInitialIncoming vStar L alpha₀)
        (lowerInitialIncomingPrime vStar L alpha₀ v)
        (Icc vStar (vStar + L)) v) ∧
    (∀ v ∈ Icc vStar (vStar + L),
      lowerInitialIncoming vStar L alpha₀ v = (1 / 2, alpha₀ v)) := by
  let I := Icc vStar (vStar + L)
  have hI : I ⊆ Ici 0 := by
    intro v hv
    exact hvStar.trans hv.1
  have hαI : ContDiffOn ℝ 1 alpha₀ I := hα.mono hI
  have hclip : Continuous (Goursat.clip vStar (vStar + L)) :=
    Goursat.continuous_clip _ _
  have hmap : ∀ v, Goursat.clip vStar (vStar + L) v ∈ I := by
    intro v
    exact Goursat.clip_mem_Icc (le_add_of_nonneg_right hL.le) v
  have hαglob : Continuous
      (fun v => alpha₀ (Goursat.clip vStar (vStar + L) v)) :=
    hαI.continuousOn.comp_continuous hclip hmap
  have hprime : ContinuousOn (derivWithin alpha₀ I) I :=
    hαI.continuousOn_derivWithin
      (uniqueDiffOn_Icc (by linarith only [hL])) (by norm_num)
  constructor
  · exact continuous_const.prodMk hαglob
  constructor
  · change ContinuousOn
      (fun v => (0, derivWithin alpha₀ I
        (Goursat.clip vStar (vStar + L) v))) I
    exact continuousOn_const.prodMk
      (hprime.comp hclip.continuousOn (fun v hv => hmap v))
  constructor
  · intro v hv
    have heq : EqOn (lowerInitialIncoming vStar L alpha₀)
        (fun t => ((1 / 2 : ℝ), alpha₀ t)) I := by
      intro t ht
      simp [lowerInitialIncoming, Goursat.clip_eq_self ht]
    have hderiv : HasDerivWithinAt
        (fun t => ((1 / 2 : ℝ), alpha₀ t))
        (0, derivWithin alpha₀ I v) I v :=
      ((hasDerivAt_const v (1 / 2 : ℝ)).hasDerivWithinAt).prodMk
        ((hαI.differentiableOn (by norm_num) v hv).hasDerivWithinAt)
    have hevent : lowerInitialIncoming vStar L alpha₀ =ᶠ[𝓝[I] v]
        (fun t => ((1 / 2 : ℝ), alpha₀ t)) :=
      Filter.eventually_of_mem self_mem_nhdsWithin
        (fun t ht => heq ht)
    simpa [lowerInitialIncomingPrime, Goursat.clip_eq_self hv] using
      (hderiv.congr_of_eventuallyEq hevent (heq hv))
  · intro v hv
    simp [lowerInitialIncoming, Goursat.clip_eq_self hv]

end ChristodoulouBV.Uniqueness

end
