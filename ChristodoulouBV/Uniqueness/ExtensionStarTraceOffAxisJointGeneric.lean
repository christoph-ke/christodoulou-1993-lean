module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.CompatibleFamilyTerminalRectangle
public import ChristodoulouBV.C1Solution.ExtractionCore
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# A common terminal rectangle argument for old-family fields

The same cutoff-independent vertical derivative estimate and compact-triangle
regularity give a jointly continuous trace for any compatible scalar field.
This lemma is used for all lower-order fields on off-axis rectangles.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A compatible scalar component of the old family has a jointly continuous
terminal trace if its vertical derivative has one bound independent of the
cutoff. The regularity hypothesis concerns each finite member, not the
terminal trace. -/
theorem exists_joint_terminal_trace_of_compatible_c1_family
    {vStar a vBar M : ℝ} {F : ℝ → ℝ × ℝ → ℝ}
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hM : 0 ≤ M)
    (hcompat : ∀ b₁ ∈ Ioo (0 : ℝ) vStar,
      ∀ b₂ ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar (min b₁ b₂),
        F b₁ (u, v) = F b₂ (u, v))
    (hc1 : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ T : ℝ, 0 < T → T < b →
        ContDiffOn ℝ 1 (F b) (closedCoordTriangle 0 T))
    (hbound : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Ioc 0 a, ∀ v ∈ Ioo vBar b,
        |deriv (fun w => F b (u, w)) v| ≤ M) :
    ∃ G : ℝ × ℝ → ℝ,
      ContinuousOn G (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          G (u, v) = F b (u, v) := by
  apply exists_compatible_family_terminal_rectangle
    (le_refl 0) ha.le haBar hBarStar hM hcompat
  · intro b hb t ht
    let T : ℝ := (t + b) / 2
    have htB : t < b := ht.2
    have hT : 0 < T := by dsimp [T]; linarith only [ha, haBar, ht.1, htB]
    have hTb : T < b := by dsimp [T]; linarith only [htB]
    have htT : t < T := by dsimp [T]; linarith only [htB]
    apply (hc1 b hb T hT hTb).continuousOn.mono
    intro p hp
    exact ⟨hp.1.1, (hp.1.2.trans_lt (haBar.trans_le hp.2.1)).le,
      (hp.2.2.trans_lt htT).le⟩
  · intro b hb u hu v hv
    let T : ℝ := (v + b) / 2
    have hvb : v < b := hv.2
    have hT : 0 < T := by dsimp [T]; linarith only [ha, haBar, hv.1, hvb]
    have hTb : T < b := by dsimp [T]; linarith only [hvb]
    have hvT : v < T := by dsimp [T]; linarith only [hvb]
    exact (vertical_hasDerivAt_of_closed_jet
      (hc1 b hb T hT hTb) hu.1
      (hu.2.trans_lt (haBar.trans hv.1)) hvT
      (g := (fderivWithin ℝ (F b) (closedCoordTriangle 0 T) (u, v)) (0, 1))
      rfl).differentiableAt
  · intro b hb u hu v hv
    by_cases hu0 : u = 0
    · subst u
      let T : ℝ := (v + b) / 2
      have hT : 0 < T := by dsimp [T]; linarith only [ha, haBar, hv.1, hv.2]
      have hTb : T < b := by dsimp [T]; linarith only [hv.2]
      have hvT : v < T := by dsimp [T]; linarith only [hv.2]
      let K := closedCoordTriangle 0 T
      let J : ℝ → ℝ := fun s =>
        |(fderivWithin ℝ (F b) K (s, v)) (0, 1)|
      have hunique : UniqueDiffOn ℝ K :=
        uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
          (by rw [interior_closedCoordTriangle]
              exact openCoordTriangle_nonempty hT)
      have hjet : ContinuousOn (fun p => fderivWithin ℝ (F b) K p) K :=
        (hc1 b hb T hT hTb).continuousOn_fderivWithin hunique (by norm_num)
      have hJ : ContinuousOn J (Icc 0 a) := by
        apply ((hjet.clm_apply continuousOn_const).abs).comp
          (continuous_id.prodMk continuous_const).continuousOn
        intro s hs
        exact ⟨hs.1, ((hs.2.trans_lt haBar).trans_le hv.1.le).le, hvT.le⟩
      have hJbound : ∀ s ∈ Ioo 0 a, J s ≤ M := by
        intro s hs
        have hsV : s < v := hs.2.trans (haBar.trans hv.1)
        have hder := vertical_hasDerivAt_of_closed_jet
          (hc1 b hb T hT hTb) hs.1.le hsV hvT
          (g := (fderivWithin ℝ (F b) K (s, v)) (0, 1)) rfl
        change |(fderivWithin ℝ (F b) K (s, v)) (0, 1)| ≤ M
        rw [← hder.deriv]
        exact hbound b hb s ⟨hs.1, hs.2.le⟩ v hv
      have hclosed : closure (Ioo 0 a) = Icc 0 a :=
        closure_Ioo (ne_of_lt ha)
      have hJ0 : J 0 ≤ M := le_on_closure hJbound
        (by rw [hclosed]; exact hJ) (by rw [hclosed]; exact continuousOn_const)
        (by rw [hclosed]; exact ⟨le_refl 0, ha.le⟩)
      have hder := vertical_hasDerivAt_of_closed_jet
        (hc1 b hb T hT hTb) (le_refl 0) (ha.trans (haBar.trans hv.1)) hvT
        (g := (fderivWithin ℝ (F b) K (0, v)) (0, 1)) rfl
      simpa only [J, hder.deriv] using hJ0
    · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      exact hbound b hb u ⟨huPos, hu.2⟩ v hv

end ChristodoulouBV.Uniqueness

end
