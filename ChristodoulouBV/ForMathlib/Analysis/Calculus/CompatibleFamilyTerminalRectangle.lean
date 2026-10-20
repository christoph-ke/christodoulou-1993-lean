module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.BoundedVerticalTerminalRectangle
import Mathlib.Tactic.Linarith

/-!
# Joint terminal trace of a compatible family on a rectangle

Finite members agree on their common lower rectangles. A uniform bound on
their vertical derivatives gives one jointly continuous terminal extension.
-/

public section

open Set Filter
open scoped Topology

/-- Compatible finite-cutoff fields with a uniform vertical derivative bound
have a continuous trace on the closed rectangle, including the top corners. -/
theorem exists_compatible_family_terminal_rectangle
    {u₀ u₁ vBar vStar M : ℝ} {F : ℝ → ℝ × ℝ → ℝ}
    (hu₀ : 0 ≤ u₀) (hu : u₀ ≤ u₁)
    (huBar : u₁ < vBar) (hBarStar : vBar < vStar)
    (hM : 0 ≤ M)
    (hcompat : ∀ b₁ ∈ Ioo (0 : ℝ) vStar,
      ∀ b₂ ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ico vBar (min b₁ b₂),
        F b₁ (u, v) = F b₂ (u, v))
    (hcont : ∀ b ∈ Ioo (0 : ℝ) vStar, ∀ t ∈ Ico vBar b,
      ContinuousOn (F b) (Icc u₀ u₁ ×ˢ Icc vBar t))
    (hdiff : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ioo vBar b,
        DifferentiableAt ℝ (fun w => F b (u, w)) v)
    (hbound : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ioo vBar b,
        |deriv (fun w => F b (u, w)) v| ≤ M) :
    ∃ G : ℝ × ℝ → ℝ,
      ContinuousOn G (Icc u₀ u₁ ×ˢ Icc vBar vStar) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ico vBar b,
          G (u, v) = F b (u, v) := by
  let q : ℝ → ℝ := fun v => (v + vStar) / 2
  let f : ℝ × ℝ → ℝ := fun p => F (q p.2) p
  have hq (v : ℝ) (hvBar : vBar ≤ v) (hvStar : v < vStar) :
      q v ∈ Ioo (0 : ℝ) vStar ∧ v < q v := by
    dsimp [q]
    have hv0 : 0 < v := hu₀.trans_lt ((hu.trans_lt huBar).trans_le hvBar)
    constructor
    · constructor <;> linarith
    · linarith
  have hflocal (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv : v ∈ Ioo vBar vStar) :
      (fun w => f (u, w)) =ᶠ[𝓝 v] (fun w => F (q v) (u, w)) := by
    have hqv := hq v hv.1.le hv.2
    filter_upwards [Ioo_mem_nhds hv.1 (lt_min hqv.2 hv.2)] with w hw
    have hqw := hq w hw.1.le (hw.2.trans_le (min_le_right _ _))
    exact hcompat (q w) hqw.1 (q v) hqv.1 u hu' w
      ⟨hw.1.le, lt_min hqw.2 (hw.2.trans_le (min_le_left _ _))⟩
  have hfLower (t : ℝ) (ht : t ∈ Ico vBar vStar) :
      ContinuousOn f (Icc u₀ u₁ ×ˢ Icc vBar t) := by
    let b : ℝ := q t
    have hb := hq t ht.1 ht.2
    have htB : t ∈ Ico vBar b := ⟨ht.1, hb.2⟩
    apply (hcont b hb.1 t htB).congr
    intro p hp
    have hpStar : p.2 < vStar := hp.2.2.trans_lt ht.2
    have hqp := hq p.2 hp.2.1 hpStar
    have hpB : p.2 < b := hp.2.2.trans_lt hb.2
    exact hcompat (q p.2) hqp.1 b hb.1 p.1 hp.1 p.2
      ⟨hp.2.1, lt_min hqp.2 hpB⟩
  have hfDiff (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv : v ∈ Ioo vBar vStar) :
      DifferentiableAt ℝ (fun w => f (u, w)) v := by
    have hqv := hq v hv.1.le hv.2
    exact (hdiff (q v) hqv.1 u hu' v ⟨hv.1, hqv.2⟩).congr_of_eventuallyEq
      (hflocal u hu' v hv)
  have hfBound (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv : v ∈ Ioo vBar vStar) :
      |deriv (fun w => f (u, w)) v| ≤ M := by
    have hqv := hq v hv.1.le hv.2
    rw [(hflocal u hu' v hv).deriv_eq]
    exact hbound (q v) hqv.1 u hu' v ⟨hv.1, hqv.2⟩
  obtain ⟨G, hG, hGeq⟩ :=
    exists_continuousOn_closed_rectangle_of_vertical_deriv_bound
      hu hBarStar hM hfLower hfDiff hfBound
  refine ⟨G, hG, ?_⟩
  intro b hb u hu' v hv
  have hvStar : v < vStar := hv.2.trans hb.2
  have hqv := hq v hv.1 hvStar
  calc
    G (u, v) = f (u, v) := hGeq u hu' v ⟨hv.1, hvStar⟩
    _ = F (q v) (u, v) := rfl
    _ = F b (u, v) := hcompat (q v) hqv.1 b hb u hu' v
      ⟨hv.1, lt_min hqv.2 hv.2⟩

end
