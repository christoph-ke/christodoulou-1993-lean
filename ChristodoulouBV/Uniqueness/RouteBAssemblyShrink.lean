module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyEdgeJoin
public import ChristodoulouBV.Uniqueness.RouteBAssemblyEdgeBounds
import Mathlib.Tactic.Linarith

/-!
# Keeping uniform edge bounds beyond the terminal line

A joined C¹ edge shares the old uniform bounds on `[a,vStar]`. Strictly
larger constants then remain valid on a short segment beyond `vStar`.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- If globally C¹ functions agree on a nondegenerate closed interval,
ordinary derivative bounds pass between them even at the endpoints. -/
theorem deriv_abs_le_of_eqOn_Icc
    {a b C : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hg : ContDiff ℝ 1 g)
    (heq : EqOn f g (Icc a b))
    (hbound : ∀ x ∈ Icc a b, |deriv f x| ≤ C) :
    ∀ x ∈ Icc a b, |deriv g x| ≤ C := by
  have hinterior : ∀ x ∈ Ioo a b, |deriv g x| ≤ C := by
    intro x hx
    have hlocal : f =ᶠ[𝓝 x] g := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact heq ⟨hy.1.le, hy.2.le⟩
    rw [← hlocal.deriv_eq]
    exact hbound x ⟨hx.1.le, hx.2.le⟩
  have hclosure : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hcont : ContinuousOn (fun x => |deriv g x|) (Icc a b) :=
    ((contDiff_one_iff_deriv.mp hg).2.continuousOn).abs
  intro x hx
  exact le_on_closure hinterior
    (by rw [hclosure]; exact hcont)
    (by rw [hclosure]; exact continuousOn_const)
    (by rw [hclosure]; exact hx)

/-- After joining, the cutoff-independent old bounds persist on a short
new edge with a strictly positive expansion floor. The new height can be
chosen below any prescribed positive height. -/
theorem exists_short_joined_edge_bounds
    {a vStar η c Clam H : ℝ} {g h gOld hOld : ℝ → ℝ}
    (haStar : a < vStar) (hη : 0 < η) (hc : 0 < c)
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hgEq : EqOn gOld g (Icc a vStar))
    (hhEq : EqOn hOld h (Icc a vStar))
    (hOldBounds : ∀ v ∈ Icc a vStar,
      c ≤ gOld v ∧ |deriv gOld v| ≤ Clam ∧
        |hOld v| ≤ H ∧ |deriv hOld v| ≤ H) :
    ∃ η' : ℝ, 0 < η' ∧ η' < η ∧
      ∀ v ∈ Icc a (vStar + η'),
        c / 2 ≤ g v ∧ |deriv g v| ≤ Clam + 1 ∧
          |h v| ≤ H + 1 ∧ |deriv h v| ≤ H + 1 := by
  have hgDeriv : ∀ v ∈ Icc a vStar, |deriv g v| ≤ Clam :=
    deriv_abs_le_of_eqOn_Icc haStar hg hgEq
      (fun v hv => (hOldBounds v hv).2.1)
  have hhDeriv : ∀ v ∈ Icc a vStar, |deriv h v| ≤ H :=
    deriv_abs_le_of_eqOn_Icc haStar hh hhEq
      (fun v hv => (hOldBounds v hv).2.2.2)
  have hStarMem : vStar ∈ Icc a vStar := ⟨haStar.le, le_rfl⟩
  have hstar := hOldBounds vStar hStarMem
  have hgStar : c / 2 < g vStar := by
    rw [← hgEq hStarMem]
    linarith only [hc, hstar.1]
  have hgDStar : |deriv g vStar| < Clam + 1 := by
    linarith only [hgDeriv vStar hStarMem]
  have hhStar : |h vStar| < H + 1 := by
    rw [← hhEq hStarMem]
    linarith only [hstar.2.2.1]
  have hhDStar : |deriv h vStar| < H + 1 := by
    linarith only [hhDeriv vStar hStarMem]
  have hgDCont : Continuous (fun v => deriv g v) :=
    (contDiff_one_iff_deriv.mp hg).2
  have hhDCont : Continuous (fun v => deriv h v) :=
    (contDiff_one_iff_deriv.mp hh).2
  have hnearG : {v : ℝ | c / 2 < g v} ∈ 𝓝 vStar :=
    (isOpen_lt continuous_const hg.continuous).mem_nhds hgStar
  have hnearGD : {v : ℝ | |deriv g v| < Clam + 1} ∈ 𝓝 vStar :=
    (isOpen_lt hgDCont.abs continuous_const).mem_nhds hgDStar
  have hnearH : {v : ℝ | |h v| < H + 1} ∈ 𝓝 vStar :=
    (isOpen_lt hh.continuous.abs continuous_const).mem_nhds hhStar
  have hnearHD : {v : ℝ | |deriv h v| < H + 1} ∈ 𝓝 vStar :=
    (isOpen_lt hhDCont.abs continuous_const).mem_nhds hhDStar
  have hnear : {v : ℝ | c / 2 < g v ∧
      |deriv g v| < Clam + 1 ∧
      |h v| < H + 1 ∧ |deriv h v| < H + 1} ∈ 𝓝 vStar := by
    filter_upwards [hnearG, hnearGD, hnearH, hnearHD]
      with v hgv hgdv hhv hhdv
    exact ⟨hgv, hgdv, hhv, hhdv⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let η' : ℝ := min (η / 2) (δ / 2)
  have hη' : 0 < η' := lt_min (half_pos hη) (half_pos hδ)
  have hη'η : η' < η :=
    (min_le_left _ _).trans_lt (by linarith only [hη])
  have hη'δ : η' < δ :=
    (min_le_right _ _).trans_lt (by linarith only [hδ])
  refine ⟨η', hη', hη'η, ?_⟩
  intro v hv
  by_cases hvStar : v ≤ vStar
  · have hvOld : v ∈ Icc a vStar := ⟨hv.1, hvStar⟩
    have hOld := hOldBounds v hvOld
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hgEq hvOld]
      linarith only [hc, hOld.1]
    · linarith only [hgDeriv v hvOld]
    · rw [← hhEq hvOld]
      linarith only [hOld.2.2.1]
    · linarith only [hhDeriv v hvOld]
  · have hStarv : vStar ≤ v := (lt_of_not_ge hvStar).le
    have hdist : dist v vStar < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hStarv)]
      linarith only [hv.2, hη'δ]
    obtain ⟨hGv, hGDv, hHv, hHDv⟩ := hball (Metric.mem_ball.mpr hdist)
    exact ⟨hGv.le, hGDv.le, hHv.le, hHDv.le⟩

end ChristodoulouBV.Uniqueness

end
