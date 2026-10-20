module

public import ChristodoulouBV.C1Solution.AxisLocalExistence
import Mathlib.Tactic

/-!
# Quantitative normalization of an incoming axis edge

Uniform bounds on the physical edge put every sufficiently short prescribed
subinterval into the numerical Picard box.
-/

@[expose] public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- A single Picard norm determined by the physical lower expansion bound and
the uniform first-order edge bounds. -/
def uniformAxisM (c Clam H : ℝ) : ℝ := max 1 (max (Clam / (2 * c)) H)

/-- The lifetime includes both the quantitative normalization interval and
the numerical Picard lifetime. -/
def uniformAxisLifetime (c Clam H : ℝ) : ℝ :=
  min (1 / (8 * uniformAxisM c Clam H))
    ((numericalLedger (uniformAxisM c Clam H)).lifetime (uniformAxisM c Clam H))

/-- The uniform Picard norm is at least one. -/
theorem one_le_uniformAxisM (c Clam H : ℝ) : 1 ≤ uniformAxisM c Clam H :=
  le_max_left _ _

/-- The prescribed lifetime is strictly positive. -/
theorem uniformAxisLifetime_pos (c Clam H : ℝ) :
    0 < uniformAxisLifetime c Clam H := by
  have hM := one_le_uniformAxisM c Clam H
  unfold uniformAxisLifetime
  apply lt_min
  · positivity
  · exact numerical_lifetime_pos hM

/-- A global C¹ physical edge with uniform bounds supplies `EdgeData` on
every prescribed endpoint inside the quantitative lifetime. -/
theorem edgeData_of_uniform_bounds {a L b c Clam H : ℝ}
    {g hEdge : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 hEdge)
    (hc : 0 < c) (hL : 0 < L)
    (hglo : ∀ v ∈ Icc a (a + L), c ≤ g v)
    (hgderiv : ∀ v ∈ Icc a (a + L), |deriv g v| ≤ Clam)
    (hhval : ∀ v ∈ Icc a (a + L), |hEdge v| ≤ H)
    (hhderiv : ∀ v ∈ Icc a (a + L), |deriv hEdge v| ≤ H)
    (hab : a < b) (hbL : b ≤ a + L)
    (hsmall : b - a ≤ uniformAxisLifetime c Clam H) :
    let k := 1 / (2 * g a)
    let M := uniformAxisM c Clam H
    0 < k ∧ k * g a = 1 / 2 ∧
      EdgeData a b M (fun v => k * g v) hEdge := by
  dsimp only
  let k : ℝ := 1 / (2 * g a)
  let M := uniformAxisM c Clam H
  have hga : 0 < g a := hc.trans_le (hglo a ⟨le_rfl, by linarith only [hL]⟩)
  have hk : 0 < k := by dsimp [k]; positivity
  have hka : k * g a = 1 / 2 := by
    dsimp [k]
    field_simp [ne_of_gt hga]
  have hClam : 0 ≤ Clam :=
    (abs_nonneg _).trans (hgderiv a ⟨le_rfl, by linarith only [hL]⟩)
  have hM : 1 ≤ M := one_le_uniformAxisM c Clam H
  have hCM : Clam / (2 * c) ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hHM : H ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hkbound : k ≤ 1 / (2 * c) := by
    dsimp [k]
    exact one_div_le_one_div_of_le (by positivity) (by
      have := hglo a ⟨le_rfl, by linarith only [hL]⟩
      linarith only [this])
  have hkC : k * Clam ≤ M := by
    calc
      k * Clam ≤ (1 / (2 * c)) * Clam :=
        mul_le_mul_of_nonneg_right hkbound hClam
      _ = Clam / (2 * c) := by ring
      _ ≤ M := hCM
  have hgnorm : ContDiff ℝ 1 (fun v => k * g v) := contDiff_const.mul hg
  have hnormderiv (v : ℝ) : deriv (fun t => k * g t) v = k * deriv g v := by
    exact ((hg.differentiable (by norm_num) v).hasDerivAt.const_mul k).deriv
  have hnormbound (v : ℝ) (hv : v ∈ Icc a b) :
      |deriv (fun t => k * g t) v| ≤ M := by
    have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
    rw [hnormderiv, abs_mul, abs_of_pos hk]
    exact (mul_le_mul_of_nonneg_left (hgderiv v hvL) hk.le).trans hkC
  have hwidth : b - a ≤ 1 / (8 * M) :=
    hsmall.trans (min_le_left _ _)
  have hvar (v : ℝ) (hv : v ∈ Icc a b) :
      |k * g v - k * g a| ≤ M * (v - a) := by
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (f := fun t => k * g t) (x := a) (y := v)
      (fun t _ => hgnorm.differentiable (by norm_num) t)
      (fun t ht => by simpa only [Real.norm_eq_abs] using hnormbound t ht)
      ⟨le_rfl, hab.le⟩ hv
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hv.1)] using h
  have hmargin (v : ℝ) (hv : v ∈ Icc a b) :
      |k * g v - k * g a| ≤ 1 / 8 := by
    have hMv : M * (v - a) ≤ M * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith only [hv.2]) (by linarith only [hM])
    have hMw : M * (b - a) ≤ M * (1 / (8 * M)) :=
      mul_le_mul_of_nonneg_left hwidth (by linarith only [hM])
    have hcancel : M * (1 / (8 * M)) = 1 / 8 := by
      have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM
      field_simp [ne_of_gt hMpos]
    exact (hvar v hv).trans (hMv.trans (hMw.trans_eq hcancel))
  refine ⟨hk, hka, ?_⟩
  exact {
    g_c1 := hgnorm
    h_c1 := hh
    g_lower := by
      intro v hv
      have := (abs_le.mp (hmargin v hv)).1
      rw [hka] at this
      linarith only [this]
    g_upper := by
      intro v hv
      have := (abs_le.mp (hmargin v hv)).2
      rw [hka] at this
      linarith only [this]
    g_deriv_bound := hnormbound
    h_bound := by
      intro v hv
      exact (hhval v ⟨hv.1, hv.2.trans hbL⟩).trans hHM
    h_deriv_bound := by
      intro v hv
      exact (hhderiv v ⟨hv.1, hv.2.trans hbL⟩).trans hHM }

end ChristodoulouBV.AxisPicard

end
