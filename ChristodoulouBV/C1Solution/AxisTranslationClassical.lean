module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceSystem
public import ChristodoulouBV.Uniqueness.RescalingBasic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Translation of classical axis triangles

The unit-scale affine chart moves an incoming edge from `u = a` to `u = 0`.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.Uniqueness

/-- The unit-scale affine chart identifies the shifted and zero-edge
classical developments. -/
theorem axisTriangleDevelopment_shift_iff {a b u v : ℝ} :
    (a + u, a + v) ∈ axisTriangleDevelopment a b ↔
      (u, v) ∈ axisTriangleDevelopment 0 (b - a) := by
  change (a ≤ a + u ∧ a + u < a + v ∧ a + v < b) ↔
    (0 ≤ u ∧ u < v ∧ v < b - a)
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The unit-scale affine chart identifies the closed triangles. -/
theorem closedCoordTriangle_shift_iff {a b u v : ℝ} :
    (a + u, a + v) ∈ closedCoordTriangle a b ↔
      (u, v) ∈ closedCoordTriangle 0 (b - a) := by
  change (a ≤ a + u ∧ a + u ≤ a + v ∧ a + v ≤ b) ↔
    (0 ≤ u ∧ u ≤ v ∧ v ≤ b - a)
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

/-- Relative C¹ regularity pulls back along the unit-scale affine chart. -/
theorem contDiffOn_shift_axis {a b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => f (a + p.1, a + p.2))
      (closedCoordTriangle 0 (b - a)) := by
  have hc : ContDiff ℝ 1 (fun p : ℝ × ℝ => (a + p.1, a + p.2)) := by
    fun_prop
  apply hf.comp hc.contDiffOn
  intro p hp
  exact closedCoordTriangle_shift_iff.mpr hp

/-- A classical solution on a translated axis triangle gives a classical
solution on the corresponding zero-edge triangle. -/
theorem AxisClassicalSolution.shift {a b : ℝ} {S : Fields}
    (H : AxisClassicalSolution a b S) :
    AxisClassicalSolution 0 (b - a) (rescaledFields S a 1) := by
  let R := rescaledFields S a 1
  have memdev {u v : ℝ}
      (hp : (u, v) ∈ axisTriangleDevelopment 0 (b - a)) :
      (a + u, a + v) ∈ axisTriangleDevelopment a b :=
    axisTriangleDevelopment_shift_iff.mpr hp
  have memclosed {u v : ℝ}
      (hp : (u, v) ∈ closedCoordTriangle 0 (b - a)) :
      (a + u, a + v) ∈ closedCoordTriangle a b :=
    closedCoordTriangle_shift_iff.mpr hp
  refine {
    r_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul, div_one] using contDiffOn_shift_axis H.r_c1
    phi_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul] using contDiffOn_shift_axis H.phi_c1
    m_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul, div_one] using contDiffOn_shift_axis H.m_c1
    lam_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul] using contDiffOn_shift_axis H.lam_c1
    nu_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul] using contDiffOn_shift_axis H.nu_c1
    alpha_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul] using contDiffOn_shift_axis H.alpha_c1
    beta_c1 := by simpa only [R, rescaledFields, affineCoordinate,
      one_mul] using contDiffOn_shift_axis H.beta_c1
    r_v := by
      intro u v hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.r_v (a + u) (a + v) (memdev hp)).comp_const_add a v
    r_u := by
      intro u v hu hp
      have hau : a < a + u := by linarith
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.r_u (a + u) (a + v) hau (memdev hp)).comp_const_add a u
    psi_v := by
      intro u v hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.psi_v (a + u) (a + v) (memdev hp)).comp_const_add a v
    psi_u := by
      intro u v hu hp
      have hau : a < a + u := by linarith
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.psi_u (a + u) (a + v) hau (memdev hp)).comp_const_add a u
    m_v := by
      intro u v hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one,
        Fields.theta] using
        (H.m_v (a + u) (a + v) (memdev hp)).comp_const_add a v
    m_u := by
      intro u v hu hp
      have hau : a < a + u := by linarith
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one,
        Fields.zeta] using
        (H.m_u (a + u) (a + v) hau (memdev hp)).comp_const_add a u
    lam_u := by
      intro u v hu hp
      have hau : a < a + u := by linarith
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.lam_u (a + u) (a + v) hau (memdev hp)).comp_const_add a u
    nu_v := by
      intro u v hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.nu_v (a + u) (a + v) (memdev hp)).comp_const_add a v
    theta_u := by
      intro u v hu hp
      have hau : a < a + u := by linarith
      simpa only [R, Fields.zeta, Fields.theta, rescaledFields,
        affineCoordinate, one_mul, div_one] using
        (H.theta_u (a + u) (a + v) hau (memdev hp)).comp_const_add a u
    zeta_v := by
      intro u v hp
      change HasDerivAt
        (fun w => R.beta u w - R.nu u w * R.phi u w)
        (-(R.nu u v / R.r u v * R.theta u v)) v
      simpa only [R, Fields.zeta, Fields.theta, rescaledFields,
        affineCoordinate, one_mul, div_one] using
        (H.zeta_v (a + u) (a + v) (memdev hp)).comp_const_add a v
    alpha_u := by
      intro u v hu hp
      have hau : a < a + u := by linarith
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.alpha_u (a + u) (a + v) hau (memdev hp)).comp_const_add a u
    beta_v := by
      intro u v hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        (H.beta_v (a + u) (a + v) (memdev hp)).comp_const_add a v
    r_axis := by
      intro u hu
      have hau : a + u ∈ Icc a b := by
        constructor <;> linarith [hu.1, hu.2]
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        H.r_axis (a + u) hau
    m_axis := by
      intro u hu
      have hau : a + u ∈ Icc a b := by
        constructor <;> linarith [hu.1, hu.2]
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        H.m_axis (a + u) hau
    r_pos := by
      intro p hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        H.r_pos _ (memdev hp)
    lam_pos := by
      intro p hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul] using
        H.lam_pos _ (memclosed hp)
    nu_neg := by
      intro p hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul] using
        H.nu_neg _ (memdev hp)
    gap_pos := by
      intro p hp
      simpa only [R, rescaledFields, affineCoordinate, one_mul, div_one] using
        H.gap_pos _ (memdev hp) }

end ChristodoulouBV.C1Solution

end
