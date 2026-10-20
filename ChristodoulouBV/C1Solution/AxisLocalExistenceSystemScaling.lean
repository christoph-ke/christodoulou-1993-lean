module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceSystem
public import ChristodoulouBV.C1Solution.AxisLocalExistenceScaling
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Physical scaling of classical axis equations

The seven physical fields have radial weight one except for the scalar field.
The characteristic equations keep their form under a positive constant scale.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.C1Solution

/-- Constant physical scaling preserves the classical axis system. -/
theorem AxisClassicalSolution.physicalScale {a b : ℝ} {S : Fields}
    (H : AxisClassicalSolution a b S) {c : ℝ} (hc : 0 < c) :
    AxisClassicalSolution a b (physicalScaleFields c S) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  refine {
    r_c1 := ?_
    phi_c1 := ?_
    m_c1 := ?_
    lam_c1 := ?_
    nu_c1 := ?_
    alpha_c1 := ?_
    beta_c1 := ?_
    r_v := ?_
    r_u := ?_
    psi_v := ?_
    psi_u := ?_
    m_v := ?_
    m_u := ?_
    lam_u := ?_
    nu_v := ?_
    theta_u := ?_
    zeta_v := ?_
    alpha_u := ?_
    beta_v := ?_
    r_axis := ?_
    m_axis := ?_
    r_pos := ?_
    lam_pos := ?_
    nu_neg := ?_
    gap_pos := ?_ }
  · simpa only [physicalScaleFields] using (contDiffOn_const.mul H.r_c1)
  · exact H.phi_c1
  · simpa only [physicalScaleFields] using (contDiffOn_const.mul H.m_c1)
  · simpa only [physicalScaleFields] using (contDiffOn_const.mul H.lam_c1)
  · simpa only [physicalScaleFields] using (contDiffOn_const.mul H.nu_c1)
  · simpa only [physicalScaleFields] using (contDiffOn_const.mul H.alpha_c1)
  · simpa only [physicalScaleFields] using (contDiffOn_const.mul H.beta_c1)
  · intro u v hp
    simpa only [physicalScaleFields] using (H.r_v u v hp).const_mul c
  · intro u v hu hp
    simpa only [physicalScaleFields] using (H.r_u u v hu hp).const_mul c
  · intro u v hp
    simpa only [physicalScaleFields, mul_assoc] using (H.psi_v u v hp).const_mul c
  · intro u v hu hp
    simpa only [physicalScaleFields, mul_assoc] using (H.psi_u u v hu hp).const_mul c
  · intro u v hp
    have h := (H.m_v u v hp).const_mul c
    convert h using 1 <;> try rfl
    rw [physicalScaleFields_massRatio c S u v hcne,
      physicalScaleFields_theta]
    simp only [physicalScaleFields]
    have hlam : S.lam u v ≠ 0 := ne_of_gt (H.lam_pos (u, v)
      ⟨hp.1, hp.2.1.le, hp.2.2.le⟩)
    field_simp [hcne, hlam]
  · intro u v hu hp
    have h := (H.m_u u v hu hp).const_mul c
    convert h using 1 <;> try rfl
    rw [physicalScaleFields_massRatio c S u v hcne,
      physicalScaleFields_zeta]
    simp only [physicalScaleFields]
    have hnu : S.nu u v ≠ 0 := ne_of_lt (H.nu_neg (u, v) hp)
    field_simp [hcne, hnu]
  · intro u v hu hp
    have h := (H.lam_u u v hu hp).const_mul c
    convert h using 1 <;> try rfl
    rw [physicalScaleFields_massRatio c S u v hcne]
    simp only [physicalScaleFields]
    have hr : S.r u v ≠ 0 := ne_of_gt (H.r_pos (u, v) hp)
    have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
      ne_of_gt (H.gap_pos (u, v) hp)
    field_simp [hcne, hr, hgap]
  · intro u v hp
    have h := (H.nu_v u v hp).const_mul c
    convert h using 1 <;> try rfl
    rw [physicalScaleFields_massRatio c S u v hcne]
    simp only [physicalScaleFields]
    have hr : S.r u v ≠ 0 := ne_of_gt (H.r_pos (u, v) hp)
    have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
      ne_of_gt (H.gap_pos (u, v) hp)
    field_simp [hcne, hr, hgap]
  · intro u v hu hp
    have h := (H.theta_u u v hu hp).const_mul c
    convert h using 1
    · funext w
      exact physicalScaleFields_theta c S w v
    · rw [physicalScaleFields_zeta]
      simp only [physicalScaleFields]
      have hr : S.r u v ≠ 0 := ne_of_gt (H.r_pos (u, v) hp)
      field_simp [hcne, hr]
  · intro u v hp
    have h := (H.zeta_v u v hp).const_mul c
    convert h using 1
    · funext w
      exact physicalScaleFields_zeta c S u w
    · rw [physicalScaleFields_theta]
      simp only [physicalScaleFields]
      have hr : S.r u v ≠ 0 := ne_of_gt (H.r_pos (u, v) hp)
      field_simp [hcne, hr]
  · intro u v hu hp
    have h := (H.alpha_u u v hu hp).const_mul c
    convert h using 1 <;> try rfl
    rw [physicalScaleFields_massRatio c S u v hcne]
    simp only [physicalScaleFields]
    have hr : S.r u v ≠ 0 := ne_of_gt (H.r_pos (u, v) hp)
    have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
      ne_of_gt (H.gap_pos (u, v) hp)
    field_simp [hcne, hr, hgap]
  · intro u v hp
    have h := (H.beta_v u v hp).const_mul c
    convert h using 1 <;> try rfl
    rw [physicalScaleFields_massRatio c S u v hcne]
    simp only [physicalScaleFields]
    have hr : S.r u v ≠ 0 := ne_of_gt (H.r_pos (u, v) hp)
    have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
      ne_of_gt (H.gap_pos (u, v) hp)
    field_simp [hcne, hr, hgap]
  · intro u hu
    simp [physicalScaleFields, H.r_axis u hu]
  · intro u hu
    simp [physicalScaleFields, H.m_axis u hu]
  · intro p hp
    exact mul_pos hc (H.r_pos p hp)
  · intro p hp
    exact mul_pos hc (H.lam_pos p hp)
  · intro p hp
    exact mul_neg_of_pos_of_neg hc (H.nu_neg p hp)
  · intro p hp
    rw [physicalScaleFields_massRatio c S p.1 p.2 hcne]
    exact H.gap_pos p hp

end ChristodoulouBV.C1Solution

end
