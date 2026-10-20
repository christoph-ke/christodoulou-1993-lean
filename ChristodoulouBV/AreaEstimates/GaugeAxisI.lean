module

public import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The weighted-average boundary term in Lemma 4.1

The source's quantity `I` is represented by its literal outgoing integral.
Its quotient by the radius is the difference between the outgoing scalar
quotient and the scalar field, which vanishes continuously at the axis.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV

/-- The integral `I(u,v)` in the proof of Lemma 4.1. -/
noncomputable def sourceI (S : Fields) (u v : ℝ) : ℝ :=
  ∫ t in u..v,
    (S.alpha u v / S.lam u v - S.alpha u t / S.lam u t) * S.lam u t

/-- The literal source integral equals radius times the difference between
the outgoing quotient and `φ` at every strict development point. -/
theorem sourceI_eq_radius_mul_quotient_sub_phi {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    sourceI S u v = S.r u v *
      (S.alpha u v / S.lam u v - S.phi u v) := by
  let K := closedCoordTriangle 0 B
  have hseg : ∀ t ∈ Icc u v, (u, t) ∈ K := by
    intro t ht
    exact ⟨hu, ht.1, ht.2.trans hv⟩
  have hlam : ContinuousOn (S.lam u) (Icc u v) :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hseg)
  have halpha : ContinuousOn (S.alpha u) (Icc u v) :=
    ((C1Solution.alpha_contDiffOn hB hBb H).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hseg)
  have hlamNe (t : ℝ) (ht : t ∈ Icc u v) : S.lam u t ≠ 0 := by
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
    exact ne_of_gt (hc.trans_le (hcl (u, t) (hseg t ht)))
  have hint₁ : IntervalIntegrable
      (fun t => S.alpha u v / S.lam u v * S.lam u t) volume u v :=
    (continuousOn_const.mul hlam).intervalIntegrable_of_Icc huv.le
  have hint₂ : IntervalIntegrable (S.alpha u) volume u v :=
    halpha.intervalIntegrable_of_Icc huv.le
  have hI : sourceI S u v =
      (S.alpha u v / S.lam u v) * (∫ t in u..v, S.lam u t) -
      (∫ t in u..v, S.alpha u t) := by
    rw [sourceI]
    have hcongr : (∫ t in u..v,
        (S.alpha u v / S.lam u v - S.alpha u t / S.lam u t) * S.lam u t) =
        ∫ t in u..v,
          (S.alpha u v / S.lam u v * S.lam u t - S.alpha u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le huv.le] at ht
      have hne := hlamNe t ht
      field_simp
    rw [hcongr, intervalIntegral.integral_sub hint₁ hint₂,
      intervalIntegral.integral_const_mul]
  have hr := C1Solution.canonicalRadius_eq_radius hB hBb H hu huv hv
  have hψ := C1Solution.canonicalScalarRadius_eq_radius_mul_phi hB hBb H
    hu huv hv
  change (∫ t in u..v, S.lam u t) = S.r u v at hr
  change (∫ t in u..v, S.alpha u t) = S.r u v * S.phi u v at hψ
  rw [hI, hr, hψ]
  ring

/-- The source boundary term `I/r` tends to zero at every accessible regular
axis point of a smaller C¹ triangle. -/
theorem s4_i_axis {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) B) :
    Tendsto (fun v => sourceI S u v / S.r u v)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun p =>
    S.alpha p.1 p.2 / S.lam p.1 p.2 - S.phi p.1 p.2
  have hF : ContinuousOn F K :=
    (C1Solution.alpha_div_lam_contDiffOn hB hBb H).continuousOn.sub
      (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1.continuousOn
  have hslice : ContinuousOn (fun v => F (u, v)) (Icc u B) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu.1.le, hv.1, hv.2⟩)
  have huK : u ∈ Icc 0 B := ⟨hu.1.le, hu.2.le⟩
  have hlamPos : 0 < S.lam u u := by
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
    exact hc.trans_le (hcl (u, u) ⟨hu.1.le, le_rfl, hu.2.le⟩)
  have hFzero : F (u, u) = 0 := by
    dsimp [F]
    rw [C1Solution.alpha_eq_lam_mul_phi_axis hB hBb H huK]
    field_simp [ne_of_gt hlamPos]
    ring
  have hright : ContinuousWithinAt (fun v => F (u, v)) (Ici u) u :=
    (continuousWithinAt_Icc_iff_Ici hu.2).mp
      (hslice.continuousWithinAt ⟨le_rfl, hu.2.le⟩)
  have hlim : Tendsto (fun v => F (u, v)) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hFzero] using (hright.mono Ioi_subset_Ici_self).tendsto
  have heq : (fun v => sourceI S u v / S.r u v) =ᶠ[𝓝[>] u]
      (fun v => F (u, v)) := by
    filter_upwards [Ioo_mem_nhdsGT hu.2] with v hv
    have hI := sourceI_eq_radius_mul_quotient_sub_phi hB hBb H
      hu.1.le hv.1 hv.2.le
    have hr : S.r u v ≠ 0 := ne_of_gt
      (H.solution.radius_pos (u, v) ⟨hu.1.le, hv.1, hv.2.trans hBb⟩)
    dsimp [F]
    rw [hI]
    field_simp
  exact hlim.congr' heq.symm

end ChristodoulouBV

end
