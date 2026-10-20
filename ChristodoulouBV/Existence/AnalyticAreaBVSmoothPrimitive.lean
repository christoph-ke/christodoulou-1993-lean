module

public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothJets
import Mathlib.Tactic

/-!
# Absolute continuity of the smooth physical area primitive

The scalar density has the mixed derivative proved for the area-section construction. The other
factor is C¹. The product rule and the ordinary correction integral give
the signed Jacobian density almost everywhere on each compact section.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem smooth_f_ac_ae
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z A B : ℝ}
    (hab : A ≤ B) (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain) :
    AbsolutelyContinuousOnInterval
      (fun t => areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t))) A B ∧
      ∀ᵐ t ∂volume, t ∈ Icc A B →
        deriv (fun t => areaSectionF k
          (areaSectionCoefficients S (areaPhysicalPoint k z t))) t =
            areaSectionP (areaSectionCoefficients S (areaPhysicalPoint k z t)) := by
  cases hki : k.incoming with
  | false =>
    have hseg : outSeg z A B ⊆ globalDomain := by
      rintro ⟨u, v⟩ ⟨rfl, hv⟩
      simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using hs hv
    have heq : (fun t => areaSectionF k
        (areaSectionCoefficients S (areaPhysicalPoint k z t))) =
        (fun t => S.zeta z t / S.r z t) := by
      funext t
      simp only [areaSectionF, areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      change (S.beta z t - S.nu z t * S.phi z t) * (S.r z t)⁻¹ = _
      rw [Fields.zeta, div_eq_mul_inv]
    rw [heq]
    simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using
      h.outgoing_mixed_scalar_density hab hseg
  | true =>
    have hseg : inSeg z A B ⊆ globalDomain := by
      rintro ⟨u, v⟩ ⟨hu, rfl⟩
      simpa only [areaPhysicalPoint, hki, ite_true] using hs hu
    have heq : (fun t => areaSectionF k
        (areaSectionCoefficients S (areaPhysicalPoint k z t))) =
        (fun t => S.theta t z / S.r t z) := by
      funext t
      simp only [areaSectionF, areaPhysicalPoint, hki, ite_true]
      change (S.alpha t z - S.lam t z * S.phi t z) * (S.r t z)⁻¹ = _
      rw [Fields.theta, div_eq_mul_inv]
    rw [heq]
    simpa only [areaPhysicalPoint, hki, ite_true] using
      h.incoming_mixed_scalar_density hab hseg

/-- A smooth physical primitive is absolutely continuous, with the
signed Stieltjes density `f g' - h` almost everywhere. -/
theorem SmoothSolutionBounds.area_physical_primitive_ac_ae
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z b A B : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain) :
    AbsolutelyContinuousOnInterval (areaPhysicalPrimitive k S z b) A B ∧
      ∀ᵐ t ∂volume, t ∈ Icc A B →
        deriv (areaPhysicalPrimitive k S z b) t =
          areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t)) *
            deriv (fun x => areaSectionG k
              (areaSectionCoefficients S (areaPhysicalPoint k z x))) t -
              areaSectionH k (areaSectionCoefficients S (areaPhysicalPoint k z t)) := by
  let f := fun t => areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  let g := fun t => areaSectionG k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  let q := fun t => areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  obtain ⟨hf, hfd⟩ := smooth_f_ac_ae h k hab hs
  have hpoint : ContDiffOn ℝ 1 (areaPhysicalPoint k z) (Icc A B) := by
    change ContDiffOn ℝ 1 (fun t => areaPhysicalPoint k z t) (Icc A B)
    cases k <;> simp only [areaPhysicalPoint, AreaSectionPair.incoming,
      Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hgC : ContDiffOn ℝ 1 g (Icc A B) := (h.area_pair_contDiffOn k).2.comp hpoint hs
  have hgC' : ContDiffOn ℝ 1 g (uIcc A B) := by
    simpa only [uIcc_of_le hab] using hgC
  have hg : AbsolutelyContinuousOnInterval g A B := hgC'.absolutelyContinuousOnInterval
  have hqc : ContinuousOn q (Icc A B) :=
    (area_section_q_continuous k).continuousOn.comp
      (h.area_section_coefficients_continuousOn.comp hpoint.continuousOn hs)
        (fun _ _ => mem_univ _)
  have hq : IntervalIntegrable q volume A B := hqc.intervalIntegrable_of_Icc hab
  have hbU : b ∈ uIcc A B := by simpa only [uIcc_of_le hab] using hb
  have hI := hq.absolutelyContinuousOnInterval_intervalIntegral (c := b) hbU
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f b * g b) A B :=
    (LipschitzWith.const (f b * g b)).lipschitzOnWith.absolutelyContinuousOnInterval
  have he : areaPhysicalPrimitive k S z b =
      (fun t => f t * g t - f b * g b - ∫ x in b..t, q x) := rfl
  rw [he]
  refine ⟨((hf.fun_mul hg).fun_sub hconst).fun_sub hI, ?_⟩
  filter_upwards [hfd, hf.ae_differentiableAt, hg.ae_differentiableAt,
    hq.ae_hasDerivAt_integral] with t ht hft hgt hit hti
  have htu : t ∈ uIcc A B := by simpa only [uIcc_of_le hab] using hti
  have hd : HasDerivAt (fun x => f x * g x - f b * g b - ∫ s in b..x, q s)
      (deriv f t * g t + f t * deriv g t - q t) t :=
    (((hft htu).hasDerivAt.fun_mul (hgt htu).hasDerivAt).sub_const (f b * g b)).fun_sub
      (hit htu b hbU)
  rw [hd.deriv, ht hti]
  dsimp only [q, areaSectionQ, f, g]
  ring

end ChristodoulouBV

end
