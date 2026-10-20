module

public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothJacobian
import Mathlib.Tactic

/-!
# Smooth area densities

The signed derivative of the section primitive can differ from the
printed ordered Jacobian by orientation. Its absolute value is exactly
the smooth analytic area density in all four cases.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Each ordered smooth area map is C¹ on the global development. -/
theorem SmoothSolutionBounds.area_pair_map_contDiffOn
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) :
    ContDiffOn ℝ 1 (areaPairMap k S) globalDomain := by
  obtain ⟨hφ, hg⟩ := h.area_pair_contDiffOn k
  cases k with
  | phiAlphaLam => exact hφ.prodMk hg
  | lamPhi => exact hg.prodMk hφ
  | phiBetaNu => exact hφ.prodMk hg
  | nuPhi => exact hg.prodMk hφ

/-- The absolute smooth Jacobian equals the absolute signed density of
the physical section primitive. -/
theorem SmoothSolutionBounds.area_jacobian_density
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    |(fderiv ℝ (areaPairMap k S) (u, v)).det| =
      |areaSectionF k (areaSectionCoefficients S (u, v)) *
        (fderiv ℝ (fun p => areaSectionG k (areaSectionCoefficients S p)) (u, v))
          (areaInnerDirection k) - areaSectionH k (areaSectionCoefficients S (u, v))| := by
  let φ := fun p : ℝ × ℝ => S.phi p.1 p.2
  let g := fun p : ℝ × ℝ => areaSectionG k (areaSectionCoefficients S p)
  let p : ℝ × ℝ := (u, v)
  have hp : p ∈ globalDomain := ⟨hu.le, huv⟩
  have hn : globalDomain ∈ 𝓝 p :=
    mem_of_superset (isOpen_areaSmoothDomain.mem_nhds ⟨hu, huv⟩)
      (fun q hq => ⟨hq.1.le, hq.2⟩)
  obtain ⟨hφC, hgC⟩ := h.area_pair_contDiffOn k
  have hφd : DifferentiableAt ℝ φ p :=
    (hφC.differentiableOn (by norm_num) p hp).differentiableAt hn
  have hgd : DifferentiableAt ℝ g p :=
    (hgC.differentiableOn (by norm_num) p hp).differentiableAt hn
  obtain ⟨hφu, hφv, _, _, _, _⟩ := h.area_first_jets hu huv
  have hgt := h.area_g_transport_jet k hu huv
  have hf : areaSectionF k (areaSectionCoefficients S p) =
      (fderiv ℝ φ p) (areaTransverseDirection k) := by
    cases hki : k.incoming with
    | false =>
      simp only [areaSectionF, hki, Bool.false_eq_true, ite_false]
      change (S.beta u v - S.nu u v * S.phi u v) * (S.r u v)⁻¹ = _
      simp only [areaTransverseDirection, hki, Bool.false_eq_true, ite_false,
        φ, p, hφu, Fields.zeta, div_eq_mul_inv]
    | true =>
      simp only [areaSectionF, hki, ite_true]
      change (S.alpha u v - S.lam u v * S.phi u v) * (S.r u v)⁻¹ = _
      simp only [areaTransverseDirection, hki, ite_true, φ, p, hφv,
        Fields.theta, div_eq_mul_inv]
  have hh : areaSectionH k (areaSectionCoefficients S p) =
      (fderiv ℝ φ p) (areaInnerDirection k) *
        (fderiv ℝ g p) (areaTransverseDirection k) := by
    change _ = _ *
      (fderiv ℝ (fun p => areaSectionG k (areaSectionCoefficients S p)) (u, v))
        (areaTransverseDirection k)
    rw [hgt]
    cases k with
    | phiAlphaLam =>
      change (S.alpha u v - S.lam u v * S.phi u v) * (S.r u v)⁻¹ *
        (IsBVSolution.radiusCoeff S u v * (S.phi u v * S.lam u v - S.alpha u v) *
          (S.lam u v)⁻¹ ^ 2) = _
      rw [show (fderiv ℝ φ p) (areaInnerDirection .phiAlphaLam) =
        S.theta u v / S.r u v from hφv]
      rw [Fields.theta, div_eq_mul_inv]
      rfl
    | lamPhi =>
      change (S.alpha u v - S.lam u v * S.phi u v) * (S.r u v)⁻¹ *
        IsBVSolution.radiusCoeff S u v = _
      rw [show (fderiv ℝ φ p) (areaInnerDirection .lamPhi) =
        S.theta u v / S.r u v from hφv]
      rw [Fields.theta, div_eq_mul_inv]
      rfl
    | phiBetaNu =>
      change (S.beta u v - S.nu u v * S.phi u v) * (S.r u v)⁻¹ *
        (IsBVSolution.radiusCoeff S u v * (S.phi u v * S.nu u v - S.beta u v) *
          (S.nu u v)⁻¹ ^ 2) = _
      rw [show (fderiv ℝ φ p) (areaInnerDirection .phiBetaNu) =
        S.zeta u v / S.r u v from hφu]
      rw [Fields.zeta, div_eq_mul_inv]
      rfl
    | nuPhi =>
      change (S.beta u v - S.nu u v * S.phi u v) * (S.r u v)⁻¹ *
        IsBVSolution.radiusCoeff S u v = _
      rw [show (fderiv ℝ φ p) (areaInnerDirection .nuPhi) =
        S.zeta u v / S.r u v from hφu]
      rw [Fields.zeta, div_eq_mul_inv]
      rfl
  rw [hf, hh]
  change |(fderiv ℝ (areaPairMap k S) p).det| =
    |(fderiv ℝ φ p) (areaTransverseDirection k) *
      (fderiv ℝ g p) (areaInnerDirection k) -
      (fderiv ℝ φ p) (areaInnerDirection k) *
      (fderiv ℝ g p) (areaTransverseDirection k)|
  have hJ := det_fderiv_prodMk hφd hgd
  have hJ' := det_fderiv_prodMk hgd hφd
  cases k with
  | phiAlphaLam =>
    simp only [areaInnerDirection, areaTransverseDirection, AreaSectionPair.incoming,
      Bool.false_eq_true, ite_false]
    change |(fderiv ℝ (fun p => (φ p, g p)) p).det| = _
    rw [hJ]
  | lamPhi =>
    simp only [areaInnerDirection, areaTransverseDirection, AreaSectionPair.incoming,
      Bool.false_eq_true, ite_false]
    change |(fderiv ℝ (fun p => (g p, φ p)) p).det| = _
    rw [hJ']
    exact (congrArg abs (by ring)).trans (abs_neg _)
  | phiBetaNu =>
    simp only [areaInnerDirection, areaTransverseDirection, AreaSectionPair.incoming, ite_true]
    change |(fderiv ℝ (fun p => (φ p, g p)) p).det| = _
    rw [hJ]
    exact (congrArg abs (by ring)).trans (abs_neg _)
  | nuPhi =>
    simp only [areaInnerDirection, areaTransverseDirection, AreaSectionPair.incoming, ite_true]
    change |(fderiv ℝ (fun p => (g p, φ p)) p).det| = _
    rw [hJ']
    congr 1
    ring

end ChristodoulouBV

end
