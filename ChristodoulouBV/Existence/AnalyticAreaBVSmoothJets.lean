module

public import ChristodoulouBV.Existence.AreaSectionLimit
public import ChristodoulouBV.AreaEstimates.FieldTransportJacobian
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Smooth first jets for the four analytic area pairs

The frozen scalar-radius and mixed transport primitives identify the
classical first jets of a smooth approximant. These identities are used
only to identify the analytic carrier with the smooth Jacobian measure.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Strict interior of the global development, used for classical jets. -/
@[expose] def areaSmoothDomain : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}

/-- The classical area carrier domain is open. -/
theorem isOpen_areaSmoothDomain : IsOpen areaSmoothDomain :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_snd)

/-- The four second components and the scalar field are C¹ on the global
development of a smooth approximant. -/
theorem SmoothSolutionBounds.area_pair_contDiffOn
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) globalDomain ∧
      ContDiffOn ℝ 1 (fun p => areaSectionG k (areaSectionCoefficients S p))
        globalDomain := by
  have hs : globalDomain ⊆ closure globalDomain := fun p hp => subset_closure hp
  have hl := h.solution.lam_c1.mono hs
  have hn := h.solution.nu_c1.mono hs
  have hp := h.solution.phi_c1.mono hs
  have ht := h.solution.theta_c1.mono hs
  have hz := h.solution.zeta_c1.mono hs
  have hα : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2) globalDomain := by
    apply (ht.add (hl.mul hp)).congr
    intro p _
    simp only [Fields.theta]
    ring
  have hβ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2) globalDomain := by
    apply (hz.add (hn.mul hp)).congr
    intro p _
    simp only [Fields.zeta]
    ring
  have hlne (p : ℝ × ℝ) (hp : p ∈ globalDomain) : S.lam p.1 p.2 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (h.geometry p hp).1).ne'
  have hnne (p : ℝ × ℝ) (hp : p ∈ globalDomain) : S.nu p.1 p.2 ≠ 0 := by
    have hb := (h.geometry p hp).2.2.1
    have hn0 : S.nu p.1 p.2 < 0 := by linarith only [hb]
    exact hn0.ne
  refine ⟨hp, ?_⟩
  cases k with
  | phiAlphaLam =>
    change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2 * (S.lam p.1 p.2)⁻¹) _
    simpa only [div_eq_mul_inv] using hα.fun_div hl hlne
  | lamPhi => exact hl
  | phiBetaNu =>
    change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2 * (S.nu p.1 p.2)⁻¹) _
    simpa only [div_eq_mul_inv] using hβ.fun_div hn hnne
  | nuPhi => exact hn

/-- At every strict interior point the six scalar and transport jets
are the frozen densities. No a.e. derivative is evaluated at a BV jump. -/
theorem SmoothSolutionBounds.area_first_jets
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    (fderiv ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v)) (1, 0) =
        S.zeta u v / S.r u v ∧
    (fderiv ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v)) (0, 1) =
        S.theta u v / S.r u v ∧
    (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (1, 0) =
        IsBVSolution.radiusCoeff S u v ∧
    (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (0, 1) =
        IsBVSolution.radiusCoeff S u v ∧
    (fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2) (u, v)) (1, 0) =
        IsBVSolution.radiusCoeff S u v * S.phi u v ∧
    (fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, v)) (0, 1) =
        IsBVSolution.radiusCoeff S u v * S.phi u v := by
  let B := v + 1
  let b := v + 2
  have hv : 0 < v := hu.trans huv
  have hB : 0 < B := by dsimp only [B]; linarith only [hv]
  have hb : 0 < b := by dsimp only [b]; linarith only [hv]
  have hBb : B < b := by dsimp only [B, b]; linarith
  have hvB : v < B := lt_add_one v
  let H := h.finite b hb
  have hpK : (u, v) ∈ closedCoordTriangle 0 B := by
    simpa only [closedCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) ≤ u ∧ u ≤ v ∧ v ≤ B from ⟨hu.le, huv.le, hvB.le⟩)
  have hpI : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    simpa only [openCoordTriangle, mem_ofPred_eq] using
      (show (0 : ℝ) < u ∧ u < v ∧ v < B from ⟨hu, huv, hvB⟩)
  have hK : closedCoordTriangle 0 B ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpI) interior_subset
  have hθ := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet hB hBb H hpK
  have hζ := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet hB hBb H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le,
    fderivWithin_of_mem_nhds hK] at hθ hζ
  have hr : S.r u v ≠ 0 := (h.solution.solution.radius_pos (u, v) ⟨hu.le, huv⟩).ne'
  obtain ⟨hl, hn, hα, hβ⟩ := C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  have hc : C1Solution.canonicalMixedCoefficient b S (u, v) =
      IsBVSolution.radiusCoeff S u v :=
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H hu.le huv hvB.le
  rw [fderivWithin_of_mem_nhds hK, hc] at hl hn hα hβ
  refine ⟨?_, ?_, hl, hn, hα, hβ⟩
  · exact (eq_div_iff hr).mpr (by simpa only [mul_comm] using hζ.symm)
  · exact (eq_div_iff hr).mpr (by simpa only [mul_comm] using hθ.symm)

end ChristodoulouBV

end
