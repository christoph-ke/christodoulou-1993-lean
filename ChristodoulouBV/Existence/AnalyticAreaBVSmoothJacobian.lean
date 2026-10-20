module

public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothJets
import Mathlib.Tactic

/-!
# The smooth Jacobian densities represented by the section primitives

The mixed transport jets identify the ordinary correction term in the
four primitives. Their absolute derivative density is the absolute
Jacobian of the printed ordered field pair.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The four ordered planar maps in (6.4a)--(6.4d). -/
@[expose] noncomputable def areaPairMap (k : AreaSectionPair) (S : Fields)
    (p : ℝ × ℝ) : ℝ × ℝ :=
  if k = .lamPhi ∨ k = .nuPhi then
    (areaSectionG k (areaSectionCoefficients S p), S.phi p.1 p.2)
  else (S.phi p.1 p.2, areaSectionG k (areaSectionCoefficients S p))

/-- The inner null-coordinate direction in each physical chart. -/
@[expose] def areaInnerDirection (k : AreaSectionPair) : ℝ × ℝ :=
  if k.incoming then (1, 0) else (0, 1)

/-- The transverse transport direction in each physical chart. -/
@[expose] def areaTransverseDirection (k : AreaSectionPair) : ℝ × ℝ :=
  if k.incoming then (0, 1) else (1, 0)

/-- The mixed transport density of the BV component of each area pair. -/
@[expose] def areaSectionTransportG (k : AreaSectionPair) (c : Fin 9 → ℝ) : ℝ :=
  match k with
  | .phiAlphaLam => c 6 * (c 3 * c 1 - c 4) * c 7 ^ 2
  | .lamPhi => c 6
  | .phiBetaNu => c 6 * (c 3 * c 2 - c 5) * c 8 ^ 2
  | .nuPhi => c 6

private theorem smooth_base_differentiable
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) {p : ℝ × ℝ} (hp : p ∈ areaSmoothDomain) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2) p ∧
    DifferentiableAt ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2) p ∧
    DifferentiableAt ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2) p ∧
    DifferentiableAt ℝ (fun q : ℝ × ℝ => S.alpha q.1 q.2) p ∧
    DifferentiableAt ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2) p := by
  have hpG : p ∈ globalDomain := ⟨hp.1.le, hp.2⟩
  have hG : closure globalDomain ∈ 𝓝 p :=
    mem_of_superset (isOpen_areaSmoothDomain.mem_nhds hp)
      (fun q hq => subset_closure ⟨hq.1.le, hq.2⟩)
  have hφ := (h.solution.phi_c1.differentiableOn (by norm_num) p
    (subset_closure hpG)).differentiableAt hG
  have hl := (h.solution.lam_c1.differentiableOn (by norm_num) p
    (subset_closure hpG)).differentiableAt hG
  have hn := (h.solution.nu_c1.differentiableOn (by norm_num) p
    (subset_closure hpG)).differentiableAt hG
  have ht := (h.solution.theta_c1.differentiableOn (by norm_num) p
    (subset_closure hpG)).differentiableAt hG
  have hz := (h.solution.zeta_c1.differentiableOn (by norm_num) p
    (subset_closure hpG)).differentiableAt hG
  have heα : (fun q : ℝ × ℝ => S.alpha q.1 q.2) =
      (fun q => S.theta q.1 q.2 + S.lam q.1 q.2 * S.phi q.1 q.2) := by
    funext q
    simp only [Fields.theta]
    ring
  have heβ : (fun q : ℝ × ℝ => S.beta q.1 q.2) =
      (fun q => S.zeta q.1 q.2 + S.nu q.1 q.2 * S.phi q.1 q.2) := by
    funext q
    simp only [Fields.zeta]
    ring
  refine ⟨hφ, hl, hn, ?_, ?_⟩
  · rw [heα]
    exact ht.fun_add (hl.fun_mul hφ)
  · rw [heβ]
    exact hz.fun_add (hn.fun_mul hφ)

private theorem fderiv_quotient_real
    {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (hne : g p ≠ 0) :
    fderiv ℝ (fun q => f q / g q) p =
      (1 / g p) • fderiv ℝ f p - (f p / g p ^ 2) • fderiv ℝ g p := by
  have hi := (hasFDerivAt_inv hne).comp p hg.hasFDerivAt
  have hm := hf.hasFDerivAt.mul hi
  change fderiv ℝ (f * ((fun y : ℝ => y⁻¹) ∘ g)) p = _
  rw [hm.fderiv]
  apply ContinuousLinearMap.ext
  intro e
  simp only [add_apply, sub_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  field_simp [hne]
  ring

/-- The classical transverse derivative of the second component is
exactly the transport density used in the area primitive's correction term. -/
theorem SmoothSolutionBounds.area_g_transport_jet
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    (fderiv ℝ (fun p => areaSectionG k (areaSectionCoefficients S p)) (u, v))
        (areaTransverseDirection k) =
      areaSectionTransportG k (areaSectionCoefficients S (u, v)) := by
  obtain ⟨_, hl, hn, hα, hβ⟩ := smooth_base_differentiable h (p := (u, v)) ⟨hu, huv⟩
  obtain ⟨_, _, hlu, hnv, hαu, hβv⟩ := h.area_first_jets hu huv
  have hlne : S.lam u v ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (h.geometry (u, v) ⟨hu.le, huv⟩).1).ne'
  have hnne : S.nu u v ≠ 0 := by
    have hh := (h.geometry (u, v) ⟨hu.le, huv⟩).2.2.1
    have hn0 : S.nu u v < 0 := by linarith only [hh]
    exact hn0.ne
  cases k with
  | phiAlphaLam =>
    change (fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2 * (S.lam p.1 p.2)⁻¹)
      (u, v)) (1, 0) = _
    rw [← show (fun p : ℝ × ℝ => S.alpha p.1 p.2 / S.lam p.1 p.2) =
      (fun p => S.alpha p.1 p.2 * (S.lam p.1 p.2)⁻¹) from
        funext (fun _ => div_eq_mul_inv _ _), fderiv_quotient_real hα hl hlne]
    simp only [sub_apply, smul_apply, smul_eq_mul, hαu, hlu, areaSectionTransportG]
    change _ = IsBVSolution.radiusCoeff S u v *
      (S.phi u v * S.lam u v - S.alpha u v) * (S.lam u v)⁻¹ ^ 2
    field_simp
  | lamPhi => exact hlu
  | phiBetaNu =>
    change (fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2 * (S.nu p.1 p.2)⁻¹)
      (u, v)) (0, 1) = _
    rw [← show (fun p : ℝ × ℝ => S.beta p.1 p.2 / S.nu p.1 p.2) =
      (fun p => S.beta p.1 p.2 * (S.nu p.1 p.2)⁻¹) from
        funext (fun _ => div_eq_mul_inv _ _), fderiv_quotient_real hβ hn hnne]
    simp only [sub_apply, smul_apply, smul_eq_mul, hβv, hnv, areaSectionTransportG]
    change _ = IsBVSolution.radiusCoeff S u v *
      (S.phi u v * S.nu u v - S.beta u v) * (S.nu u v)⁻¹ ^ 2
    field_simp
  | nuPhi => exact hnv

end ChristodoulouBV

end
