module

public import ChristodoulouBV.Existence.TransportLimit
public import ChristodoulouBV.Existence.AreaLowerSemicontinuityLower
import Mathlib.Tactic

/-!
# Concrete coefficients for the four area sections

The scalar partial derivatives are represented by their frozen densities
`ζ/r` and `θ/r`. Their mixed derivative density is
`-(λ * ζ + ν * θ) / r²`. This avoids evaluating a classical derivative
at a BV jump. The Stieltjes expression uses the pointwise
integration-by-parts primitive, including the prescribed jump values.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The four ordered field pairs in (6.4a)--(6.4d), in printed order. -/
inductive AreaSectionPair
  | phiAlphaLam
  | lamPhi
  | phiBetaNu
  | nuPhi
  deriving DecidableEq

/-- Whether the variation variable of a pair is the incoming coordinate. -/
@[expose] def AreaSectionPair.incoming : AreaSectionPair → Bool
  | .phiAlphaLam | .lamPhi => false
  | .phiBetaNu | .nuPhi => true

/-- The coefficients needed in an area primitive. The entries are
`1/r, λ, ν, φ, α, β, rᵤᵥ, 1/λ, 1/ν`. -/
@[expose] noncomputable def areaSectionCoefficients (S : Fields) (p : ℝ × ℝ) :
    Fin 9 → ℝ :=
  ![(S.r p.1 p.2)⁻¹, S.lam p.1 p.2, S.nu p.1 p.2, S.phi p.1 p.2,
    S.alpha p.1 p.2, S.beta p.1 p.2, IsBVSolution.radiusCoeff S p.1 p.2,
    (S.lam p.1 p.2)⁻¹, (S.nu p.1 p.2)⁻¹]

/-- The first scalar density, with the orientation of the area pair. -/
@[expose] def areaSectionF (k : AreaSectionPair) (z : Fin 9 → ℝ) : ℝ :=
  if k.incoming then (z 4 - z 1 * z 3) * z 0
  else (z 5 - z 2 * z 3) * z 0

/-- The BV field in the area pair. -/
@[expose] def areaSectionG (k : AreaSectionPair) (z : Fin 9 → ℝ) : ℝ :=
  match k with
  | .phiAlphaLam => z 4 * z 7
  | .lamPhi => z 1
  | .phiBetaNu => z 5 * z 8
  | .nuPhi => z 2

/-- The mixed scalar density, before the coordinate Jacobian is inserted. -/
@[expose] def areaSectionP (z : Fin 9 → ℝ) : ℝ :=
  -(z 1 * (z 5 - z 2 * z 3) + z 2 * (z 4 - z 1 * z 3)) * z 0 ^ 2

/-- The ordinary-integral correction, before the coordinate Jacobian.
The quotient transport densities follow from `αᵤ = rᵤᵥ φ`,
`βᵥ = rᵤᵥ φ`, `λᵤ = rᵤᵥ`, and `νᵥ = rᵤᵥ`. -/
@[expose] def areaSectionH (k : AreaSectionPair) (z : Fin 9 → ℝ) : ℝ :=
  match k with
  | .phiAlphaLam =>
    (z 4 - z 1 * z 3) * z 0 * (z 6 * (z 3 * z 1 - z 4) * z 7 ^ 2)
  | .lamPhi => (z 4 - z 1 * z 3) * z 0 * z 6
  | .phiBetaNu =>
    (z 5 - z 2 * z 3) * z 0 * (z 6 * (z 3 * z 2 - z 5) * z 8 ^ 2)
  | .nuPhi => (z 5 - z 2 * z 3) * z 0 * z 6

/-- Every coefficient formula for the four section primitives is continuous
as a function of the nine algebraic coefficients. -/
theorem area_section_formulas_continuous (k : AreaSectionPair) :
    Continuous (areaSectionF k) ∧ Continuous (areaSectionG k) ∧
      Continuous areaSectionP ∧ Continuous (areaSectionH k) := by
  change Continuous (fun z => areaSectionF k z) ∧
    Continuous (fun z => areaSectionG k z) ∧
    Continuous (fun z => areaSectionP z) ∧ Continuous (fun z => areaSectionH k z)
  cases k <;>
    simp only [areaSectionF, areaSectionG, areaSectionP, areaSectionH,
      AreaSectionPair.incoming, Bool.false_eq_true, ite_false, ite_true] <;>
    exact ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

/-- The physical affine null section. Both orientations use the same unit
parameter, so its signed derivative is `b - a`. -/
@[expose] def areaNullSection (k : AreaSectionPair) (z a b x : ℝ) : ℝ × ℝ :=
  if k.incoming then (a + (b - a) * x, z) else (z, a + (b - a) * x)

/-- The affine null-section map is continuous. -/
theorem area_null_section_continuous (k : AreaSectionPair) (z a b : ℝ) :
    Continuous (areaNullSection k z a b) := by
  change Continuous (fun x => areaNullSection k z a b x)
  cases k <;> simp only [areaNullSection, AreaSectionPair.incoming,
    Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- The pointwise integration-by-parts primitive on an affine null
section. Both density terms contain the signed coordinate factor `b-a`. -/
@[expose] noncomputable def areaSectionPrimitive (k : AreaSectionPair)
    (S : Fields) (z a b : ℝ) : ℝ → ℝ :=
  let c := fun x => areaSectionCoefficients S (areaNullSection k z a b x)
  intervalIntegral.productPrimitive
    (fun x => areaSectionF k (c x)) (fun x => areaSectionG k (c x))
    (fun x => (b - a) * areaSectionP (c x))
    (fun x => (b - a) * areaSectionH k (c x))

/-- All nine raw coefficients converge on the shared seven-field
subsequence. No representative at a jump is replaced in this statement. -/
theorem RadiusLimitData.area_section_coefficients_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun n => areaSectionCoefficients (T (d.subsequence n)) p)
      atTop (𝓝 (areaSectionCoefficients d.rawFields p)) := by
  rw [tendsto_pi_nhds]
  intro i
  have hr := d.radius_limit.tendsto_at hp
  have hφ := d.scalar_locally_uniform h |>.tendsto_at hp
  have hg := (expansions_limit h d).2.2 p hp
  have hl0 : d.lam p.1 p.2 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hg.1)
  have hn0 : d.nu p.1 p.2 ≠ 0 := by linarith only [hg.2.2.1]
  fin_cases i
  · exact hr.inv₀ (d.radius_pos h hp).ne'
  · exact d.lam_limit p hp
  · exact d.nu_limit p hp
  · exact hφ
  · exact d.alpha_limit p hp
  · exact d.beta_limit p hp
  · exact d.raw_radius_coeff_limit h hp
  · exact (d.lam_limit p hp).inv₀ hl0
  · exact (d.nu_limit p hp).inv₀ hn0

end ChristodoulouBV

end
