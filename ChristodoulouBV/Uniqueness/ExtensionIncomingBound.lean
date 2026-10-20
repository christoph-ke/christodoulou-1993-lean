module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFlux
public import ChristodoulouBV.Uniqueness.ExtensionIncomingQuotient
public import ChristodoulouBV.Uniqueness.ExtensionIncomingGronwall
public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge

/-!
# Preparatory off-axis bounds for Theorem 5.1

The finite-interval flux and quotient estimates are proved in the imported
modules. The family-level estimate for the incoming weighted supremum requires
their uniform application on an exhaustion of the off-axis strip.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- The favorable outgoing flux inequality holds at each strict interior
point of a C¹ family member. The coefficient identities are obtained from the frozen first-order equations. -/
theorem incoming_flux_deriv_le_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    deriv (fun t => S.zeta u t ^ 2 /
      (S.r u t * (-S.nu u t))) v ≤
      2 * |S.zeta u v * S.theta u v| / (S.r u v) ^ 2 := by
  have hp0 := hp
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hrpos := H.solution.radius_pos (u, v) hpU
  have hlampos := H.solution.lam_pos (u, v) hpU
  have hgap := H.mass_gap_pos_of_c1 hpU
  have hnuneg := (H.reduced_signs_of_c1 hpU).1
  have hr0 : S.r u v ≠ 0 := ne_of_gt hrpos
  have hq0 : 1 - 2 * S.m u v / S.r u v ≠ 0 := ne_of_gt hgap
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v ≤ B := by dsimp [B]; linarith
  have hmnonneg : 0 ≤ S.m u v := C1Solution.mass_nonneg hB hBb H hu.le huv hvB
  have hnu : HasDerivAt (S.nu u)
      (2 * S.m u v *
        (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
        S.nu u v / (S.r u v) ^ 2) v := by
    convert nu_hasDerivAt_v_of_c1 H hp0 using 1
    field_simp [hr0, hq0]
  have hzeta : HasDerivAt (S.zeta u)
      ((-S.nu u v) * S.theta u v / S.r u v) v := by
    convert zeta_hasDerivAt_v_of_c1 H hp0 using 1
    ring
  exact incoming_flux_deriv_le (radius_hasDerivAt_v_of_c1 H hp0)
    hnu hzeta hrpos hnuneg hlampos.le hmnonneg
    (div_nonneg hlampos.le hgap.le)

/-- Uniform radius and scalar bounds control the source in the outgoing flux
inequality, with a constant independent of the finite cutoff. -/
theorem incoming_flux_source_le_of_uniform_fields
    {ρ r ζ θ Z T : ℝ}
    (hρ : 0 < ρ) (hr : ρ ≤ r)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T)
    (hζ : |ζ| ≤ Z) (hθ : |θ| ≤ T) :
    2 * |ζ * θ| / r ^ 2 ≤ 2 * Z * T / ρ ^ 2 := by
  have hrpos : 0 < r := hρ.trans_le hr
  have hprod : |ζ * θ| ≤ Z * T := by
    rw [abs_mul]
    exact mul_le_mul hζ hθ (abs_nonneg _) hZ
  have hsq : ρ ^ 2 ≤ r ^ 2 := by nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hrpos) (sq_pos_of_pos hρ)).2
  have hZT : 0 ≤ Z * T := mul_nonneg hZ hT
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hZT,
    mul_nonneg (sub_nonneg.mpr hprod) (sq_nonneg ρ)]

end ChristodoulouBV.Uniqueness

end
