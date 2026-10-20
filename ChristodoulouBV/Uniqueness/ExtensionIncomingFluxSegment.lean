module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingBound
public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarFamily
import ChristodoulouBV.BVSolution.Signs
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Outgoing flux bound on one C¹ member

The favorable flux derivative and scalar source estimate integrate along
any off-axis outgoing segment inside one member.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming flux on one outgoing segment is bounded by its value at
the left edge plus a linear source term. The coefficient is independent of
the mass gap. -/
theorem incoming_flux_le_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u vBar v ρ M : ℝ}
    (hu : 0 < u) (huBar : u < vBar) (hBarv : vBar ≤ v) (hvb : v < b)
    (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hr : ∀ w ∈ Icc vBar v, ρ ≤ S.r u w)
    (hθ : ∀ w ∈ Icc vBar v, |S.theta u w| ≤ M)
    (hζ : ∀ w ∈ Icc vBar v, |S.zeta u w| ≤ M) :
    S.zeta u v ^ 2 / (S.r u v * (-S.nu u v)) ≤
      S.zeta u vBar ^ 2 / (S.r u vBar * (-S.nu u vBar)) +
        (2 * M ^ 2 / ρ ^ 2) * (v - vBar) := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hmap (w : ℝ) (hw : w ∈ Icc vBar v) :
      (u, w) ∈ closedCoordTriangle 0 B := by
    change 0 ≤ u ∧ u ≤ w ∧ w ≤ B
    exact ⟨hu.le, huBar.le.trans hw.1, hw.2.trans hvB.le⟩
  have hcontR : ContinuousOn (S.r u) (Icc vBar v) := by
    have hcanonical : ContinuousOn
        (fun w => C1Solution.canonicalRadius S (u, w)) (Icc vBar v) :=
      (C1Solution.canonicalRadius_contDiffOn hB hBb H).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    apply hcanonical.congr
    intro w hw
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H
      hu.le (huBar.trans_le hw.1) (hw.2.trans hvB.le)).symm
  have hcontNu : ContinuousOn (S.nu u) (Icc vBar v) := by
    apply H.nu_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro w hw
    apply subset_closure
    exact ⟨hu.le, huBar.trans_le hw.1, hw.2.trans_lt hvb⟩
  have hcontZeta : ContinuousOn (S.zeta u) (Icc vBar v) := by
    apply H.zeta_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro w hw
    apply subset_closure
    exact ⟨hu.le, huBar.trans_le hw.1, hw.2.trans_lt hvb⟩
  have hpU (w : ℝ) (hw : w ∈ Icc vBar v) :
      (u, w) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, huBar.trans_le hw.1, hw.2.trans_lt hvb⟩
  have hposR : ∀ w ∈ Icc vBar v, 0 < S.r u w :=
    fun w hw => H.solution.radius_pos (u, w) (hpU w hw)
  have hnegNu : ∀ w ∈ Icc vBar v, S.nu u w < 0 :=
    fun w hw => (H.reduced_signs_of_c1 (hpU w hw)).1
  have hderiv : ∀ w ∈ Ioo vBar v, ∃ mass κ Θ L : ℝ,
      HasDerivAt (S.r u) L w ∧
      HasDerivAt (S.nu u)
        (2 * mass * κ * S.nu u w / (S.r u w) ^ 2) w ∧
      HasDerivAt (S.zeta u) ((-S.nu u w) * Θ / S.r u w) w ∧
      0 ≤ L ∧ 0 ≤ mass ∧ 0 ≤ κ ∧
      2 * |S.zeta u w * Θ| / (S.r u w) ^ 2 ≤ 2 * M ^ 2 / ρ ^ 2 := by
    intro w hw
    have hp : (u, w) ∈ openDevelopment 0 b := by
      have huw : u < w := huBar.trans hw.1
      have hwb : w < b := hw.2.trans hvb
      exact ⟨⟨hu, huw.trans hwb⟩, ⟨huw, hwb⟩⟩
    have hpu := hpU w ⟨hw.1.le, hw.2.le⟩
    have hrpos := H.solution.radius_pos (u, w) hpu
    have hgap := H.mass_gap_pos_of_c1 hpu
    have hlam := H.solution.lam_pos (u, w) hpu
    have hmass : 0 ≤ S.m u w := by
      let B₀ := (w + b) / 2
      have hwpos : 0 < w := hu.trans (huBar.trans hw.1)
      have hwb : w < b := hw.2.trans hvb
      have hB₀ : 0 < B₀ := by dsimp [B₀]; linarith only [hwpos, hwb]
      have hB₀b : B₀ < b := by dsimp [B₀]; linarith only [hwb]
      have hwB₀ : w ≤ B₀ := by dsimp [B₀]; linarith only [hwb]
      exact C1Solution.mass_nonneg hB₀ hB₀b H hu.le (huBar.trans hw.1) hwB₀
    refine ⟨S.m u w, S.lam u w /
      (1 - 2 * S.m u w / S.r u w), S.theta u w, S.lam u w,
      radius_hasDerivAt_v_of_c1 H hp, ?_, ?_, hlam.le, hmass,
      div_nonneg hlam.le hgap.le, ?_⟩
    · convert nu_hasDerivAt_v_of_c1 H hp using 1
      field_simp [ne_of_gt hrpos, ne_of_gt hgap]
    · convert zeta_hasDerivAt_v_of_c1 H hp using 1
      ring
    · simpa only [pow_two, mul_assoc] using incoming_flux_source_le_of_uniform_fields hρ
        (hr w ⟨hw.1.le, hw.2.le⟩) hM hM
        (hζ w ⟨hw.1.le, hw.2.le⟩)
        (hθ w ⟨hw.1.le, hw.2.le⟩)
  exact incoming_flux_le_initial_add_linear hBarv hcontR hcontNu
    hcontZeta hposR hnegNu hderiv

end ChristodoulouBV.Uniqueness

end
