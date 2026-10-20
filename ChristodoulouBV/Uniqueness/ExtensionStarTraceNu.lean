module

public import ChristodoulouBV.ForMathlib.ODE.InteriorLinearGrowth
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceExpansion
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Incoming expansion bound from the cubic mass estimate

The outgoing `ν` equation is linear. Its coefficient is uniformly bounded by
the cubic mass estimate, and the axis identity supplies its initial value.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The axis value of `λ` inherits the initial-gauge upper bound by closed
triangle continuity. -/
theorem lam_axis_le_half_of_initial_gauge
    {b u v : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2)
    (hu : 0 < u) (huv : u < v) (hvb : v < b) :
    S.lam u u ≤ 1 / 2 := by
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hu, huv, hvb]
  have hBb : B < b := by dsimp [B]; linarith only [hvb]
  have hvB : v < B := by dsimp [B]; linarith only [hvb]
  have hcont : ContinuousOn (S.lam u) (Icc u v) :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨hu.le, hw.1, hw.2.trans hvB.le⟩)
  have hcont' : ContinuousOn (S.lam u) (closure (Ioo u v)) := by
    rwa [closure_Ioo (ne_of_lt huv)]
  have hclosure : u ∈ closure (Ioo u v) := by
    rw [closure_Ioo (ne_of_lt huv)]
    exact ⟨le_refl u, huv.le⟩
  apply le_on_closure
    (fun w hw => lam_le_half_of_initial_gauge H hr hu.le hw.1 (hw.2.trans hvb))
    hcont' continuousOn_const hclosure

/-- A one-member bound for the incoming expansion on an outgoing ray. The
mass and gap hypotheses will be supplied uniformly by the family estimates. -/
theorem nu_abs_le_of_cubic_mass_on_outgoing
    {b u v B q₀ R : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hrGauge : ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2)
    (hu : 0 < u) (huv : u < v) (hvb : v < b)
    (hq₀ : 0 < q₀)
    (hmass : ∀ w ∈ Ioo u v,
      2 * S.m u w / S.r u w ≤ B ^ 2 / 12 * (S.r u w) ^ 2)
    (hgap : ∀ w ∈ Ioo u v,
      q₀ ≤ 1 - 2 * S.m u w / S.r u w)
    (hrUpper : ∀ w ∈ Ioo u v, S.r u w ≤ R) :
    |S.nu u v| ≤ (1 / 2 : ℝ) *
      Real.exp ((B ^ 2 * R / (24 * q₀)) * (v - u)) := by
  let T := (v + b) / 2
  have hT : 0 < T := by dsimp [T]; linarith only [hu, huv, hvb]
  have hTb : T < b := by dsimp [T]; linarith only [hvb]
  have hvT : v < T := by dsimp [T]; linarith only [hvb]
  have hrect (w : ℝ) (hw : w ∈ Icc u v) :
      (u, w) ∈ closedCoordTriangle 0 T :=
    ⟨hu.le, hw.1, hw.2.trans hvT.le⟩
  have hcont : ContinuousOn (S.nu u) (Icc u v) :=
    ((C1Solution.five_fields_contDiffOn hT hTb H).2.1.continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn hrect
  let f : ℝ → ℝ := fun w => -S.nu u w
  let A : ℝ → ℝ := fun w =>
    (2 * S.m u w / S.r u w) * S.lam u w /
      ((1 - 2 * S.m u w / S.r u w) * S.r u w)
  let C : ℝ := B ^ 2 * R / (24 * q₀)
  have hfcont : ContinuousOn f (Icc u v) := hcont.neg
  have haxis : S.nu u u = -S.lam u u :=
    C1Solution.nu_eq_neg_lam_axis hT hTb H ⟨hu.le, (huv.trans hvT).le⟩
  have hfloorAxis : 0 < S.lam u u := by
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hT hTb H
    exact hc.trans_le (hcl (u, u) ⟨hu.le, le_rfl, (huv.trans hvT).le⟩)
  have hfnonneg : ∀ w ∈ Icc u v, 0 ≤ f w := by
    intro w hw
    by_cases hwu : w = u
    · subst w
      dsimp [f]
      rw [haxis]
      linarith only [hfloorAxis]
    · have huw : u < w := lt_of_le_of_ne hw.1 (Ne.symm hwu)
      have hsign := H.reduced_signs_of_c1
        (show (u, w) ∈ developmentWithInitialEdge b from
          ⟨hu.le, huw, hw.2.trans_lt hvb⟩)
      dsimp [f]
      linarith only [hsign.1]
  have hA : ∀ w ∈ Ioo u v, A w ≤ C := by
    intro w hw
    have hp : (u, w) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, hw.1, hw.2.trans hvb⟩
    have hrad : 0 < S.r u w := H.solution.radius_pos (u, w) hp
    have hcoeff := mass_ratio_coefficient_le_linear_radius (B := B) hrad hq₀
      (hgap w hw) (by convert hmass w hw using 1; ring)
    have hlam0 : 0 ≤ S.lam u w := (H.solution.lam_pos (u, w) hp).le
    have hlam : S.lam u w ≤ 1 / 2 :=
      lam_le_half_of_initial_gauge H hrGauge hu.le hw.1 (hw.2.trans hvb)
    have hfirst : A w ≤
        (S.lam u w) * (B ^ 2 / (12 * q₀) * S.r u w) := by
      dsimp [A]
      have heq : (2 * S.m u w / S.r u w) * S.lam u w /
          ((1 - 2 * S.m u w / S.r u w) * S.r u w) =
          S.lam u w * ((2 * S.m u w / S.r u w) /
            ((1 - 2 * S.m u w / S.r u w) * S.r u w)) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hcoeff hlam0
    have hsecond : (S.lam u w) * (B ^ 2 / (12 * q₀) * S.r u w) ≤
        (1 / 2 : ℝ) * (B ^ 2 / (12 * q₀) * S.r u w) :=
      mul_le_mul_of_nonneg_right hlam (by positivity)
    have hthird : (1 / 2 : ℝ) * (B ^ 2 / (12 * q₀) * S.r u w) ≤ C := by
      have hco : 0 ≤ B ^ 2 / (12 * q₀) := by positivity
      have hbound := mul_le_mul_of_nonneg_left (hrUpper w hw) hco
      calc
        (1 / 2 : ℝ) * (B ^ 2 / (12 * q₀) * S.r u w) ≤
            (1 / 2 : ℝ) * (B ^ 2 / (12 * q₀) * R) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = C := by dsimp [C]; ring
    exact hfirst.trans (hsecond.trans hthird)
  have hderiv : ∀ w ∈ Ioo u v,
      HasDerivAt f (A w * f w) w := by
    intro w hw
    have hp : (u, w) ∈ openDevelopment 0 b :=
      ⟨⟨hu, hw.1.trans (hw.2.trans hvb)⟩,
        ⟨hw.1, hw.2.trans hvb⟩⟩
    convert (nu_hasDerivAt_v_of_c1 H hp).neg using 1
    dsimp [f, A]
    ring
  have hmain := ChristodoulouBV.ForMathlib.nonneg_le_initial_mul_exp_of_interior_linear_deriv
    huv.le hfcont hfnonneg hA hderiv v ⟨huv.le, le_rfl⟩
  have haxisUpper : S.lam u u ≤ 1 / 2 :=
    lam_axis_le_half_of_initial_gauge H hrGauge hu huv hvb
  have hνnegative : S.nu u v < 0 :=
    (H.reduced_signs_of_c1
      (show (u, v) ∈ developmentWithInitialEdge b from ⟨hu.le, huv, hvb⟩)).1
  have hvalue : |S.nu u v| = f v := by
    dsimp [f]
    rw [abs_of_neg hνnegative]
  rw [hvalue]
  have hbase : f u = S.lam u u := by dsimp [f]; rw [haxis]; ring
  rw [hbase] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_right haxisUpper (Real.exp_nonneg _))

end ChristodoulouBV.Uniqueness

end
