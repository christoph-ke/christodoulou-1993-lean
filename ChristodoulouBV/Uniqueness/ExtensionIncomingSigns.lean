module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingBound
public import ChristodoulouBV.BVSolution.C1InitialCompatibility
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Incoming monotonicity on finite C¹ developments

The mixed radius equation and the positive mass branch make the outgoing
expansion nonincreasing along each incoming segment. The result includes the
initial edge, where only a relative C¹ jet is given by the frozen carrier.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- On an off-axis segment of one C¹ member, `λ` is nonincreasing in `u`.
This sign propagates the mass gap on the incoming strip. -/
theorem lam_antitone_on_incoming_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {a c v : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hcv : c < v)
    (hvb : v < b) :
    S.lam c v ≤ S.lam a v := by
  let f : ℝ → ℝ := fun u => S.lam u v
  have hcont : ContinuousOn f (Icc a c) := by
    have hbase : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2)
        (closure (developmentWithInitialEdge b)) := H.lam_c1.continuousOn
    apply hbase.comp (continuous_id.prodMk continuous_const).continuousOn
    intro u hu
    apply subset_closure
    exact ⟨ha.trans hu.1, hu.2.trans_lt hcv, hvb⟩
  have hdiff : DifferentiableOn ℝ f (interior (Icc a c)) := by
    intro u hu
    have hu' : u ∈ Ioo a c := by simpa only [interior_Icc] using hu
    have hpos : 0 < u := lt_of_le_of_lt ha hu'.1
    have huv : u < v := hu'.2.trans hcv
    have hB : 0 < (v + b) / 2 := by linarith
    have hBb : (v + b) / 2 < b := by linarith
    have hvB : v < (v + b) / 2 := by linarith
    have hC := (C1Solution.five_fields_contDiffOn hB hBb H).1
    have hCi : (u, v) ∈ interior (closedCoordTriangle 0 ((v + b) / 2)) := by
      rw [interior_closedCoordTriangle]
      exact ⟨hpos, huv, hvB⟩
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v) :=
      ((hC.differentiableOn (by norm_num)).mono interior_subset (u, v) hCi).differentiableAt
        (isOpen_interior.mem_nhds hCi)
    have hpair : DifferentiableAt ℝ (fun t : ℝ => (t, v)) u :=
      (differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ => t) u).prodMk
        (differentiableAt_const v)
    exact (hd.comp u hpair).differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Icc a c), deriv f u ≤ 0 := by
    intro u hu
    have hu' : u ∈ Ioo a c := by simpa only [interior_Icc] using hu
    have hpos : 0 < u := lt_of_le_of_lt ha hu'.1
    have huv : u < v := hu'.2.trans hcv
    rw [show deriv f u =
      (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) from
      H.lam_deriv_u_of_c1 hpos huv hvb]
    have hp : (u, v) ∈ developmentWithInitialEdge b := ⟨hpos.le, huv, hvb⟩
    have hs := H.reduced_signs_of_c1 hp
    have hr := H.solution.radius_pos (u, v) hp
    have hden : 0 < (1 - 2 * S.m u v / S.r u v) * S.r u v :=
      mul_pos (by linarith [hs.2.2.2]) hr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hs.2.2.1 hs.2.1.le) hs.1.le) hden.le
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a c) hcont hdiff hderiv
  exact hanti ⟨le_rfl, hac⟩ ⟨hac, le_rfl⟩ hac

/-- Gauge data and the radial sign bound `λ` by its initial value on any
incoming segment of a finite C¹ family member. -/
theorem lam_le_half_of_initial_gauge {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ w ∈ Ioo (0 : ℝ) b, S.r 0 w = w / 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvb : v < b) :
    S.lam u v ≤ 1 / 2 := by
  calc
    S.lam u v ≤ S.lam 0 v := lam_antitone_on_incoming_of_c1 H (le_refl 0) hu huv hvb
    _ = 1 / 2 := ChristodoulouBV.initial_lam_eq_of_gauge H hr ⟨lt_of_le_of_lt hu huv, hvb⟩

end ChristodoulouBV.Uniqueness

end
