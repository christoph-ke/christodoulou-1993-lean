module

public import ChristodoulouBV.ForMathlib.Gronwall.TwoVariable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# A uniform estimate for a coupled characteristic transport system

The two scalar transport equations have derivatives bounded by the sum of
the two scalar amplitudes. A two-variable Volterra estimate turns bounds on
the two characteristic edges into a bound on a closed rectangle.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- A coupled characteristic system with bounded transport coefficients has
an explicit bound depending only on its edge data and the rectangle size. -/
theorem scalar_transport_rectangle_bound
    {a b c d C A Z : ℝ} {θ ζ : ℝ → ℝ → ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (hθcont : ContinuousOn (fun p : ℝ × ℝ => θ p.1 p.2)
      (Icc a b ×ˢ Icc c d))
    (hζcont : ContinuousOn (fun p : ℝ × ℝ => ζ p.1 p.2)
      (Icc a b ×ˢ Icc c d))
    (hθedge : ∀ v ∈ Icc c d, |θ a v| ≤ A)
    (hζedge : ∀ u ∈ Icc a b, |ζ u c| ≤ Z)
    (hθderiv : ∀ u ∈ Ioo a b, ∀ v ∈ Icc c d,
      DifferentiableAt ℝ (fun s => θ s v) u ∧
        |deriv (fun s => θ s v) u| ≤ C * (|θ u v| + |ζ u v|))
    (hζderiv : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d,
      DifferentiableAt ℝ (ζ u) v ∧
        |deriv (ζ u) v| ≤ C * (|θ u v| + |ζ u v|)) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      |θ u v| + |ζ u v| ≤
        2 * (A + Z) * (Real.exp ((4 * C + 1) * (u - a)) *
          Real.exp ((4 * C + 1) * (v - c))) := by
  let F : ℝ → ℝ → ℝ := fun u v => |θ u v| + |ζ u v|
  let R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) R :=
    hθcont.abs.add hζcont.abs
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hFcont
  have hF0 : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, 0 ≤ F u v := by
    intro u hu v hv
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB0 : 0 ≤ B := by
    have h := hB (a, c) ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hcd⟩⟩
    exact (hF0 a ⟨le_rfl, hab⟩ c ⟨le_rfl, hcd⟩).trans
      ((le_abs_self (F a c)).trans (by simpa only [Real.norm_eq_abs] using h))
  have hFB : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, F u v ≤ B := by
    intro u hu v hv
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB (u, v) ⟨hu, hv⟩)
  have hFu : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntervalIntegrable (fun s => F s v) volume a u := by
    intro u hu v hv
    have hc : ContinuousOn (fun s => F s v) (Icc a u) := by
      apply hFcont.comp (continuous_id.prodMk continuous_const).continuousOn
      intro s hs
      exact ⟨⟨hs.1, hs.2.trans hu.2⟩, hv⟩
    exact hc.intervalIntegrable_of_Icc hu.1
  have hFv : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      IntervalIntegrable (F u) volume c v := by
    intro u hu v hv
    have hc : ContinuousOn (F u) (Icc c v) := by
      apply hFcont.comp (continuous_const.prodMk continuous_id).continuousOn
      intro t ht
      exact ⟨hu, ⟨ht.1, ht.2.trans hv.2⟩⟩
    exact hc.intervalIntegrable_of_Icc hv.1
  have hθineq (u : ℝ) (hu : u ∈ Icc a b)
      (v : ℝ) (hv : v ∈ Icc c d) :
      |θ u v| ≤ A + C * ∫ s in a..u, F s v := by
    have hc : ContinuousOn (fun s => θ s v) (Icc a u) := by
      apply hθcont.comp (continuous_id.prodMk continuous_const).continuousOn
      intro s hs
      exact ⟨⟨hs.1, hs.2.trans hu.2⟩, hv⟩
    have hd : DifferentiableOn ℝ (fun s => θ s v) (Ioo a u) := by
      intro s hs
      exact (hθderiv s ⟨hs.1, hs.2.trans_le hu.2⟩ v hv).1.differentiableWithinAt
    have hderiv : ∀ᵐ s, s ∈ Ioo a u →
        ‖deriv (fun t => θ t v) s‖ ≤ C * F s v :=
      Filter.Eventually.of_forall (fun s hs => by
        simpa only [Real.norm_eq_abs] using
          (hθderiv s ⟨hs.1, hs.2.trans_le hu.2⟩ v hv).2)
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hu.1 hc hd hderiv
      ((hFu u hu v hv).const_mul C)
    have htri := abs_add_le (θ a v) (θ u v - θ a v)
    have hsum : |θ u v| ≤ |θ a v| + |θ u v - θ a v| := by
      convert htri using 1; ring_nf
    calc
      |θ u v| ≤ |θ a v| + |θ u v - θ a v| := hsum
      _ ≤ A + C * ∫ s in a..u, F s v := by
        rw [intervalIntegral.integral_const_mul] at h
        have h' : |θ u v - θ a v| ≤ C * ∫ s in a..u, F s v := by
          simpa only [Real.norm_eq_abs] using h
        exact add_le_add (hθedge v hv) h'
  have hζineq (u : ℝ) (hu : u ∈ Icc a b)
      (v : ℝ) (hv : v ∈ Icc c d) :
      |ζ u v| ≤ Z + C * ∫ t in c..v, F u t := by
    have hc : ContinuousOn (ζ u) (Icc c v) := by
      apply hζcont.comp (continuous_const.prodMk continuous_id).continuousOn
      intro t ht
      exact ⟨hu, ⟨ht.1, ht.2.trans hv.2⟩⟩
    have hd : DifferentiableOn ℝ (ζ u) (Ioo c v) := by
      intro t ht
      exact (hζderiv u hu t ⟨ht.1, ht.2.trans_le hv.2⟩).1.differentiableWithinAt
    have hderiv : ∀ᵐ t, t ∈ Ioo c v →
        ‖deriv (ζ u) t‖ ≤ C * F u t :=
      Filter.Eventually.of_forall (fun t ht => by
        simpa only [Real.norm_eq_abs] using
          (hζderiv u hu t ⟨ht.1, ht.2.trans_le hv.2⟩).2)
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hv.1 hc hd hderiv
      ((hFv u hu v hv).const_mul C)
    have hsum : |ζ u v| ≤ |ζ u c| + |ζ u v - ζ u c| := by
      convert abs_add_le (ζ u c) (ζ u v - ζ u c) using 1; ring_nf
    calc
      |ζ u v| ≤ |ζ u c| + |ζ u v - ζ u c| := hsum
      _ ≤ Z + C * ∫ t in c..v, F u t := by
        rw [intervalIntegral.integral_const_mul] at h
        have h' : |ζ u v - ζ u c| ≤ C * ∫ t in c..v, F u t := by
          simpa only [Real.norm_eq_abs] using h
        exact add_le_add (hζedge u hu) h'
  have hineq : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      F u v ≤ (A + Z) + C * (∫ s in a..u, F s v) +
        C * (∫ t in c..v, F u t) := by
    intro u hu v hv
    dsimp [F]
    linarith only [hθineq u hu v hv, hζineq u hu v hv]
  exact intervalIntegral.le_two_variable_volterra_exp hab hcd hC hB0
    (add_nonneg hA hZ) hF0 hFB (fun _ _ _ _ => le_refl _) hFu hFv
    (fun u hu v hv => hineq u hu v hv)

end ChristodoulouBV.Uniqueness

end
