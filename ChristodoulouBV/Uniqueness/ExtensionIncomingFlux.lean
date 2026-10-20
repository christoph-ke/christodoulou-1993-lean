module

public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The off-axis incoming flux identity

The quantity `ζ²/(r |ν|)` has an outgoing derivative whose damping terms
have a favorable sign. This elementary calculus lemma is independent of the
choice of a finite member of the compatible solution family.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- The outgoing flux identity from the radius, incoming expansion, and
scalar transport equations. Here `M`, `K`, `Θ`, and `L` denote the pointwise
values of mass, `λ/(1-μ)`, scalar derivative, and outgoing expansion. -/
theorem incoming_flux_hasDerivAt
    {r nu zeta : ℝ → ℝ} {v M K Θ L : ℝ}
    (hr : HasDerivAt r L v)
    (hnu : HasDerivAt nu (2 * M * K * nu v / (r v) ^ 2) v)
    (hzeta : HasDerivAt zeta ((-nu v) * Θ / r v) v)
    (hr0 : r v ≠ 0) (hnu0 : nu v ≠ 0) :
    HasDerivAt (fun w => zeta w ^ 2 / (r w * (-nu w)))
      (2 * zeta v * Θ / (r v)^2 -
        (zeta v ^ 2 / (r v * (-nu v))) *
          (L / r v + 2 * M * K / (r v)^2)) v := by
  have hden : r v * -nu v ≠ 0 := mul_ne_zero hr0 (neg_ne_zero.mpr hnu0)
  convert (hzeta.pow 2).div (hr.mul hnu.neg) hden using 1
  simp only [Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
  field_simp
  ring

/-- The same identity yields a pointwise upper derivative bound whenever
the damping coefficient is nonnegative. -/
theorem incoming_flux_deriv_le
    {r nu zeta : ℝ → ℝ} {v M K Θ L : ℝ}
    (hr : HasDerivAt r L v)
    (hnu : HasDerivAt nu (2 * M * K * nu v / (r v) ^ 2) v)
    (hzeta : HasDerivAt zeta ((-nu v) * Θ / r v) v)
    (hrpos : 0 < r v) (hnuneg : nu v < 0)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K) :
    deriv (fun w => zeta w ^ 2 / (r w * (-nu w))) v ≤
      2 * |zeta v * Θ| / (r v)^2 := by
  have hflux := incoming_flux_hasDerivAt hr hnu hzeta
    (ne_of_gt hrpos) (ne_of_lt hnuneg)
  rw [hflux.deriv]
  have hneg : 0 < -nu v := neg_pos.mpr hnuneg
  have hG : 0 ≤ zeta v ^ 2 / (r v * (-nu v)) := by positivity
  have hdamp : 0 ≤ L / r v + 2 * M * K / (r v)^2 := by positivity
  have hsource : zeta v * Θ ≤ |zeta v * Θ| := le_abs_self _
  have hsource' : 2 * zeta v * Θ / (r v)^2 ≤
      2 * |zeta v * Θ| / (r v)^2 := by
    have hmul : 2 * zeta v * Θ ≤ 2 * |zeta v * Θ| := by nlinarith [hsource]
    exact div_le_div_of_nonneg_right hmul (sq_nonneg (r v))
  nlinarith [mul_nonneg hG hdamp]

/-- A uniform bound for the scalar source bounds the flux on a finite
outgoing segment. The statement needs no positive lower bound for `1-μ`. -/
theorem incoming_flux_le_initial_add_linear
    {r nu zeta : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b)
    (hrcont : ContinuousOn r (Set.Icc a b))
    (hnucont : ContinuousOn nu (Set.Icc a b))
    (hzcont : ContinuousOn zeta (Set.Icc a b))
    (hrpos : ∀ w ∈ Set.Icc a b, 0 < r w)
    (hnuneg : ∀ w ∈ Set.Icc a b, nu w < 0)
    (hderiv : ∀ w ∈ Set.Ioo a b, ∃ M K Θ L : ℝ,
      HasDerivAt r L w ∧
      HasDerivAt nu (2 * M * K * nu w / (r w) ^ 2) w ∧
      HasDerivAt zeta ((-nu w) * Θ / r w) w ∧
      0 ≤ L ∧ 0 ≤ M ∧ 0 ≤ K ∧
      2 * |zeta w * Θ| / (r w) ^ 2 ≤ C) :
    zeta b ^ 2 / (r b * (-nu b)) ≤
      zeta a ^ 2 / (r a * (-nu a)) + C * (b - a) := by
  let G : ℝ → ℝ := fun w => zeta w ^ 2 / (r w * (-nu w))
  have hden : ∀ w ∈ Set.Icc a b, r w * (-nu w) ≠ 0 := by
    intro w hw
    exact ne_of_gt (mul_pos (hrpos w hw) (neg_pos.mpr (hnuneg w hw)))
  have hGcont : ContinuousOn G (Set.Icc a b) :=
    (hzcont.pow 2).div (hrcont.mul hnucont.neg) hden
  have hGderiv : ∀ w ∈ Set.Ioo a b,
      HasDerivWithinAt G (deriv G w) (Set.Ioi w) w := by
    intro w hw
    obtain ⟨M, K, Θ, L, hr, hnu, hzeta, hL, hM, hK, _⟩ := hderiv w hw
    have hf := incoming_flux_hasDerivAt hr hnu hzeta
      (ne_of_gt (hrpos w ⟨hw.1.le, hw.2.le⟩))
      (ne_of_lt (hnuneg w ⟨hw.1.le, hw.2.le⟩))
    have heq : deriv G w =
        2 * zeta w * Θ / (r w) ^ 2 -
          (zeta w ^ 2 / (r w * (-nu w))) *
            (L / r w + 2 * M * K / (r w) ^ 2) := hf.deriv
    rw [heq]
    exact hf.hasDerivWithinAt
  have hGderiv_le : ∀ w ∈ Set.Ioo a b, deriv G w ≤ C := by
    intro w hw
    obtain ⟨M, K, Θ, L, hr, hnu, hzeta, hL, hM, hK, hsource⟩ := hderiv w hw
    exact (incoming_flux_deriv_le hr hnu hzeta
      (hrpos w ⟨hw.1.le, hw.2.le⟩)
      (hnuneg w ⟨hw.1.le, hw.2.le⟩) hL hM hK).trans hsource
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (by simp)
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hab hGcont hGderiv hconst hGderiv_le
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  change G b ≤ G a + C * (b - a)
  linarith only [h]

end ChristodoulouBV.Uniqueness

end
