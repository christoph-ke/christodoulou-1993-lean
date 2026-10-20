module

public import ChristodoulouBV.C1Solution.UniquenessMassVolterra
public import ChristodoulouBV.C1Solution.UniquenessQuadratic
import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterra
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Fixed-ray difference of canonical masses

The attenuated Volterra representation converts the two quadratic-kernel
estimates into a cubic estimate for the difference of the canonical double
masses.  Only outgoing values and vertical jets enter this estimate.
-/

public section

open Set MeasureTheory

namespace intervalIntegral

/-- The attenuation primitives on one outgoing ray retain their quadratic
difference bound when the kernel comparison is known only on that ray. -/
theorem abs_attenuationPrimitive_sub_le_on_ray
    {u s v K D : ℝ} {k₁ k₂ : ℝ × ℝ → ℝ}
    (hsv : s ≤ v)
    (hk₁ : ContinuousOn (fun t => k₁ (u, t)) (Icc s v))
    (hk₂ : ContinuousOn (fun t => k₂ (u, t)) (Icc s v))
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hbound : ∀ t ∈ Icc s v,
      |k₁ (u, t) - k₂ (u, t)| ≤ K * (t - u) * D) :
    |(∫ t in s..v, k₁ (u, t)) - (∫ t in s..v, k₂ (u, t))| ≤
      K * (v - u) ^ 2 * D / 2 := by
  have hi₁ : IntervalIntegrable (fun t => k₁ (u, t)) volume s v :=
    hk₁.intervalIntegrable_of_Icc hsv
  have hi₂ : IntervalIntegrable (fun t => k₂ (u, t)) volume s v :=
    hk₂.intervalIntegrable_of_Icc hsv
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  have h := abs_integral_le_half_sq_of_abs_le_linear hsv (mul_nonneg hK hD)
    (hi₁.sub hi₂) (by
      intro t ht
      simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using
        hbound t ht)
  nlinarith only [h]

/-- The cubic attenuation difference estimate with all difference bounds
restricted to the outgoing ray through `u`. -/
theorem abs_attenuatedVolterraIntegral_sub_le_on_ray
    {a b u v J₀ JΔ KΔ D : ℝ} {j₁ j₂ k₁ k₂ : ℝ × ℝ → ℝ}
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) (hsize : b - a ≤ 1)
    (hj₁ : ContinuousOn j₁ (closedCoordTriangle a b))
    (hj₂ : ContinuousOn j₂ (closedCoordTriangle a b))
    (hk₁ : ContinuousOn k₁ (closedCoordTriangle a b))
    (hk₂ : ContinuousOn k₂ (closedCoordTriangle a b))
    (hkpos₁ : ∀ p ∈ closedCoordTriangle a b, 0 ≤ k₁ p)
    (hkpos₂ : ∀ p ∈ closedCoordTriangle a b, 0 ≤ k₂ p)
    (hJ₀ : 0 ≤ J₀) (hKΔ : 0 ≤ KΔ) (hD : 0 ≤ D)
    (hsource₂ : ∀ t ∈ Icc u v,
      0 ≤ j₂ (u, t) ∧ j₂ (u, t) ≤ J₀ * (t - u) ^ 2)
    (hjdifference : ∀ t ∈ Icc u v,
      |j₁ (u, t) - j₂ (u, t)| ≤ JΔ * (t - u) ^ 2 * D)
    (hkdifference : ∀ t ∈ Icc u v,
      |k₁ (u, t) - k₂ (u, t)| ≤ KΔ * (t - u) * D) :
    |attenuatedVolterraIntegral j₁ k₁ u v -
      attenuatedVolterraIntegral j₂ k₂ u v| ≤
      (JΔ / 3 + J₀ * KΔ / 6) * (v - u) ^ 3 * D := by
  have hseg : ∀ s ∈ Icc u v, (u, s) ∈ closedCoordTriangle a b := by
    intro s hs
    exact ⟨hu, hs.1, hs.2.trans hv⟩
  have hqcont₁ := continuousOn_verticalVolterraPrimitive hk₁
  have hqcont₂ := continuousOn_verticalVolterraPrimitive hk₂
  have harg : ContinuousOn (fun s : ℝ => ((u, s), v)) (Icc u v) := by fun_prop
  have hmap : MapsTo (fun s : ℝ => ((u, s), v))
      (Icc u v) (closedVolterraTriple a b) := by
    intro s hs
    exact ⟨hu, hs.1, hs.2, hv⟩
  have hq₁ : ContinuousOn (fun s => ∫ t in s..v, k₁ (u, t)) (Icc u v) :=
    hqcont₁.comp harg hmap
  have hq₂ : ContinuousOn (fun s => ∫ t in s..v, k₂ (u, t)) (Icc u v) :=
    hqcont₂.comp harg hmap
  have hi₁ : IntervalIntegrable
      (fun s => j₁ (u, s) * Real.exp (-(∫ t in s..v, k₁ (u, t))))
      volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact (hj₁.comp (continuous_const.prodMk continuous_id).continuousOn hseg).mul
      (Real.continuous_exp.comp_continuousOn hq₁.neg)
  have hi₂ : IntervalIntegrable
      (fun s => j₂ (u, s) * Real.exp (-(∫ t in s..v, k₂ (u, t))))
      volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact (hj₂.comp (continuous_const.prodMk continuous_id).continuousOn hseg).mul
      (Real.continuous_exp.comp_continuousOn hq₂.neg)
  have hd : 0 ≤ v - u ∧ v - u ≤ 1 := ⟨sub_nonneg.mpr huv, by linarith⟩
  have hd2 : (v - u) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (v - u)]
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      |j₁ (u, s) * Real.exp (-(∫ t in s..v, k₁ (u, t))) -
        j₂ (u, s) * Real.exp (-(∫ t in s..v, k₂ (u, t)))| ≤
        (JΔ + J₀ * KΔ / 2) * (s - u) ^ 2 * D := by
    let q₁ := ∫ t in s..v, k₁ (u, t)
    let q₂ := ∫ t in s..v, k₂ (u, t)
    let e₁ := Real.exp (-q₁)
    let e₂ := Real.exp (-q₂)
    have hq₁pos : 0 ≤ q₁ :=
      intervalIntegral.integral_nonneg hs.2 (fun t ht =>
        hkpos₁ _ ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
    have hq₂pos : 0 ≤ q₂ :=
      intervalIntegral.integral_nonneg hs.2 (fun t ht =>
        hkpos₂ _ ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
    have he₁pos : 0 ≤ e₁ := (Real.exp_pos _).le
    have he₁le : e₁ ≤ 1 := (Real.exp_le_one_iff).2 (neg_nonpos.mpr hq₁pos)
    have hediff : |e₁ - e₂| ≤ KΔ * (v - u) ^ 2 * D / 2 :=
      (abs_exp_neg_sub_exp_neg_le hq₁pos hq₂pos).trans (by
        apply abs_attenuationPrimitive_sub_le_on_ray hs.2
        · exact hk₁.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun t ht => ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
        · exact hk₂.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun t ht => ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
        · exact hKΔ
        · exact hD
        · intro t ht
          exact hkdifference t ⟨hs.1.trans ht.1, ht.2⟩)
    have hj₂bound := hsource₂ s hs
    have hjdiff := hjdifference s hs
    have hfirst : |(j₁ (u, s) - j₂ (u, s)) * e₁| ≤
        JΔ * (s - u) ^ 2 * D := by
      rw [abs_mul, abs_of_nonneg he₁pos]
      exact (mul_le_of_le_one_right (abs_nonneg _) he₁le).trans hjdiff
    have hsecond : |j₂ (u, s) * (e₁ - e₂)| ≤
        J₀ * (s - u) ^ 2 * (KΔ * (v - u) ^ 2 * D / 2) := by
      rw [abs_mul, abs_of_nonneg hj₂bound.1]
      exact mul_le_mul hj₂bound.2 hediff (abs_nonneg _)
        (mul_nonneg hJ₀ (sq_nonneg _))
    have hsecond' : J₀ * (s - u) ^ 2 * (KΔ * (v - u) ^ 2 * D / 2) ≤
        J₀ * (s - u) ^ 2 * (KΔ * D / 2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hJ₀ (sq_nonneg _))
      nlinarith [mul_nonneg hKΔ hD]
    calc
      _ = |(j₁ (u, s) - j₂ (u, s)) * e₁ + j₂ (u, s) * (e₁ - e₂)| := by
        congr 1
        ring
      _ ≤ |(j₁ (u, s) - j₂ (u, s)) * e₁| + |j₂ (u, s) * (e₁ - e₂)| :=
        abs_add_le _ _
      _ ≤ JΔ * (s - u) ^ 2 * D +
          J₀ * (s - u) ^ 2 * (KΔ * D / 2) :=
        add_le_add hfirst (hsecond.trans hsecond')
      _ = _ := by ring
  have hmain := abs_integral_le_third_cube_of_abs_le_quadratic
    (A := (JΔ + J₀ * KΔ / 2) * D) huv
    (hi₁.sub hi₂) (by
      intro s hs
      have h := hpoint s hs
      convert h using 1
      ring)
  have heq : attenuatedVolterraIntegral j₁ k₁ u v -
      attenuatedVolterraIntegral j₂ k₂ u v =
      ∫ s in u..v,
        (j₁ (u, s) * Real.exp (-(∫ t in s..v, k₁ (u, t))) -
         j₂ (u, s) * Real.exp (-(∫ t in s..v, k₂ (u, t)))) := by
    rw [attenuatedVolterraIntegral, attenuatedVolterraIntegral,
      intervalIntegral.integral_sub hi₁ hi₂]
  rw [heq]
  nlinarith only [hmain]

end intervalIntegral

namespace ChristodoulouBV.C1Solution

/-- On a triangle of width at most one, the two canonical double masses
obey the cubic fixed-ray difference estimate with the explicit quadratic-kernel and mass-jet
coefficients. -/
theorem canonical_mass_numerator_sub_le_difference
    {b₁ b₂ B c C Bv : ℝ}
    (hB : 0 < B) (hBwidth : B ≤ 1)
    (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |canonicalMassNumerator b₁ S₁ (u, v) -
      canonicalMassNumerator b₂ S₂ (u, v)| ≤
      ((Bv ^ 2 + 2 * C * Bv *
          ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / 3 +
        C * Bv ^ 2 *
          (((Bv ^ 2 + 2 * C * Bv *
            ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / c) +
            C * Bv ^ 2 / c ^ 2) / 6) *
        (v - u) ^ 3 * outgoingDifference B hB.le S₁ S₂ u := by
  let K := closedCoordTriangle 0 B
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let j₁ := intervalIntegral.weightedDiagonalQuadraticKernel w₁ (outgoingQuotient S₁)
  let j₂ := intervalIntegral.weightedDiagonalQuadraticKernel w₂ (outgoingQuotient S₂)
  let k₁ := intervalIntegral.weightedDiagonalQuotientKernel w₁ (outgoingQuotient S₁)
  let k₂ := intervalIntegral.weightedDiagonalQuotientKernel w₂ (outgoingQuotient S₂)
  let D := outgoingDifference B hB.le S₁ S₂ u
  let J₀ := C * Bv ^ 2
  let JΔ := Bv ^ 2 + 2 * C * Bv *
    ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))
  let KΔ := JΔ / c + C * Bv ^ 2 / c ^ 2
  have hD : 0 ≤ D := outgoing_difference_nonneg hB hB₁ hB₂ H₁ H₂
    ⟨hu, huv.trans hv⟩
  have hJ₀ : 0 ≤ J₀ := by dsimp [J₀]; positivity
  have hKΔ : 0 ≤ KΔ := by dsimp [KΔ, JΔ]; positivity
  have hw₁ : ContinuousOn w₁ K :=
    (five_fields_contDiffOn hB hB₁ H₁).1.continuousOn
  have hw₂ : ContinuousOn w₂ K :=
    (five_fields_contDiffOn hB hB₂ H₂).1.continuousOn
  have hf₂ : ContinuousOn (outgoingQuotient S₂) K :=
    (alpha_div_lam_contDiffOn hB hB₂ H₂).continuousOn
  have hj₁ : ContinuousOn j₁ K :=
    (canonical_mass_kernels_contDiffOn hB hB₁ H₁).1.continuousOn
  have hj₂ : ContinuousOn j₂ K :=
    (canonical_mass_kernels_contDiffOn hB hB₂ H₂).1.continuousOn
  have hk₁ : ContinuousOn k₁ K :=
    (canonical_mass_kernels_contDiffOn hB hB₁ H₁).2.continuousOn
  have hk₂ : ContinuousOn k₂ K :=
    (canonical_mass_kernels_contDiffOn hB hB₂ H₂).2.continuousOn
  have hkpos₁ : ∀ p ∈ K, 0 ≤ k₁ p := by
    intro p hp
    rcases p with ⟨x, y⟩
    rcases lt_or_eq_of_le hp.2.1 with hlt | heq
    · have hr := intervalIntegral.mul_sub_le_weightedDiagonalRadius
        hw₁ (fun q hq => (hweight₁ q hq).1) hp.1 hlt.le hp.2.2
      have hrpos : 0 < intervalIntegral.weightedDiagonalRadius w₁ (x, y) :=
        (mul_pos hc (sub_pos.mpr hlt)).trans_le hr
      simp only [k₁, intervalIntegral.weightedDiagonalQuotientKernel,
        hlt, ↓reduceIte]
      exact div_nonneg
        (intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
          (hc.le.trans (hweight₁ (x, y) hp).1)) hrpos.le
    · change x = y at heq
      subst y
      simp [k₁, intervalIntegral.weightedDiagonalQuotientKernel_diag]
  have hkpos₂ : ∀ p ∈ K, 0 ≤ k₂ p := by
    intro p hp
    rcases p with ⟨x, y⟩
    rcases lt_or_eq_of_le hp.2.1 with hlt | heq
    · have hr := intervalIntegral.mul_sub_le_weightedDiagonalRadius
        hw₂ (fun q hq => (hweight₂ q hq).1) hp.1 hlt.le hp.2.2
      have hrpos : 0 < intervalIntegral.weightedDiagonalRadius w₂ (x, y) :=
        (mul_pos hc (sub_pos.mpr hlt)).trans_le hr
      simp only [k₂, intervalIntegral.weightedDiagonalQuotientKernel,
        hlt, ↓reduceIte]
      exact div_nonneg
        (intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
          (hc.le.trans (hweight₂ (x, y) hp).1)) hrpos.le
    · change x = y at heq
      subst y
      simp [k₂, intervalIntegral.weightedDiagonalQuotientKernel_diag]
  have hjet₂ : ∀ p ∈ K,
      HasFDerivWithinAt (outgoingQuotient S₂)
        (fderivWithin ℝ (outgoingQuotient S₂) K p) K p := by
    intro p hp
    exact ((alpha_div_lam_contDiffOn hB hB₂ H₂).differentiableOn
      (by norm_num) p hp).hasFDerivWithinAt
  have hsource₂ : ∀ p ∈ K,
      0 ≤ j₂ p ∧ j₂ p ≤ J₀ * (p.2 - p.1) ^ 2 := by
    intro p hp
    exact ⟨intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
      (hc.le.trans (hweight₂ p hp).1),
      intervalIntegral.weightedDiagonalQuadraticKernel_le_mul_sq_gap
        hw₂ hf₂ hweight₂ hc hBv hjet₂ hhvertical₂ hp⟩
  have hjdifference : ∀ t ∈ Icc u v,
      |j₁ (u, t) - j₂ (u, t)| ≤ JΔ * (t - u) ^ 2 * D := by
    intro t ht
    exact canonical_quadratic_kernel_sub_le_difference
      hB hB₁ hB₂ hc hC hBv H₁ H₂ hweight₁ hweight₂
      hhvertical₁ hhvertical₂ hu ht.1 (ht.2.trans hv)
  have hkdifference : ∀ t ∈ Icc u v,
      |k₁ (u, t) - k₂ (u, t)| ≤ KΔ * (t - u) * D := by
    intro t ht
    exact canonical_quotient_kernel_sub_le_difference
      hB hB₁ hB₂ hc hBv H₁ H₂ hweight₁ hweight₂
      hhvertical₁ hhvertical₂ hu ht.1 (ht.2.trans hv)
  have hvol := intervalIntegral.abs_attenuatedVolterraIntegral_sub_le_on_ray
    hu huv hv (by simpa using hBwidth) hj₁ hj₂ hk₁ hk₂
    hkpos₁ hkpos₂ hJ₀ hKΔ hD
    (fun t ht => hsource₂ (u, t) ⟨hu, ht.1, ht.2.trans hv⟩)
    hjdifference hkdifference
  rw [canonical_mass_numerator_eq_attenuatedVolterra hB hB₁ H₁
      ⟨hu, huv, hv⟩,
    canonical_mass_numerator_eq_attenuatedVolterra hB hB₂ H₂
      ⟨hu, huv, hv⟩]
  simpa only [j₁, j₂, k₁, k₂, w₁, w₂, J₀, JΔ, KΔ, D] using hvol

end ChristodoulouBV.C1Solution

end
