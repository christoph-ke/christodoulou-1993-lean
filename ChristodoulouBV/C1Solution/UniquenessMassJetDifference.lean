module

public import ChristodoulouBV.C1Solution.UniquenessMassDifference
import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernel
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Vertical difference of canonical masses

The fixed-ray mass value estimate and the vertical mass equation give the
quadratic difference bound for the outgoing jet of the double mass.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- On a compact triangle, the canonical quadratic source and its quotient
kernel have the common outgoing axis bounds needed by the mass equation. -/
theorem canonical_mass_kernel_value_bounds
    {b B c C Bv : ℝ} (hB : 0 < B) (hBb : B < b)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hweight : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hhvertical : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
    let j := intervalIntegral.weightedDiagonalQuadraticKernel w (outgoingQuotient S)
    let k := intervalIntegral.weightedDiagonalQuotientKernel w (outgoingQuotient S)
    (0 ≤ j p ∧ j p ≤ C * Bv ^ 2 * (p.2 - p.1) ^ 2) ∧
    (0 ≤ k p ∧ k p ≤ (C * Bv ^ 2 / c) * (p.2 - p.1)) := by
  dsimp only
  let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let f := outgoingQuotient S
  have hw : ContinuousOn w (closedCoordTriangle 0 B) :=
    (five_fields_contDiffOn hB hBb H).1.continuousOn
  have hf : ContinuousOn f (closedCoordTriangle 0 B) :=
    (alpha_div_lam_contDiffOn hB hBb H).continuousOn
  have hjet : ∀ q ∈ closedCoordTriangle 0 B,
      HasFDerivWithinAt f
        (fderivWithin ℝ f (closedCoordTriangle 0 B) q)
        (closedCoordTriangle 0 B) q := by
    intro q hq
    exact ((alpha_div_lam_contDiffOn hB hBb H).differentiableOn
      (by norm_num) q hq).hasFDerivWithinAt
  have hjpos : 0 ≤ intervalIntegral.weightedDiagonalQuadraticKernel w f p :=
    intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
      (hc.le.trans (hweight p hp).1)
  have hjbound := intervalIntegral.weightedDiagonalQuadraticKernel_le_mul_sq_gap
    hw hf hweight hc hBv hjet hhvertical hp
  have hkbound := intervalIntegral.weightedDiagonalQuotientKernel_bounds_on_jetBox
    hw hf hweight hc hBv hjet hhvertical hp
  exact ⟨⟨hjpos, hjbound⟩,
    by simpa only [intervalIntegral.weightedDiagonalQuotientValueCoefficient]
      using hkbound⟩

/-- The canonical double mass is nonnegative and has its exact cubic
outgoing bound on every smaller closed triangle. -/
theorem canonical_mass_numerator_nonneg_le
    {b T c C Bv : ℝ} (hT : 0 < T) (hTb : T < b)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hweight : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hhvertical : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    0 ≤ canonicalMassNumerator b S (u, v) ∧
      canonicalMassNumerator b S (u, v) ≤
        (C * Bv ^ 2 / 3) * (v - u) ^ 3 := by
  let K := closedCoordTriangle 0 T
  let w : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let j := intervalIntegral.weightedDiagonalQuadraticKernel w (outgoingQuotient S)
  let k := intervalIntegral.weightedDiagonalQuotientKernel w (outgoingQuotient S)
  have hj : ContinuousOn j K :=
    (canonical_mass_kernels_contDiffOn hT hTb H).1.continuousOn
  have hk : ContinuousOn k K :=
    (canonical_mass_kernels_contDiffOn hT hTb H).2.continuousOn
  have hsource : ∀ p ∈ K,
      0 ≤ j p ∧ j p ≤ (C * Bv ^ 2) * (p.2 - p.1) ^ 2 := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hT hTb hc hBv H
      hweight hhvertical hp).1
  have hkernel : ∀ p ∈ K, 0 ≤ k p := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hT hTb hc hBv H
      hweight hhvertical hp).2.1
  have h := intervalIntegral.attenuatedVolterraIntegral_nonneg_le
    hu huv hv hj hk hkernel hsource
  rw [canonical_mass_numerator_eq_attenuatedVolterra hT hTb H
    ⟨hu, huv, hv⟩]
  constructor
  · exact h.1
  · calc
      _ ≤ C * Bv ^ 2 * (v - u) ^ 3 / 3 := h.2
      _ = _ := by ring

/-- The vertical jet of the canonical double mass has the quadratic
single-input Volterra bound at width at most one. -/
theorem canonical_mass_numerator_vertical_jet_abs_le
    {b T c C Bv : ℝ} (hT : 0 < T) (hTwidth : T ≤ 1) (hTb : T < b)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hweight : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hhvertical : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    |(fderivWithin ℝ (canonicalMassNumerator b S)
      (closedCoordTriangle 0 T) (u, v)) (0, 1)| ≤
      (C * Bv ^ 2 + (C * Bv ^ 2 / c) * (C * Bv ^ 2 / 3)) *
        (v - u) ^ 2 := by
  let K := closedCoordTriangle 0 T
  let w : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let j := intervalIntegral.weightedDiagonalQuadraticKernel w (outgoingQuotient S)
  let k := intervalIntegral.weightedDiagonalQuotientKernel w (outgoingQuotient S)
  let V : ℝ × ℝ → ℝ := fun p =>
    intervalIntegral.attenuatedVolterraIntegral j k p.1 p.2
  have hj : ContDiffOn ℝ 1 j K :=
    (canonical_mass_kernels_contDiffOn hT hTb H).1
  have hk : ContDiffOn ℝ 1 k K :=
    (canonical_mass_kernels_contDiffOn hT hTb H).2
  have hsource : ∀ p ∈ K,
      0 ≤ j p ∧ j p ≤ (C * Bv ^ 2) * (p.2 - p.1) ^ 2 := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hT hTb hc hBv H
      hweight hhvertical hp).1
  have hkernel : ∀ p ∈ K,
      0 ≤ k p ∧ k p ≤ (C * Bv ^ 2 / c) * (p.2 - p.1) := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hT hTb hc hBv H
      hweight hhvertical hp).2
  have hC : 0 ≤ C := by
    have hp : (0, 0) ∈ K := ⟨le_rfl, le_rfl, hT.le⟩
    have hbox := hweight (0, 0) hp
    linarith only [hc, hbox.1, hbox.2]
  have hval := intervalIntegral.abs_fderivWithin_attenuatedVolterraIntegral_vertical_le
    hT hu huv hv (by simpa using hTwidth) hj hk
    (by positivity) (by positivity)
    hsource hkernel
  have heq : EqOn (canonicalMassNumerator b S) V K := by
    intro p hp
    exact canonical_mass_numerator_eq_attenuatedVolterra hT hTb H hp
  rw [fderivWithin_congr' heq ⟨hu, huv, hv⟩]
  exact hval

/-- The outgoing jet of the canonical double mass differs by at most the
explicit quadratic mass-jet coefficient times the moving four-field difference. -/
theorem canonical_mass_numerator_vertical_jet_sub_le_difference
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
    |(fderivWithin ℝ (canonicalMassNumerator b₁ S₁)
        (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ (canonicalMassNumerator b₂ S₂)
        (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
      (let J₀ := C * Bv ^ 2
       let JΔ := Bv ^ 2 + 2 * C * Bv *
         ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))
       let K₀ := J₀ / c
       let KΔ := JΔ / c + J₀ / c ^ 2
       JΔ + KΔ * (J₀ / 3) +
         K₀ * (JΔ / 3 + J₀ * KΔ / 6)) *
        (v - u) ^ 2 * outgoingDifference B hB.le S₁ S₂ u := by
  let K := closedCoordTriangle 0 B
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let j₁ := intervalIntegral.weightedDiagonalQuadraticKernel w₁ (outgoingQuotient S₁)
  let j₂ := intervalIntegral.weightedDiagonalQuadraticKernel w₂ (outgoingQuotient S₂)
  let k₁ := intervalIntegral.weightedDiagonalQuotientKernel w₁ (outgoingQuotient S₁)
  let k₂ := intervalIntegral.weightedDiagonalQuotientKernel w₂ (outgoingQuotient S₂)
  let D := outgoingDifference B hB.le S₁ S₂ u
  let d := v - u
  let J₀ := C * Bv ^ 2
  let JΔ := Bv ^ 2 + 2 * C * Bv *
    ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))
  let K₀ := J₀ / c
  let KΔ := JΔ / c + J₀ / c ^ 2
  let J₁ := canonicalMassNumerator b₁ S₁ (u, v)
  let J₂ := canonicalMassNumerator b₂ S₂ (u, v)
  have hp : (u, v) ∈ K := ⟨hu, huv, hv⟩
  have hD : 0 ≤ D := outgoing_difference_nonneg hB hB₁ hB₂ H₁ H₂
    ⟨hu, huv.trans hv⟩
  have hd : 0 ≤ d ∧ d ≤ 1 := ⟨sub_nonneg.mpr huv, by dsimp [d]; linarith⟩
  have hd2 : d ^ 2 ≤ 1 := by nlinarith only [hd.1, hd.2]
  have hd4 : d ^ 4 ≤ d ^ 2 := by
    calc
      d ^ 4 = d ^ 2 * d ^ 2 := by ring
      _ ≤ d ^ 2 * 1 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg d)
      _ = d ^ 2 := by ring
  have hj₁ : ContinuousOn j₁ K :=
    (canonical_mass_kernels_contDiffOn hB hB₁ H₁).1.continuousOn
  have hk₁ : ContinuousOn k₁ K :=
    (canonical_mass_kernels_contDiffOn hB hB₁ H₁).2.continuousOn
  have hsource₁ : ∀ p ∈ K,
      0 ≤ j₁ p ∧ j₁ p ≤ J₀ * (p.2 - p.1) ^ 2 := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hB hB₁ hc hBv H₁
      hweight₁ hhvertical₁ hp).1
  have hkernel₁ : ∀ p ∈ K,
      0 ≤ k₁ p ∧ k₁ p ≤ K₀ * (p.2 - p.1) := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hB hB₁ hc hBv H₁
      hweight₁ hhvertical₁ hp).2
  have hkernel₂ : ∀ p ∈ K,
      0 ≤ k₂ p ∧ k₂ p ≤ K₀ * (p.2 - p.1) := by
    intro p hp
    exact (canonical_mass_kernel_value_bounds hB hB₂ hc hBv H₂
      hweight₂ hhvertical₂ hp).2
  have hJ₁raw := intervalIntegral.attenuatedVolterraIntegral_nonneg_le
    hu huv hv hj₁ hk₁ (fun p hp => (hkernel₁ p hp).1) hsource₁
  have hJ₁ : 0 ≤ J₁ ∧ J₁ ≤ J₀ * d ^ 3 / 3 := by
    rw [← canonical_mass_numerator_eq_attenuatedVolterra hB hB₁ H₁ hp]
      at hJ₁raw
    exact hJ₁raw
  have hJdiff : |J₁ - J₂| ≤ (JΔ / 3 + J₀ * KΔ / 6) * d ^ 3 * D :=
    canonical_mass_numerator_sub_le_difference hB hBwidth hB₁ hB₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
      hu huv hv
  have hjd : |j₁ (u, v) - j₂ (u, v)| ≤ JΔ * d ^ 2 * D :=
    canonical_quadratic_kernel_sub_le_difference hB hB₁ hB₂ hc hC hBv
      H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂ hu huv hv
  have hkd : |k₁ (u, v) - k₂ (u, v)| ≤ KΔ * d * D :=
    canonical_quotient_kernel_sub_le_difference hB hB₁ hB₂ hc hBv
      H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂ hu huv hv
  have hkj := hkernel₂ (u, v) hp
  have hKΔ : 0 ≤ KΔ := by dsimp [KΔ, JΔ, J₀]; positivity
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, J₀]; positivity
  have hprod : |k₁ (u, v) * J₁ - k₂ (u, v) * J₂| ≤
      (KΔ * (J₀ / 3) + K₀ * (JΔ / 3 + J₀ * KΔ / 6)) * d ^ 2 * D := by
    have hfirst : |(k₁ (u, v) - k₂ (u, v)) * J₁| ≤
        KΔ * (J₀ / 3) * d ^ 2 * D := by
      rw [abs_mul, abs_of_nonneg hJ₁.1]
      calc
        _ ≤ (KΔ * d * D) * J₁ :=
          mul_le_mul_of_nonneg_right hkd hJ₁.1
        _ ≤ (KΔ * d * D) * (J₀ * d ^ 3 / 3) :=
          mul_le_mul_of_nonneg_left hJ₁.2 (by positivity)
        _ = (KΔ * (J₀ / 3) * D) * d ^ 4 := by ring
        _ ≤ (KΔ * (J₀ / 3) * D) * d ^ 2 :=
          mul_le_mul_of_nonneg_left hd4 (by positivity)
        _ = _ := by ring
    have hsecond : |k₂ (u, v) * (J₁ - J₂)| ≤
        K₀ * (JΔ / 3 + J₀ * KΔ / 6) * d ^ 2 * D := by
      rw [abs_mul, abs_of_nonneg hkj.1]
      calc
        _ ≤ (K₀ * d) * |J₁ - J₂| :=
          mul_le_mul_of_nonneg_right hkj.2 (abs_nonneg _)
        _ ≤ (K₀ * d) * ((JΔ / 3 + J₀ * KΔ / 6) * d ^ 3 * D) :=
          mul_le_mul_of_nonneg_left hJdiff (by positivity)
        _ = (K₀ * (JΔ / 3 + J₀ * KΔ / 6) * D) * d ^ 4 := by ring
        _ ≤ (K₀ * (JΔ / 3 + J₀ * KΔ / 6) * D) * d ^ 2 :=
          mul_le_mul_of_nonneg_left hd4 (by positivity)
        _ = _ := by ring
    calc
      _ = |(k₁ (u, v) - k₂ (u, v)) * J₁ +
            k₂ (u, v) * (J₁ - J₂)| := by congr 1; ring
      _ ≤ |(k₁ (u, v) - k₂ (u, v)) * J₁| +
          |k₂ (u, v) * (J₁ - J₂)| := abs_add_le _ _
      _ ≤ _ := by nlinarith only [hfirst, hsecond]
  rw [canonical_mass_numerator_vertical_ode hB hB₁ H₁ hu huv hv,
    canonical_mass_numerator_vertical_ode hB hB₂ H₂ hu huv hv]
  have hval : |(j₁ (u, v) - k₁ (u, v) * J₁) -
      (j₂ (u, v) - k₂ (u, v) * J₂)| ≤
      |j₁ (u, v) - j₂ (u, v)| +
      |k₁ (u, v) * J₁ - k₂ (u, v) * J₂| := by
    have h := abs_add_le (j₁ (u, v) - j₂ (u, v))
      (-(k₁ (u, v) * J₁ - k₂ (u, v) * J₂))
    have heq : (j₁ (u, v) - k₁ (u, v) * J₁) -
        (j₂ (u, v) - k₂ (u, v) * J₂) =
        (j₁ (u, v) - j₂ (u, v)) -
          (k₁ (u, v) * J₁ - k₂ (u, v) * J₂) := by ring
    rw [heq]
    simpa only [sub_eq_add_neg, abs_neg] using h
  have hfinal := hval.trans (add_le_add hjd hprod)
  dsimp only [J₀, JΔ, K₀, KΔ, D, d, j₁, j₂, k₁, k₂, w₁, w₂,
    J₁, J₂] at hfinal ⊢
  nlinarith only [hfinal]

end ChristodoulouBV.C1Solution

end
