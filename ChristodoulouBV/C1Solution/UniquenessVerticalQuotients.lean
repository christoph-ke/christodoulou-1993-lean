module

public import ChristodoulouBV.C1Solution.UniquenessVerticalPairBox
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxJets
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsSquared
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Vertical-only two-input bounds for removable cubic quotients

The outgoing uniqueness seminorm controls the vertical jets of the cubic mass
and radius, but not the differences of their horizontal jets. This box records
precisely the data used by the vertical quotient estimates.
-/

public section

open Set

namespace intervalIntegral

/-- A single cubic-over-linear quotient has a linear outgoing jet bound
using only the outgoing jets of its numerator and radius. -/
theorem CubicRationalTriangleBox.linearQuotient_vertical_bound
    {a b c J₀ Jv Rv : ℝ} (X : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c)
    (hJ : ∀ p ∈ closedCoordTriangle a b,
      |X.J p| ≤ J₀ * (p.2 - p.1) ^ 3)
    (hJv : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ X.J (closedCoordTriangle a b) p) (0, 1)| ≤
        Jv * (p.2 - p.1) ^ 2)
    (hRv : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ X.r (closedCoordTriangle a b) p) (0, 1)| ≤ Rv) :
    ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (cubicLinearQuotient X.J X.r)
        (closedCoordTriangle a b) p) (0, 1)| ≤
        (Jv / c + J₀ * Rv / c ^ 2) * (p.2 - p.1) := by
  let K := closedCoordTriangle a b
  have hA := (X.squaredQuotient_hasJet hab hc).1
  have hμ := contDiffOn_cubicLinearQuotient hA X.r_c1 hc
    X.ρ_lower X.r_factor
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ (cubicLinearQuotient X.J X.r) K q) (0, 1)|) K :=
    ((hμ.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).abs
  have hboundcont : ContinuousOn
      (fun q : ℝ × ℝ => (Jv / c + J₀ * Rv / c ^ 2) * (q.2 - q.1)) K := by
    fun_prop
  intro p hp
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr : c * (q.2 - q.1) ≤ X.r q := by
    rw [X.r_factor q hqK]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (X.ρ_lower q hqK) hd.le
  have hscalar := abs_quotientJet_le_of_cubic_gap_bounds
    hc hd hr (hJ q hqK) (hJv q hqK) (hRv q hqK)
  rw [X.linearQuotient_jet_interior hc hq]
  simp only [smul_apply, smul_eq_mul, sub_apply]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

/-- A single cubic-over-square quotient has a bounded outgoing jet
using only outgoing numerator and radius jets. -/
theorem CubicRationalTriangleBox.squaredQuotient_vertical_bound
    {a b c J₀ Jv Rv : ℝ} (X : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c)
    (hJ₀ : 0 ≤ J₀) (hJv : 0 ≤ Jv) (hRv : 0 ≤ Rv)
    (hJ : ∀ p ∈ closedCoordTriangle a b,
      |X.J p| ≤ J₀ * (p.2 - p.1) ^ 3)
    (hJi : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ X.J (closedCoordTriangle a b) p) (0, 1)| ≤
        Jv * (p.2 - p.1) ^ 2)
    (hRi : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ X.r (closedCoordTriangle a b) p) (0, 1)| ≤ Rv) :
    ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (cubicSquaredQuotient X.J X.r)
        (closedCoordTriangle a b) p) (0, 1)| ≤
        Jv / c ^ 2 + 2 * J₀ * Rv / c ^ 3 := by
  let K := closedCoordTriangle a b
  have hA := (X.squaredQuotient_hasJet hab hc).1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ (cubicSquaredQuotient X.J X.r) K q) (0, 1)|) K :=
    ((hA.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).abs
  have hboundcont : ContinuousOn
      (fun _ : ℝ × ℝ => Jv / c ^ 2 + 2 * J₀ * Rv / c ^ 3) K :=
    continuousOn_const
  intro p hp
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr : c * (q.2 - q.1) ≤ X.r q := by
    rw [X.r_factor q hqK]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (X.ρ_lower q hqK) hd.le
  have hscalar := abs_squaredQuotientJet_le_of_cubic_gap_bounds
    hc hd hJ₀ hJv hRv hr (hJ q hqK) (hJi q hqK) (hRi q hqK)
  rw [X.squaredQuotient_jet_interior hc hq]
  simp only [smul_apply, smul_eq_mul, sub_apply]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

/-- Two cubic rational boxes with common value and vertical-jet estimates.
No difference of horizontal jets is assumed. -/
structure CubicRationalVerticalPairBox (a b c : ℝ) where
  /-- First structural box. -/
  first : CubicRationalTriangleBox a b c
  /-- Second structural box. -/
  second : CubicRationalTriangleBox a b c
  /-- Common cubic mass coefficient. -/
  J₀ : ℝ
  /-- Common quadratic outgoing mass-jet coefficient. -/
  Jv : ℝ
  /-- Cubic mass difference coefficient. -/
  JΔ : ℝ
  /-- Outgoing mass-jet difference coefficient. -/
  JΔv : ℝ
  /-- Common outgoing radius-jet coefficient. -/
  Rv : ℝ
  /-- Common outgoing radius-jet difference coefficient. -/
  RΔv : ℝ
  /-- Fixed-ray input distance. -/
  D : ℝ → ℝ
  /-- The moving ray distance is continuous. -/
  D_continuous : Continuous D
  /-- The moving ray distance is nonnegative on the triangle's base interval. -/
  D_nonneg : ∀ u ∈ Icc a b, 0 ≤ D u
  /-- All numeric bound coefficients are nonnegative. -/
  bounds_nonneg : 0 ≤ J₀ ∧ 0 ≤ Jv ∧ 0 ≤ JΔ ∧ 0 ≤ JΔv ∧
    0 ≤ Rv ∧ 0 ≤ RΔv
  /-- Both cubic numerators have the common value bound. -/
  J_bound : ∀ p ∈ closedCoordTriangle a b,
    |first.J p| ≤ J₀ * (p.2 - p.1) ^ 3 ∧
    |second.J p| ≤ J₀ * (p.2 - p.1) ^ 3
  /-- The outgoing first jets of both numerators have quadratic bounds. -/
  J_vertical_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ first.J (closedCoordTriangle a b) p) (0, 1)| ≤
      Jv * (p.2 - p.1) ^ 2 ∧
    |(fderivWithin ℝ second.J (closedCoordTriangle a b) p) (0, 1)| ≤
      Jv * (p.2 - p.1) ^ 2
  /-- The mass difference vanishes cubically. -/
  J_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |first.J p - second.J p| ≤ JΔ * (p.2 - p.1) ^ 3 * D p.1
  /-- The outgoing mass-jet difference vanishes quadratically. -/
  J_vertical_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ first.J (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ second.J (closedCoordTriangle a b) p) (0, 1)| ≤
        JΔv * (p.2 - p.1) ^ 2 * D p.1
  /-- The radius difference vanishes linearly. -/
  r_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |first.r p - second.r p| ≤ (p.2 - p.1) * D p.1
  /-- Both outgoing radius jets have a common value bound. -/
  r_vertical_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ first.r (closedCoordTriangle a b) p) (0, 1)| ≤ Rv ∧
    |(fderivWithin ℝ second.r (closedCoordTriangle a b) p) (0, 1)| ≤ Rv
  /-- The outgoing radius-jet difference is controlled by the ray distance. -/
  r_vertical_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ first.r (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ second.r (closedCoordTriangle a b) p) (0, 1)| ≤
        RΔv * D p.1

/-- Common outgoing jet bounds for the two removable quotients. -/
theorem CubicRationalVerticalPairBox.quotient_vertical_bounds
    {a b c : ℝ} (B : CubicRationalVerticalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      (|(fderivWithin ℝ (cubicLinearQuotient B.first.J B.first.r)
          (closedCoordTriangle a b) p) (0, 1)| ≤
            (B.Jv / c + B.J₀ * B.Rv / c ^ 2) * (p.2 - p.1) ∧
       |(fderivWithin ℝ (cubicLinearQuotient B.second.J B.second.r)
          (closedCoordTriangle a b) p) (0, 1)| ≤
            (B.Jv / c + B.J₀ * B.Rv / c ^ 2) * (p.2 - p.1)) ∧
      (|(fderivWithin ℝ (cubicSquaredQuotient B.first.J B.first.r)
          (closedCoordTriangle a b) p) (0, 1)| ≤
            B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3 ∧
       |(fderivWithin ℝ (cubicSquaredQuotient B.second.J B.second.r)
          (closedCoordTriangle a b) p) (0, 1)| ≤
            B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3) := by
  have hfirstμ := B.first.linearQuotient_vertical_bound hab hc
    (fun p hp => (B.J_bound p hp).1)
    (fun p hp => (B.J_vertical_bound p hp).1)
    (fun p hp => (B.r_vertical_bound p hp).1)
  have hsecondμ := B.second.linearQuotient_vertical_bound hab hc
    (fun p hp => (B.J_bound p hp).2)
    (fun p hp => (B.J_vertical_bound p hp).2)
    (fun p hp => (B.r_vertical_bound p hp).2)
  rcases B.bounds_nonneg with ⟨hJ₀, hJv, _, _, hRv, _⟩
  have hfirstA := B.first.squaredQuotient_vertical_bound hab hc
    hJ₀ hJv hRv
    (fun p hp => (B.J_bound p hp).1)
    (fun p hp => (B.J_vertical_bound p hp).1)
    (fun p hp => (B.r_vertical_bound p hp).1)
  have hsecondA := B.second.squaredQuotient_vertical_bound hab hc
    hJ₀ hJv hRv
    (fun p hp => (B.J_bound p hp).2)
    (fun p hp => (B.J_vertical_bound p hp).2)
    (fun p hp => (B.r_vertical_bound p hp).2)
  intro p hp
  exact ⟨⟨hfirstμ p hp, hsecondμ p hp⟩,
    ⟨hfirstA p hp, hsecondA p hp⟩⟩

/-- The cubic-over-linear value difference retains its quadratic gap
factor with only fixed-ray value inputs. -/
theorem CubicRationalVerticalPairBox.linearQuotient_value_sub_bound
    {a b c : ℝ} (B : CubicRationalVerticalPairBox a b c) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |cubicLinearQuotient B.first.J B.first.r p -
        cubicLinearQuotient B.second.J B.second.r p| ≤
          (B.JΔ / c + B.J₀ / c ^ 2) * (p.2 - p.1) ^ 2 * B.D p.1 := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · have hd : 0 < p.2 - p.1 := sub_pos.mpr hstrict
    have hr₁ : c * (p.2 - p.1) ≤ B.first.r p := by
      rw [B.first.r_factor p hp]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (B.first.ρ_lower p hp) hd.le
    have hr₂ : c * (p.2 - p.1) ≤ B.second.r p := by
      rw [B.second.r_factor p hp]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (B.second.ρ_lower p hp) hd.le
    have h := abs_div_sub_div_le_of_cubic_gap_bounds hc hd
      hr₁ hr₂ (B.r_sub_bound p hp) (B.J_bound p hp).2
      (B.J_sub_bound p hp)
    simpa only [cubicLinearQuotient, hstrict, ↓reduceIte] using h
  · simp only [cubicLinearQuotient, hstrict, ↓reduceIte, sub_self, abs_zero]
    rcases B.bounds_nonneg with ⟨hJ₀, _, hJΔ, _, _, _⟩
    have hcoef : 0 ≤ B.JΔ / c + B.J₀ / c ^ 2 := by positivity
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    exact mul_nonneg (mul_nonneg hcoef (sq_nonneg _))
      (B.D_nonneg p.1 ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2⟩)

/-- Both cubic-over-square quotient values vanish linearly at the axis. -/
theorem CubicRationalVerticalPairBox.squaredQuotient_value_bounds
    {a b c : ℝ} (B : CubicRationalVerticalPairBox a b c) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |cubicSquaredQuotient B.first.J B.first.r p| ≤
        (B.J₀ / c ^ 2) * (p.2 - p.1) ∧
      |cubicSquaredQuotient B.second.J B.second.r p| ≤
        (B.J₀ / c ^ 2) * (p.2 - p.1) := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · have hd : 0 < p.2 - p.1 := sub_pos.mpr hstrict
    have hr₁ : c * (p.2 - p.1) ≤ B.first.r p := by
      rw [B.first.r_factor p hp]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (B.first.ρ_lower p hp) hd.le
    have hr₂ : c * (p.2 - p.1) ≤ B.second.r p := by
      rw [B.second.r_factor p hp]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (B.second.ρ_lower p hp) hd.le
    have h₁ := abs_div_sq_le_of_cubic_gap_bound hc hd hr₁
      (B.J_bound p hp).1
    have h₂ := abs_div_sq_le_of_cubic_gap_bound hc hd hr₂
      (B.J_bound p hp).2
    simpa only [cubicSquaredQuotient, hstrict, ↓reduceIte] using
      And.intro h₁ h₂
  · simp only [cubicSquaredQuotient, hstrict, ↓reduceIte, abs_zero]
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hcoord.2.1
    have hJ₀ := B.bounds_nonneg.1
    exact ⟨mul_nonneg (div_nonneg hJ₀ (sq_nonneg c)) hd,
      mul_nonneg (div_nonneg hJ₀ (sq_nonneg c)) hd⟩

/-- The vertical-only box gives the cubic-over-square value difference,
including its zero value on the axis. -/
theorem CubicRationalVerticalPairBox.squaredQuotient_value_sub_bound
    {a b c : ℝ} (B : CubicRationalVerticalPairBox a b c) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |cubicSquaredQuotient B.first.J B.first.r p -
        cubicSquaredQuotient B.second.J B.second.r p| ≤
          (B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3) *
            (p.2 - p.1) * B.D p.1 := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · have hd : 0 < p.2 - p.1 := sub_pos.mpr hstrict
    have hr₁ : c * (p.2 - p.1) ≤ B.first.r p := by
      rw [B.first.r_factor p hp]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (B.first.ρ_lower p hp) hd.le
    have hr₂ : c * (p.2 - p.1) ≤ B.second.r p := by
      rw [B.second.r_factor p hp]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (B.second.ρ_lower p hp) hd.le
    have h := abs_div_sq_sub_div_sq_le_of_cubic_gap_bounds hc hd
      B.bounds_nonneg.1 B.bounds_nonneg.2.2.1
      (B.D_nonneg p.1 ⟨hp.1, hp.2.1.trans hp.2.2⟩)
      hr₁ hr₂ (B.r_sub_bound p hp) (B.J_bound p hp).2 (B.J_sub_bound p hp)
    simpa only [cubicSquaredQuotient, hstrict, ↓reduceIte] using h
  · have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
    simp only [cubicSquaredQuotient, hstrict, ↓reduceIte, sub_self, abs_zero]
    have hcoef : 0 ≤ B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3 := by
      have h₀ := B.bounds_nonneg.1
      have hΔ := B.bounds_nonneg.2.2.1
      positivity
    exact mul_nonneg (mul_nonneg hcoef hd)
      (B.D_nonneg p.1 ⟨hp.1, hp.2.1.trans hp.2.2⟩)

/-- The outgoing jet difference of the cubic-over-linear quotient needs
only outgoing numerator and radius jets. -/
theorem CubicRationalVerticalPairBox.linearQuotient_vertical_sub_bound
    {a b c : ℝ} (B : CubicRationalVerticalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (cubicLinearQuotient B.first.J B.first.r)
          (closedCoordTriangle a b) p) (0, 1) -
        (fderivWithin ℝ (cubicLinearQuotient B.second.J B.second.r)
          (closedCoordTriangle a b) p) (0, 1)| ≤
        (B.JΔv / c + B.Jv / c ^ 2 +
          B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
          2 * B.J₀ * B.Rv / c ^ 3) * (p.2 - p.1) * B.D p.1 := by
  let K := closedCoordTriangle a b
  have hA₁ := (B.first.squaredQuotient_hasJet hab hc).1
  have hA₂ := (B.second.squaredQuotient_hasJet hab hc).1
  have hμ₁ := contDiffOn_cubicLinearQuotient hA₁ B.first.r_c1 hc
    B.first.ρ_lower B.first.r_factor
  have hμ₂ := contDiffOn_cubicLinearQuotient hA₂ B.second.r_c1 hc
    B.second.ρ_lower B.second.r_factor
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont₁ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicLinearQuotient B.first.J B.first.r) K q) (0, 1)) K :=
    (hμ₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hcont₂ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicLinearQuotient B.second.J B.second.r) K q) (0, 1)) K :=
    (hμ₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ
          (cubicLinearQuotient B.first.J B.first.r) K q) (0, 1) -
        (fderivWithin ℝ
          (cubicLinearQuotient B.second.J B.second.r) K q) (0, 1)|) K :=
    (hcont₁.sub hcont₂).abs
  have hboundcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        (B.JΔv / c + B.Jv / c ^ 2 +
          B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
          2 * B.J₀ * B.Rv / c ^ 3) * (q.2 - q.1) * B.D q.1) K := by
    exact (continuousOn_const.mul
      (continuous_snd.continuousOn.sub continuous_fst.continuousOn)).mul
      ((B.D_continuous.comp continuous_fst).continuousOn)
  intro p hp
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr₁ : c * (q.2 - q.1) ≤ B.first.r q := by
    rw [B.first.r_factor q hqK]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (B.first.ρ_lower q hqK) hd.le
  have hr₂ : c * (q.2 - q.1) ≤ B.second.r q := by
    rw [B.second.r_factor q hqK]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (B.second.ρ_lower q hqK) hd.le
  rcases B.bounds_nonneg with ⟨hJ₀, hJv, hJΔ, hJΔv, hRv, hRΔv⟩
  have hD : 0 ≤ B.D q.1 :=
    B.D_nonneg q.1 ⟨hqK.1, hqK.2.1.trans hqK.2.2⟩
  have hscalar := abs_quotientJet_sub_le_of_cubic_gap_bounds
    hc hd hJ₀ hJv hJΔ hJΔv hRv hRΔv hD
    hr₁ hr₂ (B.r_sub_bound q hqK)
    (B.J_bound q hqK).2 (B.J_sub_bound q hqK)
    (B.J_vertical_bound q hqK).2 (B.J_vertical_sub_bound q hqK)
    (B.r_vertical_bound q hqK).1 (B.r_vertical_bound q hqK).2
    (B.r_vertical_sub_bound q hqK)
  rw [B.first.linearQuotient_jet_interior hc hq,
    B.second.linearQuotient_jet_interior hc hq]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

/-- The outgoing jet difference of the cubic-over-square quotient needs
no horizontal difference estimate. -/
theorem CubicRationalVerticalPairBox.squaredQuotient_vertical_sub_bound
    {a b c : ℝ} (B : CubicRationalVerticalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (cubicSquaredQuotient B.first.J B.first.r)
          (closedCoordTriangle a b) p) (0, 1) -
        (fderivWithin ℝ (cubicSquaredQuotient B.second.J B.second.r)
          (closedCoordTriangle a b) p) (0, 1)| ≤
        (B.JΔv / c ^ 2 + 2 * B.Jv / c ^ 3 +
          2 * B.JΔ * B.Rv / c ^ 3 +
          2 * B.J₀ * B.RΔv / c ^ 3 +
          6 * B.J₀ * B.Rv / c ^ 4) * B.D p.1 := by
  let K := closedCoordTriangle a b
  have hA₁ := (B.first.squaredQuotient_hasJet hab hc).1
  have hA₂ := (B.second.squaredQuotient_hasJet hab hc).1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont₁ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicSquaredQuotient B.first.J B.first.r) K q) (0, 1)) K :=
    (hA₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hcont₂ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicSquaredQuotient B.second.J B.second.r) K q) (0, 1)) K :=
    (hA₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ
          (cubicSquaredQuotient B.first.J B.first.r) K q) (0, 1) -
        (fderivWithin ℝ
          (cubicSquaredQuotient B.second.J B.second.r) K q) (0, 1)|) K :=
    (hcont₁.sub hcont₂).abs
  have hboundcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        (B.JΔv / c ^ 2 + 2 * B.Jv / c ^ 3 +
          2 * B.JΔ * B.Rv / c ^ 3 +
          2 * B.J₀ * B.RΔv / c ^ 3 +
          6 * B.J₀ * B.Rv / c ^ 4) * B.D q.1) K := by
    exact continuousOn_const.mul
      ((B.D_continuous.comp continuous_fst).continuousOn)
  intro p hp
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr₁ : c * (q.2 - q.1) ≤ B.first.r q := by
    rw [B.first.r_factor q hqK]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (B.first.ρ_lower q hqK) hd.le
  have hr₂ : c * (q.2 - q.1) ≤ B.second.r q := by
    rw [B.second.r_factor q hqK]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (B.second.ρ_lower q hqK) hd.le
  rcases B.bounds_nonneg with ⟨hJ₀, hJv, hJΔ, hJΔv, hRv, hRΔv⟩
  have hD : 0 ≤ B.D q.1 :=
    B.D_nonneg q.1 ⟨hqK.1, hqK.2.1.trans hqK.2.2⟩
  have hscalar := abs_squaredQuotientJet_sub_le_of_cubic_gap_bounds
    hc hd hJ₀ hJv hJΔ hJΔv hRv hRΔv hD
    hr₁ hr₂ (B.r_sub_bound q hqK)
    (B.J_bound q hqK).2 (B.J_sub_bound q hqK)
    (B.J_vertical_bound q hqK).2 (B.J_vertical_sub_bound q hqK)
    (B.r_vertical_bound q hqK).1 (B.r_vertical_bound q hqK).2
    (B.r_vertical_sub_bound q hqK)
  rw [B.first.squaredQuotient_jet_interior hc hq,
    B.second.squaredQuotient_jet_interior hc hq]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

end intervalIntegral

end
