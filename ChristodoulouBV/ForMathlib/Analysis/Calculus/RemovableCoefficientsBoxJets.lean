module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Closed-triangle first-jet bounds for removable quotients

The scalar quotient estimates apply on the interior, where both denominators
are nonzero. Continuity of the already-constructed first jets extends each
inequality to the diagonal and the other edges.
-/

public section

open Set

namespace intervalIntegral

/-- A continuous relative coordinate jet obeys a closed-triangle bound if
the corresponding scalar quotient-rule expression obeys it in the interior. -/
theorem CubicRationalTriangleBox.linearQuotient_jet_bound
    {a b c J₀ J₁ R₁ : ℝ}
    (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c)
    (hJ : ∀ p ∈ closedCoordTriangle a b,
      |B.J p| ≤ J₀ * (p.2 - p.1) ^ 3)
    (hJi : ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ B.J (closedCoordTriangle a b) p) e| ≤
          J₁ * (p.2 - p.1) ^ 2)
    (hRi : ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ B.r (closedCoordTriangle a b) p) e| ≤ R₁) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ (cubicLinearQuotient B.J B.r)
          (closedCoordTriangle a b) p) e| ≤
            (J₁ / c + J₀ * R₁ / c ^ 2) * (p.2 - p.1) := by
  let K := closedCoordTriangle a b
  have hA := (B.squaredQuotient_hasJet hab hc).1
  have hμ := contDiffOn_cubicLinearQuotient hA B.r_c1 hc
    B.ρ_lower B.r_factor
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  intro p hp e he
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ (cubicLinearQuotient B.J B.r) K q) e|) K :=
    ((hμ.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).abs
  have hboundcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        (J₁ / c + J₀ * R₁ / c ^ 2) * (q.2 - q.1)) K := by fun_prop
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr : c * (q.2 - q.1) ≤ B.r q := by
    rw [B.r_factor q hqK]
    calc
      c * (q.2 - q.1) = (q.2 - q.1) * c := mul_comm _ _
      _ ≤ (q.2 - q.1) * B.ρ q :=
        mul_le_mul_of_nonneg_left (B.ρ_lower q hqK) hd.le
  have hscalar := abs_quotientJet_le_of_cubic_gap_bounds hc hd hr
    (hJ q hqK) (hJi q hqK e he) (hRi q hqK e he)
  rw [B.linearQuotient_jet_interior hc hq]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

/-- The analogous closed-triangle first-jet bound for the
cubic-over-square quotient retains the factor two. -/
theorem CubicRationalTriangleBox.squaredQuotient_jet_bound
    {a b c J₀ J₁ R₁ : ℝ}
    (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c)
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁) (hR₁ : 0 ≤ R₁)
    (hJ : ∀ p ∈ closedCoordTriangle a b,
      |B.J p| ≤ J₀ * (p.2 - p.1) ^ 3)
    (hJi : ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ B.J (closedCoordTriangle a b) p) e| ≤
          J₁ * (p.2 - p.1) ^ 2)
    (hRi : ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ B.r (closedCoordTriangle a b) p) e| ≤ R₁) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ (cubicSquaredQuotient B.J B.r)
          (closedCoordTriangle a b) p) e| ≤
            J₁ / c ^ 2 + 2 * J₀ * R₁ / c ^ 3 := by
  let K := closedCoordTriangle a b
  have hA := (B.squaredQuotient_hasJet hab hc).1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  intro p hp e he
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ (cubicSquaredQuotient B.J B.r) K q) e|) K :=
    ((hA.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).abs
  have hboundcont : ContinuousOn
      (fun _ : ℝ × ℝ => J₁ / c ^ 2 + 2 * J₀ * R₁ / c ^ 3) K :=
    continuousOn_const
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr : c * (q.2 - q.1) ≤ B.r q := by
    rw [B.r_factor q hqK]
    calc
      c * (q.2 - q.1) = (q.2 - q.1) * c := mul_comm _ _
      _ ≤ (q.2 - q.1) * B.ρ q :=
        mul_le_mul_of_nonneg_left (B.ρ_lower q hqK) hd.le
  have hscalar := abs_squaredQuotientJet_le_of_cubic_gap_bounds
    hc hd hJ₀ hJ₁ hR₁ hr (hJ q hqK)
      (hJi q hqK e he) (hRi q hqK e he)
  rw [B.squaredQuotient_jet_interior hc hq]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

/-- Both coordinate jets of the two cubic-over-linear quotients have the
same first-order bound on the entire closed triangle. -/
theorem CubicRationalPairBox.linearQuotient_jet_bounds
    {a b c : ℝ} (B : CubicRationalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ (cubicLinearQuotient B.first.J B.first.r)
          (closedCoordTriangle a b) p) e| ≤
            (B.J₁ / c + B.J₀ * B.R₁ / c ^ 2) * (p.2 - p.1) ∧
        |(fderivWithin ℝ (cubicLinearQuotient B.second.J B.second.r)
          (closedCoordTriangle a b) p) e| ≤
            (B.J₁ / c + B.J₀ * B.R₁ / c ^ 2) * (p.2 - p.1) := by
  have h₁ := B.first.linearQuotient_jet_bound hab hc
    (fun p hp => by
      rw [abs_of_nonneg (B.J_bound p hp).1.1]
      exact (B.J_bound p hp).1.2)
    (fun p hp e he => (B.J_jet_bound p hp e he).1)
    (fun p hp e he => (B.r_jet_bound p hp e he).1)
  have h₂ := B.second.linearQuotient_jet_bound hab hc
    (fun p hp => by
      rw [abs_of_nonneg (B.J_bound p hp).2.1]
      exact (B.J_bound p hp).2.2)
    (fun p hp e he => (B.J_jet_bound p hp e he).2)
    (fun p hp e he => (B.r_jet_bound p hp e he).2)
  exact fun p hp e he => ⟨h₁ p hp e he, h₂ p hp e he⟩

/-- Both coordinate jets of the cubic-over-square quotients have a common
uniform bound, including on the axis. -/
theorem CubicRationalPairBox.squaredQuotient_jet_bounds
    {a b c : ℝ} (B : CubicRationalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ (cubicSquaredQuotient B.first.J B.first.r)
          (closedCoordTriangle a b) p) e| ≤
            B.J₁ / c ^ 2 + 2 * B.J₀ * B.R₁ / c ^ 3 ∧
        |(fderivWithin ℝ (cubicSquaredQuotient B.second.J B.second.r)
          (closedCoordTriangle a b) p) e| ≤
            B.J₁ / c ^ 2 + 2 * B.J₀ * B.R₁ / c ^ 3 := by
  have h₁ := B.first.squaredQuotient_jet_bound hab hc
    B.J₀_nonneg B.J₁_nonneg B.R₁_nonneg
    (fun p hp => by
      rw [abs_of_nonneg (B.J_bound p hp).1.1]
      exact (B.J_bound p hp).1.2)
    (fun p hp e he => (B.J_jet_bound p hp e he).1)
    (fun p hp e he => (B.r_jet_bound p hp e he).1)
  have h₂ := B.second.squaredQuotient_jet_bound hab hc
    B.J₀_nonneg B.J₁_nonneg B.R₁_nonneg
    (fun p hp => by
      rw [abs_of_nonneg (B.J_bound p hp).2.1]
      exact (B.J_bound p hp).2.2)
    (fun p hp e he => (B.J_jet_bound p hp e he).2)
    (fun p hp e he => (B.r_jet_bound p hp e he).2)
  exact fun p hp e he => ⟨h₁ p hp e he, h₂ p hp e he⟩

/-- The two-input coordinate-jet difference of the cubic-over-linear
quotient has the five-term quotient-rule coefficient on the closed
triangle. -/
theorem CubicRationalPairBox.linearQuotient_jet_sub_bound
    {a b c : ℝ} (B : CubicRationalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ (cubicLinearQuotient B.first.J B.first.r)
            (closedCoordTriangle a b) p) e -
          (fderivWithin ℝ (cubicLinearQuotient B.second.J B.second.r)
            (closedCoordTriangle a b) p) e| ≤
          (B.JΔ₁ / c + B.J₁ / c ^ 2 +
            B.JΔ₀ * B.R₁ / c ^ 2 + B.J₀ * B.RΔ / c ^ 2 +
            2 * B.J₀ * B.R₁ / c ^ 3) * (p.2 - p.1) * B.D := by
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
  intro p hp e he
  have hcont₁ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicLinearQuotient B.first.J B.first.r) K q) e) K :=
    (hμ₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hcont₂ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicLinearQuotient B.second.J B.second.r) K q) e) K :=
    (hμ₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ
          (cubicLinearQuotient B.first.J B.first.r) K q) e -
        (fderivWithin ℝ
          (cubicLinearQuotient B.second.J B.second.r) K q) e|) K :=
    (hcont₁.sub hcont₂).abs
  have hboundcont : ContinuousOn
      (fun q : ℝ × ℝ =>
        (B.JΔ₁ / c + B.J₁ / c ^ 2 +
          B.JΔ₀ * B.R₁ / c ^ 2 + B.J₀ * B.RΔ / c ^ 2 +
          2 * B.J₀ * B.R₁ / c ^ 3) * (q.2 - q.1) * B.D) K := by fun_prop
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr₁ : c * (q.2 - q.1) ≤ B.first.r q := by
    rw [B.first.r_factor q hqK]
    calc
      c * (q.2 - q.1) = (q.2 - q.1) * c := mul_comm _ _
      _ ≤ (q.2 - q.1) * B.first.ρ q :=
        mul_le_mul_of_nonneg_left (B.first.ρ_lower q hqK) hd.le
  have hr₂ : c * (q.2 - q.1) ≤ B.second.r q := by
    rw [B.second.r_factor q hqK]
    calc
      c * (q.2 - q.1) = (q.2 - q.1) * c := mul_comm _ _
      _ ≤ (q.2 - q.1) * B.second.ρ q :=
        mul_le_mul_of_nonneg_left (B.second.ρ_lower q hqK) hd.le
  have hJ₂ : |B.second.J q| ≤ B.J₀ * (q.2 - q.1) ^ 3 := by
    rw [abs_of_nonneg (B.J_bound q hqK).2.1]
    exact (B.J_bound q hqK).2.2
  have hscalar := abs_quotientJet_sub_le_of_cubic_gap_bounds
    hc hd B.J₀_nonneg B.J₁_nonneg B.JΔ₀_nonneg B.JΔ₁_nonneg
    B.R₁_nonneg B.RΔ_nonneg B.D_nonneg
    hr₁ hr₂ (B.r_sub_bound q hqK)
    hJ₂ (B.J_sub_bound q hqK)
    (B.J_jet_bound q hqK e he).2
    (B.J_jet_sub_bound q hqK e he)
    (B.r_jet_bound q hqK e he).1
    (B.r_jet_bound q hqK e he).2
    (B.r_jet_sub_bound q hqK e he)
  rw [B.first.linearQuotient_jet_interior hc hq,
    B.second.linearQuotient_jet_interior hc hq]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

/-- The two-input coordinate-jet difference of the cubic-over-square
quotient has the derivative coefficient with factors two and six. -/
theorem CubicRationalPairBox.squaredQuotient_jet_sub_bound
    {a b c : ℝ} (B : CubicRationalPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |(fderivWithin ℝ (cubicSquaredQuotient B.first.J B.first.r)
            (closedCoordTriangle a b) p) e -
          (fderivWithin ℝ (cubicSquaredQuotient B.second.J B.second.r)
            (closedCoordTriangle a b) p) e| ≤
          (B.JΔ₁ / c ^ 2 + 2 * B.J₁ / c ^ 3 +
            2 * B.JΔ₀ * B.R₁ / c ^ 3 +
            2 * B.J₀ * B.RΔ / c ^ 3 +
            6 * B.J₀ * B.R₁ / c ^ 4) * B.D := by
  let K := closedCoordTriangle a b
  have hA₁ := (B.first.squaredQuotient_hasJet hab hc).1
  have hA₂ := (B.second.squaredQuotient_hasJet hab hc).1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  intro p hp e he
  have hcont₁ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicSquaredQuotient B.first.J B.first.r) K q) e) K :=
    (hA₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hcont₂ : ContinuousOn
      (fun q => (fderivWithin ℝ
        (cubicSquaredQuotient B.second.J B.second.r) K q) e) K :=
    (hA₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hjetcont : ContinuousOn
      (fun q => |(fderivWithin ℝ
          (cubicSquaredQuotient B.first.J B.first.r) K q) e -
        (fderivWithin ℝ
          (cubicSquaredQuotient B.second.J B.second.r) K q) e|) K :=
    (hcont₁.sub hcont₂).abs
  have hboundcont : ContinuousOn
      (fun _ : ℝ × ℝ =>
        (B.JΔ₁ / c ^ 2 + 2 * B.J₁ / c ^ 3 +
          2 * B.JΔ₀ * B.R₁ / c ^ 3 +
          2 * B.J₀ * B.RΔ / c ^ 3 +
          6 * B.J₀ * B.R₁ / c ^ 4) * B.D) K := continuousOn_const
  refine (le_on_closedCoordTriangle_of_interior hab hjetcont hboundcont ?_) p hp
  intro q hq
  have hqK : q ∈ K := interior_subset hq
  have hq' : q ∈ openCoordTriangle a b := by
    simpa only [K, interior_closedCoordTriangle] using hq
  have hd : 0 < q.2 - q.1 := sub_pos.mpr hq'.2.1
  have hr₁ : c * (q.2 - q.1) ≤ B.first.r q := by
    rw [B.first.r_factor q hqK]
    calc
      c * (q.2 - q.1) = (q.2 - q.1) * c := mul_comm _ _
      _ ≤ (q.2 - q.1) * B.first.ρ q :=
        mul_le_mul_of_nonneg_left (B.first.ρ_lower q hqK) hd.le
  have hr₂ : c * (q.2 - q.1) ≤ B.second.r q := by
    rw [B.second.r_factor q hqK]
    calc
      c * (q.2 - q.1) = (q.2 - q.1) * c := mul_comm _ _
      _ ≤ (q.2 - q.1) * B.second.ρ q :=
        mul_le_mul_of_nonneg_left (B.second.ρ_lower q hqK) hd.le
  have hJ₂ : |B.second.J q| ≤ B.J₀ * (q.2 - q.1) ^ 3 := by
    rw [abs_of_nonneg (B.J_bound q hqK).2.1]
    exact (B.J_bound q hqK).2.2
  have hscalar := abs_squaredQuotientJet_sub_le_of_cubic_gap_bounds
    hc hd B.J₀_nonneg B.J₁_nonneg B.JΔ₀_nonneg B.JΔ₁_nonneg
    B.R₁_nonneg B.RΔ_nonneg B.D_nonneg
    hr₁ hr₂ (B.r_sub_bound q hqK)
    hJ₂ (B.J_sub_bound q hqK)
    (B.J_jet_bound q hqK e he).2
    (B.J_jet_sub_bound q hqK e he)
    (B.r_jet_bound q hqK e he).1
    (B.r_jet_bound q hqK e he).2
    (B.r_jet_sub_bound q hqK e he)
  rw [B.first.squaredQuotient_jet_interior hc hq,
    B.second.squaredQuotient_jet_interior hc hq]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  convert hscalar using 1
  · congr 1
    simp only [div_eq_mul_inv]
    ring

end intervalIntegral

end
