module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesGap
public import ChristodoulouBV.Uniqueness.UnionRepresentativesLimits
import ChristodoulouBV.BVSolution.PrelocalFieldBounds

/-!
# Uniform incoming transport bounds below a mixed terminal segment

The mass gap estimate and the BV bounds on the two expansions make the
incoming mixed coefficient uniformly bounded on the compact segment near its
terminal outgoing level.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A nonsingular rational transport coefficient is bounded by bounds on its
five factors. -/
theorem abs_mixed_coefficient_le
    {μ ell ν g r K N d R : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hlam0 : 0 ≤ ell) (hlam : ell ≤ K) (hnu : |ν| ≤ N)
    (hd : 0 < d) (hg : d ≤ g) (hR : 0 < R) (hr : R ≤ r) :
    |μ * ell * ν / (g * r)| ≤ K * N / (d * R) := by
  have hK : 0 ≤ K := hlam0.trans hlam
  have hN : 0 ≤ N := (abs_nonneg ν).trans hnu
  have hgpos : 0 < g := hd.trans_le hg
  have hrpos : 0 < r := hR.trans_le hr
  have hden : 0 < g * r := mul_pos hgpos hrpos
  have hden0 : 0 < d * R := mul_pos hd hR
  have hmulLam : μ * ell ≤ K := by
    calc
      μ * ell ≤ 1 * ell := mul_le_mul_of_nonneg_right hμ1 hlam0
      _ = ell := one_mul ell
      _ ≤ K := hlam
  have hnum : μ * ell * |ν| ≤ K * N := by
    calc
      μ * ell * |ν| ≤ K * |ν| :=
        mul_le_mul_of_nonneg_right hmulLam (abs_nonneg _)
      _ ≤ K * N := mul_le_mul_of_nonneg_left hnu hK
  have hdenle : d * R ≤ g * r := by
    calc
      d * R ≤ g * R := mul_le_mul_of_nonneg_right hg hR.le
      _ ≤ g * r := mul_le_mul_of_nonneg_left hr hgpos.le
  have hprod : (μ * ell * |ν|) * (d * R) ≤ (K * N) * (g * r) := by
    calc
      (μ * ell * |ν|) * (d * R) ≤ (K * N) * (d * R) :=
        mul_le_mul_of_nonneg_right hnum hden0.le
      _ ≤ (K * N) * (g * r) :=
        mul_le_mul_of_nonneg_left hdenle (mul_nonneg hK hN)
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hμ0,
    abs_of_nonneg hlam0, abs_of_pos hden]
  exact (div_le_div_iff₀ hden hden0).2 hprod

/-- Both incoming transport integrands of the first source have one finite
uniform bound on a strip below a mixed terminal segment. -/
theorem first_source_incoming_coefficients_uniform_below_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t in 𝓝[<] v,
        b < t ∧ ∀ s ∈ Icc a b,
          |IsBVSolution.radiusCoeff S₁ s t| ≤ C ∧
          |IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t| ≤ C := by
  obtain ⟨d, hd, hgap⟩ :=
    first_source_mass_gap_uniform_below_top h₁ h₂ hdata hab hseg hb
  obtain ⟨c, hc, hlow⟩ := h₁.lam_bounded_below
  obtain ⟨K, hupper, _⟩ := h₁.exists_uniform_radius_upper
  obtain ⟨N, hnuUpper⟩ := h₁.nu_bounded_below
  have hb0 : 0 ≤ b := (h₁.solution.development.wedge hb).1
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  let w := (b + v) / 2
  have hbw : b < w := by dsimp [w]; linarith only [hbv]
  have hwv : w < v := by dsimp [w]; linarith only [hbv]
  have h0w : (0, w) ∈ U₁ :=
    h₁.solution.development.past_mem hb le_rfl hb0
      (lt_of_le_of_lt hb0 hbw) hwv
  let B := |S₁.phi 0 w| + 2 * max h₁.item3_variation.choose 0
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let R := c * (v - b) / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : 0 ≤ K := by
    have hcp := hlow (b, v) hb
    have hKp := hupper (b, v) hb
    linarith
  have hN : 0 ≤ N := by
    have hnp := hnuUpper (b, v) hb
    have hnneg := h₁.nu_le_neg_lower hc hlow hb
    linarith
  let C₀ := K * N / (d * R)
  have hC₀ : 0 ≤ C₀ := div_nonneg (mul_nonneg hK hN)
    (mul_pos hd hR).le
  let C := C₀ * max B 1
  have hC : 0 ≤ C :=
    mul_nonneg hC₀ ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _))
  have ha0 : 0 ≤ a := by
    have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
      change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨⟨le_rfl, hab⟩, rfl⟩)
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgap, Ioo_mem_nhdsLT hwv] with t ht htw
  have hstrip : inSeg t a b ⊆ U₁ :=
    h₁.solution.development.in_seg_subset hb ha0 hab le_rfl ht.1 htw.2
  refine ⟨ht.1, ?_⟩
  intro s hs
  have hsU : (s, t) ∈ U₁ := hstrip (by
    change s ∈ Icc a b ∧ t ∈ ({t} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hμ := h₁.mass_ratio_bounds hsU
  have hlam := hupper (s, t) hsU
  have hlam0 := (h₁.solution.lam_pos (s, t) hsU).le
  have hνneg := h₁.nu_le_neg_lower hc hlow hsU
  have hν : |S₁.nu s t| ≤ N := by
    rw [abs_of_nonpos (by linarith : S₁.nu s t ≤ 0)]
    exact hnuUpper (s, t) hsU
  have hr : R ≤ S₁.r s t := by
    have hrad := h₁.radius_lower hlow hsU
    have hst : s ≤ b := hs.2
    have htw' : w < t := htw.1
    dsimp [w] at htw'
    have hdist : (v - b) / 2 ≤ t - s := by
      linarith only [htw', hst]
    have hmul := mul_le_mul_of_nonneg_left hdist hc.le
    dsimp [R]
    nlinarith only [hrad, hmul]
  have hcoeff : |IsBVSolution.radiusCoeff S₁ s t| ≤ C₀ := by
    unfold IsBVSolution.radiusCoeff
    exact abs_mixed_coefficient_le hμ.1 hμ.2.le hlam0 hlam hν hd
      (ht.2 s hs) hR hr
  have hφ : |S₁.phi s t| ≤ B := h₁.phi_abs_le_reference_variation h0w hsU
  have hcoeffC : |IsBVSolution.radiusCoeff S₁ s t| ≤ C := by
    calc
      |IsBVSolution.radiusCoeff S₁ s t| ≤ C₀ := hcoeff
      _ = C₀ * 1 := (mul_one C₀).symm
      _ ≤ C := mul_le_mul_of_nonneg_left (le_max_right B 1) hC₀
  have hphiC : |IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t| ≤ C := by
    rw [abs_mul]
    calc
      |IsBVSolution.radiusCoeff S₁ s t| * |S₁.phi s t| ≤ C₀ * B :=
        mul_le_mul hcoeff hφ (abs_nonneg _) hC₀
      _ ≤ C := mul_le_mul_of_nonneg_left (le_max_left B 1) hC₀
  exact ⟨hcoeffC, hphiC⟩

end ChristodoulouBV.Uniqueness

end
