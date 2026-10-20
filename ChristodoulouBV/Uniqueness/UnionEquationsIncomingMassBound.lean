module

public import ChristodoulouBV.Uniqueness.UnionEquationsOutgoing
import ChristodoulouBV.BVSolution.PrelocalFieldBounds

/-!
# Uniform mass density bound below a mixed incoming terminal segment

The beta transport estimate, source variation bounds, and negative incoming
expansion bound control the quadratic incoming mass density.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- An elementary bound for the incoming mass density away from zero
incoming expansion. -/
theorem abs_mass_in_density_le
    {μ ζ ν c Z : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hc : 0 < c) (hν : ν ≤ -c) (hZ : 0 ≤ Z) (hζ : |ζ| ≤ Z) :
    |(1 - μ) * ζ ^ 2 / (2 * ν)| ≤ Z ^ 2 / (2 * c) := by
  have hgap0 : 0 ≤ 1 - μ := by linarith
  have hgap1 : 1 - μ ≤ 1 := by linarith
  have hνneg : ν < 0 := by linarith
  have hνabs : c ≤ |ν| := by rw [abs_of_neg hνneg]; linarith
  have hden : 0 < 2 * |ν| := by
    have : 0 < |ν| := abs_pos.mpr (ne_of_lt hνneg)
    positivity
  have hden0 : 0 < 2 * c := by positivity
  have hsq : ζ ^ 2 ≤ Z ^ 2 := by
    rw [← sq_abs ζ]
    exact (sq_le_sq₀ (abs_nonneg ζ) hZ).2 hζ
  have hnum : (1 - μ) * ζ ^ 2 ≤ Z ^ 2 := by
    calc
      (1 - μ) * ζ ^ 2 ≤ 1 * ζ ^ 2 :=
        mul_le_mul_of_nonneg_right hgap1 (sq_nonneg ζ)
      _ = ζ ^ 2 := one_mul _
      _ ≤ Z ^ 2 := hsq
  have hprod : ((1 - μ) * ζ ^ 2) * (2 * c) ≤
      Z ^ 2 * (2 * |ν|) := by
    calc
      ((1 - μ) * ζ ^ 2) * (2 * c) ≤ Z ^ 2 * (2 * c) :=
        mul_le_mul_of_nonneg_right hnum hden0.le
      _ ≤ Z ^ 2 * (2 * |ν|) :=
        mul_le_mul_of_nonneg_left (by gcongr) (sq_nonneg Z)
  rw [abs_div, abs_mul, abs_of_nonneg hgap0,
    abs_of_nonneg (sq_nonneg ζ), abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (div_le_div_iff₀ hden hden0).2 hprod

/-- The first source's incoming mass density has one constant bound on the
whole segment at all sufficiently high lower outgoing levels. -/
theorem first_source_mass_in_density_uniform_below_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b,
        |(1 - 2 * S₁.m s t / S₁.r s t) * (S₁.zeta s t) ^ 2 /
          (2 * S₁.nu s t)| ≤ C := by
  obtain ⟨g, _hgInt, ⟨Bβ, hBβ, hgBound⟩, hbetaEv⟩ :=
    first_source_beta_dominated_below_mixed_top h₁ h₂ hdata hab hseg hb
  obtain ⟨N, hN⟩ := h₁.nu_bounded_below
  obtain ⟨c, hc, hlow⟩ := h₁.lam_bounded_below
  have hb0 : 0 ≤ b := (h₁.solution.development.wedge hb).1
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  let w := (b + v) / 2
  have hbw : b < w := by dsimp [w]; linarith only [hbv]
  have hwv : w < v := by dsimp [w]; linarith only [hbv]
  have h0w : (0, w) ∈ U₁ :=
    h₁.solution.development.past_mem hb le_rfl hb0
      (lt_of_le_of_lt hb0 hbw) hwv
  let Bφ := |S₁.phi 0 w| + 2 * max h₁.item3_variation.choose 0
  have hBφ : 0 ≤ Bφ := by dsimp [Bφ]; positivity
  have hN0 : 0 ≤ N := by
    have hn := h₁.nu_le_neg_lower hc hlow hb
    have hN' := hN (b, v) hb
    linarith
  let Z := Bβ + N * Bφ
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let C := Z ^ 2 / (2 * c)
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) (by positivity)
  have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have ha0 : 0 ≤ a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbetaEv, Ioo_mem_nhdsLT hwv] with t hbeta ht s hs
  have hstrip : inSeg t a b ⊆ U₁ :=
    h₁.solution.development.in_seg_subset hb ha0 hab le_rfl
      (hbw.trans ht.1) ht.2
  have hsU : (s, t) ∈ U₁ := hstrip (by
    change s ∈ Icc a b ∧ t ∈ ({t} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hφ : |S₁.phi s t| ≤ Bφ := h₁.phi_abs_le_reference_variation h0w hsU
  have hν : |S₁.nu s t| ≤ N := by
    have hn := h₁.nu_le_neg_lower hc hlow hsU
    rw [abs_of_neg (by linarith : S₁.nu s t < 0)]
    exact hN (s, t) hsU
  have hβ : |S₁.beta s t| ≤ Bβ := (hbeta s hs).trans (hgBound s hs)
  have hζ : |S₁.zeta s t| ≤ Z := by
    rw [Fields.zeta]
    calc
      |S₁.beta s t - S₁.nu s t * S₁.phi s t| ≤
        |S₁.beta s t| + |S₁.nu s t * S₁.phi s t| := abs_sub _ _
      _ ≤ Bβ + N * Bφ := by
        rw [abs_mul]
        exact add_le_add hβ (mul_le_mul hν hφ (abs_nonneg _) hN0)
  have hμ := h₁.mass_ratio_bounds hsU
  have hn := h₁.nu_le_neg_lower hc hlow hsU
  exact abs_mass_in_density_le hμ.1 hμ.2.le hc hn hZ hζ

end ChristodoulouBV.Uniqueness

end
