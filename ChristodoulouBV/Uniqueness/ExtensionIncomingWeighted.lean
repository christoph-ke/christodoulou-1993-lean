module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeFamily
public import ChristodoulouBV.Uniqueness.ExtensionCutoff
import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finiteness of the incoming weighted derivative supremum

The off-axis strip estimate controls values near the missing outgoing edge.
One fixed finite member controls the remaining compact portion of the ray.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming weighted values defining `D′(u₀)` are bounded above for
every nonnegative weight, using only the compatible C¹ family, initial data,
and the tail mass bound. This discharges the missing off-axis estimate in
Theorem 5.1. -/
theorem incoming_weighted_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ η δ : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀Star : u₀ < vStar) (hη : η < 1) (hδ : 0 ≤ δ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ η) :
    BddAbove (incomingWeightedAlphaPrimeValues u₀ vStar δ S) := by
  let u₁ : ℝ := (u₀ + vStar) / 2
  let vBar : ℝ := (u₁ + vStar) / 2
  have hu₀u₁ : u₀ < u₁ := by dsimp [u₁]; linarith
  have hu₁v : u₁ < vBar := by dsimp [u₁, vBar]; linarith
  have hvBarStar : vBar < vStar := by dsimp [u₁, vBar]; linarith
  have hvBar : 0 < vBar := hu₀.trans (hu₀u₁.trans hu₁v)
  obtain ⟨P, hP, hprime⟩ :=
    exists_alphaPrime_bound_on_incoming_strip hu₀ hu₀u₁ hu₁v
      hvBarStar hη hα hfamily htail
  let b₀ : ℝ := (vBar + vStar) / 2
  let B : ℝ := (vBar + b₀) / 2
  have hBarb₀ : vBar < b₀ := by dsimp [b₀]; linarith
  have hb₀Star : b₀ < vStar := by dsimp [b₀]; linarith
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨hvBar.trans hBarb₀, hb₀Star⟩
  have hBarB : vBar < B := by dsimp [B]; linarith
  have hBb₀ : B < b₀ := by dsimp [B]; linarith
  obtain ⟨M₀, _, hM₀⟩ :=
    exists_weighted_alphaPrime_bound_on_finite_member
      hvBar hBarB hBb₀ hδ (hfamily b₀ hb₀).1
  let R : ℝ := vStar / 2
  have hR : 0 < R := by dsimp [R]; linarith
  let M : ℝ := max M₀ (R ^ δ * P)
  refine ⟨M, ?_⟩
  rintro x ⟨b, hb, p, hpu, hpv, hp, rfl⟩
  have hpU : (p : ℝ × ℝ) ∈ developmentWithInitialEdge b :=
    ⟨hp.1.1.le, hp.2.1, hp.2.2⟩
  by_cases hlow : p.1.2 ≤ vBar
  · have hp₀ : (p : ℝ × ℝ) ∈ openDevelopment 0 b₀ := by
      refine ⟨⟨hp.1.1, ?_⟩, ⟨hp.2.1, ?_⟩⟩
      · exact hp.2.1.trans (hlow.trans_lt hBarb₀)
      · exact hlow.trans_lt hBarb₀
    have hfields := family_fields_eq_on_common_development hfamily hb hb₀
      ⟨hpU, ⟨hp₀.1.1.le, hp₀.2.1, hp₀.2.2⟩⟩
    have hprimeEq := family_alphaPrime_eq_on_common_development
      hfamily hb hb₀ hp hp₀
    have hbound := hM₀ (p : ℝ × ℝ) hp₀ hlow
      (alphaPrimeDomain_of_open (hfamily b₀ hb₀).1 hp₀)
    have hlowbound : (S b).r p.1.1 p.1.2 ^ δ *
        |alphaPrime (S b) p| ≤ M₀ := by
      simpa only [hfields.1, hprimeEq] using hbound
    exact hlowbound.trans (le_max_left _ _)
  · have hvBarv : vBar ≤ p.1.2 := le_of_not_ge hlow
    have hpb : p.1.2 < b := hp.2.2
    have hprimeBound : |alphaPrime (S b) p| ≤ P := by
      rw [alphaPrime_eq_deriv]
      simpa only [hpu] using hprime b hb p.1.2 hvBarv hpb
    have hrpos : 0 < (S b).r p.1.1 p.1.2 :=
      (hfamily b hb).1.solution.radius_pos (p : ℝ × ℝ) hpU
    have hrupper : (S b).r p.1.1 p.1.2 ≤ R := by
      have hv : p.1.2 ∈ Ioo (0 : ℝ) b :=
        ⟨hu₀.trans hpv.1, hpb⟩
      calc
        (S b).r p.1.1 p.1.2 ≤ (S b).r 0 p.1.2 :=
          radius_antitone_on_incoming_of_c1 (hfamily b hb).1
            (le_refl 0) (by rw [hpu]; exact hu₀.le) hp.2.1 hpb
        _ = p.1.2 / 2 := ((hfamily b hb).2 p.1.2 hv).1
        _ ≤ R := by dsimp [R]; linarith [hpv.2]
    have hrpow : (S b).r p.1.1 p.1.2 ^ δ ≤ R ^ δ :=
      Real.rpow_le_rpow hrpos.le hrupper hδ
    have hweighted : (S b).r p.1.1 p.1.2 ^ δ *
        |alphaPrime (S b) p| ≤ R ^ δ * P :=
      mul_le_mul hrpow hprimeBound (abs_nonneg _) (by positivity)
    exact hweighted.trans (le_max_right _ _)

end ChristodoulouBV.Uniqueness

end
