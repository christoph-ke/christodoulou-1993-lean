module

public import ChristodoulouBV.Existence.C1ContinuationCorner
public import ChristodoulouBV.Existence.C1ContinuationAgreement
public import ChristodoulouBV.Frozen.Theorem5_1
import Mathlib.Tactic

/-!
# Continuation of the small-variation C¹ family

The uniform corner limit supplies the tail premise for the positive
threshold obtained from sealed Theorem 5.1. Sealed Theorem 3.1 and C¹
field recovery identify the resulting larger solution with every old
finite member. Hence the maximal existence parameter is infinite.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- Sealed Theorem 5.1 produces a larger finite development. Its numerical
threshold is never used: `eta_for_family` works for every positive threshold. -/
theorem s6_t51_new
    {alpha₀ : ℝ → ℝ} (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v) :
    ∃ v₁ : ℝ, vStar < v₁ ∧ ∃ T : Fields,
      IsC1Solution (developmentWithInitialEdge v₁) T ∧
      ∀ v ∈ Ioo (0 : ℝ) v₁, T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v := by
  obtain ⟨ε₁, hε₁, hcontinue⟩ := ChristodoulouBV.theorem5_1
  exact hcontinue alpha₀ vStar hStar hα family hfamily
    (eta_for_family hStar hD hfamily hε₁)

/-- A small-variation finite C¹ family extends beyond its terminal parameter
and agrees with the new solution in all fields on every old development,
including the initial edge. -/
theorem continue_c1_family
    {alpha₀ : ℝ → ℝ} (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v) :
    ∃ v₁ : ℝ, vStar < v₁ ∧ ∃ T : Fields,
      IsC1Solution (developmentWithInitialEdge v₁) T ∧
      (∀ v ∈ Ioo (0 : ℝ) v₁, T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar, ∀ p ∈ developmentWithInitialEdge b,
        T.r p.1 p.2 = (family b).r p.1 p.2 ∧
        T.phi p.1 p.2 = (family b).phi p.1 p.2 ∧
        T.m p.1 p.2 = (family b).m p.1 p.2 ∧
        T.lam p.1 p.2 = (family b).lam p.1 p.2 ∧
        T.nu p.1 p.2 = (family b).nu p.1 p.2 ∧
        T.alpha p.1 p.2 = (family b).alpha p.1 p.2 ∧
        T.beta p.1 p.2 = (family b).beta p.1 p.2 ∧
        T.theta p.1 p.2 = (family b).theta p.1 p.2 ∧
        T.zeta p.1 p.2 = (family b).zeta p.1 p.2 := by
  obtain ⟨v₁, hv₁, T, HT, hdataT⟩ := s6_t51_new hα hStar hD hfamily
  refine ⟨v₁, hv₁, T, HT, hdataT, ?_⟩
  intro b hb p hp
  exact s6_continue_agreement HT (hfamily b hb).1 hdataT (hfamily b hb).2
    ⟨hp.1, hp.2.1, hp.2.2.trans (hb.2.trans hv₁)⟩ hp

/-- The maximal C¹ existence parameter for small smooth data is infinite:
a finite parameter would have the strictly larger development supplied by
`continue_c1_family`. The smallness constant is the fixed bootstrap threshold. -/
theorem c1MaximalParameter_eq_top_of_small_variation
    (alpha₀ : ℝ → ℝ) (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    c1MaximalParameter alpha₀ = ∞ := by
  by_contra hfinite
  let vStar := (c1MaximalParameter alpha₀).toReal
  have hStar : ENNReal.ofReal vStar = c1MaximalParameter alpha₀ :=
    ENNReal.ofReal_toReal hfinite
  obtain ⟨hpos, family, hfamily⟩ := endpoint_family alpha₀ hα hD hStar
  have hfamily' : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v :=
    fun b hb => ⟨(hfamily b hb).1, (hfamily b hb).2.1⟩
  obtain ⟨v₁, hv₁, T, HT, hdataT, _⟩ := continue_c1_family hα hpos hD hfamily'
  have hdev : C1InitialDevelopment alpha₀ v₁ := ⟨hpos.trans hv₁, T, HT, hdataT⟩
  have hle : ENNReal.ofReal v₁ ≤ c1MaximalParameter alpha₀ :=
    le_sSup ⟨v₁, hdev, rfl⟩
  have hlt : c1MaximalParameter alpha₀ < ENNReal.ofReal v₁ := by
    rw [← hStar]
    exact (ENNReal.ofReal_lt_ofReal_iff (hpos.trans hv₁)).mpr hv₁
  exact (not_lt_of_ge hle) hlt

end ChristodoulouBV

end
