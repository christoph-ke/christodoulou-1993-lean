module

public import ChristodoulouBV.Existence.C1ContinuationTail
public import ChristodoulouBV.Existence.C1ContinuationMass
import Mathlib.Tactic

/-!
# Uniform corner smallness for the finite C¹ family

The mass ratio tends uniformly to zero at a finite terminal corner.
Consequently the family satisfies the tail premise of Theorem 5.1 for
any positive threshold, without knowing the threshold's numerical value.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The patched mass ratio is nonnegative and is controlled by outgoing
quotient variation, with the original datum's variation as coefficient. -/
theorem endpointPatch_mass_ratio_le_variation
    {alpha₀ : ℝ → ℝ} {vStar : ℝ}
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) vStar) (hv : v ∈ Ioo u vStar) :
    let P := endpointPatch family vStar
    0 ≤ 2 * P.m u v / P.r u v ∧
      ENNReal.ofReal (2 * P.m u v / P.r u v) ≤
        ENNReal.ofReal (15 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) *
          eVariationOn (fun t => P.alpha u t / P.lam u t) (Ioo u vStar) := by
  let P := endpointPatch family vStar
  obtain ⟨a, hva, haStar⟩ := exists_between hv.2
  obtain ⟨b, hab, hbStar⟩ := exists_between haStar
  obtain ⟨B, haB, hBb⟩ := exists_between hab
  have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hu.1.trans (hv.1.trans (hva.trans hab)), hbStar⟩
  obtain ⟨HS, hdata⟩ := hfamily b hb
  have h := s6_finite_cutoff_mass_ratio_le_variation
    (hu.1.trans (hv.1.trans (hva.trans haB))) hBb HS hdata hD
    (hu.1.trans (hv.1.trans hva)) haB ⟨hu.1, hv.1.trans hva⟩ ⟨hv.1, hva⟩
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.1.le, hv.1, hva.trans hab⟩
  have hpoint := endpointPatch_agrees hfamily hb hp
  have hratio : 2 * P.m u v / P.r u v =
      2 * (family b).m u v / (family b).r u v :=
    congrArg₂ (fun m r : ℝ => 2 * m / r) hpoint.2.2.1 hpoint.1
  have hq : EqOn (fun t => P.alpha u t / P.lam u t)
      (fun t => (family b).alpha u t / (family b).lam u t) (Ioo u a) := by
    intro t ht
    have htval := endpointPatch_agrees hfamily hb
      (show (u, t) ∈ developmentWithInitialEdge b from ⟨hu.1.le, ht.1, ht.2.trans hab⟩)
    exact congrArg₂ (· / ·) htval.2.2.2.2.2.1 htval.2.2.2.1
  rw [← hratio, ← eVariationOn.congr hq] at h
  constructor
  · rw [hratio]
    exact ((IsC1Solution.isBVSolution_development hb.1 HS).mass_ratio_bounds hp).1
  · exact h.trans (mul_le_mul_of_nonneg_left
      (eVariationOn.mono _ (Ioo_subset_Ioo_right haStar.le)) bot_le)

/-- The terminal-corner mass ratio is uniformly smaller than any prescribed
positive threshold. -/
theorem s6_corner_mu
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u₀ ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar,
        2 * (endpointPatch family vStar).m p.1 p.2 /
          (endpointPatch family vStar).r p.1 p.2 ≤ ε := by
  let P := endpointPatch family vStar
  let M := ENNReal.ofReal (15 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)
  have hlim : Tendsto (fun u => M * eVariationOn
      (fun v => P.alpha u v / P.lam u v) (Ioo u vStar))
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (eq6_3 hStar hD hfamily).1 (Or.inr ENNReal.ofReal_ne_top)
  have hevent : ∀ᶠ u in 𝓝[<] vStar,
      M * eVariationOn (fun v => P.alpha u v / P.lam u v) (Ioo u vStar) ≤
        ENNReal.ofReal ε :=
    ENNReal.tendsto_nhds_zero.mp hlim _ (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨w, hw, hbound⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hevent
  let u₀ := max (vStar / 2) w
  have hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨(half_pos hStar).trans_le (le_max_left _ _),
      max_lt (half_lt_self hStar) hw⟩
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp
  have hu : p.1 ∈ Ioo (0 : ℝ) vStar := ⟨hu₀.1.trans hp.1.1, hp.1.2⟩
  obtain ⟨hμnonneg, hμ⟩ := endpointPatch_mass_ratio_le_variation hD hfamily hu hp.2
  have hsmall := hμ.trans (hbound ⟨(le_max_right _ _).trans_lt hp.1.1, hp.1.2⟩)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
  simpa only [ENNReal.toReal_ofReal hμnonneg, ENNReal.toReal_ofReal hε.le] using hreal

/-- A single tail bound works for every family member and every positive
threshold. This is the exact mass-bound carrier required by frozen
Theorem 5.1, with no numerical knowledge of its existential threshold. -/
theorem eta_for_family
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u₀ ∈ Ioo (0 : ℝ) vStar, ∃ η : ℝ, η < ε ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
          2 * (family b).m p.1 p.2 / (family b).r p.1 p.2 ≤ η := by
  obtain ⟨u₀, hu₀, hbound⟩ := s6_corner_mu hStar hD hfamily (half_pos hε)
  refine ⟨u₀, hu₀, ε / 2, half_lt_self hε, ?_⟩
  intro b hb p hp
  have hpoint := endpointPatch_agrees hfamily hb hp.2
  have hratio : 2 * (endpointPatch family vStar).m p.1 p.2 /
      (endpointPatch family vStar).r p.1 p.2 =
        2 * (family b).m p.1 p.2 / (family b).r p.1 p.2 :=
    congrArg₂ (fun m r : ℝ => 2 * m / r) hpoint.2.2.1 hpoint.1
  exact hratio ▸ hbound p hp.1

end ChristodoulouBV

end
