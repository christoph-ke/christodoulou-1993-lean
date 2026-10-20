module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyGap
import ChristodoulouBV.Uniqueness.UnionRepresentativesGap
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# A uniform quotient ceiling on the incoming strip

The positive quotient `λ/(1-2m/r)` decreases along incoming rays. The
initial-edge ceiling therefore applies to every member of the compatible
family, uniformly before the missing outgoing endpoint.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The initial-edge quotient ceiling persists through
each member of the incoming strip, independently of its cutoff. -/
theorem exists_quotient_ceiling_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 ≤ u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₁ → vBar ≤ v → v < b →
          (S b).lam u v /
            (1 - 2 * (S b).m u v / (S b).r u v) ≤ K := by
  obtain ⟨K, hK, hinitial⟩ :=
    exists_initial_quotient_ceiling_before_star
      (hu₁.trans_lt hu₁v) hvBarStar hα hfamily
  refine ⟨K, hK, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  let H := (hfamily b hb).1
  have hseg : inSeg v 0 u ⊆ developmentWithInitialEdge b := by
    intro p hp
    have hp' : p.1 ∈ Icc 0 u ∧ p.2 = v := by
      simpa [inSeg] using hp
    rcases hp' with ⟨hp', hpv⟩
    change 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < b
    rw [hpv]
    exact ⟨hp'.1, hp'.2.trans_lt (huu₁.trans_lt (hu₁v.trans_le hvBarv)), hvb⟩
  have hquot := incoming_lam_quotient_le_left
    (H.isBVSolution_development hb.1)
    hu (huu₁.trans_lt (hu₁v.trans_le hvBarv)) hseg
    (show u ∈ Icc 0 u from ⟨hu, le_refl u⟩)
  exact hquot.trans (hinitial b hb v hvBarv hvb)

end ChristodoulouBV.Uniqueness

end
