module

public import ChristodoulouBV.Existence.GlobalC1Bounds
public import ChristodoulouBV.Existence.C1Continuation
import Mathlib.Tactic

/-!
# Global C¹ existence for small-variation data

Continuation makes the maximal C¹ parameter infinite. The compatible finite
family then gives one total field solving the equations on every finite
chart and globally. Its bootstrap margins, six geometry inequalities, and
universal three-term ray variation bounds all concern this same witness.
The exhaustion retains the quantitative data needed by the smooth
approximation sequence and the quantitative existence witness.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- Exhaust the compatible finite C¹ family for small-variation data. The
same global witness retains exact initial traces, all-field agreement with
the selected finite family, the bootstrap and slice estimates at every scale,
and the universal endpoint coefficient on the full null rays, including `u=0`.
The threshold is the fixed `epsilonChosen` shared with the BV branch. -/
theorem exists_global_c1_small_variation
    (alpha₀ : ℝ → ℝ) (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ T : Fields,
      IsC1Solution globalDomain T ∧
      (∀ v : ℝ, 0 < v → T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) ∧
      (∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) T) ∧
      (∀ b : ℝ, ∀ hb : 0 < b,
        ∀ hm : ENNReal.ofReal b < c1MaximalParameter alpha₀,
        ∀ p ∈ developmentWithInitialEdge b,
        let F := c1FamilyField alpha₀ b hb hm
        T.r p.1 p.2 = F.r p.1 p.2 ∧
          T.phi p.1 p.2 = F.phi p.1 p.2 ∧
          T.m p.1 p.2 = F.m p.1 p.2 ∧
          T.lam p.1 p.2 = F.lam p.1 p.2 ∧
          T.nu p.1 p.2 = F.nu p.1 p.2 ∧
          T.alpha p.1 p.2 = F.alpha p.1 p.2 ∧
          T.beta p.1 p.2 = F.beta p.1 p.2 ∧
          T.theta p.1 p.2 = F.theta p.1 p.2 ∧
          T.zeta p.1 p.2 = F.zeta p.1 p.2) ∧
      (∀ a : ℝ, 0 < a →
        let P := Uniqueness.rescaledFields T 0 a
        sourceZ P < s4Epsilon0 ∧
          (∀ u ∈ Ico (0 : ℝ) 1,
            e1OutgoingTVFinite P u 1 ≤
              ENNReal.ofReal (s4SliceTVK * (sourceD P).toReal)) ∧
          (∀ v ∈ Ioo (0 : ℝ) 1,
            e1IncomingTVFinite P 0 v ≤
              ENNReal.ofReal (s4SliceTVK * (sourceD P).toReal))) ∧
      (∀ p ∈ globalDomain,
        (1 / 3 : ℝ) + 1 / 36 ≤ T.lam p.1 p.2 ∧
        -(2 / 3 : ℝ) + 1 / 36 ≤ T.nu p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 + 1 / 36 ≤ (1 / 3 : ℝ)) ∧
      (∀ p ∈ globalDomain,
        (1 / 3 : ℝ) ≤ T.lam p.1 p.2 ∧ T.lam p.1 p.2 ≤ 1 / 2 ∧
        (1 / 3 : ℝ) ≤ -T.nu p.1 p.2 ∧ -T.nu p.1 p.2 ≤ 2 / 3 ∧
        (2 / 3 : ℝ) ≤ 1 - 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        1 - 2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1) ∧
      (∀ u : ℝ, 0 ≤ u → e1OutgoingTV T u ≤
        ENNReal.ofReal (s6EndpointTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) ∧
      (∀ v : ℝ, 0 < v → e1IncomingTV T v ≤
        ENNReal.ofReal (s6EndpointTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) := by
  have hmax := c1MaximalParameter_eq_top_of_small_variation alpha₀ hα hD
  have hcut (b : ℝ) : 0 < max b 0 + 1 := by linarith [le_max_right b 0]
  have hlt (b : ℝ) : ENNReal.ofReal (max b 0 + 1) < c1MaximalParameter alpha₀ := by
    rw [hmax]
    exact ENNReal.ofReal_lt_top
  let family : ℝ → Fields := fun b => c1FamilyField alpha₀ _ (hcut b) (hlt b)
  have hfamily : ∀ b : ℝ, 0 < b →
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v := by
    intro b _
    obtain ⟨H, hdata⟩ := c1FamilyField_spec alpha₀ (hcut b) (hlt b)
    have hbc : b < max b 0 + 1 := by linarith [le_max_left b 0]
    exact ⟨C1Solution.isC1Solution_restrict_initialEdge H hbc.le,
      fun v hv => hdata v ⟨hv.1, hv.2.trans hbc⟩⟩
  let T := globalC1Patch family
  have hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) T :=
    fun _ hb => globalC1Patch_isC1Solution hfamily hb
  have hdata : ∀ v : ℝ, 0 < v → T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v :=
    fun _ hv => globalC1Patch_initial_data hfamily hv
  have hmargin := global_c1_bootstrap_margins hfinite hdata hD
  have hgeometry := global_c1_geometry hfinite hdata hD
  have hglobal : IsC1Solution globalDomain T :=
    isC1Solution_global_of_finite hfinite
      ⟨2 / 3, fun p hp => (hgeometry p hp).2.2.2.1⟩
      ⟨1 / 3, by norm_num, fun p hp => (hgeometry p hp).1⟩
  obtain ⟨hOut, hIn⟩ := global_c1_universal_tv_bound hfinite hdata hD
  refine ⟨T, hglobal, hdata, hfinite, ?_, ?_, hmargin, hgeometry, hOut, hIn⟩
  · intro b hb hm p hp
    obtain ⟨HF, hdataF⟩ := c1FamilyField_spec alpha₀ hb hm
    exact c1_developments_agree (hfinite b hb) HF
      (fun v hv => hdata v hv.1) hdataF hp hp
  · intro a ha
    have h := global_c1_no_first_exit hfinite hdata hD ha
    exact ⟨h.2.1, h.2.2.2⟩

/-- The global C¹ branch in the exact carrier and trace form of the frozen
Theorems 6.1 and 6.2 statement. This is a projection of the enriched witness theorem. -/
theorem exists_global_c1_small_variation_solution
    (alpha₀ : ℝ → ℝ) (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ T : Fields, IsC1Solution globalDomain T ∧
      ∀ v : ℝ, 0 < v → T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v := by
  obtain ⟨T, HT, hdata, _⟩ := exists_global_c1_small_variation alpha₀ hα hD
  exact ⟨T, HT, hdata⟩

end ChristodoulouBV

end
