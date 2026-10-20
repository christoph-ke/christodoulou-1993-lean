module

public import ChristodoulouBV.Uniqueness.ExtensionFamily
public import ChristodoulouBV.Uniqueness.ExtensionTransportEquation
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Finite cutoffs in the extension argument

The suprema in Christodoulou's proof are sampled from the compatible family
only where each member is defined. Their real-valued `sSup` convention does
not assert boundedness on the full open development. Compact bounds are
proved separately on finite cutoffs.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The truncated development on p. 1172, lines 19–22: the old open triangle
with the closure of the upper triangle removed. -/
def truncatedDevelopment (u₀ u₁ vStar : ℝ) : Set (ℝ × ℝ) :=
  openDevelopment u₀ vStar \ closure (openDevelopment u₁ vStar)

/-- The values whose supremum is `A′(u₁)`. Each value is taken from a member
of the family at a point in that member's actual off-axis domain. -/
def weightedAlphaPrimeValues (u₀ u₁ vStar δ : ℝ) (S : ℝ → Fields) : Set ℝ :=
  {x | ∃ b ∈ Ioo (0 : ℝ) vStar,
    ∃ p : AlphaPrimeDomain (S b),
      (p : ℝ × ℝ) ∈ truncatedDevelopment u₀ u₁ vStar ∧
      (p : ℝ × ℝ) ∈ openDevelopment 0 b ∧
      x = (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p|}

/-- The source's weighted supremum `A′(u₁)`. Its real `sSup` is used for
estimates only after a boundedness argument; it is not asserted finite here
on the full open development. -/
noncomputable def weightedAlphaPrimeSup (u₀ u₁ vStar δ : ℝ)
    (S : ℝ → Fields) : ℝ :=
  sSup (weightedAlphaPrimeValues u₀ u₁ vStar δ S)

/-- The portion of `A′(u₁)` sampled below a finite outgoing cutoff `t`.
The chosen family member may depend on `t`; the bound used in the final
absorption argument must come separately from the incoming strip and weighted absorption estimates. -/
def weightedAlphaPrimeValuesBelow (u₀ u₁ vStar δ t : ℝ)
    (S : ℝ → Fields) : Set ℝ :=
  {x | ∃ b ∈ Ioo (0 : ℝ) vStar,
    ∃ p : AlphaPrimeDomain (S b),
      (p : ℝ × ℝ) ∈ truncatedDevelopment u₀ u₁ vStar ∧
      (p : ℝ × ℝ) ∈ openDevelopment 0 b ∧ p.1.2 ≤ t ∧
      x = (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p|}

/-- The finite-cutoff weighted supremum, used only with its compact
boundedness theorem. -/
noncomputable def finiteWeightedAlphaPrimeSup (u₀ u₁ vStar δ t : ℝ)
    (S : ℝ → Fields) : ℝ :=
  sSup (weightedAlphaPrimeValuesBelow u₀ u₁ vStar δ t S)

/-- The weighted values on the initial incoming line in (5.3). -/
def incomingWeightedAlphaPrimeValues (u₀ vStar δ : ℝ)
    (S : ℝ → Fields) : Set ℝ :=
  {x | ∃ b ∈ Ioo (0 : ℝ) vStar,
    ∃ p : AlphaPrimeDomain (S b),
      p.1.1 = u₀ ∧ p.1.2 ∈ Ioo u₀ vStar ∧
      (p : ℝ × ℝ) ∈ openDevelopment 0 b ∧
      x = (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p|}

/-- The source's `D′(u₀)`. Finiteness as `v ↑ vStar` follows from the incoming strip estimates. -/
noncomputable def incomingWeightedAlphaPrimeSup (u₀ vStar δ : ℝ)
    (S : ℝ → Fields) : ℝ :=
  sSup (incomingWeightedAlphaPrimeValues u₀ vStar δ S)

/-- An off-axis point of a C¹ member lies in the domain of `α′`. -/
theorem alphaPrimeDomain_of_open {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ openDevelopment 0 b) :
    p ∈ AlphaPrimeDomain S := by
  exact ⟨hp.1.1, hp.2.1,
    H.solution.lam_pos p ⟨hp.1.1.le, hp.2.1, hp.2.2⟩⟩

/-- Select a member strictly beyond a finite cutoff. The choice is made
after `t < vStar`, so no member at the missing endpoint is required. -/
theorem exists_family_member_beyond_cutoff
    {alpha₀ : ℝ → ℝ} {vStar t : ℝ} {S : ℝ → Fields}
    (ht : 0 < t) (htStar : t < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ b ∈ Ioo t vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) := by
  let b := (t + vStar) / 2
  have htb : t < b := by dsimp [b]; linarith
  have hbStar : b < vStar := by dsimp [b]; linarith
  exact ⟨b, ⟨htb, hbStar⟩,
    (hfamily b ⟨ht.trans htb, hbStar⟩).1⟩

/-- On a finite cutoff the selected member has a closed C¹ radius and a
C¹ quotient `θ/λ`. The quotient vanishes at every axis point of the cutoff;
the radius has positive outgoing coordinate jet there and off the axis. -/
private theorem exists_compatible_finite_cutoff_basic
    {alpha₀ : ℝ → ℝ} {vStar t : ℝ} {S : ℝ → Fields}
    (ht : 0 < t) (htStar : t < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ b ∈ Ioo t vStar, ∃ B : ℝ, t < B ∧ B < b ∧
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      ContDiffOn ℝ 1 (C1Solution.canonicalRadius (S b))
        (closedCoordTriangle 0 B) ∧
      ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => (S b).theta p.1 p.2 / (S b).lam p.1 p.2)
        (closedCoordTriangle 0 B) ∧
      (∀ u ∈ Icc (0 : ℝ) t,
        (S b).theta u u / (S b).lam u u = 0) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ p ∈ closedCoordTriangle 0 B,
        c ≤ (S b).lam p.1 p.2) := by
  obtain ⟨b, hb, H⟩ := exists_family_member_beyond_cutoff ht htStar hfamily
  let B := (t + b) / 2
  have htB : t < B := by dsimp [B]; linarith [hb.1]
  have hBb : B < b := by dsimp [B]; linarith [hb.1]
  have hB : 0 < B := ht.trans htB
  obtain ⟨hlam, _, _, htheta, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
  have hne : ∀ p ∈ closedCoordTriangle 0 B,
      (S b).lam p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hcl p hp))
  refine ⟨b, hb, B, htB, hBb, H,
    C1Solution.canonicalRadius_contDiffOn hB hBb H,
    htheta.div hlam hne, ?_, ⟨c, hc, hcl⟩⟩
  intro u hu
  have huB : u ∈ Icc (0 : ℝ) B := ⟨hu.1, hu.2.trans htB.le⟩
  rw [C1Solution.theta_axis_eq_zero hB hBb H huB]
  simp

/-- The classical outgoing derivative agrees with the continuous closed
triangle jet at every strict point of a smaller triangle. -/
theorem alphaPrime_eq_closed_vertical_jet {b B : ℝ}
    (hB : 0 < B) (hBb : B < b) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 B) :
    alphaPrime S ⟨p, alphaPrimeDomain_of_open H
      (show p ∈ openDevelopment 0 b from by
        change 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B at hp
        exact ⟨⟨hp.1, hp.2.1.trans (hp.2.2.trans hBb)⟩,
          ⟨hp.2.1, hp.2.2.trans hBb⟩⟩)⟩ =
      (fderivWithin ℝ
        (fun q : ℝ × ℝ => S.alpha q.1 q.2 / S.lam q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1) / S.lam p.1 p.2 := by
  change 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B at hp
  let F : ℝ × ℝ → ℝ := fun q => S.alpha q.1 q.2 / S.lam q.1 q.2
  let K := closedCoordTriangle 0 B
  have hqi : p ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hF : ContDiffOn ℝ 1 F K := C1Solution.alpha_div_lam_contDiffOn hB hBb H
  have hdiff : DifferentiableAt ℝ F p :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset p hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hwithin : fderivWithin ℝ F K p = fderiv ℝ F p :=
    fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) p (interior_subset hqi)) hdiff
  have hpair : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
  have hcomp : HasDerivAt (fun t => F (p.1, t))
      (fderiv ℝ F p (0, 1)) p.2 := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt p.2 hpair
  rw [alphaPrime_eq_deriv]
  change deriv (fun t => F (p.1, t)) p.2 / S.lam p.1 p.2 = _
  rw [hcomp.deriv, hwithin]

/-- Compact C¹ regularity gives a finite weighted `α′` bound for one member
on every cutoff strictly below its endpoint. This bound may depend on the
cutoff and on the chosen member; the weighted absorption estimate uses it only to justify finite suprema
before its separate uniform absorption argument. -/
theorem exists_weighted_alphaPrime_bound_on_finite_member
    {b B t δ : ℝ} (ht : 0 < t) (htB : t < B) (hBb : B < b)
    (hδ : 0 ≤ δ) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ openDevelopment 0 b,
      p.2 ≤ t → ∀ hp : p ∈ AlphaPrimeDomain S,
      S.r p.1 p.2 ^ δ * |alphaPrime S ⟨p, hp⟩| ≤ M := by
  let K := closedCoordTriangle 0 B
  let Q : ℝ × ℝ → ℝ := fun q => S.alpha q.1 q.2 / S.lam q.1 q.2
  let F : ℝ × ℝ → ℝ := fun q =>
    C1Solution.canonicalRadius S q ^ δ *
      |(fderivWithin ℝ Q K q) (0, 1) / S.lam q.1 q.2|
  have hB : 0 < B := ht.trans htB
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hqC1 : ContDiffOn ℝ 1 Q K := C1Solution.alpha_div_lam_contDiffOn hB hBb H
  have hjet : ContinuousOn (fun q => (fderivWithin ℝ Q K q) (0, 1)) K :=
    (hqC1.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hrC : ContinuousOn (C1Solution.canonicalRadius S) K :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).continuousOn
  have hrpow : ContinuousOn (fun q => C1Solution.canonicalRadius S q ^ δ) K :=
    (Real.continuous_rpow_const hδ).continuousOn.comp hrC (fun _ _ => mem_univ _)
  have hlam : ContinuousOn (fun q : ℝ × ℝ => S.lam q.1 q.2) K :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
  have hne : ∀ q ∈ K, S.lam q.1 q.2 ≠ 0 :=
    fun q hq => ne_of_gt (hc.trans_le (hcl q hq))
  have hF : ContinuousOn F K := hrpow.mul ((hjet.div hlam hne).abs)
  obtain ⟨q, hqK, hqMax⟩ := (isCompact_closedCoordTriangle 0 B).exists_isMaxOn
    ⟨(0, 0), by change 0 ≤ (0 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ B
                exact ⟨le_rfl, le_rfl, hB.le⟩⟩ hF
  refine ⟨max 0 (F q), le_max_left _ _, ?_⟩
  intro p hp hpt hpDomain
  have hpK : p ∈ K := ⟨hp.1.1.le, hp.2.1.le, hpt.trans htB.le⟩
  have hpOpen : p ∈ openCoordTriangle 0 B :=
    ⟨hp.1.1, hp.2.1, hpt.trans_lt htB⟩
  have hrEq := C1Solution.canonicalRadius_eq_radius hB hBb H
    hp.1.1.le hp.2.1 (hpt.trans htB.le)
  have hprime := alphaPrime_eq_closed_vertical_jet hB hBb H hpOpen
  change S.r p.1 p.2 ^ δ *
    |alphaPrime S ⟨p, hpDomain⟩| ≤ max 0 (F q)
  calc
    S.r p.1 p.2 ^ δ *
        |alphaPrime S ⟨p, hpDomain⟩| = F p := by
          dsimp [F, Q, K]
          rw [← hrEq, hprime]
    _ ≤ F q := hqMax hpK
    _ ≤ max 0 (F q) := le_max_right _ _

/-- Compatibility includes the outgoing quotient derivative: equality of
`α` and `λ` on the common open development gives equality of `α′`. -/
theorem family_alphaPrime_eq_on_common_development
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {S : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {b₁ b₂ : ℝ} (hb₁ : b₁ ∈ Ioo (0 : ℝ) vStar)
    (hb₂ : b₂ ∈ Ioo (0 : ℝ) vStar)
    {p : ℝ × ℝ} (hp₁ : p ∈ openDevelopment 0 b₁)
    (hp₂ : p ∈ openDevelopment 0 b₂) :
    alphaPrime (S b₁) ⟨p, alphaPrimeDomain_of_open (hfamily b₁ hb₁).1 hp₁⟩ =
      alphaPrime (S b₂) ⟨p, alphaPrimeDomain_of_open (hfamily b₂ hb₂).1 hp₂⟩ := by
  have hvmin : p.2 ∈ Ioo p.1 (min b₁ b₂) :=
    ⟨hp₁.2.1, lt_min hp₁.2.2 hp₂.2.2⟩
  have heq : (fun v => (S b₁).alpha p.1 v / (S b₁).lam p.1 v) =ᶠ[𝓝 p.2]
      (fun v => (S b₂).alpha p.1 v / (S b₂).lam p.1 v) := by
    filter_upwards [isOpen_Ioo.mem_nhds hvmin] with v hv
    have hp₁v : (p.1, v) ∈ developmentWithInitialEdge b₁ :=
      ⟨hp₁.1.1.le, hv.1, hv.2.trans_le (min_le_left _ _)⟩
    have hp₂v : (p.1, v) ∈ developmentWithInitialEdge b₂ :=
      ⟨hp₂.1.1.le, hv.1, hv.2.trans_le (min_le_right _ _)⟩
    rcases family_fields_eq_on_common_development hfamily hb₁ hb₂
      ⟨hp₁v, hp₂v⟩ with ⟨_, _, _, hlam, _, halpha, _⟩
    rw [halpha, hlam]
  rcases family_fields_eq_on_common_development hfamily hb₁ hb₂
    ⟨⟨hp₁.1.1.le, hp₁.2.1, hp₁.2.2⟩,
      ⟨hp₂.1.1.le, hp₂.2.1, hp₂.2.2⟩⟩ with ⟨_, _, _, hlam, _, _, _⟩
  rw [alphaPrime_eq_deriv, alphaPrime_eq_deriv, heq.deriv_eq, hlam]

/-- Every compatible weighted value below `t < vStar` is bounded by one
compact member selected after `t`. This is the finite-cutoff boundedness
assertion needed before applying `sSup` in the estimate chain. -/
theorem weightedAlphaPrimeValuesBelow_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ δ t : ℝ} {S : ℝ → Fields}
    (ht : 0 < t) (htStar : t < vStar) (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    BddAbove (weightedAlphaPrimeValuesBelow u₀ u₁ vStar δ t S) := by
  obtain ⟨b₀, hb₀, B, htB, hBb₀, H₀, _, _, _, _⟩ :=
    exists_compatible_finite_cutoff_basic ht htStar hfamily
  obtain ⟨M, _, hM⟩ :=
    exists_weighted_alphaPrime_bound_on_finite_member ht htB hBb₀ hδ H₀
  refine ⟨M, ?_⟩
  rintro x ⟨b, hb, p, _, hp, hpt, rfl⟩
  have hp₀ : (p : ℝ × ℝ) ∈ openDevelopment 0 b₀ := by
    refine ⟨⟨hp.1.1, ?_⟩, ⟨hp.2.1, ?_⟩⟩
    · exact hp.2.1.trans (hpt.trans_lt hb₀.1)
    · exact hpt.trans_lt hb₀.1
  have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨ht.trans hb₀.1, hb₀.2⟩
  rcases family_fields_eq_on_common_development hfamily hb hb₀Star
    ⟨⟨hp.1.1.le, hp.2.1, hp.2.2⟩,
      ⟨hp₀.1.1.le, hp₀.2.1, hp₀.2.2⟩⟩ with ⟨hr, _, _, _, _, _, _⟩
  have hprime := family_alphaPrime_eq_on_common_development
    hfamily hb hb₀Star hp hp₀
  have hbound := hM p hp₀ hpt (alphaPrimeDomain_of_open H₀ hp₀)
  simpa only [hr, hprime] using hbound

/-- The canonical radius is a strictly increasing (C^1) coordinate on
each finite outgoing ray. Its value at the axis is exactly zero. -/
theorem finite_cutoff_radius_strictMonoOn
    {b B u t : ℝ} (hu : 0 ≤ u) (hut : u < t) (htB : t < B)
    (hBb : B < b) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (fun v => C1Solution.canonicalRadius S (u, v)) (Icc u t) ∧
    StrictMonoOn (fun v => C1Solution.canonicalRadius S (u, v)) (Icc u t) ∧
    C1Solution.canonicalRadius S (u, u) = 0 := by
  let R : ℝ → ℝ := fun v => C1Solution.canonicalRadius S (u, v)
  let L : ℝ → ℝ := fun v => S.lam u v
  have hB : 0 < B := lt_of_le_of_lt hu (hut.trans htB)
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc u t)
      (closedCoordTriangle 0 B) := by
    intro v hv
    exact ⟨hu, hv.1, hv.2.trans htB.le⟩
  have hpair : ContDiff ℝ 1 (fun v : ℝ => (u, v)) :=
    contDiff_const.prodMk contDiff_id
  have hR : ContDiffOn ℝ 1 R (Icc u t) :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).comp
      hpair.contDiffOn hmap
  have hL : ContinuousOn L (Icc u t) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hderiv : ∀ v ∈ Ioo u t, deriv R v = L v := by
    intro v hv
    have hInt : IntervalIntegrable L volume u v :=
      (hL.mono (Icc_subset_Icc le_rfl hv.2.le)).intervalIntegrable_of_Icc hv.1.le
    have hCont : ContinuousAt L v :=
      hL.continuousAt (Icc_mem_nhds hv.1 hv.2)
    have hMeas : StronglyMeasurableAtFilter L (𝓝 v) :=
      (hL.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter
        isOpen_Ioo v hv
    have hHas := intervalIntegral.integral_hasDerivAt_right hInt
      hMeas hCont
    change HasDerivAt R (L v) v at hHas
    exact hHas.deriv
  have hmono : StrictMonoOn R (Icc u t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc u t) hR.continuousOn
    intro v hv
    have hv' : v ∈ Ioo u t := by simpa only [interior_Icc] using hv
    rw [hderiv v hv']
    have hp : (u, v) ∈ developmentWithInitialEdge b :=
      ⟨hu, hv'.1, hv'.2.trans (htB.trans hBb)⟩
    exact H.solution.lam_pos (u, v) hp
  exact ⟨hR, hmono, (C1Solution.canonical_outgoing_axis S u).1⟩

private theorem exists_contDiffOn_radius_reparam
    {a b : ℝ} (hab : a < b) {R Q : ℝ → ℝ}
    (hR : ContDiffOn ℝ 1 R (Icc a b))
    (hQ : ContDiffOn ℝ 1 Q (Icc a b))
    (hRa : R a = 0)
    (hRpos : ∀ v ∈ Icc a b, 0 < derivWithin R (Icc a b) v) :
    ∃ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Icc 0 (R b)) ∧
      f 0 = Q a ∧ ∀ v ∈ Icc a b, f (R v) = Q v := by
  have hmono : StrictMonoOn R (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hR.continuousOn
    intro v hv
    have hv' : v ∈ Ioo a b := by simpa only [interior_Icc] using hv
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hv'.1 hv'.2)]
    exact hRpos v ⟨hv'.1.le, hv'.2.le⟩
  have hRb : 0 < R b := by
    rw [← hRa]
    exact hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  have himage : R '' Icc a b = Icc 0 (R b) := by
    simpa only [hRa] using
      hR.continuousOn.image_Icc_of_monotoneOn hab.le hmono.monotoneOn
  let e : Icc a b ≃o Icc 0 (R b) :=
    (hmono.orderIso R (Icc a b)).trans
      (Set.orderIsoOfEq _ _ himage)
  let j : ℝ → Icc 0 (R b) := projIcc 0 (R b) hRb.le
  let g : ℝ → ℝ := fun x => (e.symm (j x)).1
  have hj : Continuous j := continuous_projIcc
  have hg : Continuous g :=
    continuous_subtype_val.comp (e.symm.continuous.comp hj)
  have hgmem (x : ℝ) : g x ∈ Icc a b := (e.symm (j x)).property
  have hg_left : ∀ v ∈ Icc a b, g (R v) = v := by
    intro v hv
    have hRv : R v ∈ Icc 0 (R b) := by
      rw [← himage]
      exact ⟨v, hv, rfl⟩
    have hjv : j (R v) = e ⟨v, hv⟩ := by
      apply Subtype.ext
      change (projIcc 0 (R b) hRb.le (R v) : ℝ) = R v
      exact congrArg Subtype.val (projIcc_of_mem hRb.le hRv)
    change (e.symm (j (R v))).1 = v
    rw [hjv, e.symm_apply_apply]
  have hg_right : ∀ x ∈ Icc 0 (R b), R (g x) = x := by
    intro x hx
    have hx' : x ∈ R '' Icc a b := by rw [himage]; exact hx
    obtain ⟨v, hv, rfl⟩ := hx'
    rw [hg_left v hv]
  have hRjet : ContinuousOn (derivWithin R (Icc a b)) (Icc a b) :=
    hR.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hgdiff : DifferentiableOn ℝ g (Icc 0 (R b)) := by
    intro x hx
    let v := g x
    have hv : v ∈ Icc a b := hgmem x
    have hp : 0 < derivWithin R (Icc a b) v := hRpos v hv
    let d := derivWithin R (Icc a b) v
    let E : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hp.ne')
    have hF : HasFDerivWithinAt R (E : ℝ →L[ℝ] ℝ) (Icc a b) v := by
      apply hasFDerivWithinAt_iff_hasDerivWithinAt.mpr
      simpa [E, d] using
        (hR.differentiableOn (by norm_num) v hv).hasDerivWithinAt
    have hgt : Tendsto g (𝓝[Icc 0 (R b)] x) (𝓝[Icc a b] v) :=
      hg.continuousWithinAt.tendsto_nhdsWithin (fun y _ => hgmem y)
    have hright : ∀ᶠ y in 𝓝[Icc 0 (R b)] x, R (g y) = y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hg_right y hy
    exact (hF.of_local_left_inverse hgt hx hright).differentiableWithinAt
  have hgderiv : ∀ x ∈ Icc 0 (R b),
      derivWithin g (Icc 0 (R b)) x =
        (derivWithin R (Icc a b) (g x))⁻¹ := by
    intro x hx
    let v := g x
    have hv : v ∈ Icc a b := hgmem x
    have hp : 0 < derivWithin R (Icc a b) v := hRpos v hv
    let d := derivWithin R (Icc a b) v
    let E : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hp.ne')
    have hF : HasFDerivWithinAt R (E : ℝ →L[ℝ] ℝ) (Icc a b) v := by
      apply hasFDerivWithinAt_iff_hasDerivWithinAt.mpr
      simpa [E, d] using
        (hR.differentiableOn (by norm_num) v hv).hasDerivWithinAt
    have hgt : Tendsto g (𝓝[Icc 0 (R b)] x) (𝓝[Icc a b] v) :=
      hg.continuousWithinAt.tendsto_nhdsWithin (fun y _ => hgmem y)
    have hright : ∀ᶠ y in 𝓝[Icc 0 (R b)] x, R (g y) = y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hg_right y hy
    have h := (hF.of_local_left_inverse hgt hx hright).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hRb) x hx)
    simpa [E, d, v] using h
  have hginv : ContinuousOn (fun x =>
      (derivWithin R (Icc a b) (g x))⁻¹) (Icc 0 (R b)) := by
    have hcomp : ContinuousOn (fun x => derivWithin R (Icc a b) (g x))
        (Icc 0 (R b)) :=
      hRjet.comp hg.continuousOn (fun x _ => hgmem x)
    exact hcomp.inv₀ (fun x hx => (hRpos (g x) (hgmem x)).ne')
  have hgc1 : ContDiffOn ℝ 1 g (Icc 0 (R b)) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hRb)).2
    exact ⟨hgdiff, hginv.congr (fun x hx => hgderiv x hx)⟩
  let f : ℝ → ℝ := Q ∘ g
  have hfc1 : ContDiffOn ℝ 1 f (Icc 0 (R b)) :=
    hQ.comp hgc1 (fun x _ => hgmem x)
  refine ⟨f, hfc1, ?_, ?_⟩
  · simp only [f, Function.comp_apply, ← hRa, hg_left a (left_mem_Icc.mpr hab.le)]
  · intro v hv
    simp only [f, Function.comp_apply, hg_left v hv]

/-- On a finite outgoing ray, `θ/λ` is a genuine (C^1) function of the
canonical radius, with zero value at radius zero. At off-axis points the
canonical radius equals the solution's `r`, so this is the `f` used in (5.7).
No value of the arbitrary total `r` on the excluded diagonal is asserted. -/
theorem exists_finite_cutoff_radius_reparam
    {b B u t : ℝ} (hu : 0 < u) (hut : u < t) (htB : t < B)
    (hBb : B < b) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ f : ℝ → ℝ,
      ContDiffOn ℝ 1 f (Icc 0 (S.r u t)) ∧ f 0 = 0 ∧
      (∀ v ∈ Icc u t,
        f (C1Solution.canonicalRadius S (u, v)) =
          S.theta u v / S.lam u v) ∧
      (∀ v ∈ Ioc u t, f (S.r u v) = S.theta u v / S.lam u v) := by
  let R : ℝ → ℝ := fun v => C1Solution.canonicalRadius S (u, v)
  let Q : ℝ → ℝ := fun v => S.theta u v / S.lam u v
  let K := closedCoordTriangle 0 B
  have hB : 0 < B := hu.trans (hut.trans htB)
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc u t) K := by
    intro v hv
    exact ⟨hu.le, hv.1, hv.2.trans htB.le⟩
  have hpair : ContDiff ℝ 1 (fun v : ℝ => (u, v)) :=
    contDiff_const.prodMk contDiff_id
  have hRc1 : ContDiffOn ℝ 1 R (Icc u t) :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).comp
      hpair.contDiffOn hmap
  obtain ⟨hlamC1, _, _, hthetaC1, _⟩ :=
    C1Solution.five_fields_contDiffOn hB hBb H
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
  have hne : ∀ p ∈ K, S.lam p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hcl p hp))
  have hQc1 : ContDiffOn ℝ 1 Q (Icc u t) :=
    (hthetaC1.div hlamC1 hne).comp hpair.contDiffOn hmap
  have hL : ContinuousOn (fun v => S.lam u v) (Icc u t) :=
    hlamC1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hRpos : ∀ v ∈ Icc u t, 0 < derivWithin R (Icc u t) v := by
    intro v hv
    have hInt : IntervalIntegrable (fun w => S.lam u w) volume u v :=
      (hL.mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable_of_Icc hv.1
    let _ : Fact (v ∈ Icc u t) := ⟨hv⟩
    have hFTC : HasDerivWithinAt R (S.lam u v) (Icc u t) v := by
      exact intervalIntegral.integral_hasDerivWithinAt_right hInt
        (hL.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v)
        (hL v hv)
    have hderiv : derivWithin R (Icc u t) v = S.lam u v :=
      hFTC.derivWithin ((uniqueDiffOn_Icc hut) v hv)
    rw [hderiv]
    exact hc.trans_le (hcl (u, v) (hmap hv))
  have hRa : R u = 0 := (C1Solution.canonical_outgoing_axis S u).1
  obtain ⟨f, hfc1, hf0, hfQ⟩ :=
    exists_contDiffOn_radius_reparam hut hRc1 hQc1 hRa hRpos
  have hr_t : R t = S.r u t :=
    C1Solution.canonicalRadius_eq_radius hB hBb H hu.le hut htB.le
  have hzero : Q u = 0 := by
    dsimp [Q]
    rw [C1Solution.theta_axis_eq_zero hB hBb H
      ⟨hu.le, hut.trans htB |>.le⟩]
    simp
  refine ⟨f, ?_, ?_, hfQ, ?_⟩
  · rw [← hr_t]
    exact hfc1
  · rwa [hzero] at hf0
  · intro v hv
    have hr_v : R v = S.r u v :=
      C1Solution.canonicalRadius_eq_radius hB hBb H hu.le hv.1
        (hv.2.trans htB.le)
    rw [← hr_v]
    exact hfQ v ⟨hv.1.le, hv.2⟩

/-- The finite-cutoff construction for (5.4)–(5.10). For every cutoff chosen below
`vStar`, one compatible family member extends past it. The weighted values
below the cutoff have a finite supremum, and on every outgoing ray used in the
truncated estimate `θ/λ` is (C^1) in the radius coordinate with `f(0)=0`.
The compact bounds here are cutoff dependent; the uniform bound passed to
`vStar` is the separate conclusion of the incoming strip and weighted absorption estimates. -/
theorem exists_compatible_finite_cutoff
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ t δ : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁t : u₁ < t)
    (htStar : t < vStar) (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ b ∈ Ioo t vStar, ∃ B : ℝ, t < B ∧ B < b ∧
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      BddAbove (weightedAlphaPrimeValuesBelow u₀ u₁ vStar δ t S) ∧
      (∀ p ∈ truncatedDevelopment u₀ u₁ vStar,
        p.2 ≤ t → p ∈ openDevelopment 0 b) ∧
      (∀ u ∈ Ioo u₀ u₁, ∃ f : ℝ → ℝ,
        ContDiffOn ℝ 1 f (Icc 0 ((S b).r u t)) ∧ f 0 = 0 ∧
        ∀ v ∈ Ioc u t,
          f ((S b).r u v) = (S b).theta u v / (S b).lam u v) := by
  have ht : 0 < t := hu₀.trans (hu₀u₁.trans hu₁t)
  obtain ⟨b, hb, B, htB, hBb, H, _, _, _, _⟩ :=
    exists_compatible_finite_cutoff_basic ht htStar hfamily
  refine ⟨b, hb, B, htB, hBb, H,
    weightedAlphaPrimeValuesBelow_bddAbove ht htStar hδ hfamily, ?_, ?_⟩
  · intro p hp hpt
    have hpDev := hp.1
    have hvb : p.2 < b := hpt.trans_lt hb.1
    exact ⟨⟨hu₀.trans hpDev.1.1, hpDev.2.1.trans hvb⟩,
      ⟨hpDev.2.1, hvb⟩⟩
  · intro u hu
    obtain ⟨f, hfC1, hf0, _, hf⟩ :=
      exists_finite_cutoff_radius_reparam (hu₀.trans hu.1)
        (hu.2.trans hu₁t) htB hBb H
    exact ⟨f, hfC1, hf0, hf⟩

/-- A nondegenerate finite cutoff contains a genuine off-axis sample, so
its supremum never relies on the empty-set convention for `sSup`. -/
theorem weightedAlphaPrimeValuesBelow_nonempty
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ t δ : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁t : u₁ < t)
    (htStar : t < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    (weightedAlphaPrimeValuesBelow u₀ u₁ vStar δ t S).Nonempty := by
  let u := (u₀ + u₁) / 2
  let v := (u + t) / 2
  let b := (t + vStar) / 2
  have hu₀u : u₀ < u := by dsimp [u]; linarith
  have huu₁ : u < u₁ := by dsimp [u]; linarith
  have huv : u < v := by dsimp [v]; linarith
  have hvt : v < t := by dsimp [v]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hbStar : b < vStar := by dsimp [b]; linarith
  have hb : b ∈ Ioo (0 : ℝ) vStar :=
    ⟨hu₀.trans (hu₀u₁.trans (hu₁t.trans htb)), hbStar⟩
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu₀.trans hu₀u, huv.trans (hvt.trans htb)⟩,
      ⟨huv, hvt.trans htb⟩⟩
  have htrunc : (u, v) ∈ truncatedDevelopment u₀ u₁ vStar := by
    refine ⟨?_, ?_⟩
    · exact ⟨⟨hu₀u, huv.trans (hvt.trans htStar)⟩,
        ⟨huv, hvt.trans htStar⟩⟩
    · have hsub : openDevelopment u₁ vStar ⊆
          {p : ℝ × ℝ | u₁ ≤ p.1} := by
        intro p hp'
        exact hp'.1.1.le
      have hclosed : IsClosed {p : ℝ × ℝ | u₁ ≤ p.1} :=
        isClosed_le continuous_const continuous_fst
      intro hcl
      exact (not_le_of_gt huu₁) (closure_minimal hsub hclosed hcl)
  let p : AlphaPrimeDomain (S b) :=
    ⟨(u, v), alphaPrimeDomain_of_open (hfamily b hb).1 hp⟩
  refine ⟨(S b).r u v ^ δ * |alphaPrime (S b) p|, b, hb, p,
    htrunc, hp, hvt.le, rfl⟩

/-- Every weighted point value on a finite compatible cutoff lies below its
finite supremum. -/
theorem weighted_alphaPrime_le_finite_cutoff_sup
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ t δ : ℝ} {S : ℝ → Fields}
    (ht : 0 < t) (htStar : t < vStar) (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (p : AlphaPrimeDomain (S b))
    (htrunc : (p : ℝ × ℝ) ∈ truncatedDevelopment u₀ u₁ vStar)
    (hp : (p : ℝ × ℝ) ∈ openDevelopment 0 b)
    (hpt : p.1.2 ≤ t) :
    (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p| ≤
      finiteWeightedAlphaPrimeSup u₀ u₁ vStar δ t S := by
  exact le_csSup
    (weightedAlphaPrimeValuesBelow_bddAbove ht htStar hδ hfamily)
    ⟨b, hb, p, htrunc, hp, hpt, rfl⟩

/-- The finite cutoff supremum is nonnegative, as required before the
absorption inequality. -/
theorem finiteWeightedAlphaPrimeSup_nonneg
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ t δ : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁t : u₁ < t)
    (htStar : t < vStar) (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    0 ≤ finiteWeightedAlphaPrimeSup u₀ u₁ vStar δ t S := by
  obtain ⟨x, b, hb, p, htrunc, hp, hpt, rfl⟩ :=
    weightedAlphaPrimeValuesBelow_nonempty (δ := δ)
      hu₀ hu₀u₁ hu₁t htStar hfamily
  have hr : 0 ≤ (S b).r p.1.1 p.1.2 :=
    (hfamily b hb).1.solution.radius_pos p
      ⟨hp.1.1.le, hp.2.1, hp.2.2⟩ |>.le
  have hx : 0 ≤ (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p| :=
    mul_nonneg (Real.rpow_nonneg hr δ) (abs_nonneg _)
  exact hx.trans (weighted_alphaPrime_le_finite_cutoff_sup
    (hu₀.trans (hu₀u₁.trans hu₁t)) htStar hδ hfamily hb p
      htrunc hp hpt)

end ChristodoulouBV.Uniqueness

end
