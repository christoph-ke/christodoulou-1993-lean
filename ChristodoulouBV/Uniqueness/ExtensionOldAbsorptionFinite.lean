module

public import ChristodoulouBV.Uniqueness.ExtensionCutoff
public import ChristodoulouBV.Uniqueness.ExtensionOldEstimateLinear
public import ChristodoulouBV.Uniqueness.ExtensionOldEstimateCubic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Finite incoming and truncated suprema for the old extension domain

Every supremum in this file is taken below a cutoff strictly smaller than
`vStar`. The compatible family then supplies a single compact C¹ member
controlling all samples below that cutoff.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- A strict point lies in the source's truncated development precisely when
its incoming coordinate lies below the truncation line. -/
theorem mem_truncatedDevelopment_iff {u₀ u₁ vStar : ℝ}
    (hu₁Star : u₁ < vStar) {p : ℝ × ℝ} :
    p ∈ truncatedDevelopment u₀ u₁ vStar ↔
      u₀ < p.1 ∧ p.1 < u₁ ∧ p.1 < p.2 ∧ p.2 < vStar := by
  constructor
  · intro hp
    have hdev := hp.1
    have hfst : p.1 < u₁ := by
      by_contra hn
      have hcl : p ∈ closure (openDevelopment u₁ vStar) := by
        have hEq : openDevelopment u₁ vStar =
            openCoordTriangle u₁ vStar := by
          ext q
          constructor
          · intro h
            exact ⟨h.1.1, h.2.1, h.2.2⟩
          · intro h
            exact ⟨⟨h.1, h.2.1.trans h.2.2⟩,
              ⟨h.2.1, h.2.2⟩⟩
        rw [hEq]
        rw [closure_openCoordTriangle hu₁Star]
        exact ⟨le_of_not_gt hn, hdev.2.1.le, hdev.2.2.le⟩
      exact hp.2 hcl
    exact ⟨hdev.1.1, hfst, hdev.2.1, hdev.2.2⟩
  · rintro ⟨hu₀, hu₁, huv, hv⟩
    refine ⟨⟨⟨hu₀, huv.trans hv⟩, ⟨huv, hv⟩⟩, ?_⟩
    have hsub : openDevelopment u₁ vStar ⊆
        {q : ℝ × ℝ | u₁ ≤ q.1} := by
      intro q hq
      exact hq.1.1.le
    have hclosed : IsClosed {q : ℝ × ℝ | u₁ ≤ q.1} :=
      isClosed_le continuous_const continuous_fst
    intro hcl
    exact (not_le_of_gt hu₁) (closure_minimal hsub hclosed hcl)

/-- The incoming weighted values restricted to a finite outgoing cutoff. -/
def incomingWeightedAlphaPrimeValuesBelow (u₀ vStar δ t : ℝ)
    (S : ℝ → Fields) : Set ℝ :=
  {x | ∃ b ∈ Ioo (0 : ℝ) vStar,
    ∃ p : AlphaPrimeDomain (S b),
      p.1.1 = u₀ ∧ p.1.2 ∈ Ioo u₀ vStar ∧
      (p : ℝ × ℝ) ∈ openDevelopment 0 b ∧ p.1.2 ≤ t ∧
      x = (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p|}

/-- The finite incoming supremum `D′_t` in the cutoff version of (5.10). -/
noncomputable def finiteIncomingWeightedAlphaPrimeSup (u₀ vStar δ t : ℝ)
    (S : ℝ → Fields) : ℝ :=
  sSup (incomingWeightedAlphaPrimeValuesBelow u₀ vStar δ t S)

/-- Compact compatibility bounds all incoming samples below a finite cutoff. -/
theorem incomingWeightedAlphaPrimeValuesBelow_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ δ t : ℝ} {S : ℝ → Fields}
    (ht : 0 < t) (htStar : t < vStar) (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    BddAbove (incomingWeightedAlphaPrimeValuesBelow u₀ vStar δ t S) := by
  obtain ⟨b₀, hb₀, H₀⟩ :=
    exists_family_member_beyond_cutoff ht htStar hfamily
  let B := (t + b₀) / 2
  have htB : t < B := by dsimp [B]; linarith [hb₀.1]
  have hBb₀ : B < b₀ := by dsimp [B]; linarith [hb₀.1]
  obtain ⟨M, _, hM⟩ :=
    exists_weighted_alphaPrime_bound_on_finite_member ht htB hBb₀ hδ H₀
  refine ⟨M, ?_⟩
  rintro x ⟨b, hb, p, _, _, hp, hpt, rfl⟩
  have hp₀ : (p : ℝ × ℝ) ∈ openDevelopment 0 b₀ := by
    exact ⟨⟨hp.1.1, hp.2.1.trans (hpt.trans_lt hb₀.1)⟩,
      ⟨hp.2.1, hpt.trans_lt hb₀.1⟩⟩
  have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar := ⟨ht.trans hb₀.1, hb₀.2⟩
  rcases family_fields_eq_on_common_development hfamily hb hb₀Star
    ⟨⟨hp.1.1.le, hp.2.1, hp.2.2⟩,
      ⟨hp₀.1.1.le, hp₀.2.1, hp₀.2.2⟩⟩ with ⟨hr, _, _, _, _, _, _⟩
  have hprime := family_alphaPrime_eq_on_common_development
    hfamily hb hb₀Star hp hp₀
  have hbound := hM p hp₀ hpt (alphaPrimeDomain_of_open H₀ hp₀)
  simpa only [hr, hprime] using hbound

/-- An incoming weighted value below `t` lies below `D′_t`. -/
theorem incoming_weighted_alphaPrime_le_finite_sup
    {alpha₀ : ℝ → ℝ} {vStar u₀ δ t : ℝ} {S : ℝ → Fields}
    (ht : 0 < t) (htStar : t < vStar) (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (p : AlphaPrimeDomain (S b))
    (hpu : p.1.1 = u₀) (hpv : p.1.2 ∈ Ioo u₀ vStar)
    (hp : (p : ℝ × ℝ) ∈ openDevelopment 0 b) (hpt : p.1.2 ≤ t) :
    (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p| ≤
      finiteIncomingWeightedAlphaPrimeSup u₀ vStar δ t S := by
  exact le_csSup
    (incomingWeightedAlphaPrimeValuesBelow_bddAbove ht htStar hδ hfamily)
    ⟨b, hb, p, hpu, hpv, hp, hpt, rfl⟩

/-- The finite incoming cutoff contains a sample whenever `u₀<t`. -/
theorem incomingWeightedAlphaPrimeValuesBelow_nonempty
    {alpha₀ : ℝ → ℝ} {vStar u₀ δ t : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀t : u₀ < t) (htStar : t < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    (incomingWeightedAlphaPrimeValuesBelow u₀ vStar δ t S).Nonempty := by
  let v := (u₀ + t) / 2
  let b := (t + vStar) / 2
  have hu₀v : u₀ < v := by dsimp [v]; linarith
  have hvt : v < t := by dsimp [v]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hbStar : b < vStar := by dsimp [b]; linarith
  have hb : b ∈ Ioo (0 : ℝ) vStar :=
    ⟨hu₀.trans (hu₀t.trans htb), hbStar⟩
  have hp : (u₀, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu₀, hu₀v.trans (hvt.trans htb)⟩,
      ⟨hu₀v, hvt.trans htb⟩⟩
  let p : AlphaPrimeDomain (S b) :=
    ⟨(u₀, v), alphaPrimeDomain_of_open (hfamily b hb).1 hp⟩
  exact ⟨(S b).r u₀ v ^ δ * |alphaPrime (S b) p|,
    b, hb, p, rfl, ⟨hu₀v, hvt.trans htStar⟩, hp, hvt.le, rfl⟩

/-- The finite incoming supremum is nonnegative. -/
theorem finiteIncomingWeightedAlphaPrimeSup_nonneg
    {alpha₀ : ℝ → ℝ} {vStar u₀ δ t : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀t : u₀ < t) (htStar : t < vStar)
    (hδ : 0 ≤ δ)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    0 ≤ finiteIncomingWeightedAlphaPrimeSup u₀ vStar δ t S := by
  obtain ⟨x, b, hb, p, hpu, hpv, hp, hpt, rfl⟩ :=
    incomingWeightedAlphaPrimeValuesBelow_nonempty (δ := δ)
      hu₀ hu₀t htStar hfamily
  have hr : 0 ≤ (S b).r p.1.1 p.1.2 :=
    (hfamily b hb).1.solution.radius_pos p
      ⟨hp.1.1.le, hp.2.1, hp.2.2⟩ |>.le
  have hx : 0 ≤ (S b).r p.1.1 p.1.2 ^ δ * |alphaPrime (S b) p| :=
    mul_nonneg (Real.rpow_nonneg hr δ) (abs_nonneg _)
  exact hx.trans (incoming_weighted_alphaPrime_le_finite_sup
    (hu₀.trans hu₀t) htStar hδ hfamily hb p hpu hpv hp hpt)

/-- Once the incoming values are uniformly bounded, each finite incoming
supremum lies below their full supremum. -/
theorem finiteIncomingWeightedAlphaPrimeSup_le_incomingSup
    {alpha₀ : ℝ → ℝ} {vStar u₀ δ t : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀t : u₀ < t) (htStar : t < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hIncoming : BddAbove (incomingWeightedAlphaPrimeValues u₀ vStar δ S)) :
    finiteIncomingWeightedAlphaPrimeSup u₀ vStar δ t S ≤
      incomingWeightedAlphaPrimeSup u₀ vStar δ S := by
  apply csSup_le (incomingWeightedAlphaPrimeValuesBelow_nonempty
    hu₀ hu₀t htStar hfamily)
  rintro x ⟨b, hb, p, hpu, hpv, hp, _, rfl⟩
  exact le_csSup hIncoming ⟨b, hb, p, hpu, hpv, hp, rfl⟩

end ChristodoulouBV.Uniqueness

end
