module

public import ChristodoulouBV.AreaEstimates.SmallData
public import ChristodoulouBV.Frozen.IsBVSolution
public import ChristodoulouBV.Frozen.GlobalDomain
public import ChristodoulouBV.BVSolution.Signs
import Mathlib.Tactic

/-!
# Scalar shifts and the exact null ray variations

The open rays here are the sets in the three-term TV definitions below.
No sign or nonvanishing hypothesis is needed for the quotient identities:
Lean's total division makes the zero-denominator case explicit.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The three outgoing pointwise extended variations on the null ray. -/
noncomputable def e1OutgoingTV (S : Fields) (u : ℝ) : ℝ≥0∞ :=
  eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioi u) +
  eVariationOn (S.phi u) (Ioi u) +
  eVariationOn (fun v => Real.log (S.lam u v)) (Ioi u)

/-- The three incoming pointwise extended variations on the null ray. -/
noncomputable def e1IncomingTV (S : Fields) (v : ℝ) : ℝ≥0∞ :=
  eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) +
  eVariationOn (fun u => S.phi u v) (Ioo 0 v) +
  eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)

/-- The four extra right-continuity clauses of the right-continuous BV class, stated
directly for the paper fields and their actual representatives. -/
def RightBVFields (U : Set (ℝ × ℝ)) (S : Fields) : Prop :=
  (∀ p ∈ U, ContinuousWithinAt (S.lam p.1)
    {w | p.2 ≤ w ∧ (p.1, w) ∈ U} p.2) ∧
  (∀ p ∈ U, ContinuousWithinAt (S.theta p.1)
    {w | p.2 ≤ w ∧ (p.1, w) ∈ U} p.2) ∧
  (∀ p ∈ U, ContinuousWithinAt (fun s => S.nu s p.2)
    {s | p.1 ≤ s ∧ (s, p.2) ∈ U} p.1) ∧
  (∀ p ∈ U, ContinuousWithinAt (fun s => S.zeta s p.2)
    {s | p.1 ≤ s ∧ (s, p.2) ∈ U} p.1)

/-- Geometry is fixed and the scalar gains exactly the chosen constant. -/
theorem scalarShift_field_values (S : Fields) (c u v : ℝ) :
    (scalarShift S c).r u v = S.r u v ∧
    (scalarShift S c).m u v = S.m u v ∧
    (scalarShift S c).lam u v = S.lam u v ∧
    (scalarShift S c).nu u v = S.nu u v ∧
    (scalarShift S c).phi u v = S.phi u v + c := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The outgoing normalized scalar derivative gains the same constant. -/
theorem scalarShift_alpha_div_lam (S : Fields) (c u v : ℝ)
    (hLam : S.lam u v ≠ 0) :
    (scalarShift S c).alpha u v / (scalarShift S c).lam u v =
      S.alpha u v / S.lam u v + c := by
  simp only [scalarShift]
  field_simp [hLam]

/-- The incoming normalized scalar derivative gains the same constant. -/
theorem scalarShift_beta_div_nu (S : Fields) (c u v : ℝ)
    (hν : S.nu u v ≠ 0) :
    (scalarShift S c).beta u v / (scalarShift S c).nu u v =
      S.beta u v / S.nu u v + c := by
  simp only [scalarShift]
  field_simp [hν]

/-- Outgoing scalar variation is unchanged on any set. -/
theorem scalarShift_phi_variation_out (S : Fields) (c u : ℝ) (s : Set ℝ) :
    eVariationOn ((scalarShift S c).phi u) s = eVariationOn (S.phi u) s := by
  change eVariationOn (fun v => S.phi u v + c) s = _
  exact eVariationOn_add_const_real _ _ _

/-- Incoming scalar variation is unchanged on any set. -/
theorem scalarShift_phi_variation_in (S : Fields) (c v : ℝ) (s : Set ℝ) :
    eVariationOn (fun u => (scalarShift S c).phi u v) s =
      eVariationOn (fun u => S.phi u v) s := by
  change eVariationOn (fun u => S.phi u v + c) s = _
  exact eVariationOn_add_const_real _ _ _

/-- A scalar shift preserves the outgoing three-term TV on every ray. -/
theorem e1OutgoingTV_scalarShift (S : Fields) (c u : ℝ)
    (hLam : ∀ v ∈ Ioi u, S.lam u v ≠ 0) :
    e1OutgoingTV (scalarShift S c) u = e1OutgoingTV S u := by
  have hq : EqOn (fun v => (scalarShift S c).alpha u v /
      (scalarShift S c).lam u v)
      (fun v => S.alpha u v / S.lam u v + c) (Ioi u) := by
    intro v hv
    exact scalarShift_alpha_div_lam S c u v (hLam v hv)
  unfold e1OutgoingTV
  rw [eVariationOn.congr hq, eVariationOn_add_const_real,
    scalarShift_phi_variation_out]
  change _ + _ + eVariationOn (fun v => Real.log (S.lam u v)) (Ioi u) = _
  rfl

/-- A scalar shift preserves the incoming three-term TV on every ray. -/
theorem e1IncomingTV_scalarShift (S : Fields) (c v : ℝ)
    (hν : ∀ u ∈ Ioo 0 v, S.nu u v ≠ 0) :
    e1IncomingTV (scalarShift S c) v = e1IncomingTV S v := by
  have hq : EqOn (fun u => (scalarShift S c).beta u v /
      (scalarShift S c).nu u v)
      (fun u => S.beta u v / S.nu u v + c) (Ioo 0 v) := by
    intro u hu
    exact scalarShift_beta_div_nu S c u v (hν u hu)
  unfold e1IncomingTV
  rw [eVariationOn.congr hq, eVariationOn_add_const_real,
    scalarShift_phi_variation_in]
  change _ + _ + eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) = _
  rfl

/-- On the global BV development, positivity of `λ` supplies the exact
outgoing null ray shift invariance without a separate denominator premise. -/
theorem e1OutgoingTV_scalarShift_global {S : Fields}
    (H : IsBVSolution globalDomain S) (c u : ℝ) (hu : 0 ≤ u) :
    e1OutgoingTV (scalarShift S c) u = e1OutgoingTV S u := by
  apply e1OutgoingTV_scalarShift S c u
  intro v hv
  exact (H.solution.lam_pos (u, v) ⟨hu, hv⟩).ne'

/-- On the global BV development, the signed incoming expansion supplies
the exact incoming null ray shift invariance. -/
theorem e1IncomingTV_scalarShift_global {S : Fields}
    (H : IsBVSolution globalDomain S) (c v : ℝ) :
    e1IncomingTV (scalarShift S c) v = e1IncomingTV S v := by
  obtain ⟨a, ha, hLam⟩ := H.lam_bounded_below
  apply e1IncomingTV_scalarShift S c v
  intro u hu
  have hp : (u, v) ∈ globalDomain := ⟨hu.1.le, hu.2⟩
  exact ne_of_lt ((H.nu_le_neg_lower ha hLam hp).trans_lt
    (neg_lt_zero.mpr ha))

/-- The four right-continuity representative conditions survive scalar normalization. -/
theorem RightBVFields.scalarShift {U : Set (ℝ × ℝ)} {S : Fields}
    (H : RightBVFields U S) (c : ℝ) :
    RightBVFields U (scalarShift S c) := by
  rcases H with ⟨hLam, hθ, hν, hζ⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [ChristodoulouBV.scalarShift] using hLam
  · intro p hp
    have hfun : (ChristodoulouBV.scalarShift S c).theta p.1 = S.theta p.1 := by
      funext v
      exact scalarShift_theta S c p.1 v
    rw [hfun]
    exact hθ p hp
  · intro p hp
    change ContinuousWithinAt (fun s => S.nu s p.2)
      {s | p.1 ≤ s ∧ (s, p.2) ∈ U} p.1
    exact hν p hp
  · intro p hp
    have hfun : (fun s => (ChristodoulouBV.scalarShift S c).zeta s p.2) =
        (fun s => S.zeta s p.2) := by
      funext u
      exact scalarShift_zeta S c u p.2
    rw [hfun]
    exact hζ p hp

private theorem ac_add_const {f : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => f x + c) a b := by
  apply hf.congr'
  exact Filter.Eventually.of_forall (fun E => by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dist_add_right])

/-- Every paper BV clause is invariant under a constant scalar shift. -/
theorem IsBVSolution.scalarShift {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsBVSolution U S) (c : ℝ) :
    IsBVSolution U (scalarShift S c) := by
  refine {
    solution := H.solution.scalarShift c
    nu_bounded_below := H.nu_bounded_below
    lam_bounded_below := H.lam_bounded_below
    item1 := H.item1
    item2 := H.item2
    item3_ac_out := ?_
    item3_ac_in := ?_
    item3_variation := ?_
    item4 := ?_
    item5 := ?_
    item6 := ?_ }
  · intro u a b hab hseg
    exact ac_add_const (H.item3_ac_out u a b hab hseg)
  · intro v a b hab hseg
    exact ac_add_const (H.item3_ac_in v a b hab hseg)
  · obtain ⟨C, hOut, hIn⟩ := H.item3_variation
    refine ⟨C, ?_, ?_⟩
    · intro u
      change eVariationOn (fun v => S.phi u v + c) _ ≤ _
      rw [eVariationOn_add_const_real]
      exact hOut u
    · intro v
      change eVariationOn (fun u => S.phi u v + c) _ ≤ _
      rw [eVariationOn_add_const_real]
      exact hIn v
  · intro a ha
    obtain ⟨hpOut, hpIn, hfIn, hfOut⟩ := H.item4 a ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [scalarShift_phi_variation_out] using hpOut
    · simpa only [scalarShift_phi_variation_in] using hpIn
    · simpa only [scalarShift_phi_variation_in] using hfIn
    · simpa only [scalarShift_phi_variation_out] using hfOut
  · have hθeq : (ChristodoulouBV.scalarShift S c).theta = S.theta := by
      funext u v
      exact scalarShift_theta S c u v
    have hζeq : (ChristodoulouBV.scalarShift S c).zeta = S.zeta := by
      funext u v
      exact scalarShift_zeta S c u v
    simpa only [hθeq, hζeq] using H.item5
  · intro a ha
    have h := (H.item6 a ha).add ((H.item2 a ha).const_mul c)
    have heq : (fun v => (ChristodoulouBV.scalarShift S c).alpha a v +
        (ChristodoulouBV.scalarShift S c).beta a v) =
        (fun v => (S.alpha a v + S.beta a v) +
          c * (S.nu a v + S.lam a v)) := by
      funext v
      simp only [ChristodoulouBV.scalarShift]
      ring
    rw [heq]
    simpa only [mul_zero, add_zero] using h

end ChristodoulouBV

end
