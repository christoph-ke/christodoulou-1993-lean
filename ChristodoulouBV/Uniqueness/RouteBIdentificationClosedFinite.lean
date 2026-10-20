module

public import ChristodoulouBV.Uniqueness.RouteBIdentificationFinite
public import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The closed finite old/axis overlap

Continuity carries strict-overlap equality to the diagonal and incoming edge
below each finite cutoff. The old radius and mass there are their canonical
extensions; the frozen total fields do not specify diagonal values for them.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

private theorem eqOn_closed_triangle_of_eqOn_open
    {a B : ℝ} (haB : a < B) {f g : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a B))
    (hg : ContinuousOn g (closedCoordTriangle a B))
    (heq : EqOn f g (openCoordTriangle a B)) :
    EqOn f g (closedCoordTriangle a B) :=
  heq.of_subset_closure hf hg
    (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
    (by rw [closure_openCoordTriangle haB])

/-- On every finite closed triangle below `vStar`, the axis solution equals
the canonical old radius and mass and all five actual C¹ old fields. In
particular this includes its axis diagonal, without identifying the old raw
diagonal radius or mass. -/
theorem OffAxisTerminalC1Packet.axis_eq_old_on_finite_closed_triangle
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ c ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge c) (S c) ∧
      (∀ v ∈ Ioo (0 : ℝ) c,
        (S c).r 0 v = v / 2 ∧ (S c).alpha 0 v = alpha₀ v))
    {b : ℝ} {T : Fields}
    (HT : C1Solution.AxisClassicalSolution a b T) (hStarb : vStar < b)
    (hrT : ∀ v ∈ Icc a vStar, T.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      T.r a v * T.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    {b' c : ℝ} (hb' : b' ∈ Ioo a vStar) (hbc : c ∈ Ioo b' vStar)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b') :
    T.r p.1 p.2 = C1Solution.canonicalRadius (S c) p ∧
    T.phi p.1 p.2 = (S c).phi p.1 p.2 ∧
    T.m p.1 p.2 =
      C1Solution.canonicalMass c (S c) p ∧
    T.lam p.1 p.2 = (S c).lam p.1 p.2 ∧
    T.nu p.1 p.2 = (S c).nu p.1 p.2 ∧
    T.alpha p.1 p.2 = (S c).alpha p.1 p.2 ∧
    T.beta p.1 p.2 = (S c).beta p.1 p.2 ∧
    T.theta p.1 p.2 = (S c).theta p.1 p.2 ∧
    T.zeta p.1 p.2 = (S c).zeta p.1 p.2 := by
  have hc : c ∈ Ioo (0 : ℝ) vStar :=
    ⟨ha.trans (hb'.1.trans hbc.1), hbc.2⟩
  have hb'c : b' < c := hbc.1
  have hB : 0 < b' := ha.trans hb'.1
  have hB0 : closedCoordTriangle a b' ⊆ closedCoordTriangle 0 b' := by
    intro q hq
    exact ⟨ha.le.trans hq.1, hq.2.1, hq.2.2⟩
  have hBT : closedCoordTriangle a b' ⊆ closedCoordTriangle a b := by
    intro q hq
    exact ⟨hq.1, hq.2.1, hq.2.2.trans (hb'.2.trans hStarb).le⟩
  have Hc := (hfamily c hc).1
  have hOld := C1Solution.five_fields_contDiffOn hB hb'c Hc
  have hopen (q : ℝ × ℝ) (hq : q ∈ openCoordTriangle a b') :
      T.r q.1 q.2 = C1Solution.canonicalRadius (S c) q ∧
      T.phi q.1 q.2 = (S c).phi q.1 q.2 ∧
      T.m q.1 q.2 = C1Solution.canonicalMass c (S c) q ∧
      T.lam q.1 q.2 = (S c).lam q.1 q.2 ∧
      T.nu q.1 q.2 = (S c).nu q.1 q.2 ∧
      T.alpha q.1 q.2 = (S c).alpha q.1 q.2 ∧
      T.beta q.1 q.2 = (S c).beta q.1 q.2 := by
    have h := P.axis_eq_old_on_finite_cutoff_with_member ha hfamily HT hStarb
      hrT hpsiT hb' hbc hq.1.le hq.2.1 hq.2.2
    have hrad : C1Solution.canonicalRadius (S c) q =
        (S c).r q.1 q.2 :=
      C1Solution.canonicalRadius_eq_radius hB hb'c Hc
        (ha.trans hq.1).le hq.2.1 hq.2.2.le
    have hm : C1Solution.canonicalMass c (S c) q =
        (S c).m q.1 q.2 :=
      C1Solution.canonicalMass_eq_mass
        (show q ∈ developmentWithInitialEdge c from
          ⟨(ha.trans hq.1).le, hq.2.1, hq.2.2.trans hb'c⟩)
    exact ⟨h.1.trans hrad.symm, h.2.1, h.2.2.1.trans hm.symm,
      h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1⟩
  have hrad := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.r_c1.continuousOn.mono hBT)
    ((C1Solution.canonicalRadius_contDiffOn hB hb'c Hc).continuousOn.mono hB0)
    (fun q hq => (hopen q hq).1)
  have hphi := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.phi_c1.continuousOn.mono hBT)
    (hOld.2.2.1.continuousOn.mono hB0)
    (fun q hq => (hopen q hq).2.1)
  have hm := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.m_c1.continuousOn.mono hBT)
    ((C1Solution.canonicalMass_contDiffOn hB hb'c Hc).continuousOn.mono hB0)
    (fun q hq => (hopen q hq).2.2.1)
  have hlam := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.lam_c1.continuousOn.mono hBT)
    (hOld.1.continuousOn.mono hB0)
    (fun q hq => (hopen q hq).2.2.2.1)
  have hnu := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.nu_c1.continuousOn.mono hBT)
    (hOld.2.1.continuousOn.mono hB0)
    (fun q hq => (hopen q hq).2.2.2.2.1)
  have halpha := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.alpha_c1.continuousOn.mono hBT)
    ((C1Solution.alpha_contDiffOn hB hb'c Hc).continuousOn.mono hB0)
    (fun q hq => (hopen q hq).2.2.2.2.2.1)
  have hbeta := eqOn_closed_triangle_of_eqOn_open hb'.1
    (HT.beta_c1.continuousOn.mono hBT)
    ((C1Solution.beta_contDiffOn hB hb'c Hc).continuousOn.mono hB0)
    (fun q hq => (hopen q hq).2.2.2.2.2.2)
  refine ⟨hrad hp, hphi hp, hm hp, hlam hp, hnu hp,
    halpha hp, hbeta hp, ?_, ?_⟩
  · simp only [Fields.theta]
    have haPoint : T.alpha p.1 p.2 = (S c).alpha p.1 p.2 := halpha hp
    have hlPoint : T.lam p.1 p.2 = (S c).lam p.1 p.2 := hlam hp
    have hpPoint : T.phi p.1 p.2 = (S c).phi p.1 p.2 := hphi hp
    rw [haPoint, hlPoint, hpPoint]
  · simp only [Fields.zeta]
    have hbPoint : T.beta p.1 p.2 = (S c).beta p.1 p.2 := hbeta hp
    have hnPoint : T.nu p.1 p.2 = (S c).nu p.1 p.2 := hnu hp
    have hpPoint : T.phi p.1 p.2 = (S c).phi p.1 p.2 := hphi hp
    rw [hbPoint, hnPoint, hpPoint]

/-- At every point of the old union with `a ≤ u ≤ v < vStar`, the axis
triangle equals any old member defined at that point. The radius and mass
on the diagonal are the canonical old extensions. -/
theorem OffAxisTerminalC1Packet.axis_eq_old_union_pointwise
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ c ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge c) (S c) ∧
      (∀ v ∈ Ioo (0 : ℝ) c,
        (S c).r 0 v = v / 2 ∧ (S c).alpha 0 v = alpha₀ v))
    {b : ℝ} {T : Fields}
    (HT : C1Solution.AxisClassicalSolution a b T) (hStarb : vStar < b)
    (hrT : ∀ v ∈ Icc a vStar, T.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      T.r a v * T.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) vStar)
    {p : ℝ × ℝ} (hau : a ≤ p.1) (huv : p.1 ≤ p.2) (hvc : p.2 < c) :
    T.r p.1 p.2 = C1Solution.canonicalRadius (S c) p ∧
    T.phi p.1 p.2 = (S c).phi p.1 p.2 ∧
    T.m p.1 p.2 = C1Solution.canonicalMass c (S c) p ∧
    T.lam p.1 p.2 = (S c).lam p.1 p.2 ∧
    T.nu p.1 p.2 = (S c).nu p.1 p.2 ∧
    T.alpha p.1 p.2 = (S c).alpha p.1 p.2 ∧
    T.beta p.1 p.2 = (S c).beta p.1 p.2 ∧
    T.theta p.1 p.2 = (S c).theta p.1 p.2 ∧
    T.zeta p.1 p.2 = (S c).zeta p.1 p.2 := by
  let b' := (p.2 + c) / 2
  have hvb' : p.2 < b' := by dsimp [b']; linarith only [hvc]
  have hb'c : b' < c := by dsimp [b']; linarith only [hvc]
  have hb' : b' ∈ Ioo a vStar :=
    ⟨(hau.trans huv).trans_lt hvb', hb'c.trans hc.2⟩
  have hbc : c ∈ Ioo b' vStar := ⟨hb'c, hc.2⟩
  have hp : p ∈ closedCoordTriangle a b' :=
    ⟨hau, huv, hvb'.le⟩
  exact P.axis_eq_old_on_finite_closed_triangle ha hfamily HT hStarb
    hrT hpsiT hb' hbc hp

/-- The same finite closed overlap has matching relative first jets of the
seven physical fields and the two derived scalar amplitudes. Radius and mass
jets on the old side are those of their canonical extensions. -/
theorem OffAxisTerminalC1Packet.axis_relative_jets_eq_old_on_finite_closed_triangle
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ c ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge c) (S c) ∧
      (∀ v ∈ Ioo (0 : ℝ) c,
        (S c).r 0 v = v / 2 ∧ (S c).alpha 0 v = alpha₀ v))
    {b : ℝ} {T : Fields}
    (HT : C1Solution.AxisClassicalSolution a b T) (hStarb : vStar < b)
    (hrT : ∀ v ∈ Icc a vStar, T.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      T.r a v * T.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    {b' c : ℝ} (hb' : b' ∈ Ioo a vStar) (hbc : c ∈ Ioo b' vStar)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b') :
    let K := closedCoordTriangle a b'
    fderivWithin ℝ (fun q : ℝ × ℝ => T.r q.1 q.2) K p =
      fderivWithin ℝ (C1Solution.canonicalRadius (S c)) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.phi q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).phi q.1 q.2) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.m q.1 q.2) K p =
      fderivWithin ℝ (C1Solution.canonicalMass c (S c)) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.lam q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).lam q.1 q.2) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.nu q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).nu q.1 q.2) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.alpha q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).alpha q.1 q.2) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.beta q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).beta q.1 q.2) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.theta q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).theta q.1 q.2) K p ∧
    fderivWithin ℝ (fun q : ℝ × ℝ => T.zeta q.1 q.2) K p =
      fderivWithin ℝ (fun q : ℝ × ℝ => (S c).zeta q.1 q.2) K p := by
  dsimp only
  have heq (q : ℝ × ℝ) (hq : q ∈ closedCoordTriangle a b') :=
    P.axis_eq_old_on_finite_closed_triangle ha hfamily HT hStarb
      hrT hpsiT hb' hbc hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fderivWithin_congr' (fun q hq => (heq q hq).1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.2.2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.2.2.2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.2.2.2.2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.2.2.2.2.2.1) hp
  · exact fderivWithin_congr' (fun q hq => (heq q hq).2.2.2.2.2.2.2.2) hp

end ChristodoulouBV.Uniqueness

end
