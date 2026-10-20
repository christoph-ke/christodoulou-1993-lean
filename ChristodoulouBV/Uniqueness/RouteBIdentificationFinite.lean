module

public import ChristodoulouBV.Uniqueness.RouteBIdentification
public import ChristodoulouBV.C1Solution.AxisTranslationUniqueness
import Mathlib.Tactic

/-!
# Route B identification on finite old developments

The compact characteristic primitives determine the axis solution's incoming
radius and scalar field wherever an old member is defined. Translated C¹
uniqueness then identifies every field on the strict common development.
-/

public section

open Set
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- A prescribed axis triangle agrees with any old family member at each
strict point common to the axis triangle and that member. The old member is
used only at points with `v < c`; its raw diagonal radius is not involved. -/
theorem OffAxisTerminalC1Packet.axis_eq_old_member
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ c ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge c) (S c) ∧
      (∀ v ∈ Ioo (0 : ℝ) c,
        (S c).r 0 v = v / 2 ∧ (S c).alpha 0 v = alpha₀ v))
    {b : ℝ} {T : Fields}
    (HT : C1Solution.AxisClassicalSolution a b T) (hab : a < b)
    (hrT : ∀ v ∈ Icc a vStar, T.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      T.r a v * T.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) vStar)
    {u v : ℝ} (hau : a ≤ u) (huv : u < v)
    (hvb : v < b) (hvc : v < c) :
    T.r u v = (S c).r u v ∧ T.phi u v = (S c).phi u v ∧
    T.m u v = (S c).m u v ∧ T.lam u v = (S c).lam u v ∧
    T.nu u v = (S c).nu u v ∧ T.alpha u v = (S c).alpha u v ∧
    T.beta u v = (S c).beta u v ∧ T.theta u v = (S c).theta u v ∧
    T.zeta u v = (S c).zeta u v := by
  have hdata : ∀ w, a < w → w < min b c →
      T.r a w = (S c).r a w ∧ T.phi a w = (S c).phi a w := by
    intro w haw hw
    have hwb : w < b := hw.trans_le (min_le_left _ _)
    have hwc : w < c := hw.trans_le (min_le_right _ _)
    have hwI : w ∈ Icc a vStar := ⟨haw.le, hwc.le.trans hc.2.le⟩
    obtain ⟨hrOld, hpsiOld⟩ :=
      P.edge_radius_scalar_product_eq_old ha hfamily hc haw hwc
    have hr : T.r a w = (S c).r a w := (hrT w hwI).trans hrOld
    have hpsi : T.r a w * T.phi a w =
        (S c).r a w * (S c).phi a w :=
      (hpsiT w hwI).trans hpsiOld
    have hpos : 0 < T.r a w :=
      HT.r_pos (a, w) ⟨le_rfl, haw, hwb⟩
    constructor
    · exact hr
    · have hmul : T.r a w * T.phi a w =
          T.r a w * (S c).phi a w := by rwa [← hr] at hpsi
      exact (mul_left_cancel₀ hpos.ne' hmul)
  exact C1Solution.classical_axis_solution_eq_old_on_overlap
    HT hab (hfamily c hc).1 ha.le le_rfl hdata hau huv
    (lt_min hvb hvc)

/-- Any old family member whose endpoint lies between a finite cutoff and
`vStar` agrees with the axis triangle at all strict points below that cutoff. -/
theorem OffAxisTerminalC1Packet.axis_eq_old_on_finite_cutoff_with_member
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
    {u v : ℝ} (hau : a ≤ u) (huv : u < v) (hvb' : v < b') :
    T.r u v = (S c).r u v ∧ T.phi u v = (S c).phi u v ∧
    T.m u v = (S c).m u v ∧ T.lam u v = (S c).lam u v ∧
    T.nu u v = (S c).nu u v ∧ T.alpha u v = (S c).alpha u v ∧
    T.beta u v = (S c).beta u v ∧ T.theta u v = (S c).theta u v ∧
    T.zeta u v = (S c).zeta u v := by
  have hc : c ∈ Ioo (0 : ℝ) vStar := ⟨ha.trans (hb'.1.trans hbc.1), hbc.2⟩
  exact P.axis_eq_old_member ha hfamily HT
    (hb'.1.trans (hb'.2.trans hStarb))
    hrT hpsiT hc hau huv (hvb'.trans (hb'.2.trans hStarb))
    (hvb'.trans hbc.1)

/-- For every finite cutoff below `vStar`, choose a later old member and
identify all fields on the whole strict triangle below that cutoff. -/
theorem OffAxisTerminalC1Packet.axis_eq_old_on_finite_cutoff
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
    {b' : ℝ} (hb' : b' ∈ Ioo a vStar)
    {u v : ℝ} (hau : a ≤ u) (huv : u < v) (hvb' : v < b') :
    T.r u v = (S ((b' + vStar) / 2)).r u v ∧
    T.phi u v = (S ((b' + vStar) / 2)).phi u v ∧
    T.m u v = (S ((b' + vStar) / 2)).m u v ∧
    T.lam u v = (S ((b' + vStar) / 2)).lam u v ∧
    T.nu u v = (S ((b' + vStar) / 2)).nu u v ∧
    T.alpha u v = (S ((b' + vStar) / 2)).alpha u v ∧
    T.beta u v = (S ((b' + vStar) / 2)).beta u v ∧
    T.theta u v = (S ((b' + vStar) / 2)).theta u v ∧
    T.zeta u v = (S ((b' + vStar) / 2)).zeta u v := by
  have hc : (b' + vStar) / 2 ∈ Ioo (0 : ℝ) vStar := by
    constructor <;> linarith only [ha, hb'.1, hb'.2]
  have hvc : v < (b' + vStar) / 2 := by
    linarith only [hvb', hb'.2]
  exact P.axis_eq_old_member ha hfamily HT (lt_trans hb'.1 (lt_trans hb'.2 hStarb))
    hrT hpsiT hc hau huv (lt_trans hvb' (lt_trans hb'.2 hStarb)) hvc

end ChristodoulouBV.Uniqueness

end
