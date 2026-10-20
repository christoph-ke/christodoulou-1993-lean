module

public import ChristodoulouBV.AreaEstimates.SourceInputs
public import ChristodoulouBV.BVSolution.PrimitiveCalculus

/-!
# Reduced scalar and mass-ratio calculus

Only reduced solution identities, directional BV/AC and the displayed
pointwise geometry enter these proofs. No BV axis item is assumed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.SourceInputsWeak

open IsBVSolution

/-- A nonnegative mass ratio and positive radius imply nonnegative mass. -/
theorem mass_nonneg
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v : ℝ} (huv : (u, v) ∈ U) : 0 ≤ S.m u v := by
  have hp := h.radius_pos (u, v) huv
  have hm := (hmu (u, v) huv).1
  have hn := (le_div_iff₀ hp).mp hm
  linarith only [hn]

/-- The outgoing expansion lower bound gives a linear radius lower bound. -/
theorem radius_lower
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    {u v : ℝ} (huv : (u, v) ∈ U) : c * (v - u) ≤ S.r u v := by
  exact radius_ge_of_lam_ge h.development h hlam huv

/-- The positive mass gap follows from a positive radius and ratio strictly below one. -/
theorem gap_pos
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v : ℝ} (huv : (u, v) ∈ U) : 0 < gap S u v := by
  have hr := h.radius_pos (u, v) huv
  have hm := (hmu (u, v) huv).2
  dsimp only [gap]
  have ht := (div_lt_iff₀ hr).mp hm
  linarith only [ht]

/-- On a compact outgoing slice, the scalar derivative is `θ/r` almost
everywhere.  This is obtained from the two frozen primitives and the AC
product rule; it does not differentiate a BV representative pointwise. -/
theorem scalar_ae_deriv_out
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (S.phi u) t = S.theta u t / S.r u t := by
  have hD := h.development
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : outSeg u a t ⊆ U :=
    outgoing_primitive_on_subsegments hD huv hua hab hbv t ht
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (S.r u) (S.lam u) a t :=
    h.radius_out u a t ht.1 (hsub t ht)
  have hψPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r u s * S.phi u s) (S.alpha u) a t :=
    h.scalar_radius_out u a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (S.r u) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hφAC : AbsolutelyContinuousOnInterval (S.phi u) a b :=
    hACOut u a b hab (hD.out_seg_subset huv hua hab hbv)
  have hrDeriv : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (S.r u) t = S.lam u t := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hrPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hrPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hψDeriv : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (fun s => S.r u s * S.phi u s) t = S.alpha u t := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hψPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hψPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hMul := hrAC.ae_deriv_mul hφAC
  filter_upwards [hrDeriv, hψDeriv, hMul] with t hr hψ hmul ht
  have htU : (u, t) ∈ U := hD.outgoing_mem huv
    (hua.trans_le ht.1) (ht.2.trans hbv)
  have hrpos : 0 < S.r u t := h.radius_pos (u, t) htU
  have heq := hmul (by simpa only [uIcc_of_le hab] using ht)
  rw [hr ht, hψ ht] at heq
  dsimp [Fields.theta]
  apply (eq_div_iff hrpos.ne').2
  nlinarith

/-- On a contained compact incoming segment, the scalar derivative is `ζ/r`
almost everywhere.  Containment is explicit because a development point need
not have an incoming path to its axis point. -/
theorem scalar_ae_deriv_in
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    {v a b : ℝ} (hab : a ≤ b) (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun u => S.phi u v) s = S.zeta s v / S.r s v := by
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : inSeg v a t ⊆ U := by
    apply Set.Subset.trans _ hseg
    intro p hp
    have ⟨hpa, hpv⟩ : p.1 ∈ Icc a t ∧ p.2 = v := by
      simpa [inSeg] using hp
    have hpb : p.1 ∈ Icc a b := ⟨hpa.1, hpa.2.trans ht.2⟩
    simpa [inSeg] using And.intro hpb hpv
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r s v) (fun s => S.nu s v) a t :=
    h.radius_in v a t ht.1 (hsub t ht)
  have hψPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r s v * S.phi s v) (fun s => S.beta s v) a t :=
    h.scalar_radius_in v a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (fun s => S.r s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hφAC : AbsolutelyContinuousOnInterval (fun s => S.phi s v) a b :=
    hACIn v a b hab hseg
  have hrDeriv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun u => S.r u v) s = S.nu s v := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hrPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hrPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hψDeriv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun u => S.r u v * S.phi u v) s = S.beta s v := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hψPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hψPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hMul := hrAC.ae_deriv_mul hφAC
  filter_upwards [hrDeriv, hψDeriv, hMul] with s hr hψ hmul hs
  have hsU : (s, v) ∈ U := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hrpos : 0 < S.r s v := h.radius_pos (s, v) hsU
  have heq := hmul (by simpa only [uIcc_of_le hab] using hs)
  rw [hr hs, hψ hs] at heq
  dsimp [Fields.zeta]
  apply (eq_div_iff hrpos.ne').2
  nlinarith

/-- The outgoing scalar derivative identity holds almost everywhere on the
whole half-open slice, by a countable cover of compact intervals. -/
theorem scalar_ae_deriv_out_on_slice
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∀ᵐ t ∂volume, t ∈ Ioc u v →
      deriv (S.phi u) t = S.theta u t / S.r u t := by
  have hq : ∀ q : ℚ, ∀ᵐ t ∂volume,
      u < (q : ℝ) → (q : ℝ) ≤ v → t ∈ Icc (q : ℝ) v →
        deriv (S.phi u) t = S.theta u t / S.r u t := by
    intro q
    by_cases huq : u < (q : ℝ)
    · by_cases hqv : (q : ℝ) ≤ v
      · filter_upwards [(scalar_ae_deriv_out h hACOut) huv huq hqv le_rfl]
          with t ht _ _ hmem
        exact ht hmem
      · exact Filter.Eventually.of_forall (fun _ _ h => (hqv h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (huq h).elim)
  filter_upwards [eventually_countable_forall.mpr hq] with t ht hmem
  obtain ⟨q, huq, hqt⟩ := exists_rat_btwn hmem.1
  exact ht q huq (hqt.le.trans hmem.2) ⟨hqt.le, hmem.2⟩

/-- The incoming scalar derivative equals `ζ/r` almost everywhere on a
complete half-open ray, by a countable cover of compact subsegments. -/
theorem scalar_ae_deriv_in_on_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    {u v : ℝ} (_huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    ∀ᵐ s ∂volume, s ∈ Ico u v →
      deriv (fun t => S.phi t v) s = S.zeta s v / S.r s v := by
  have hq : ∀ q : ℚ, ∀ᵐ s ∂volume,
      u ≤ (q : ℝ) → (q : ℝ) < v → s ∈ Icc u (q : ℝ) →
        deriv (fun t => S.phi t v) s = S.zeta s v / S.r s v := by
    intro q
    by_cases huq : u ≤ (q : ℝ)
    · by_cases hqv : (q : ℝ) < v
      · have hseg := incoming_seg_subset_of_half_open_access hqv haccess
        filter_upwards [(scalar_ae_deriv_in h hACIn) huq hseg] with s hs _ _ hmem
        exact hs hmem
      · exact Filter.Eventually.of_forall (fun _ _ h => (hqv h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (huq h).elim)
  filter_upwards [eventually_countable_forall.mpr hq] with s hs hmem
  obtain ⟨q, hsq, hqv⟩ := exists_rat_btwn hmem.2
  exact hs q (hmem.1.trans hsq.le) hqv ⟨hmem.1, hsq.le⟩

/-- The outgoing mass ratio has its expected quotient derivative almost
everywhere on compact off-axis segments. -/
theorem mass_ratio_ae_deriv_out
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (fun s => S.m u s / S.r u s) t =
        (massV S u t * S.r u t - S.m u t * S.lam u t) /
          S.r u t ^ 2 := by
  have hD := h.development
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : outSeg u a t ⊆ U :=
    outgoing_primitive_on_subsegments hD huv hua hab hbv t ht
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (S.r u) (S.lam u) a t :=
    h.radius_out u a t ht.1 (hsub t ht)
  have hmPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (S.m u) (massV S u) a t := by
    change IntervalPrimitive (S.m u)
      (fun s => (1 - 2 * S.m u s / S.r u s) * S.theta u s ^ 2 /
        (2 * S.lam u s)) a t
    exact h.mass_out u a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (S.r u) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hmAC : AbsolutelyContinuousOnInterval (S.m u) a b :=
    absolutely_continuous_on_interval_of_primitive hab hmPrim
  have hca : 0 < c * (a - u) := mul_pos hc (sub_pos.mpr hua)
  have hrbound : ∀ t ∈ uIcc a b, c * (a - u) ≤ |S.r u t| := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htU := hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv)
    have hr := (radius_lower h hlam) htU
    have hca' : c * (a - u) ≤ c * (t - u) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.1 u) hc.le
    rw [abs_of_pos (h.radius_pos (u, t) htU)]
    exact hca'.trans hr
  have hquot := hmAC.div_and_ae_deriv hrAC hca hrbound
  have hrDeriv : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (S.r u) t = S.lam u t := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hrPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hrPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hmDeriv : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (S.m u) t = massV S u t := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hmPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hmPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  filter_upwards [hquot.2, hrDeriv, hmDeriv] with t hq hr hm ht
  rw [hq (by simpa only [uIcc_of_le hab] using ht), hr ht, hm ht]

/-- The outgoing mass-radius quotient is absolutely continuous on every
compact off-axis segment. -/
theorem mass_div_radius_ac_out
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    AbsolutelyContinuousOnInterval
      (fun t => S.m u t / S.r u t) a b := by
  have hD := h.development
  have hrAC := radius_ac_on_outgoing hD h huv hua hab hbv
  have hmAC := mass_ac_on_outgoing hD h huv hua hab hbv
  have hca : 0 < c * (a - u) := mul_pos hc (sub_pos.mpr hua)
  have hrbound : ∀ t ∈ uIcc a b, c * (a - u) ≤ |S.r u t| := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htU := hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv)
    have hr := (radius_lower h hlam) htU
    have hca' : c * (a - u) ≤ c * (t - u) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.1 u) hc.le
    rw [abs_of_pos (h.radius_pos (u, t) htU)]
    exact hca'.trans hr
  exact (hmAC.div_and_ae_deriv hrAC hca hrbound).1

/-- The incoming mass-radius quotient is absolutely continuous on an
accessible compact segment strictly below its diagonal endpoint. -/
theorem mass_div_radius_ac_in
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun s => S.m s v / S.r s v) a b := by
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : inSeg v a t ⊆ U := by
    apply Set.Subset.trans _ hseg
    intro p hp
    have ⟨hpa, hpv⟩ : p.1 ∈ Icc a t ∧ p.2 = v := by
      simpa [inSeg] using hp
    have hpb : p.1 ∈ Icc a b := ⟨hpa.1, hpa.2.trans ht.2⟩
    simpa [inSeg] using And.intro hpb hpv
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r s v) (fun s => S.nu s v) a t :=
    h.radius_in v a t ht.1 (hsub t ht)
  have hmPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.m s v) (fun s => massInDensity S s v) a t := by
    change IntervalPrimitive (fun s => S.m s v)
      (fun s => (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 /
        (2 * S.nu s v)) a t
    exact h.mass_in v a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (fun s => S.r s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hmAC : AbsolutelyContinuousOnInterval (fun s => S.m s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hmPrim
  have hcb : 0 < c * (v - b) := mul_pos hc (sub_pos.mpr hbv)
  have hrbound : ∀ s ∈ uIcc a b, c * (v - b) ≤ |S.r s v| := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsU : (s, v) ∈ U := hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs, rfl⟩)
    have hr := (radius_lower h hlam) hsU
    have hcb' : c * (v - b) ≤ c * (v - s) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hs.2 v) hc.le
    rw [abs_of_pos (h.radius_pos (s, v) hsU)]
    exact hcb'.trans hr
  exact (hmAC.div_and_ae_deriv hrAC hcb hrbound).1

/-- The incoming mass-radius quotient has the quotient-rule derivative almost
everywhere on each accessible compact off-axis segment. -/
theorem mass_ratio_ae_deriv_in
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => S.m t v / S.r t v) s =
        (massInDensity S s v * S.r s v - S.m s v * S.nu s v) /
          S.r s v ^ 2 := by
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : inSeg v a t ⊆ U := by
    apply Set.Subset.trans _ hseg
    intro p hp
    have ⟨hpa, hpv⟩ : p.1 ∈ Icc a t ∧ p.2 = v := by
      simpa [inSeg] using hp
    have hpb : p.1 ∈ Icc a b := ⟨hpa.1, hpa.2.trans ht.2⟩
    simpa [inSeg] using And.intro hpb hpv
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r s v) (fun s => S.nu s v) a t :=
    h.radius_in v a t ht.1 (hsub t ht)
  have hmPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.m s v) (fun s => massInDensity S s v) a t := by
    change IntervalPrimitive (fun s => S.m s v)
      (fun s => (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 /
        (2 * S.nu s v)) a t
    exact h.mass_in v a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (fun s => S.r s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hmAC : AbsolutelyContinuousOnInterval (fun s => S.m s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hmPrim
  have hcb : 0 < c * (v - b) := mul_pos hc (sub_pos.mpr hbv)
  have hrbound : ∀ s ∈ uIcc a b, c * (v - b) ≤ |S.r s v| := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsU : (s, v) ∈ U := hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs, rfl⟩)
    have hr := (radius_lower h hlam) hsU
    have hcb' : c * (v - b) ≤ c * (v - s) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hs.2 v) hc.le
    rw [abs_of_pos (h.radius_pos (s, v) hsU)]
    exact hcb'.trans hr
  have hquot := hmAC.div_and_ae_deriv hrAC hcb hrbound
  have hrDeriv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => S.r t v) s = S.nu s v := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hrPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hrPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hmDeriv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => S.m t v) s = massInDensity S s v := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hmPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hmPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  filter_upwards [hquot.2, hrDeriv, hmDeriv] with s hq hr hm hs
  rw [hq (by simpa only [uIcc_of_le hab] using hs), hr hs, hm hs]

/-- On a compact outgoing segment away from the axis, the positive mass
gap ratio has a uniform positive lower bound. -/
theorem exists_mass_gap_ratio_lower_out
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc a b,
      δ ≤ 1 - 2 * S.m u t / S.r u t := by
  have hq := (mass_div_radius_ac_out h hc hlam) huv hua hab hbv
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hcont : ContinuousOn
      (fun t => 1 - 2 * S.m u t / S.r u t) (Icc a b) := by
    have hh := hconst.sub (hq.const_mul 2)
    have hh' : ContinuousOn (fun t => 1 - 2 * (S.m u t / S.r u t))
        (Icc a b) := by
      have hhh : ContinuousOn ((fun t : ℝ => (1 : ℝ)) -
          fun t => 2 * (S.m u t / S.r u t)) (Icc a b) := by
        simpa only [uIcc_of_le hab] using hh.continuousOn
      convert hhh using 1
    convert hh' using 1
    funext t
    ring
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, ⟨le_rfl, hab⟩⟩ hcont
  have ht₀U := h.development.outgoing_mem huv
    (hua.trans_le ht₀.1) (ht₀.2.trans hbv)
  have hδ : 0 < 1 - 2 * S.m u t₀ / S.r u t₀ := by
    have hh := (hmu _ ht₀U).2
    linarith
  exact ⟨_, hδ, fun t ht => hmin ht⟩

/-- The incoming mass gap has a positive minimum on each accessible compact
segment below the diagonal. -/
theorem exists_mass_gap_ratio_lower_in
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc a b,
      δ ≤ 1 - 2 * S.m s v / S.r s v := by
  have hq := (mass_div_radius_ac_in h hc hlam) hab hbv hseg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun s => 1 - 2 * S.m s v / S.r s v) a b := by
    convert hconst.sub (hq.const_mul 2) using 1
    funext s
    simp only [Pi.sub_apply]
    ring
  have hcont : ContinuousOn (fun s => 1 - 2 * S.m s v / S.r s v)
      (Icc a b) := by
    simpa only [uIcc_of_le hab] using hgap.continuousOn
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, ⟨le_rfl, hab⟩⟩ hcont
  have hs₀U : (s₀, v) ∈ U := hseg (by
    change s₀ ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs₀, rfl⟩)
  have hδ : 0 < 1 - 2 * S.m s₀ v / S.r s₀ v := by
    have := (hmu _ hs₀U).2
    linarith
  exact ⟨_, hδ, fun s hs => hmin hs⟩

end ChristodoulouBV.SourceInputsWeak

end
