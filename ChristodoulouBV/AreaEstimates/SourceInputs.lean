module

public import ChristodoulouBV.BVSolution.AxisIntegrals
public import ChristodoulouBV.BVSolution.IncomingLogCoefficient
public import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives

/-!
# Source estimates for the area argument

The two estimates (3.1a,b) use variation on open characteristic
segments. Local absolute continuity removes the endpoint contributions
from the half-open versions in the BV library. The incoming statement
uses an accessible augmented triangle.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV

/-- The value at the terminal point of an outgoing BV scalar slice contributes
no extra variation: the frozen local absolute-continuity clause fixes its
left trace. -/
theorem IsBVSolution.outgoing_scalar_variation_Ioc_eq_Ioo
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    eVariationOn (S.phi u) (Ioc u v) =
      eVariationOn (S.phi u) (Ioo u v) := by
  have hlt : u < v := (h.solution.development.wedge huv).2
  let a : ℝ := (u + v) / 2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hseg : outSeg u a v ⊆ U :=
    h.solution.development.out_seg_subset huv hua hav.le le_rfl
  have hAC := h.item3_ac_out u a v hav.le hseg
  have hcont : ContinuousOn (S.phi u) (Icc a v) := by
    simpa only [uIcc_of_le hav.le] using hAC.continuousOn
  have hleft : ContinuousWithinAt (S.phi u) (Iic v) v :=
    (continuousWithinAt_Icc_iff_Iic hav).mp
      (hcont.continuousWithinAt ⟨hav.le, le_rfl⟩)
  exact eVariationOn.Ioc_eq_Ioo_of_continuousWithinAt hlt hleft

/-- The value at the initial point of an incoming BV scalar slice contributes
no extra variation on an accessible characteristic. -/
theorem IsBVSolution.incoming_scalar_variation_Ico_eq_Ioo
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    eVariationOn (fun s => S.phi s v) (Ico u v) =
      eVariationOn (fun s => S.phi s v) (Ioo u v) := by
  let b : ℝ := (u + v) / 2
  have hub : u < b := by dsimp [b]; linarith
  have hbv : b < v := by dsimp [b]; linarith
  have hseg : inSeg v u b ⊆ U := by
    intro p hp
    rcases p with ⟨s, t⟩
    have hst : s ∈ Icc u b ∧ t = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
    rcases hst with ⟨hs, rfl⟩
    exact haccess s ⟨hs.1, hs.2.trans_lt hbv⟩
  have hAC := h.item3_ac_in v u b hub.le hseg
  have hcont : ContinuousOn (fun s => S.phi s v) (Icc u b) := by
    simpa only [uIcc_of_le hub.le] using hAC.continuousOn
  have hright : ContinuousWithinAt (fun s => S.phi s v) (Ici u) u :=
    (continuousWithinAt_Icc_iff_Ici hub).mp
      (hcont.continuousWithinAt ⟨le_rfl, hub.le⟩)
  exact eVariationOn.Ico_eq_Ioo_of_continuousWithinAt huv hright

/-- The outgoing mass-ratio bound (3.1a) for any finite majorant of the
outgoing scalar quotient on the solution region. -/
theorem source_mass_ratio_out_majorant
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ p ∈ U, |S.theta p.1 p.2 / S.lam p.1 p.2| ≤ M) :
    (∫ t in u..v,
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) ≤
      M * (eVariationOn (S.phi u) (Ioo u v)).toReal := by
  have hbound : ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M := by
    intro t ht
    exact hM (u, t) (h.solution.development.outgoing_mem huv ht.1 ht.2)
  rw [← h.outgoing_scalar_variation_Ioc_eq_Ioo huv]
  exact h.eq3_1a huv hbound

/-- The incoming mass-ratio bound (3.1b) for any finite majorant on a
complete incoming ray inside an accessible augmented triangle. -/
theorem source_mass_ratio_in_majorant
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v M : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b)
    (hM : ∀ p ∈ Uniqueness.triangle a b,
      |S.zeta p.1 p.2 / S.nu p.1 p.2| ≤ M) :
    -(∫ s in u..v,
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) ≤
      M * (eVariationOn (fun s => S.phi s v) (Ioo u v)).toReal := by
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U :=
    IsBVSolution.incoming_axis_access_of_triangle hT huv
  have hbound : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ M := by
    intro s hs
    exact hM (s, v) ((Uniqueness.mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  rw [← h.incoming_scalar_variation_Ico_eq_Ioo huv.2.1 haccess]
  exact h.eq3_1b huv.2.1 haccess hbound

/-- The outgoing quotient has a finite supremum on the development. -/
theorem IsBVSolution.bddAbove_theta_div_lam
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    BddAbove {x : ℝ | ∃ p ∈ U,
      x = |S.theta p.1 p.2 / S.lam p.1 p.2|} := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  let B : ℝ := max h.item5.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B / c, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  have hpLam : 0 < S.lam p.1 p.2 := h.solution.lam_pos p hp
  have hpLo : c ≤ S.lam p.1 p.2 := hlam p hp
  have hpTheta : |S.theta p.1 p.2| ≤ B := h.theta_abs_le_global_variation hp
  rw [abs_div, abs_of_pos hpLam]
  apply (div_le_div_iff₀ hpLam hc).2
  exact (mul_le_mul_of_nonneg_right hpTheta hc.le).trans
    (mul_le_mul_of_nonneg_left hpLo hB)

/-- Equation (3.1a) with the exact supremum over the solution region and
open-segment total variation. -/
theorem source_mass_ratio_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    (∫ t in u..v,
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) ≤
      sSup {x : ℝ | ∃ p ∈ U,
        x = |S.theta p.1 p.2 / S.lam p.1 p.2|} *
        (eVariationOn (S.phi u) (Ioo u v)).toReal := by
  apply source_mass_ratio_out_majorant h huv
  intro p hp
  exact le_csSup h.bddAbove_theta_div_lam ⟨p, hp, rfl⟩

/-- The incoming quotient has a finite supremum on any accessible triangle.
The global BV variation controls `ζ` from its terminal axis trace there. -/
theorem IsBVSolution.bddAbove_zeta_div_nu_on_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b : ℝ} (hT : Uniqueness.triangle a b ⊆ U) :
    BddAbove {x : ℝ | ∃ p ∈ Uniqueness.triangle a b,
      x = |S.zeta p.1 p.2 / S.nu p.1 p.2|} := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  let B : ℝ := max h.item5.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B / c, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  have hpNu : S.nu p.1 p.2 < 0 :=
    (h.nu_le_neg_lower hc hlam (hT hp)).trans_lt (neg_lt_zero.mpr hc)
  have hpLo : c ≤ |S.nu p.1 p.2| := by
    rw [abs_of_neg hpNu]
    linarith only [h.nu_le_neg_lower hc hlam (hT hp)]
  have hpZeta : |S.zeta p.1 p.2| ≤ B :=
    h.zeta_abs_le_global_variation_of_triangle hT hp
  have hpNuPos : 0 < |S.nu p.1 p.2| := hc.trans_le hpLo
  rw [abs_div]
  apply (div_le_div_iff₀ hpNuPos hc).2
  exact (mul_le_mul_of_nonneg_right hpZeta hc.le).trans
    (mul_le_mul_of_nonneg_left hpLo hB)

/-- Equation (3.1b), with the supremum over the accessible solution triangle
and the paper's open incoming variation interval. -/
theorem source_mass_ratio_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    -(∫ s in u..v,
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) ≤
      sSup {x : ℝ | ∃ p ∈ Uniqueness.triangle a b,
        x = |S.zeta p.1 p.2 / S.nu p.1 p.2|} *
        (eVariationOn (fun s => S.phi s v) (Ioo u v)).toReal := by
  have hM : ∀ p ∈ Uniqueness.triangle a b,
      |S.zeta p.1 p.2 / S.nu p.1 p.2| ≤
      sSup {x : ℝ | ∃ p ∈ Uniqueness.triangle a b,
        x = |S.zeta p.1 p.2 / S.nu p.1 p.2|} := by
    intro p hp
    exact le_csSup (h.bddAbove_zeta_div_nu_on_triangle hT) ⟨p, hp, rfl⟩
  exact source_mass_ratio_in_majorant h hT huv hM

/-- Reduced regular-axis signs and traces used in Sections 3 and 4. The
incoming traces are asserted only when a full triangle reaches the axis. -/
theorem source_axis_signs
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    (∃ c : ℝ, 0 < c ∧ ∀ u v, (u, v) ∈ U →
      c ≤ S.lam u v ∧ S.nu u v ≤ -c ∧ 0 ≤ S.m u v ∧
      0 ≤ 2 * S.m u v / S.r u v ∧ 2 * S.m u v / S.r u v < 1) ∧
    (∀ u v, (u, v) ∈ U →
      Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) ∧
      Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ))) ∧
    (∀ a b u v, Uniqueness.triangle a b ⊆ U →
      (u, v) ∈ Uniqueness.triangle a b →
      Tendsto (fun s => S.r s v) (𝓝[<] v) (𝓝 (0 : ℝ)) ∧
      Tendsto (fun s => S.m s v) (𝓝[<] v) (𝓝 (0 : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
    refine ⟨c, hc, ?_⟩
    intro u v huv
    exact ⟨hlam (u, v) huv, h.nu_le_neg_lower hc hlam huv,
      h.mass_nonneg huv, (h.mass_ratio_bounds huv).1,
      (h.mass_ratio_bounds huv).2⟩
  · intro u v huv
    exact ⟨h.radius_tendsto_axis_out huv, h.mass_tendsto_axis_out huv⟩
  · intro a b u v hT huv
    exact ⟨h.incoming_radius_axis_trace_of_triangle hT huv,
      h.incoming_mass_axis_trace_of_triangle hT huv⟩

end ChristodoulouBV

end
