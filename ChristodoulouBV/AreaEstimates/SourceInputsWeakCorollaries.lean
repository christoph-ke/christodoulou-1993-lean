module

public import ChristodoulouBV.AreaEstimates.SourceInputsWeakBounds

/-!
# Full BV corollaries of the weak source estimates

Each original statement is recovered by one application of the weakened API.
These checks do not enter the canonical existence limit construction.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The original full-BV statement follows from the explicit weak premises. -/
theorem source_mass_ratio_out_majorant_via_weak
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ p ∈ U, |S.theta p.1 p.2 / S.lam p.1 p.2| ≤ M) :
    (∫ t in u..v,
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) ≤
      M * (eVariationOn (S.phi u) (Ioo u v)).toReal :=
  SourceInputsWeak.source_mass_ratio_out_majorant h.solution h.lam_bounded_below.choose_spec.1
    h.lam_bounded_below.choose_spec.2
    ⟨h.exists_uniform_radius_upper.choose, h.exists_uniform_radius_upper.choose_spec.2⟩
    (fun _ hp => h.mass_ratio_bounds hp) h.item3_ac_out
    (fun u => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.1 u))
    (fun u => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)) huv hM

/-- The original full-BV statement follows from the explicit weak premises. -/
theorem source_mass_ratio_in_majorant_via_weak
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v M : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b)
    (hM : ∀ p ∈ Uniqueness.triangle a b,
      |S.zeta p.1 p.2 / S.nu p.1 p.2| ≤ M) :
    -(∫ s in u..v,
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) ≤
      M * (eVariationOn (fun s => S.phi s v) (Ioo u v)).toReal :=
  SourceInputsWeak.source_mass_ratio_in_majorant h.solution h.lam_bounded_below.choose_spec.1
    h.lam_bounded_below.choose_spec.2
    (fun _ hp => h.nu_le_neg_lower h.lam_bounded_below.choose_spec.1
      h.lam_bounded_below.choose_spec.2 hp)
    ⟨h.exists_uniform_radius_upper.choose, h.exists_uniform_radius_upper.choose_spec.2⟩
    (fun _ hp => h.mass_ratio_bounds hp) h.item3_ac_in
    (fun v => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.2 v))
    (fun v => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.2 v)) hT huv hM

/-- The original full-BV statement follows from the explicit weak premises. -/
theorem mass_ratio_tendsto_zero_axis_out_via_weak
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun t => 2 * S.m u t / S.r u t) (𝓝[>] u) (𝓝 (0 : ℝ)) :=
  SourceInputsWeak.mass_ratio_tendsto_zero_axis_out h.solution h.lam_bounded_below.choose_spec.1
    h.lam_bounded_below.choose_spec.2
    ⟨h.exists_uniform_radius_upper.choose, h.exists_uniform_radius_upper.choose_spec.2⟩
    (fun _ hp => h.mass_ratio_bounds hp) h.item3_ac_out
    (fun u => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.1 u))
    (fun u => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)) huv

/-- The original full-BV statement follows from the explicit weak premises. -/
theorem mass_ratio_tendsto_zero_axis_in_of_half_open_access_via_weak
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    Tendsto (fun w => 2 * S.m w v / S.r w v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) :=
  SourceInputsWeak.mass_ratio_tendsto_zero_axis_in_of_half_open_access h.solution
    h.lam_bounded_below.choose_spec.1
    h.lam_bounded_below.choose_spec.2
    (fun _ hp => h.nu_le_neg_lower h.lam_bounded_below.choose_spec.1
      h.lam_bounded_below.choose_spec.2 hp)
    ⟨h.exists_uniform_radius_upper.choose, h.exists_uniform_radius_upper.choose_spec.2⟩
    (fun _ hp => h.mass_ratio_bounds hp) h.item3_ac_in
    (fun v => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.2 v))
    (fun v => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.2 v)) huv haccess

end ChristodoulouBV.IsBVSolution

end
