module

public import ChristodoulouBV.Uniqueness.MassHardy

/-!
# Finiteness of the outgoing weighted mass comparison

The bound is uniform in a compact top and uses only the original BV class.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The outgoing Hawking mass divided by squared axis distance is integrable
on each half-open characteristic. -/
theorem outgoing_mass_div_sq_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntegrableOn (fun t => S.m u t / (t - u) ^ 2) (Ioc u v) volume := by
  have huvlt := (h.solution.development.wedge huv).2
  have hmass := h.mass_density_integrable_on_axis_slice huv
  have hw := massV_div_distance_integrable h huv
  have hnonneg : ∀ t ∈ Ioc u v, 0 ≤ IsBVSolution.massV S u t := by
    intro t ht
    exact h.mass_density_nonneg h.solution.development
      (h.solution.development.outgoing_mem huv ht.1 ht.2)
  have hG := hardy_integrable_Ioc_nonneg huvlt hmass hw hnonneg
  apply hG.congr_fun _ measurableSet_Ioc
  intro t ht
  have hut := h.solution.development.outgoing_mem huv ht.1 ht.2
  change (∫ s in u..t, IsBVSolution.massV S u s) / (t - u) ^ 2 =
    S.m u t / (t - u) ^ 2
  rw [h.mass_out_integral_from_axis hut]

/-- The outgoing extended norm Γ is finite and uniformly bounded as the
compact top approaches the open comparison top. -/
theorem ComparisonData.Gamma_uniform_bound (D : ComparisonData) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ V, D.a < V → V < D.b →
      D.Gamma V ≤ ENNReal.ofReal M := by
  obtain ⟨M₁, hM₁, hbound₁⟩ := outgoing_mass_hardy_uniform D.h₁
  obtain ⟨M₂, hM₂, hbound₂⟩ := outgoing_mass_hardy_uniform D.h₂
  refine ⟨M₁ + M₂, add_nonneg hM₁ hM₂, ?_⟩
  intro V haV hVb
  unfold ComparisonData.Gamma
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have huv : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  have hp := D.hT huv
  have hInt₁ := outgoing_mass_div_sq_integrable D.h₁ hp.1
  have hInt₂ := outgoing_mass_div_sq_integrable D.h₂ hp.2
  have hMeas₁ : AEMeasurable
      (fun t => ENNReal.ofReal (D.S₁.m u t / (t - u) ^ 2))
      (volume.restrict (Ioc u V)) :=
    hInt₁.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpoint : ∀ t ∈ Ioc u V,
      ENNReal.ofReal (|D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
        ENNReal.ofReal (D.S₁.m u t / (t - u) ^ 2) +
          ENNReal.ofReal (D.S₂.m u t / (t - u) ^ 2) := by
    intro t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, ht.1, ht.2.trans_lt hVb⟩
    have htU := D.hT htT
    have hm₁ := D.h₁.mass_nonneg htU.1
    have hm₂ := D.h₂.mass_nonneg htU.2
    have hden : 0 ≤ (t - u) ^ 2 := sq_nonneg _
    have hsub : |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2 ≤
        D.S₁.m u t / (t - u) ^ 2 + D.S₂.m u t / (t - u) ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right
        (by simpa only [abs_of_nonneg hm₁, abs_of_nonneg hm₂] using
          (abs_sub (D.S₁.m u t) (D.S₂.m u t))) hden
    have hpos : 0 ≤ D.S₁.m u t / (t - u) ^ 2 := div_nonneg hm₁ hden
    rw [← ENNReal.ofReal_add hpos (div_nonneg hm₂ hden)]
    exact ENNReal.ofReal_le_ofReal hsub
  have hle : (∫⁻ t in Ioc u V, ENNReal.ofReal
      (|D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2)) ≤
      (∫⁻ t in Ioc u V, ENNReal.ofReal
        (D.S₁.m u t / (t - u) ^ 2)) +
      (∫⁻ t in Ioc u V, ENNReal.ofReal
        (D.S₂.m u t / (t - u) ^ 2)) := by
    calc
      _ ≤ ∫⁻ t in Ioc u V,
          (ENNReal.ofReal (D.S₁.m u t / (t - u) ^ 2) +
            ENNReal.ofReal (D.S₂.m u t / (t - u) ^ 2)) := by
              apply lintegral_mono_ae
              exact ae_restrict_of_forall_mem measurableSet_Ioc hpoint
      _ = _ := lintegral_add_left' hMeas₁ _
  calc
    (∫⁻ t in Ioc u V, ENNReal.ofReal
      (|D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2)) ≤
        (∫⁻ t in Ioc u V, ENNReal.ofReal
          (D.S₁.m u t / (t - u) ^ 2)) +
        (∫⁻ t in Ioc u V, ENNReal.ofReal
          (D.S₂.m u t / (t - u) ^ 2)) := hle
    _ ≤ ENNReal.ofReal M₁ + ENNReal.ofReal M₂ :=
      add_le_add (hbound₁ u V hp.1) (hbound₂ u V hp.2)
    _ = ENNReal.ofReal (M₁ + M₂) := (ENNReal.ofReal_add hM₁ hM₂).symm

/-- Incoming mass divided by squared terminal distance is integrable on the
full half-open characteristic supplied by a comparison triangle. -/
theorem incoming_mass_div_sq_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b) :
    IntegrableOn (fun s => S.m s v / (v - s) ^ 2) (Ico u v) volume := by
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U := by
    intro s hs
    exact hT ((mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  have hmass : IntegrableOn
      (fun s => -IsBVSolution.massInDensity S s v) (Ioc u v) volume :=
    (h.massInDensity_integrable_of_half_open_access huv.2.1 haccess).neg
  have hw : IntegrableOn
      (fun s => -IsBVSolution.massInDensity S s v / (v - s))
      (Ioc u v) volume := by
    have hh := negMassIn_div_distance_integrable h hT huv
    change Integrable _ (volume.restrict (Ico u v)) at hh
    change Integrable _ (volume.restrict (Ioc u v))
    rw [← restrict_Ico_eq_restrict_Ioc]
    exact hh
  have hnonneg : ∀ s ∈ Ico u v,
      0 ≤ -IsBVSolution.massInDensity S s v := by
    intro s hs
    linarith [h.massInDensity_nonpos (haccess s hs)]
  have hG := hardy_integrable_Ico_nonneg huv.2.1 hmass hw hnonneg
  have hcongr : IntegrableOn (fun s => S.m s v / (v - s) ^ 2)
      (Ioc u v) volume := by
    apply hG.congr_fun_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hsne hs
    have hsv : s < v := lt_of_le_of_ne hs.2 hsne
    have hst : (s, v) ∈ triangle a b :=
      (mem_triangle).2 ⟨huv.1.trans hs.1.le, hsv, huv.2.2⟩
    have hm := h.incoming_mass_axis_integral_of_triangle hT hst
    change (∫ t in s..v, -IsBVSolution.massInDensity S t v) / (v - s) ^ 2 =
      S.m s v / (v - s) ^ 2
    rw [intervalIntegral.integral_neg, hm]
  change Integrable (fun s => S.m s v / (v - s) ^ 2)
    (volume.restrict (Ico u v))
  rw [restrict_Ico_eq_restrict_Ioc]
  exact hcongr

/-- The incoming extended norm Γ* is finite with a bound independent of
the compact comparison top. -/
theorem ComparisonData.GammaStar_uniform_bound (D : ComparisonData) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ V, D.a < V → V < D.b →
      D.GammaStar V ≤ ENNReal.ofReal M := by
  obtain ⟨M₁, hM₁, hbound₁⟩ := incoming_mass_hardy_uniform D.h₁
    (fun p hp => (D.hT hp).1)
  obtain ⟨M₂, hM₂, hbound₂⟩ := incoming_mass_hardy_uniform D.h₂
    (fun p hp => (D.hT hp).2)
  refine ⟨M₁ + M₂, add_nonneg hM₁ hM₂, ?_⟩
  intro V haV hVb
  unfold ComparisonData.GammaStar
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hav : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hv.1, hv.2.trans hVb⟩
  have hp := D.hT hav
  have hInt₁ := incoming_mass_div_sq_integrable D.h₁
    (fun p hp => (D.hT hp).1) hav
  have hMeas₁ : AEMeasurable
      (fun s => ENNReal.ofReal (D.S₁.m s v / (v - s) ^ 2))
      (volume.restrict (Ico D.a v)) :=
    hInt₁.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpoint : ∀ s ∈ Ico D.a v,
      ENNReal.ofReal (|D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2) ≤
        ENNReal.ofReal (D.S₁.m s v / (v - s) ^ 2) +
          ENNReal.ofReal (D.S₂.m s v / (v - s) ^ 2) := by
    intro s hs
    have hsT : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1, hs.2, hav.2.2⟩
    have hsU := D.hT hsT
    have hm₁ := D.h₁.mass_nonneg hsU.1
    have hm₂ := D.h₂.mass_nonneg hsU.2
    have hden : 0 ≤ (v - s) ^ 2 := sq_nonneg _
    have hsub : |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2 ≤
        D.S₁.m s v / (v - s) ^ 2 + D.S₂.m s v / (v - s) ^ 2 := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right
        (by simpa only [abs_of_nonneg hm₁, abs_of_nonneg hm₂] using
          (abs_sub (D.S₁.m s v) (D.S₂.m s v))) hden
    have hpos : 0 ≤ D.S₁.m s v / (v - s) ^ 2 := div_nonneg hm₁ hden
    rw [← ENNReal.ofReal_add hpos (div_nonneg hm₂ hden)]
    exact ENNReal.ofReal_le_ofReal hsub
  have hle : (∫⁻ s in Ico D.a v, ENNReal.ofReal
      (|D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2)) ≤
      (∫⁻ s in Ico D.a v, ENNReal.ofReal
        (D.S₁.m s v / (v - s) ^ 2)) +
      (∫⁻ s in Ico D.a v, ENNReal.ofReal
        (D.S₂.m s v / (v - s) ^ 2)) := by
    calc
      _ ≤ ∫⁻ s in Ico D.a v,
          (ENNReal.ofReal (D.S₁.m s v / (v - s) ^ 2) +
            ENNReal.ofReal (D.S₂.m s v / (v - s) ^ 2)) := by
              apply lintegral_mono_ae
              exact ae_restrict_of_forall_mem measurableSet_Ico hpoint
      _ = _ := lintegral_add_left' hMeas₁ _
  have hbound₁' : (∫⁻ s in Ico D.a v, ENNReal.ofReal
      (D.S₁.m s v / (v - s) ^ 2)) ≤ ENNReal.ofReal M₁ := by
    rw [restrict_Ico_eq_restrict_Ioc]
    exact hbound₁ D.a v hav
  have hbound₂' : (∫⁻ s in Ico D.a v, ENNReal.ofReal
      (D.S₂.m s v / (v - s) ^ 2)) ≤ ENNReal.ofReal M₂ := by
    rw [restrict_Ico_eq_restrict_Ioc]
    exact hbound₂ D.a v hav
  calc
    (∫⁻ s in Ico D.a v, ENNReal.ofReal
      (|D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2)) ≤
        (∫⁻ s in Ico D.a v, ENNReal.ofReal
          (D.S₁.m s v / (v - s) ^ 2)) +
        (∫⁻ s in Ico D.a v, ENNReal.ofReal
          (D.S₂.m s v / (v - s) ^ 2)) := hle
    _ ≤ ENNReal.ofReal M₁ + ENNReal.ofReal M₂ :=
      add_le_add hbound₁' hbound₂'
    _ = ENNReal.ofReal (M₁ + M₂) := (ENNReal.ofReal_add hM₁ hM₂).symm

end ChristodoulouBV.Uniqueness

end
