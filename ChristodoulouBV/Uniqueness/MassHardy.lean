module

public import ChristodoulouBV.Uniqueness.MassWeights

/-!
# Hardy control of mass integrals with an excluded axis endpoint

The frozen mass density is defined at the axis even though the axis is outside
the solution domain. Hardy's theorem uses only its values on the half-open
characteristic, so we replace the unused endpoint value by zero.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The initial-endpoint Hardy inequality for a density nonnegative on the
half-open interval. Its arbitrary value at the excluded endpoint is ignored. -/
theorem hardy_lintegral_le_weighted_Ioc
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioc a b) volume)
    (hw : IntegrableOn (fun t => f t / (t - a)) (Ioc a b) volume)
    (hfn : ∀ t ∈ Ioc a b, 0 ≤ f t) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal
      ((∫ s in a..t, f s) / (t - a) ^ 2)) ≤
      ENNReal.ofReal (∫ t in a..b, f t / (t - a)) := by
  let g : ℝ → ℝ := fun t => if t = a then 0 else f t
  have hEq : EqOn f g (Ioc a b) := by
    intro t ht
    simp [g, ne_of_gt ht.1]
  have hfi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (hf.congr_fun hEq measurableSet_Ioc)
  have hwEq : EqOn (fun t => f t / (t - a))
      (fun t => g t / (t - a)) (Ioc a b) := by
    intro t ht
    change f t / (t - a) = g t / (t - a)
    rw [hEq ht]
  have hwi : IntervalIntegrable (fun t => g t / (t - a)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (hw.congr_fun hwEq measurableSet_Ioc)
  have hgn : ∀ t ∈ Icc a b, 0 ≤ g t := by
    intro t ht
    by_cases hta : t = a
    · simp [g, hta]
    · have hat : a < t := lt_of_le_of_ne ht.1 (by
        intro he
        exact hta he.symm)
      simpa [g, hta] using hfn t ⟨hat, ht.2⟩
  have hinner (t : ℝ) (ht : t ∈ Ioc a b) :
      (∫ s in a..t, f s) = ∫ s in a..t, g s := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
    intro s hs
    exact hEq ⟨hs.1, hs.2.le.trans ht.2⟩
  have hleft : (∫⁻ t in Ioc a b, ENNReal.ofReal
      ((∫ s in a..t, f s) / (t - a) ^ 2)) =
      ∫⁻ t in Ioc a b, ENNReal.ofReal
        ((∫ s in a..t, g s) / (t - a) ^ 2) := by
    apply lintegral_congr_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
      change ENNReal.ofReal ((∫ s in a..t, f s) / (t - a) ^ 2) =
        ENNReal.ofReal ((∫ s in a..t, g s) / (t - a) ^ 2)
      rw [hinner t ht])
  have hweight : (∫ t in a..b, g t / (t - a)) =
      ∫ t in a..b, f t / (t - a) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro t ht
    change g t / (t - a) = f t / (t - a)
    rw [← hEq ⟨ht.1, ht.2.le⟩]
  have htotal : 0 ≤ ∫ s in a..b, g s :=
    intervalIntegral.integral_nonneg hab.le hgn
  rw [hleft, ← hweight, intervalIntegral.lintegral_ofReal_integral_div_sq_eq
    hab hfi hwi hgn]
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_self _ (div_nonneg htotal (sub_nonneg.mpr hab.le))

/-- The initial-endpoint Hardy kernel is integrable when the density is
nonnegative only off the excluded endpoint. -/
theorem hardy_integrable_Ioc_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioc a b) volume)
    (hw : IntegrableOn (fun t => f t / (t - a)) (Ioc a b) volume)
    (hfn : ∀ t ∈ Ioc a b, 0 ≤ f t) :
    IntegrableOn (fun t => (∫ s in a..t, f s) / (t - a) ^ 2)
      (Ioc a b) volume := by
  let g : ℝ → ℝ := fun t => if t = a then 0 else f t
  have hEq : EqOn f g (Ioc a b) := by
    intro t ht
    simp [g, ne_of_gt ht.1]
  have hfi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (hf.congr_fun hEq measurableSet_Ioc)
  have hwEq : EqOn (fun t => f t / (t - a))
      (fun t => g t / (t - a)) (Ioc a b) := by
    intro t ht
    change f t / (t - a) = g t / (t - a)
    rw [hEq ht]
  have hwi : IntervalIntegrable (fun t => g t / (t - a)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (hw.congr_fun hwEq measurableSet_Ioc)
  have hgn : ∀ t ∈ Icc a b, 0 ≤ g t := by
    intro t ht
    by_cases hta : t = a
    · simp [g, hta]
    · have hat : a < t := lt_of_le_of_ne ht.1 (by
        intro he
        exact hta he.symm)
      simpa [g, hta] using hfn t ⟨hat, ht.2⟩
  have hGI := intervalIntegral.integrableOn_integral_div_sq hab hfi hwi hgn
  apply hGI.congr_fun _ measurableSet_Ioc
  intro t ht
  change (∫ s in a..t, g s) / (t - a) ^ 2 =
    (∫ s in a..t, f s) / (t - a) ^ 2
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
  intro s hs
  exact (hEq ⟨hs.1, hs.2.le.trans ht.2⟩).symm

/-- The outgoing Hardy mass integral has one uniform finite bound on every
axis-to-point ray of a BV solution. -/
theorem outgoing_mass_hardy_uniform
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, (u, v) ∈ U →
      (∫⁻ t in Ioc u v, ENNReal.ofReal
        (S.m u t / (t - u) ^ 2)) ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM, hbound⟩ := massV_div_distance_integral_uniform h
  refine ⟨M, hM, ?_⟩
  intro u v huv
  have huvlt := (h.solution.development.wedge huv).2
  have hmass := h.mass_density_integrable_on_axis_slice huv
  have hw := massV_div_distance_integrable h huv
  have hnonneg : ∀ t ∈ Ioc u v, 0 ≤ IsBVSolution.massV S u t := by
    intro t ht
    exact h.mass_density_nonneg h.solution.development
      (h.solution.development.outgoing_mem huv ht.1 ht.2)
  have hhardy := hardy_lintegral_le_weighted_Ioc huvlt hmass hw hnonneg
  have hleft : (∫⁻ t in Ioc u v, ENNReal.ofReal
      (S.m u t / (t - u) ^ 2)) =
      ∫⁻ t in Ioc u v, ENNReal.ofReal
        ((∫ s in u..t, IsBVSolution.massV S u s) / (t - u) ^ 2) := by
    apply lintegral_congr_ae
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
      have hut := h.solution.development.outgoing_mem huv ht.1 ht.2
      change ENNReal.ofReal (S.m u t / (t - u) ^ 2) =
        ENNReal.ofReal ((∫ s in u..t, IsBVSolution.massV S u s) / (t - u) ^ 2)
      rw [h.mass_out_integral_from_axis hut])
  rw [hleft]
  exact hhardy.trans (ENNReal.ofReal_le_ofReal (hbound u v huv))

/-- The terminal-endpoint Hardy inequality when the density is nonnegative
on the half-open incoming interval and its unused terminal value is arbitrary. -/
theorem hardy_lintegral_le_weighted_Ico
    {f : ℝ → ℝ} {a v : ℝ} (hav : a < v)
    (hf : IntegrableOn f (Ioc a v) volume)
    (hw : IntegrableOn (fun s => f s / (v - s)) (Ioc a v) volume)
    (hfn : ∀ s ∈ Ico a v, 0 ≤ f s) :
    (∫⁻ u in Ioc a v, ENNReal.ofReal
      ((∫ s in u..v, f s) / (v - u) ^ 2)) ≤
      ENNReal.ofReal (∫ s in a..v, f s / (v - s)) := by
  let g : ℝ → ℝ := fun s => if s = v then 0 else f s
  have hEq : EqOn f g (Ico a v) := by
    intro s hs
    simp [g, ne_of_lt hs.2]
  have hfiIco : IntegrableOn f (Ico a v) volume := by
    change Integrable f (volume.restrict (Ico a v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact hf
  have hwiIco : IntegrableOn (fun s => f s / (v - s))
      (Ico a v) volume := by
    change Integrable (fun s => f s / (v - s)) (volume.restrict (Ico a v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact hw
  have hfi : IntervalIntegrable g volume a v :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hav.le).2
      (hfiIco.congr_fun hEq measurableSet_Ico)
  have hwEq : EqOn (fun s => f s / (v - s))
      (fun s => g s / (v - s)) (Ico a v) := by
    intro s hs
    change f s / (v - s) = g s / (v - s)
    rw [hEq hs]
  have hwi : IntervalIntegrable (fun s => g s / (v - s)) volume a v :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hav.le).2
      (hwiIco.congr_fun hwEq measurableSet_Ico)
  have hgn : ∀ s ∈ Icc a v, 0 ≤ g s := by
    intro s hs
    by_cases hsv : s = v
    · simp [g, hsv]
    · have hsvlt : s < v := lt_of_le_of_ne hs.2 hsv
      simpa [g, hsv] using hfn s ⟨hs.1, hsvlt⟩
  have hinner (u : ℝ) (hu : u ∈ Ico a v) :
      (∫ s in u..v, f s) = ∫ s in u..v, g s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hu.2.le
    intro s hs
    exact hEq ⟨hu.1.trans hs.1.le, hs.2⟩
  have hleft : (∫⁻ u in Ioc a v, ENNReal.ofReal
      ((∫ s in u..v, f s) / (v - u) ^ 2)) =
      ∫⁻ u in Ioc a v, ENNReal.ofReal
        ((∫ s in u..v, g s) / (v - u) ^ 2) := by
    apply lintegral_congr_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ u : ℝ ∂volume, u ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with u hne hu
    have huv : u < v := lt_of_le_of_ne hu.2 hne
    change ENNReal.ofReal ((∫ s in u..v, f s) / (v - u) ^ 2) =
      ENNReal.ofReal ((∫ s in u..v, g s) / (v - u) ^ 2)
    rw [hinner u ⟨hu.1.le, huv⟩]
  have hweight : (∫ s in a..v, g s / (v - s)) =
      ∫ s in a..v, f s / (v - s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hav.le
    intro s hs
    change g s / (v - s) = f s / (v - s)
    rw [← hEq ⟨hs.1.le, hs.2⟩]
  have htotal : 0 ≤ ∫ s in a..v, g s :=
    intervalIntegral.integral_nonneg hav.le hgn
  rw [hleft, ← hweight,
    intervalIntegral.lintegral_ofReal_integral_div_sq_eq_terminal
      hav hfi hwi hgn]
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_self _ (div_nonneg htotal (sub_nonneg.mpr hav.le))

/-- The terminal Hardy kernel is integrable under the corresponding
half-open density conditions. -/
theorem hardy_integrable_Ico_nonneg
    {f : ℝ → ℝ} {a v : ℝ} (hav : a < v)
    (hf : IntegrableOn f (Ioc a v) volume)
    (hw : IntegrableOn (fun s => f s / (v - s)) (Ioc a v) volume)
    (hfn : ∀ s ∈ Ico a v, 0 ≤ f s) :
    IntegrableOn (fun u => (∫ s in u..v, f s) / (v - u) ^ 2)
      (Ioc a v) volume := by
  let g : ℝ → ℝ := fun s => if s = v then 0 else f s
  have hEq : EqOn f g (Ico a v) := by
    intro s hs
    simp [g, ne_of_lt hs.2]
  have hfiIco : IntegrableOn f (Ico a v) volume := by
    change Integrable f (volume.restrict (Ico a v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact hf
  have hwiIco : IntegrableOn (fun s => f s / (v - s))
      (Ico a v) volume := by
    change Integrable (fun s => f s / (v - s)) (volume.restrict (Ico a v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact hw
  have hfi : IntervalIntegrable g volume a v :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hav.le).2
      (hfiIco.congr_fun hEq measurableSet_Ico)
  have hwEq : EqOn (fun s => f s / (v - s))
      (fun s => g s / (v - s)) (Ico a v) := by
    intro s hs
    change f s / (v - s) = g s / (v - s)
    rw [hEq hs]
  have hwi : IntervalIntegrable (fun s => g s / (v - s)) volume a v :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hav.le).2
      (hwiIco.congr_fun hwEq measurableSet_Ico)
  have hgn : ∀ s ∈ Icc a v, 0 ≤ g s := by
    intro s hs
    by_cases hsv : s = v
    · simp [g, hsv]
    · have hsvlt : s < v := lt_of_le_of_ne hs.2 hsv
      simpa [g, hsv] using hfn s ⟨hs.1, hsvlt⟩
  have hGI := intervalIntegral.integrableOn_integral_div_sq_terminal
    hav hfi hwi hgn
  apply hGI.congr_fun_ae
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ v := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with u hne hu
  have huv : u < v := lt_of_le_of_ne hu.2 hne
  change (∫ s in u..v, g s) / (v - u) ^ 2 =
    (∫ s in u..v, f s) / (v - u) ^ 2
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le huv.le
  intro s hs
  exact (hEq ⟨hu.1.le.trans hs.1.le, hs.2⟩).symm

/-- The incoming Hardy mass integral has one uniform finite bound on a full
augmented triangle. -/
theorem incoming_mass_hardy_uniform
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b : ℝ} (hT : triangle a b ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, (u, v) ∈ triangle a b →
      (∫⁻ s in Ioc u v, ENNReal.ofReal
        (S.m s v / (v - s) ^ 2)) ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM, hbound⟩ := negMassIn_div_distance_integral_uniform h hT
  refine ⟨M, hM, ?_⟩
  intro u v huv
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
    have hsU := haccess s hs
    linarith [h.massInDensity_nonpos hsU]
  have hhardy := hardy_lintegral_le_weighted_Ico huv.2.1 hmass hw hnonneg
  have hleft : (∫⁻ s in Ioc u v, ENNReal.ofReal
      (S.m s v / (v - s) ^ 2)) =
      ∫⁻ s in Ioc u v, ENNReal.ofReal
        ((∫ t in s..v, -IsBVSolution.massInDensity S t v) / (v - s) ^ 2) := by
    apply lintegral_congr_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hsne hs
    have hsv : s < v := lt_of_le_of_ne hs.2 hsne
    have hst : (s, v) ∈ triangle a b :=
      (mem_triangle).2 ⟨huv.1.trans hs.1.le, hsv, huv.2.2⟩
    have hm := h.incoming_mass_axis_integral_of_triangle hT hst
    change ENNReal.ofReal (S.m s v / (v - s) ^ 2) =
      ENNReal.ofReal
        ((∫ t in s..v, -IsBVSolution.massInDensity S t v) / (v - s) ^ 2)
    rw [intervalIntegral.integral_neg]
    rw [hm]
  rw [hleft]
  exact hhardy.trans (ENNReal.ofReal_le_ofReal (hbound u v huv))

end ChristodoulouBV.Uniqueness

end
