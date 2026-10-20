module

public import ChristodoulouBV.AreaEstimates.AnalyticArea
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Monotone exhaustion of a finite endpoint triangle

The analytic area is a measure, so a uniform bound on every strict finite
cutoff passes to the open terminal triangle.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- Translating the values of a smooth planar map by a fixed vector leaves
its analytic Jacobian area unchanged on an open domain. -/
theorem smoothAnalyticArea_eq_of_eq_add_const_on_open
    (F G : ℝ × ℝ → ℝ × ℝ) (c : ℝ × ℝ)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hEq : ∀ p ∈ U, F p = G p + c) :
    smoothAnalyticArea F U = smoothAnalyticArea G U := by
  rw [smooth_analytic_area F hU.measurableSet,
    smooth_analytic_area G hU.measurableSet]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
  have hlocal : F =ᶠ[𝓝 p] (fun q => G q + c) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hEq q hq
  rw [hlocal.fderiv_eq, fderiv_add_const]

/-- Analytic area depends only on the restriction of a map to an open
carrier, including its ordinary Jacobian there. -/
theorem smoothAnalyticArea_eq_of_eqOn_open
    (F G : ℝ × ℝ → ℝ × ℝ)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hEq : EqOn F G U) :
    smoothAnalyticArea F U = smoothAnalyticArea G U := by
  rw [smooth_analytic_area F hU.measurableSet,
    smooth_analytic_area G hU.measurableSet]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
  have hlocal : F =ᶠ[𝓝 p] G := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hEq hq
  rw [hlocal.fderiv_eq]

/-- Uniform analytic-area bounds on all finite terminal cutoffs pass to the
open endpoint. The value at cutoff zero is included to simplify the countable
exhaustion and is automatically zero for the analytic area measure. -/
theorem s6_analytic_area_exhaustion_bound (F : ℝ × ℝ → ℝ × ℝ)
    {vStar : ℝ} (hStar : 0 < vStar) {C : ℝ≥0∞}
    (hcutoff : ∀ b : ℝ, 0 ≤ b → b < vStar →
      smoothAnalyticArea F (openCoordTriangle 0 b) ≤ C) :
    smoothAnalyticArea F (openCoordTriangle 0 vStar) ≤ C := by
  let b : ℕ → ℝ := fun n => vStar * (1 - 1 / ((n : ℝ) + 1))
  let E : ℕ → Set (ℝ × ℝ) := fun n => openCoordTriangle 0 (b n)
  have hden (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hInv (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) :=
    div_pos one_pos (hden n)
  have hbnonneg (n : ℕ) : 0 ≤ b n := by
    dsimp [b]
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (hden n)).mpr
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    exact mul_nonneg hStar.le (sub_nonneg.mpr hle)
  have hblt (n : ℕ) : b n < vStar := by
    dsimp [b]
    have hpos := hInv n
    nlinarith [mul_pos hStar hpos]
  have hbmono : Monotone b := by
    intro n m hnm
    dsimp [b]
    have hdenle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hinvle : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (hden n) hdenle
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hinvle 1) hStar.le
  have hEmono : Monotone E := by
    intro n m hnm p hp
    simp only [E, openCoordTriangle, mem_ofPred_eq] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le (hbmono hnm)⟩
  have hbTendsto : Tendsto b atTop (𝓝 vStar) := by
    have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hsub : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
        atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hdiv)
    simpa only [b, mul_one] using (tendsto_const_nhds.mul hsub)
  have hUnion : (⋃ n : ℕ, E n) = openCoordTriangle 0 vStar := by
    apply Set.Subset.antisymm
    · intro p hpUnion
      obtain ⟨n, hp⟩ := Set.mem_iUnion.mp hpUnion
      simp only [E, openCoordTriangle, mem_ofPred_eq] at hp ⊢
      exact ⟨hp.1, hp.2.1, hp.2.2.trans (hblt n)⟩
    · intro p hp
      simp only [openCoordTriangle, mem_ofPred_eq] at hp
      have hev : ∀ᶠ n : ℕ in atTop, p.2 < b n :=
        hbTendsto.eventually (eventually_gt_nhds hp.2.2)
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      simp only [E, openCoordTriangle, mem_ofPred_eq]
      exact ⟨hp.1, hp.2.1, hn n le_rfl⟩
  have hlimit : Tendsto (fun n => smoothAnalyticArea F (E n)) atTop
      (𝓝 (smoothAnalyticArea F (openCoordTriangle 0 vStar))) := by
    simpa only [hUnion, Function.comp_def] using
      (MeasureTheory.tendsto_measure_iUnion_atTop (μ := smoothAnalyticArea F)
        hEmono)
  exact le_of_tendsto hlimit
    (Filter.Eventually.of_forall fun n => hcutoff (b n) (hbnonneg n) (hblt n))

/-- A uniform mass bound on all strict initial intervals passes to a finite
terminal interval by monotone exhaustion. This is used for the complete
initial logarithmic residual, including its quadratic correction. -/
theorem s6_measure_interval_exhaustion_bound (μ : Measure ℝ)
    {vStar : ℝ} (hStar : 0 < vStar) {C : ℝ≥0∞}
    (hcutoff : ∀ b : ℝ, 0 ≤ b → b < vStar → μ (Ioo (0 : ℝ) b) ≤ C) :
    μ (Ioo (0 : ℝ) vStar) ≤ C := by
  let b : ℕ → ℝ := fun n => vStar * (1 - 1 / ((n : ℝ) + 1))
  let E : ℕ → Set ℝ := fun n => Ioo (0 : ℝ) (b n)
  have hden (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hInv (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) :=
    div_pos one_pos (hden n)
  have hbnonneg (n : ℕ) : 0 ≤ b n := by
    dsimp [b]
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (hden n)).mpr
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    exact mul_nonneg hStar.le (sub_nonneg.mpr hle)
  have hblt (n : ℕ) : b n < vStar := by
    dsimp [b]
    have hpos := hInv n
    nlinarith [mul_pos hStar hpos]
  have hbmono : Monotone b := by
    intro n m hnm
    dsimp [b]
    have hdenle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hinvle : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (hden n) hdenle
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hinvle 1) hStar.le
  have hEmono : Monotone E := by
    intro n m hnm x hx
    exact ⟨hx.1, hx.2.trans_le (hbmono hnm)⟩
  have hbTendsto : Tendsto b atTop (𝓝 vStar) := by
    have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hsub : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
        atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hdiv)
    simpa only [b, mul_one] using (tendsto_const_nhds.mul hsub)
  have hUnion : (⋃ n : ℕ, E n) = Ioo (0 : ℝ) vStar := by
    apply Set.Subset.antisymm
    · intro x hxUnion
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hxUnion
      exact ⟨hx.1, hx.2.trans (hblt n)⟩
    · intro x hx
      have hev : ∀ᶠ n : ℕ in atTop, x < b n :=
        hbTendsto.eventually (eventually_gt_nhds hx.2)
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
      exact Set.mem_iUnion.mpr ⟨n, ⟨hx.1, hn n le_rfl⟩⟩
  have hlimit : Tendsto (fun n => μ (E n)) atTop
      (𝓝 (μ (Ioo (0 : ℝ) vStar))) := by
    simpa only [hUnion, Function.comp_def] using
      (MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ) hEmono)
  exact le_of_tendsto hlimit
    (Filter.Eventually.of_forall fun n => hcutoff (b n) (hbnonneg n) (hblt n))

/-- Uniform bounds on finite cutoffs imply integrability at the terminal
interval once measurability on that interval has been established locally. -/
theorem s6_integrableOn_of_uniform_cutoff
    (f : ℝ → ℝ) {vStar : ℝ} (hStar : 0 < vStar) {C : ℝ≥0∞}
    (hC : C ≠ ∞)
    (hMeas : AEStronglyMeasurable f
      (volume.restrict (Ioo (0 : ℝ) vStar)))
    (hNonneg : ∀ v : ℝ, 0 ≤ f v)
    (hBound : ∀ b : ℝ, 0 ≤ b → b < vStar →
      (∫⁻ v in Ioo (0 : ℝ) b, ENNReal.ofReal (f v)) ≤ C) :
    IntegrableOn f (Ioo (0 : ℝ) vStar) := by
  let μ := volume.withDensity (fun v => ENNReal.ofReal (f v))
  have hMass : μ (Ioo (0 : ℝ) vStar) ≤ C :=
    s6_measure_interval_exhaustion_bound μ hStar (by
      intro b hb hbStar
      simpa only [μ, withDensity_apply _ measurableSet_Ioo] using
        hBound b hb hbStar)
  have hFinite : (∫⁻ v in Ioo (0 : ℝ) vStar,
      ENNReal.ofReal (f v)) ≠ ∞ := by
    rw [← withDensity_apply _ measurableSet_Ioo]
    exact ne_top_of_le_ne_top hC hMass
  exact (lintegral_ofReal_ne_top_iff_integrable hMeas
    (Filter.Eventually.of_forall fun v => hNonneg v)).mp hFinite

/-- Measurability on every strict initial interval glues to the open terminal
interval. The exhaustion is countable, as required for almost everywhere
measurability. -/
theorem s6_aestronglyMeasurable_of_cutoffs
    (f : ℝ → ℝ) {vStar : ℝ} (hStar : 0 < vStar)
    (hLocal : ∀ b : ℝ, 0 ≤ b → b < vStar →
      AEStronglyMeasurable f (volume.restrict (Ioo (0 : ℝ) b))) :
    AEStronglyMeasurable f
      (volume.restrict (Ioo (0 : ℝ) vStar)) := by
  let b : ℕ → ℝ := fun n => vStar * (1 - 1 / ((n : ℝ) + 1))
  have hden (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hbnonneg (n : ℕ) : 0 ≤ b n := by
    dsimp [b]
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (hden n)).mpr
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    exact mul_nonneg hStar.le (sub_nonneg.mpr hle)
  have hblt (n : ℕ) : b n < vStar := by
    dsimp [b]
    have hpos : 0 < 1 / ((n : ℝ) + 1) := div_pos one_pos (hden n)
    nlinarith [mul_pos hStar hpos]
  have hbTendsto : Tendsto b atTop (𝓝 vStar) := by
    have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hsub : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
        atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hdiv)
    simpa only [b, mul_one] using (tendsto_const_nhds.mul hsub)
  have hUnion : (⋃ n : ℕ, Ioo (0 : ℝ) (b n)) = Ioo (0 : ℝ) vStar := by
    apply Set.Subset.antisymm
    · intro x hxUnion
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hxUnion
      exact ⟨hx.1, hx.2.trans (hblt n)⟩
    · intro x hx
      have hev : ∀ᶠ n : ℕ in atTop, x < b n :=
        hbTendsto.eventually (eventually_gt_nhds hx.2)
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
      exact Set.mem_iUnion.mpr ⟨n, ⟨hx.1, hn n le_rfl⟩⟩
  rw [← hUnion]
  exact aestronglyMeasurable_iUnion_iff.mpr
    (fun n => hLocal (b n) (hbnonneg n) (hblt n))

/-- One-dimensional nonnegative integrals are invariant under the physical
dilation after including the Jacobian factor. No measurability assumption on
the integrand is needed, because dilation is a measurable embedding. -/
theorem s6_lintegral_dilation (f : ℝ → ℝ≥0∞)
    {a u : ℝ} (ha : 0 < a) :
    (∫⁻ v in Ioo (u / a) 1,
      ENNReal.ofReal a * f (a * v)) =
      ∫⁻ v in Ioo u a, f v := by
  let g : ℝ → ℝ := fun v => a * v
  have hg : MeasurableEmbedding g :=
    (Homeomorph.mulLeft₀ a ha.ne').measurableEmbedding
  have hpre : g ⁻¹' Ioo u a = Ioo (u / a) 1 := by
    ext v
    change (u < a * v ∧ a * v < a) ↔ (u / a < v ∧ v < 1)
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨(div_lt_iff₀ ha).mpr (by simpa [mul_comm] using h₁), ?_⟩
      have h := (lt_div_iff₀ ha).mpr (by simpa [mul_comm] using h₂)
      simpa only [div_self ha.ne'] using h
    · rintro ⟨h₁, h₂⟩
      refine ⟨by simpa [mul_comm] using (div_lt_iff₀ ha).mp h₁, ?_⟩
      have h : v < a / a := by simpa only [div_self ha.ne'] using h₂
      simpa [mul_comm] using (lt_div_iff₀ ha).mp h
  have hmap : (volume.restrict (Ioo (u / a) 1)).map g =
      ENNReal.ofReal |a⁻¹| • (volume.restrict (Ioo u a)) := by
    rw [← hpre, ← Measure.restrict_map hg.measurable measurableSet_Ioo]
    rw [Real.map_volume_mul_left ha.ne', Measure.restrict_smul]
  have hfactor : ENNReal.ofReal a * ENNReal.ofReal |a⁻¹| = 1 := by
    rw [abs_of_pos (inv_pos.mpr ha), ← ENNReal.ofReal_mul ha.le,
      mul_inv_cancel₀ ha.ne']
    norm_num
  calc
    (∫⁻ v in Ioo (u / a) 1,
        ENNReal.ofReal a * f (a * v)) =
      ENNReal.ofReal a * ∫⁻ v in Ioo (u / a) 1, f (g v) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal a * ∫⁻ v, f v ∂
        ((volume.restrict (Ioo (u / a) 1)).map g) := by
      rw [hg.lintegral_map]
    _ = ENNReal.ofReal a *
        (ENNReal.ofReal |a⁻¹| * ∫⁻ v in Ioo u a, f v) := by
      rw [hmap, lintegral_smul_measure]
      rfl
    _ = ∫⁻ v in Ioo u a, f v := by
      rw [← mul_assoc, hfactor, one_mul]

/-- Uniform measure bounds on terminal cutoffs of `(u,vStar)` pass to the
entire open interval. -/
theorem s6_measure_terminal_exhaustion_bound (μ : Measure ℝ)
    {u vStar : ℝ} (huStar : u < vStar) {C : ℝ≥0∞}
    (hcutoff : ∀ a : ℝ, u ≤ a → a < vStar → μ (Ioo u a) ≤ C) :
    μ (Ioo u vStar) ≤ C := by
  let a : ℕ → ℝ := fun n =>
    u + (vStar - u) * (1 - 1 / ((n : ℝ) + 1))
  have hden (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hInv (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) :=
    div_pos one_pos (hden n)
  have haLow (n : ℕ) : u ≤ a n := by
    dsimp [a]
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (hden n)).mpr
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    nlinarith [mul_nonneg (sub_pos.mpr huStar).le
      (sub_nonneg.mpr hle)]
  have haTop (n : ℕ) : a n < vStar := by
    dsimp [a]
    nlinarith [mul_pos (sub_pos.mpr huStar) (hInv n)]
  have haMono : Monotone a := by
    intro n m hnm
    dsimp [a]
    have hdenle : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hinvle : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (hden n) hdenle
    simpa only [add_comm u] using add_le_add_left
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hinvle 1)
        (sub_pos.mpr huStar).le) u
  have haTendsto : Tendsto a atTop (𝓝 vStar) := by
    have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hsub : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
        atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hdiv)
    have h : Tendsto
        (fun n : ℕ => u + (vStar - u) *
          (1 - 1 / ((n : ℝ) + 1)))
        atTop (𝓝 (u + (vStar - u) * 1)) :=
      (tendsto_const_nhds (x := u)).add
        ((tendsto_const_nhds (x := vStar - u)).mul hsub)
    simpa only [a, mul_one, show u + (vStar - u) = vStar by ring] using h
  have hE : Monotone (fun n : ℕ => Ioo u (a n)) := by
    intro n m hnm x hx
    exact ⟨hx.1, hx.2.trans_le (haMono hnm)⟩
  have hUnion : (⋃ n : ℕ, Ioo u (a n)) = Ioo u vStar := by
    apply Set.Subset.antisymm
    · intro x hxUnion
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hxUnion
      exact ⟨hx.1, hx.2.trans (haTop n)⟩
    · intro x hx
      have hev : ∀ᶠ n : ℕ in atTop, x < a n :=
        haTendsto.eventually (eventually_gt_nhds hx.2)
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
      exact Set.mem_iUnion.mpr ⟨n, ⟨hx.1, hn n le_rfl⟩⟩
  have hlimit : Tendsto (fun n => μ (Ioo u (a n))) atTop
      (𝓝 (μ (Ioo u vStar))) := by
    simpa only [hUnion, Function.comp_def] using
      (MeasureTheory.tendsto_measure_iUnion_atTop (μ := μ) hE)
  exact le_of_tendsto hlimit
    (Filter.Eventually.of_forall fun n => hcutoff (a n) (haLow n) (haTop n))

/-- A uniform variation bound on every strict terminal cutoff controls the
variation on the open terminal interval. Every finite ordered sample lies
below one cutoff. -/
theorem s6_variation_terminal_exhaustion_bound (f : ℝ → ℝ)
    {u vStar : ℝ} (_huStar : u < vStar) {C : ℝ≥0∞}
    (hcutoff : ∀ a : ℝ, u < a → a < vStar →
      eVariationOn f (Ioo u a) ≤ C) :
    eVariationOn f (Ioo u vStar) ≤ C := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  obtain ⟨hp₁, hp₂, _⟩ := hp
  obtain ⟨a, hp₂a, haStar⟩ := exists_between hp₂.2
  have hua : u < a := hp₂.1.trans hp₂a
  have hSub : Ioo u vStar ∩ Icc p.1 p.2 ⊆ Ioo u a := by
    intro x hx
    exact ⟨hx.1.1, hx.2.2.trans_lt hp₂a⟩
  exact (eVariationOn.mono f hSub).trans (hcutoff a hua haStar)

end ChristodoulouBV

end
