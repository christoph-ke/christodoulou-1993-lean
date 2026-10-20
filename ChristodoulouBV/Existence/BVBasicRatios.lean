module

public import ChristodoulouBV.Existence.BVBasicAxisMean
public import ChristodoulouBV.Existence.BVBasicVariation
public import ChristodoulouBV.BVSolution.AxisIntegrals
import Mathlib.Tactic

/-!
# Weighted ratio estimates for the canonical limit

The contraction is proved on outgoing intervals beginning at the axis
and incoming intervals ending at the axis. These are the one-sided
carriers used in the four axis variation limits.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

private theorem primitive_congr_density {F g k : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : IntervalPrimitive F g a b) (he : EqOn g k (Icc a b)) :
    IntervalPrimitive F k a b := by
  have hae : ∀ᵐ t ∂volume, t ∈ Ι a b → g t = k t := by
    filter_upwards [] with t ht
    rw [uIoc_of_le hab] at ht
    exact he ⟨ht.1.le, ht.2⟩
  exact ⟨h.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae),
    h.2.trans (intervalIntegral.integral_congr_ae hae)⟩

private theorem primitive_reflect {F g : ℝ → ℝ} {a b : ℝ}
    (h : IntervalPrimitive F g (-b) (-a)) :
    IntervalPrimitive (fun t => F (-t)) (fun t => -g (-t)) a b := by
  have hi : IntervalIntegrable (fun t => g (-t)) volume a b := by
    have hh := h.1.comp_sub_left 0
    simpa only [zero_sub, neg_neg] using hh.symm
  refine ⟨hi.neg, ?_⟩
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg]
  linarith only [h.2]

/-- The two canonical normalized scalar derivatives have a uniform raw
amplitude bound. Its scalar offset is explicit; all coefficients are
universal. -/
theorem bv_ratio_amplitudes
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      |d.scalarRightFields.alpha p.1 p.2 / d.scalarRightFields.lam p.1 p.2| ≤
        12 * D.toReal + 2 * C ∧
      |d.scalarRightFields.beta p.1 p.2 / d.scalarRightFields.nu p.1 p.2| ≤
        12 * D.toReal + 2 * C := by
  intro p hp
  obtain ⟨_, _, _, _, _, hα, hβ⟩ := transport_shift_fields_limit h hD d hp
  have hraw := (alpha_beta_limit h d).2.2.2
  have hαb : |d.scalarRightFields.alpha p.1 p.2| ≤ 2 * D.toReal + C / 2 :=
    le_of_tendsto hα.abs (Eventually.of_forall (fun n =>
      (hraw _ (transport_shift_mem hp n)).1))
  have hβb : |d.scalarRightFields.beta p.1 p.2| ≤ 4 * D.toReal + 2 * C / 3 :=
    le_of_tendsto hβ.abs (Eventually.of_forall (fun n =>
      (hraw _ (transport_shift_mem hp n)).2))
  obtain ⟨hl0, _, hn0, _, _⟩ := scalar_right_fields_geometry h hD d p hp
  have hlpos : 0 < d.scalarRightFields.lam p.1 p.2 := by linarith only [hl0]
  have hnpos : 0 < -d.scalarRightFields.nu p.1 p.2 := by linarith only [hn0]
  have hC := (h 0).offset_nonneg
  have hD0 : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  constructor
  · rw [abs_div, abs_of_pos hlpos, div_le_iff₀ hlpos]
    have hm := mul_le_mul_of_nonneg_left hl0
      (show 0 ≤ 12 * D.toReal + 2 * C by positivity)
    nlinarith only [hm, hαb, hD0, hC]
  · rw [abs_div, abs_of_neg (neg_pos.mp hnpos), div_le_iff₀ hnpos]
    have hm := mul_le_mul_of_nonneg_left hn0
      (show 0 ≤ 12 * D.toReal + 2 * C by positivity)
    nlinarith only [hm, hβb]

private theorem ratio_bv_sections
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → BoundedVariationOn
      (fun v => d.scalarRightFields.alpha u v / d.scalarRightFields.lam u v) (Ioi u)) ∧
    ∀ v, 0 < v → BoundedVariationOn
      (fun u => d.scalarRightFields.beta u v / d.scalarRightFields.nu u v) (Ioo 0 v) := by
  obtain ⟨hout, hin⟩ := scalar_right_fields_three_term_tv h hD d
  have hV : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) < ∞ := by finiteness
  constructor
  · intro u hu
    exact ne_of_lt (((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (hout u hu))).trans_lt hV)
  · intro v hv
    exact ne_of_lt (((le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (hin v hv))).trans_lt hV)

/-- The outgoing BV form of Lemma 4.1 on every finite interval beginning
at the regular axis, including the initial outgoing ray. -/
theorem bv_outgoing_ratio_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b : ℝ} (hu : 0 ≤ u) (hub : u < b) :
    eVariationOn (d.scalarRightFields.phi u) (Ioo u b) ≤
      eVariationOn (fun v => d.scalarRightFields.alpha u v /
        d.scalarRightFields.lam u v) (Ioo u b) := by
  have H := transport_limit_is_solution h hD d
  have hgeom := scalar_right_fields_geometry h hD d
  have hα := (right_scalar_radius_primitive_limit h hD d).1
  have hr0 : Tendsto (fun v => d.radius (u, v)) (𝓝[>] u) (𝓝 0) := by
    have hc : Continuous (fun v : ℝ => d.radius (u, v)) :=
      d.radius_continuous.comp (continuous_const.prodMk continuous_id)
    have ht := hc.tendsto u
    rw [d.radius_axis h hu] at ht
    exact ht.mono_left inf_le_left
  have hN0 : Tendsto (fun v => d.scalarRadius (u, v)) (𝓝[>] u) (𝓝 0) := by
    have hc : Continuous (fun v : ℝ => d.scalarRadius (u, v)) :=
      d.scalarRadius_continuous.comp (continuous_const.prodMk continuous_id)
    have ht := hc.tendsto u
    rw [d.scalarRadius_axis h hu] at ht
    exact ht.mono_left inf_le_left
  apply bv_axis_weighted_variation_le
    (r := fun v => d.radius (u, v)) (N := fun v => d.scalarRadius (u, v))
    (w := d.scalarRightFields.lam u) (L := 1) (M := 12 * D.toReal + 2 * C)
    (fun v hv => d.radius_pos h ⟨hu, hv.1⟩) ?_
    (fun v hv => (bv_ratio_amplitudes h hD d (u, v) ⟨hu, hv.1⟩).1)
    (((ratio_bv_sections h hD d).1 u hu).mono Ioo_subset_Ioi_self) ?_ ?_ hr0 hN0
  · intro v hv
    obtain ⟨hl0, hl1, _⟩ := hgeom (u, v) ⟨hu, hv.1⟩
    have hl : 0 ≤ d.scalarRightFields.lam u v := by linarith only [hl0]
    exact ⟨hl, by rw [abs_of_nonneg hl]; linarith only [hl1]⟩
  · intro x hx y hy hxy
    exact H.radius_out u x y hxy (fun p hp => by
      rcases hp with ⟨rfl, hp⟩
      exact ⟨hu, hx.1.trans_le hp.1⟩)
  · intro x hx y hy hxy
    apply primitive_congr_density hxy
      (hα u x y hxy (fun p hp => by
        rcases hp with ⟨rfl, hp⟩
        exact ⟨hu, hx.1.trans_le hp.1⟩))
    intro v hv
    have hl := H.lam_pos (u, v) ⟨hu, hx.1.trans_le hv.1⟩
    change d.rightAlpha u v =
      d.rightLam u v * (d.rightAlpha u v / d.rightLam u v)
    exact (mul_div_cancel₀ _ hl.ne').symm

/-- The incoming BV form of Lemma 4.1 on every terminal interval ending
at the regular axis. Reflection keeps the exact open carrier. -/
theorem bv_incoming_ratio_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {l v : ℝ} (hl : 0 ≤ l) (hlv : l < v) :
    eVariationOn (fun u => d.scalarRightFields.phi u v) (Ioo l v) ≤
      eVariationOn (fun u => d.scalarRightFields.beta u v /
        d.scalarRightFields.nu u v) (Ioo l v) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hgeom := scalar_right_fields_geometry h hD d
  have hβ := (right_scalar_radius_primitive_limit h hD d).2
  have hmaps : MapsTo (fun t : ℝ => -t) (Ioo (-v) (-l)) (Ioo l v) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  have himage : (fun t : ℝ => -t) '' Ioo (-v) (-l) = Ioo l v := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hmaps hs
    · intro ht
      exact ⟨-t, by constructor <;> linarith only [ht.1, ht.2], neg_neg t⟩
  have hneg : AntitoneOn (fun t : ℝ => -t) (Ioo (-v) (-l)) :=
    fun _ _ _ _ hst => neg_le_neg hst
  have hr0 : Tendsto (fun t => d.radius (-t, v)) (𝓝[>] (-v)) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => d.radius (-t, v)) (-v) :=
      (d.radius_continuous.comp (continuous_neg.prodMk continuous_const)).continuousAt
    have ht : Tendsto (fun t : ℝ => d.radius (-t, v)) (𝓝[>] (-v))
        (𝓝 (d.radius (-(-v), v))) := hc.tendsto.mono_left inf_le_left
    rw [neg_neg, d.radius_axis h (hl.trans hlv.le)] at ht
    exact ht
  have hN0 : Tendsto (fun t => d.scalarRadius (-t, v)) (𝓝[>] (-v)) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => d.scalarRadius (-t, v)) (-v) :=
      (d.scalarRadius_continuous.comp (continuous_neg.prodMk continuous_const)).continuousAt
    have ht : Tendsto (fun t : ℝ => d.scalarRadius (-t, v)) (𝓝[>] (-v))
        (𝓝 (d.scalarRadius (-(-v), v))) := hc.tendsto.mono_left inf_le_left
    rw [neg_neg, d.scalarRadius_axis h (hl.trans hlv.le)] at ht
    exact ht
  have hqBV : BoundedVariationOn (fun t => S.beta (-t) v / S.nu (-t) v)
      (Ioo (-v) (-l)) := by
    apply ne_of_lt
    have he := eVariationOn.comp_eq_of_antitoneOn
      (fun u => S.beta u v / S.nu u v) (fun t : ℝ => -t) hneg
    simp only [Function.comp_def, himage] at he
    rw [he]
    exact ((ratio_bv_sections h hD d).2 v (hl.trans_lt hlv)).mono
      (fun _ ht => ⟨hl.trans_lt ht.1, ht.2⟩) |>.lt_top
  have hcore := bv_axis_weighted_variation_le
    (r := fun t => d.radius (-t, v)) (N := fun t => d.scalarRadius (-t, v))
    (w := fun t => -S.nu (-t) v) (q := fun t => S.beta (-t) v / S.nu (-t) v)
    (A := -v) (B := -l) (L := 1) (M := 12 * D.toReal + 2 * C)
    (fun t ht => d.radius_pos h ⟨hl.trans (hmaps ht).1.le, (hmaps ht).2⟩)
    (fun t ht => by
      obtain ⟨_, _, hn0, hn1, _⟩ := hgeom (-t, v)
        ⟨hl.trans (hmaps ht).1.le, (hmaps ht).2⟩
      have hn : 0 ≤ -S.nu (-t) v := by linarith only [hn0]
      exact ⟨hn, by rw [abs_of_nonneg hn]; linarith only [hn1]⟩)
    (fun t ht => (bv_ratio_amplitudes h hD d (-t, v)
      ⟨hl.trans (hmaps ht).1.le, (hmaps ht).2⟩).2) hqBV
    (fun x hx y hy hxy => primitive_reflect
      (H.radius_in v (-y) (-x) (neg_le_neg hxy) (fun p hp => by
        rcases hp with ⟨hp, rfl⟩
        exact ⟨(hl.trans (hmaps hy).1.le).trans hp.1,
          hp.2.trans_lt (hmaps hx).2⟩)))
    (fun x hx y hy hxy => by
      apply primitive_congr_density hxy
        (primitive_reflect (hβ v (-y) (-x) (neg_le_neg hxy) (fun p hp => by
          rcases hp with ⟨hp, rfl⟩
          exact ⟨(hl.trans (hmaps hy).1.le).trans hp.1,
            hp.2.trans_lt (hmaps hx).2⟩)))
      intro t ht
      have hp : (-t, v) ∈ globalDomain := by
        have ht' : t ∈ Ioo (-v) (-l) := ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
        exact ⟨hl.trans (hmaps ht').1.le, (hmaps ht').2⟩
      have hn0 := (hgeom (-t, v) hp).2.2.1
      have hn : S.nu (-t) v ≠ 0 := by linarith only [hn0]
      change -S.beta (-t) v = -S.nu (-t) v * (S.beta (-t) v / S.nu (-t) v)
      field_simp [hn]) hr0 hN0
  have hφeq := eVariationOn.comp_eq_of_antitoneOn
    (fun u => S.phi u v) (fun t : ℝ => -t) hneg
  have hqeq := eVariationOn.comp_eq_of_antitoneOn
    (fun u => S.beta u v / S.nu u v) (fun t : ℝ => -t) hneg
  simp only [Function.comp_def, himage] at hφeq hqeq
  rw [← hφeq, ← hqeq]
  exact hcore

/-- The scalar quotient variation estimates for the single canonical field record.
These sharp one-sided estimates control the scalar quotients; their
proof assumes no variation bound on `φ`. -/
theorem bv_ratio_bridge
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u b, 0 ≤ u → u < b →
      eVariationOn (d.scalarRightFields.phi u) (Ioo u b) ≤
        eVariationOn (fun v => d.scalarRightFields.alpha u v /
          d.scalarRightFields.lam u v) (Ioo u b)) ∧
    ∀ l v, 0 ≤ l → l < v →
      eVariationOn (fun u => d.scalarRightFields.phi u v) (Ioo l v) ≤
        eVariationOn (fun u => d.scalarRightFields.beta u v /
          d.scalarRightFields.nu u v) (Ioo l v) := by
  exact ⟨fun _ _ hu hub => bv_outgoing_ratio_variation h hD d hu hub,
    fun _ _ hl hlv => bv_incoming_ratio_variation h hD d hl hlv⟩

/-- The primitive-based contraction extends to the entire outgoing ray
by exhaustion. The initial ray `u = 0` is included. -/
theorem bv_global_outgoing_ratio_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u : ℝ} (hu : 0 ≤ u) :
    eVariationOn (d.scalarRightFields.phi u) (Ioi u) ≤
      eVariationOn (fun v => d.scalarRightFields.alpha u v /
        d.scalarRightFields.lam u v) (Ioi u) := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  apply iSup_le
  rintro ⟨x, y⟩
  apply iSup_le
  rintro ⟨_hx, hy, _hxy⟩
  calc
    _ ≤ eVariationOn (d.scalarRightFields.phi u) (Ioo u (y + 1)) :=
      eVariationOn.mono _ (fun t ht => ⟨ht.1, ht.2.2.trans_lt (lt_add_one y)⟩)
    _ ≤ eVariationOn (fun v => d.scalarRightFields.alpha u v /
        d.scalarRightFields.lam u v) (Ioo u (y + 1)) :=
      bv_outgoing_ratio_variation h hD d hu (hy.trans (lt_add_one y))
    _ ≤ _ := eVariationOn.mono _ Ioo_subset_Ioi_self

/-- Right continuity removes the lower endpoint cost in the incoming
contraction. This covers the complete frozen incoming section at `l = 0`. -/
theorem bv_incoming_ratio_variation_Ico
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {l v : ℝ} (hl : 0 ≤ l) (hlv : l < v) :
    eVariationOn (fun u => d.scalarRightFields.phi u v) (Ico l v) ≤
      eVariationOn (fun u => d.scalarRightFields.beta u v /
        d.scalarRightFields.nu u v) (Ico l v) := by
  have hp : (l, v) ∈ globalDomain := ⟨hl, hlv⟩
  have hn0 := (scalar_right_fields_geometry h hD d (l, v) hp).2.2.1
  have hn : d.scalarRightFields.nu l v ≠ 0 := by linarith only [hn0]
  have hq : ContinuousWithinAt
      (fun u => d.scalarRightFields.beta u v / d.scalarRightFields.nu u v) (Ici l) l :=
    ((right_scalar_derivatives_continuous h hD d (l, v) hp).2).div
      ((right_expansions_continuous h hD d (l, v) hp).2) hn
  have hphi : ContinuousWithinAt (fun u => d.scalarRightFields.phi u v) (Ici l) l := by
    have hN : Continuous (fun u : ℝ => d.scalarRadius (u, v)) :=
      d.scalarRadius_continuous.comp (continuous_id.prodMk continuous_const)
    have hR : Continuous (fun u : ℝ => d.radius (u, v)) :=
      d.radius_continuous.comp (continuous_id.prodMk continuous_const)
    exact (hN.continuousAt.div hR.continuousAt (d.radius_pos h hp).ne').continuousWithinAt
  rw [eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hlv hphi,
    eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hlv hq]
  exact bv_incoming_ratio_variation h hD d hl hlv

end ChristodoulouBV

end
