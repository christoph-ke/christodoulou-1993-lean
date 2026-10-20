module

public import ChristodoulouBV.Uniqueness.LocalContraction
public import ChristodoulouBV.Uniqueness.Rescaling
import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives

/-!
# Axis localization for BV uniqueness

Item 4 of the frozen BV class supplies one future scale on which both scalar
variations are small. The affine chart carries the augmented triangle and its
initial edge to the unit comparison triangle.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A quantity tending to zero from the right is bounded by any positive
extended-real threshold at every sufficiently small positive scale. -/
private theorem eventually_le_of_tendsto_zero
    {f : ℝ → ENNReal} (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 < h → h < η → f h ≤ ENNReal.ofReal ε := by
  have hpos : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hev : {h : ℝ | f h < ENNReal.ofReal ε} ∈ 𝓝[>] (0 : ℝ) :=
    hf (Iio_mem_nhds hpos)
  obtain ⟨η, hη, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  exact ⟨η, hη, fun h hh hhη => (hsub ⟨hh, hhη⟩).le⟩

/-- The outgoing variation on every augmented point is bounded by item 4's
future outgoing envelope at the same scale. -/
theorem outgoing_variation_le_axis_envelope
    {U : Set (ℝ × ℝ)} {S : Fields} {a h u v : ℝ}
    (hT : triangle a (a + h) ⊆ U)
    (huv : (u, v) ∈ triangle a (a + h)) :
    eVariationOn (S.phi u) (Ioo u v) ≤
      ⨆ δ ∈ Ico (0 : ℝ) h,
        eVariationOn (S.phi (a + δ))
          {w | w ∈ Ioo (a + δ) (a + h) ∧ (a + δ, w) ∈ U} := by
  obtain ⟨hau, huvlt, hvh⟩ := mem_triangle.mp huv
  have hδ : u - a ∈ Ico (0 : ℝ) h := ⟨sub_nonneg.mpr hau, by linarith⟩
  have hsub : Ioo u v ⊆
      {w | w ∈ Ioo (a + (u - a)) (a + h) ∧
        (a + (u - a), w) ∈ U} := by
    intro w hw
    have haw : a + (u - a) = u := by ring
    rw [haw]
    exact ⟨⟨hw.1, hw.2.trans hvh⟩,
      hT ⟨hau, hw.1, hw.2.trans hvh⟩⟩
  calc
    eVariationOn (S.phi u) (Ioo u v) ≤
        eVariationOn (S.phi (a + (u - a)))
          {w | w ∈ Ioo (a + (u - a)) (a + h) ∧
            (a + (u - a), w) ∈ U} := by
              simpa only [show a + (u - a) = u by ring] using
                eVariationOn.mono (S.phi u) hsub
    _ ≤ _ := by
      apply le_iSup_of_le (u - a)
      apply le_iSup_of_le hδ
      exact le_rfl

/-- The incoming variation on every augmented point is bounded by item 4's
future incoming envelope at the same scale. -/
theorem incoming_variation_le_axis_envelope
    {U : Set (ℝ × ℝ)} {S : Fields} {a h u v : ℝ}
    (hT : triangle a (a + h) ⊆ U)
    (huv : (u, v) ∈ triangle a (a + h)) :
    eVariationOn (fun s => S.phi s v) (Ioo u v) ≤
      ⨆ δ ∈ Ioc (0 : ℝ) h,
        eVariationOn (fun s => S.phi s (a + δ))
          {w | w ∈ Ioo a (a + δ) ∧ (w, a + δ) ∈ U} := by
  obtain ⟨hau, huvlt, hvh⟩ := mem_triangle.mp huv
  have hδ : v - a ∈ Ioc (0 : ℝ) h := ⟨by linarith, by linarith⟩
  have hsub : Ioo u v ⊆
      {w | w ∈ Ioo a (a + (v - a)) ∧
        (w, a + (v - a)) ∈ U} := by
    intro w hw
    have hav : a + (v - a) = v := by ring
    rw [hav]
    exact ⟨⟨hau.trans_lt hw.1, hw.2⟩,
      hT ⟨hau.trans hw.1.le, hw.2, hvh⟩⟩
  calc
    eVariationOn (fun s => S.phi s v) (Ioo u v) ≤
        eVariationOn (fun s => S.phi s (a + (v - a)))
          {w | w ∈ Ioo a (a + (v - a)) ∧
            (w, a + (v - a)) ∈ U} := by
              simpa only [show a + (v - a) = v by ring] using
                eVariationOn.mono (fun s => S.phi s v) hsub
    _ ≤ _ := by
      apply le_iSup_of_le (v - a)
      apply le_iSup_of_le hδ
      exact le_rfl

/-- The source outgoing `X` on a full local triangle is bounded by item 4's
future outgoing envelope, including the limiting initial slice. -/
theorem localX_le_axis_envelope
    {U : Set (ℝ × ℝ)} {S : Fields} {a h : ℝ}
    (hT : triangle a (a + h) ⊆ U) :
    localX S a (a + h) ≤
      ⨆ δ ∈ Ico (0 : ℝ) h,
        eVariationOn (S.phi (a + δ))
          {v | v ∈ Ioo (a + δ) (a + h) ∧ (a + δ, v) ∈ U} := by
  unfold localX
  refine iSup_le fun u => iSup_le fun hu => ?_
  have hδ : u - a ∈ Ico (0 : ℝ) h := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hsub : Ioo u (a + h) ⊆
      {v | v ∈ Ioo (a + (u - a)) (a + h) ∧
        (a + (u - a), v) ∈ U} := by
    intro v hv
    have hau : a + (u - a) = u := by ring
    rw [hau]
    exact ⟨hv, hT ⟨hu.1.le, hv.1, hv.2⟩⟩
  calc
    eVariationOn (S.phi u) (Ioo u (a + h)) ≤
        eVariationOn (S.phi (a + (u - a)))
          {v | v ∈ Ioo (a + (u - a)) (a + h) ∧
            (a + (u - a), v) ∈ U} := by
              simpa only [show a + (u - a) = u by ring] using
                eVariationOn.mono (S.phi u) hsub
    _ ≤ _ := by
      apply le_iSup_of_le (u - a)
      apply le_iSup_of_le hδ
      exact le_rfl

/-- The source incoming `Y` on a full local triangle is bounded by item 4's
future incoming envelope. -/
theorem localY_le_axis_envelope
    {U : Set (ℝ × ℝ)} {S : Fields} {a h : ℝ}
    (hT : triangle a (a + h) ⊆ U) :
    localY S a (a + h) ≤
      ⨆ δ ∈ Ioc (0 : ℝ) h,
        eVariationOn (fun u => S.phi u (a + δ))
          {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ U} := by
  unfold localY
  refine iSup_le fun v => iSup_le fun hv => ?_
  have hδ : v - a ∈ Ioc (0 : ℝ) h := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hsub : Ioo a v ⊆
      {u | u ∈ Ioo a (a + (v - a)) ∧
        (u, a + (v - a)) ∈ U} := by
    intro u hu
    have hav : a + (v - a) = v := by ring
    rw [hav]
    exact ⟨hu, hT ⟨hu.1.le, hu.2, hv.2⟩⟩
  calc
    eVariationOn (fun u => S.phi u v) (Ioo a v) ≤
        eVariationOn (fun u => S.phi u (a + (v - a)))
          {u | u ∈ Ioo a (a + (v - a)) ∧
            (u, a + (v - a)) ∈ U} := by
              simpa only [show a + (v - a) = v by ring] using
                eVariationOn.mono (fun u => S.phi u v) hsub
    _ ≤ _ := by
      apply le_iSup_of_le (v - a)
      apply le_iSup_of_le hδ
      exact le_rfl

/-- Item 4 controls both local scalar variations, at every smaller positive
scale for which the full augmented triangle lies in the development. The
same bound also holds on every point's open characteristic segments. -/
theorem axis_variations_small
    {U : Set (ℝ × ℝ)} {S : Fields} {a ε : ℝ}
    (hS : IsBVSolution U S) (ha : a ∈ adjacentAxis U) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, 0 < h → h < η →
      triangle a (a + h) ⊆ U →
      localX S a (a + h) ≤ ENNReal.ofReal ε ∧
      localY S a (a + h) ≤ ENNReal.ofReal ε ∧
      ∀ u v, (u, v) ∈ triangle a (a + h) →
        eVariationOn (S.phi u) (Ioo u v) ≤ ENNReal.ofReal ε ∧
        eVariationOn (fun s => S.phi s v) (Ioo u v) ≤ ENNReal.ofReal ε := by
  obtain ⟨ηo, hηo, ho⟩ :=
    eventually_le_of_tendsto_zero (hS.item4 a ha).future_outgoing hε
  obtain ⟨ηi, hηi, hi⟩ :=
    eventually_le_of_tendsto_zero (hS.item4 a ha).future_incoming hε
  refine ⟨min ηo ηi, lt_min hηo hηi, ?_⟩
  intro h hh hhη hT
  have hO := ho h hh (hhη.trans_le (min_le_left _ _))
  have hI := hi h hh (hhη.trans_le (min_le_right _ _))
  refine ⟨(localX_le_axis_envelope hT).trans hO,
    (localY_le_axis_envelope hT).trans hI, ?_⟩
  intro u v huv
  exact ⟨(outgoing_variation_le_axis_envelope hT huv).trans hO,
    (incoming_variation_le_axis_envelope hT huv).trans hI⟩

/-- On a full augmented triangle, scalar absolute continuity removes the
included endpoint cost in the two scalar axis-variation conventions. The
axis endpoint itself is never put in a closed segment. -/
theorem characteristic_variations_eq_open
    {U : Set (ℝ × ℝ)} {S : Fields} {a h u v : ℝ}
    (hS : IsBVSolution U S)
    (hT : triangle a (a + h) ⊆ U)
    (huv : (u, v) ∈ triangle a (a + h)) :
    eVariationOn (S.phi u) (Ioc u v) =
      eVariationOn (S.phi u) (Ioo u v) ∧
    eVariationOn (fun s => S.phi s v) (Ico u v) =
      eVariationOn (fun s => S.phi s v) (Ioo u v) := by
  obtain ⟨hau, huvlt, hvh⟩ := mem_triangle.mp huv
  let t : ℝ := (u + v) / 2
  have hut : u < t := by dsimp [t]; linarith
  have htv : t < v := by dsimp [t]; linarith
  have hout : AbsolutelyContinuousOnInterval (S.phi u) t v :=
    hS.item3_ac_out u t v htv.le
      ((outSeg_subset_triangle hau hut htv.le hvh).trans hT)
  have hin : AbsolutelyContinuousOnInterval (fun s => S.phi s v) u t :=
    hS.item3_ac_in v u t hut.le
      ((inSeg_subset_triangle hau hut.le htv hvh).trans hT)
  have hout_mem : Icc t v ∈ 𝓝[Iic v] v := by
    apply mem_of_superset
      (inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htv))
        self_mem_nhdsWithin)
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hin_mem : Icc u t ∈ 𝓝[Ici u] u := by
    apply mem_of_superset
      (inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hut)))
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have hout_on : ContinuousOn (S.phi u) (Icc t v) := by
    simpa only [uIcc_of_le htv.le] using hout.continuousOn
  have hin_on : ContinuousOn (fun s => S.phi s v) (Icc u t) := by
    simpa only [uIcc_of_le hut.le] using hin.continuousOn
  have hout_cont : ContinuousWithinAt (S.phi u) (Iic v) v :=
    (hout_on.continuousWithinAt ⟨htv.le, le_rfl⟩).mono_of_mem_nhdsWithin hout_mem
  have hin_cont : ContinuousWithinAt (fun s => S.phi s v) (Ici u) u :=
    (hin_on.continuousWithinAt ⟨le_rfl, hut.le⟩).mono_of_mem_nhdsWithin hin_mem
  exact ⟨(eVariationOn.Ioc_eq_Ioo_of_continuousWithinAt huvlt hout_cont),
    (eVariationOn.Ico_eq_Ioo_of_continuousWithinAt huvlt hin_cont)⟩

/-- A future common overlap witness and item 4 give one augmented triangle
with all four local scalar variations bounded by the same prescribed positive
threshold. The threshold is fixed before the final radius. -/
theorem common_axis_variations_small
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields} {a A V ε : ℝ}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hp : (A, V) ∈ U₁ ∩ U₂) (ha : 0 ≤ a) (haA : a < A)
    (hdata : ∀ v, (a, v) ∈ U₁ ∩ U₂ →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v)
    (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧
      triangle a (a + h) ⊆ U₁ ∩ U₂ ∧
      (∀ v ∈ Ioo a (a + h),
        S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) ∧
      localX S₁ a (a + h) ≤ ENNReal.ofReal ε ∧
      localY S₁ a (a + h) ≤ ENNReal.ofReal ε ∧
      localX S₂ a (a + h) ≤ ENNReal.ofReal ε ∧
      localY S₂ a (a + h) ≤ ENNReal.ofReal ε ∧
      (∀ u v, (u, v) ∈ triangle a (a + h) →
        eVariationOn (S₁.phi u) (Ioo u v) ≤ ENNReal.ofReal ε ∧
        eVariationOn (fun s => S₁.phi s v) (Ioo u v) ≤ ENNReal.ofReal ε ∧
        eVariationOn (S₂.phi u) (Ioo u v) ≤ ENNReal.ofReal ε ∧
        eVariationOn (fun s => S₂.phi s v) (Ioo u v) ≤ ENNReal.ofReal ε) := by
  have hAV : A < V := (h₁.solution.development.wedge hp.1).2
  have hT₀ : triangle a A ⊆ U₁ ∩ U₂ :=
    common_triangle h₁.solution.development h₂.solution.development hp
      ha le_rfl hAV.le
  have hmid : (a, (a + A) / 2) ∈ triangle a A := by
    exact ⟨le_rfl, by linarith, by linarith⟩
  have haxis₁ : a ∈ adjacentAxis U₁ :=
    h₁.solution.development.axis_mem (hT₀ hmid).1
  have haxis₂ : a ∈ adjacentAxis U₂ :=
    h₂.solution.development.axis_mem (hT₀ hmid).2
  obtain ⟨η₁, hη₁, hsmall₁⟩ := axis_variations_small h₁ haxis₁ hε
  obtain ⟨η₂, hη₂, hsmall₂⟩ := axis_variations_small h₂ haxis₂ hε
  let h : ℝ := min (A - a) (min η₁ η₂) / 2
  have hh : 0 < h := by
    dsimp [h]
    exact half_pos (lt_min (sub_pos.mpr haA) (lt_min hη₁ hη₂))
  have hA : a + h ≤ A := by
    dsimp [h]
    have hh₁ := min_le_left (A - a) (min η₁ η₂)
    linarith
  have hη₁' : h < η₁ := by
    dsimp [h]
    have hh₁ := (min_le_right (A - a) (min η₁ η₂)).trans (min_le_left η₁ η₂)
    linarith
  have hη₂' : h < η₂ := by
    dsimp [h]
    have hh₂ := (min_le_right (A - a) (min η₁ η₂)).trans (min_le_right η₁ η₂)
    linarith
  have hT : triangle a (a + h) ⊆ U₁ ∩ U₂ :=
    common_triangle h₁.solution.development h₂.solution.development hp
      ha hA (hA.trans hAV.le)
  obtain ⟨hX₁, hY₁, hpoint₁⟩ :=
    hsmall₁ h hh hη₁' (fun p hpt => (hT hpt).1)
  obtain ⟨hX₂, hY₂, hpoint₂⟩ :=
    hsmall₂ h hh hη₂' (fun p hpt => (hT hpt).2)
  refine ⟨h, hh, hT, ?_, hX₁, hY₁, hX₂, hY₂, ?_⟩
  · intro v hv
    exact hdata v (hT (initial_edge_of_triangle hv.1 hv.2))
  · intro u v huv
    obtain ⟨ho₁, hi₁⟩ := hpoint₁ u v huv
    obtain ⟨ho₂, hi₂⟩ := hpoint₂ u v huv
    exact ⟨ho₁, hi₁, ho₂, hi₂⟩

/-- After choosing one common axis scale, both normalized BV solutions live
on developments containing the augmented unit triangle. Their initial data
agree there and all four source variations satisfy (3.2). -/
theorem common_axis_normalized_variations_small
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields} {a A V ε : ℝ}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hp : (A, V) ∈ U₁ ∩ U₂) (ha : 0 ≤ a) (haA : a < A)
    (hdata : ∀ v, (a, v) ∈ U₁ ∩ U₂ →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v)
    (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ triangle a (a + h) ⊆ U₁ ∩ U₂ ∧
      IsBVSolution (rescaledDomain U₁ a h) (rescaledFields S₁ a h) ∧
      IsBVSolution (rescaledDomain U₂ a h) (rescaledFields S₂ a h) ∧
      triangle 0 1 ⊆ rescaledDomain U₁ a h ∩ rescaledDomain U₂ a h ∧
      (∀ v ∈ Ioo 0 1,
        (rescaledFields S₁ a h).r 0 v = (rescaledFields S₂ a h).r 0 v ∧
        (rescaledFields S₁ a h).phi 0 v = (rescaledFields S₂ a h).phi 0 v) ∧
      localX (rescaledFields S₁ a h) 0 1 ≤ ENNReal.ofReal ε ∧
      localY (rescaledFields S₁ a h) 0 1 ≤ ENNReal.ofReal ε ∧
      localX (rescaledFields S₂ a h) 0 1 ≤ ENNReal.ofReal ε ∧
      localY (rescaledFields S₂ a h) 0 1 ≤ ENNReal.ofReal ε := by
  obtain ⟨h, hh, hT, _, hX₁, hY₁, hX₂, hY₂, _⟩ :=
    common_axis_variations_small h₁ h₂ hp ha haA hdata hε
  have hTnorm : triangle 0 1 ⊆
      rescaledDomain U₁ a h ∩ rescaledDomain U₂ a h := by
    intro p hpt
    have hsource : affinePair a h p ∈ triangle a (a + h) := by
      rw [← affinePair_image_triangle a hh]
      exact ⟨p, hpt, rfl⟩
    exact ⟨⟨hpt.1, (hT hsource).1⟩, ⟨hpt.1, (hT hsource).2⟩⟩
  have hdata' : ∀ v ∈ Ioo 0 1,
      (rescaledFields S₁ a h).r 0 v = (rescaledFields S₂ a h).r 0 v ∧
      (rescaledFields S₁ a h).phi 0 v = (rescaledFields S₂ a h).phi 0 v := by
    intro v hv
    exact rescaled_initial_data hdata v
      (hTnorm (initial_edge_of_triangle hv.1 hv.2))
  refine ⟨h, hh, hT, rescaled_isBVSolution h₁ ha hh,
    rescaled_isBVSolution h₂ ha hh, hTnorm, hdata', ?_, ?_, ?_, ?_⟩
  · rw [rescaled_localX S₁ hh]; exact hX₁
  · rw [rescaled_localY S₁ hh]; exact hY₁
  · rw [rescaled_localX S₂ hh]; exact hX₂
  · rw [rescaled_localY S₂ hh]; exact hY₂

/-- Equal initial radius and scalar data on the common augmented triangle
also determine the Hawking mass at every point of its initial edge. -/
theorem initial_mass_eq_on_common_triangle
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields} {a b : ℝ}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hab : a < b) (hT : triangle a b ⊆ U₁ ∩ U₂)
    (hdata : ∀ v ∈ Ioo a b,
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∀ v ∈ Ioo a b, S₁.m a v = S₂.m a v :=
  (good_initial_v_set h₁ h₂ hab hT hdata).2.2

/-- At a fixed local scale, affine normalization gives a frozen BV comparison
problem on the augmented unit triangle, with its initial edge and initial
radius and scalar data. -/
theorem scaled_local_unique
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields} {a h : ℝ}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (ha : 0 ≤ a) (hh : 0 < h)
    (hT : triangle a (a + h) ⊆ U₁ ∩ U₂)
    (hdata : ∀ v ∈ Ioo a (a + h),
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
        (∀ u v, (u, v) ∈ triangle a (a + h) →
          ∀ S : Fields, (S = S₁ ∨ S = S₂) →
            eVariationOn (S.phi u) (Ioo u v) ≤ ENNReal.ofReal ε ∧
            eVariationOn (fun s => S.phi s v) (Ioo u v) ≤ ENNReal.ofReal ε) →
        ∀ u v, (u, v) ∈ triangle a (a + h) →
          S₁.r u v = S₂.r u v ∧
          S₁.phi u v = S₂.phi u v ∧
          S₁.m u v = S₂.m u v := by
  let R₁ := rescaledFields S₁ a h
  let R₂ := rescaledFields S₂ a h
  let W₁ := rescaledDomain U₁ a h
  let W₂ := rescaledDomain U₂ a h
  have hT' : triangle 0 1 ⊆ W₁ ∩ W₂ := by
    intro p hp
    have hsource : affinePair a h p ∈ triangle a (a + h) := by
      rw [← affinePair_image_triangle a hh]
      exact ⟨p, hp, rfl⟩
    obtain ⟨hu₁, hu₂⟩ := hT hsource
    exact ⟨⟨hp.1, hu₁⟩, ⟨hp.1, hu₂⟩⟩
  have hdata' : ∀ v ∈ Ioo 0 1,
      R₁.r 0 v = R₂.r 0 v ∧ R₁.phi 0 v = R₂.phi 0 v := by
    intro v hv
    have hvp : (0, v) ∈ triangle 0 1 := initial_edge_of_triangle hv.1 hv.2
    have hsource : (a, affineCoordinate a h v) ∈ triangle a (a + h) := by
      have hh' := (affinePair_image_triangle a hh).symm
      have hmem : affinePair a h (0, v) ∈ triangle a (a + h) := by
        rw [← affinePair_image_triangle a hh]
        exact ⟨(0, v), hvp, rfl⟩
      simpa only [affinePair, affineCoordinate, mul_zero, add_zero] using hmem
    have hvI : affineCoordinate a h v ∈ Ioo a (a + h) :=
      ⟨hsource.2.1, hsource.2.2⟩
    obtain ⟨hr, hφ⟩ := hdata _ hvI
    exact ⟨by simpa only [R₁, R₂, rescaledFields, affineCoordinate,
        mul_zero, add_zero] using congrArg (fun x : ℝ => x / h) hr,
      by simpa only [R₁, R₂, rescaledFields, affineCoordinate,
        mul_zero, add_zero] using hφ⟩
  let D : ComparisonData := {
    U₁ := W₁
    U₂ := W₂
    S₁ := R₁
    S₂ := R₂
    a := 0
    b := 1
    hab := by norm_num
    h₁ := rescaled_isBVSolution h₁ ha hh
    h₂ := rescaled_isBVSolution h₂ ha hh
    hT := hT'
    hdata := hdata' }
  obtain ⟨εfinal, hεfinal, hlocal⟩ := D.local_unique rfl rfl
  refine ⟨εfinal, hεfinal, ?_⟩
  intro ε hε hεfinal hsmall u v huv
  have hsmall' : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ R : Fields, (R = D.S₁ ∨ R = D.S₂) →
        (eVariationOn (R.phi x) (Ioc x y)).toReal ≤ ε ∧
        (eVariationOn (fun s => R.phi s y) (Ico x y)).toReal ≤ ε := by
    intro x y hxy R hR
    have hxy' : (x, y) ∈ triangle 0 1 := hxy
    have hsrc : (affineCoordinate a h x, affineCoordinate a h y) ∈
        triangle a (a + h) := by
      have hmem : affinePair a h (x, y) ∈ triangle a (a + h) := by
        rw [← affinePair_image_triangle a hh]
        exact ⟨(x, y), hxy', rfl⟩
      exact hmem
    rcases hR with rfl | rfl
    · have heq := characteristic_variations_eq_open (a := 0) (h := 1)
          (rescaled_isBVSolution h₁ ha hh)
          (by intro p hp; exact (hT' (by simpa only [zero_add] using hp)).1)
          (by simpa only [zero_add] using hxy')
      have hbound := hsmall _ _ hsrc S₁ (Or.inl rfl)
      constructor
      · rw [heq.1, rescaled_outgoing_variation_eq S₁ hh x y]
        exact (ENNReal.toReal_mono (by simp) hbound.1).trans_eq
          (ENNReal.toReal_ofReal hε)
      · rw [heq.2, rescaled_incoming_variation_eq S₁ hh y x]
        exact (ENNReal.toReal_mono (by simp) hbound.2).trans_eq
          (ENNReal.toReal_ofReal hε)
    · have heq := characteristic_variations_eq_open (a := 0) (h := 1)
          (rescaled_isBVSolution h₂ ha hh)
          (by intro p hp; exact (hT' (by simpa only [zero_add] using hp)).2)
          (by simpa only [zero_add] using hxy')
      have hbound := hsmall _ _ hsrc S₂ (Or.inr rfl)
      constructor
      · rw [heq.1, rescaled_outgoing_variation_eq S₂ hh x y]
        exact (ENNReal.toReal_mono (by simp) hbound.1).trans_eq
          (ENNReal.toReal_ofReal hε)
      · rw [heq.2, rescaled_incoming_variation_eq S₂ hh y x]
        exact (ENNReal.toReal_mono (by simp) hbound.2).trans_eq
          (ENNReal.toReal_ofReal hε)
  have hinv : inverseAffinePair a h (u, v) ∈ triangle 0 1 := by
    rw [← rescaledDomain_triangle a hh]
    exact ⟨by dsimp [inverseAffinePair]; exact div_nonneg (sub_nonneg.mpr huv.1) hh.le,
      by change affinePair a h (inverseAffinePair a h (u, v)) ∈ triangle a (a + h)
         rw [affinePair_inverse a hh]
         exact huv⟩
  obtain ⟨hr, hφ, hm⟩ := hlocal ε hε hεfinal hsmall'
    _ _ hinv
  have hu : affineCoordinate a h ((u - a) / h) = u := by
    dsimp [affineCoordinate]
    field_simp [hh.ne']
    ring
  have hv : affineCoordinate a h ((v - a) / h) = v := by
    dsimp [affineCoordinate]
    field_simp [hh.ne']
    ring
  have hr' : S₁.r u v / h = S₂.r u v / h := by
    simpa only [D, R₁, R₂, rescaledFields, Prod.fst, Prod.snd,
      inverseAffinePair, hu, hv] using hr
  have hφ' : S₁.phi u v = S₂.phi u v := by
    simpa only [D, R₁, R₂, rescaledFields, Prod.fst, Prod.snd,
      inverseAffinePair, hu, hv] using hφ
  have hm' : S₁.m u v / h = S₂.m u v / h := by
    simpa only [D, R₁, R₂, rescaledFields, Prod.fst, Prod.snd,
      inverseAffinePair, hu, hv] using hm
  constructor
  · apply (div_left_inj' hh.ne').mp
    exact hr'
  constructor
  · exact hφ'
  · apply (div_left_inj' hh.ne').mp
    exact hm'

end ChristodoulouBV.Uniqueness

end
