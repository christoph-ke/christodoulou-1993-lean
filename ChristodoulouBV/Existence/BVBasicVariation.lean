module

public import ChristodoulouBV.Existence.TransportLimit
import Mathlib.Tactic

/-!
# Uniform variation of the canonical BV fields

The constants below use the universal smooth and canonical limit bounds. The incoming
section includes its initial endpoint. Scalar offsets do not enter the
estimates for the invariant fields `θ` and `ζ`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem outgoing_section_bound {f : ℝ → ℝ → ℝ} {V : ℝ≥0∞}
    (h : ∀ u, 0 ≤ u → eVariationOn (f u) (Ioi u) ≤ V) (u : ℝ) :
    eVariationOn (f u) {v | (u, v) ∈ globalDomain} ≤ V := by
  by_cases hu : 0 ≤ u
  · have hs : {v | (u, v) ∈ globalDomain} = Ioi u := by
      ext v
      simp only [globalDomain, Set.mem_ofPred_eq, mem_Ioi, hu, true_and]
    rw [hs]
    exact h u hu
  · have hs : {v | (u, v) ∈ globalDomain} = ∅ := by
      ext v
      simp only [globalDomain, Set.mem_ofPred_eq, hu, false_and, Set.mem_empty_iff_false]
    rw [hs, eVariationOn.subsingleton _ Set.subsingleton_empty]
    exact bot_le

private theorem incoming_section_bound {f : ℝ → ℝ → ℝ} {V : ℝ≥0∞}
    (h : ∀ v, 0 < v → eVariationOn (fun u => f u v) (Ico 0 v) ≤ V) (v : ℝ) :
    eVariationOn (fun u => f u v) {u | (u, v) ∈ globalDomain} ≤ V := by
  change eVariationOn (fun u => f u v) (Ico 0 v) ≤ V
  by_cases hv : 0 < v
  · exact h v hv
  · rw [Ico_eq_empty_of_le (le_of_not_gt hv),
      eVariationOn.subsingleton _ Set.subsingleton_empty]
    exact bot_le

/-- The canonical fields satisfy the literal frozen item 1, uniformly
on the complete sections of `globalDomain`. -/
theorem s6_bv_item1
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ K : ℝ,
      (∀ u, eVariationOn (d.scalarRightFields.lam u)
        {v | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K) ∧
      ∀ v, eVariationOn (fun u => d.scalarRightFields.nu u v)
        {u | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K := by
  have hW : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  obtain ⟨hout, hin⟩ := right_expansions_variation h hD d
  refine ⟨(s4UniversalC * D ^ 2).toReal, ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal hW]
    exact outgoing_section_bound hout
  · rw [ENNReal.ofReal_toReal hW]
    exact incoming_section_bound hin

/-- Right continuity of the incoming scalar at the initial endpoint.
It removes its endpoint cost from the full frozen variation clause. -/
theorem bv_scalar_continuous_within_at_initial
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {v : ℝ} (hv : 0 < v) :
    ContinuousWithinAt (fun u => d.scalarRightFields.phi u v) (Ici 0) 0 := by
  have hcont : ContinuousOn (fun u => d.rawFields.phi u v) (Ico 0 v) :=
    (d.scalar_continuousOn h).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hu => hu)
  exact (hcont 0 ⟨le_rfl, hv⟩).mono_of_mem_nhdsWithin
    (by simpa only [← Ici_inter_Iio] using
      inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iio_mem_nhds hv))

/-- Both scalar section variations have the universal scalar limit bound, with
the incoming initial endpoint included. -/
theorem bv_scalar_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → eVariationOn (d.scalarRightFields.phi u) (Ioi u) ≤
      ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)) ∧
    ∀ v, 0 < v → eVariationOn (fun u => d.scalarRightFields.phi u v) (Ico 0 v) ≤
      ENNReal.ofReal (3 * s6EndpointTVK * D.toReal) := by
  obtain ⟨hout, hin⟩ := scalar_right_fields_three_term_tv h hD d
  have heq : ENNReal.ofReal (3 * s6EndpointTVK * D.toReal) =
      3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) := by
    rw [mul_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [heq]
  constructor
  · intro u hu
    exact (le_add_of_nonneg_left bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (hout u hu))
  · intro v hv
    rw [eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hv
      (bv_scalar_continuous_within_at_initial h d hv)]
    exact (le_add_of_nonneg_left bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (hin v hv))

/-- The canonical scalar satisfies all three literal frozen item-3
clauses: absolute continuity on every closed null segment and one
uniform bound for the two full section variations. -/
theorem bv_item3
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (d.scalarRightFields.phi u) a b) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (fun u => d.scalarRightFields.phi u v) a b) ∧
    ∃ K : ℝ,
      (∀ u, eVariationOn (d.scalarRightFields.phi u)
        {v | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K) ∧
      ∀ v, eVariationOn (fun u => d.scalarRightFields.phi u v)
        {u | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K := by
  obtain ⟨hacout, hacin⟩ := scalar_limit_absolute_continuity h hD d
  obtain ⟨hout, hin⟩ := bv_scalar_variation h hD d
  exact ⟨hacout, hacin, 3 * s6EndpointTVK * D.toReal,
    outgoing_section_bound hout, incoming_section_bound hin⟩

/-- The invariant amplitudes retain the universal bounds after canonical
selection. The spatial right-trace limit is the proved transport limit construction. -/
theorem bv_invariant_amplitudes
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      |d.scalarRightFields.theta p.1 p.2| ≤ 5 * D.toReal ∧
      |d.scalarRightFields.zeta p.1 p.2| ≤ 8 * D.toReal := by
  intro p hp
  obtain ⟨_, hφ, _, hl, hn, hα, hβ⟩ := transport_shift_fields_limit h hD d hp
  have hθ := hα.sub (hl.mul hφ)
  have hζ := hβ.sub (hn.mul hφ)
  exact ⟨le_of_tendsto hθ.abs (Eventually.of_forall (fun n =>
      (scalar_limit_invariant_amplitudes h d _ (transport_shift_mem hp n)).1)),
    le_of_tendsto hζ.abs (Eventually.of_forall (fun n =>
      (scalar_limit_invariant_amplitudes h d _ (transport_shift_mem hp n)).2))⟩

private theorem invariant_variation_bound
    {w q phi : ℝ → ℝ} {s : Set ℝ} {V W : ℝ≥0∞} {M : ℝ}
    (hw : ∀ t ∈ s, |w t| ≤ 1) (hq : ∀ t ∈ s, |q t - phi t| ≤ M)
    (hwV : eVariationOn w s ≤ W) (hqV : eVariationOn q s ≤ V)
    (hphiV : eVariationOn phi s ≤ V) :
    eVariationOn (fun t => w t * (q t - phi t)) s ≤
      (V + V) + ENNReal.ofReal M * W := by
  have hprod := eVariationOn.mul_le_of_abs_le hw hq
  have hsub := (eVariationOn.sub_le q phi s).trans (add_le_add hqV hphiV)
  have hm : (w * fun x => q x - phi x) = (fun t => w t * (q t - phi t)) := by
    funext t
    exact Pi.mul_apply w (fun x => q x - phi x) t
  have hs : q - phi = (fun t => q t - phi t) := by
    funext t
    exact Pi.sub_apply q phi t
  rw [hm] at hprod
  rw [hs] at hsub
  calc
    _ ≤ eVariationOn (fun t => q t - phi t) s + ENNReal.ofReal M * eVariationOn w s := by
      simpa only [ENNReal.ofReal_one, one_mul] using hprod
    _ ≤ _ := add_le_add hsub (mul_le_mul_of_nonneg_left hwV bot_le)

/-- Both invariant field variations have an explicit bound with universal
coefficients. The incoming section includes `u = 0`. -/
theorem bv_invariant_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    let V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)
    let W := s4UniversalC * D ^ 2
    (∀ u, 0 ≤ u → eVariationOn (d.scalarRightFields.theta u) (Ioi u) ≤
      (V + V) + ENNReal.ofReal (24 * D.toReal) * W) ∧
    ∀ v, 0 < v → eVariationOn (fun u => d.scalarRightFields.zeta u v) (Ico 0 v) ≤
      (V + V) + ENNReal.ofReal (24 * D.toReal) * W := by
  let S := d.scalarRightFields
  have hgeom := scalar_right_fields_geometry h hD d
  have hamp := bv_invariant_amplitudes h hD d
  obtain ⟨hlV, hnV⟩ := right_expansions_variation h hD d
  obtain ⟨hphiout, hphiin⟩ := bv_scalar_variation h hD d
  obtain ⟨hout, hin⟩ := scalar_right_fields_three_term_tv h hD d
  have hVe : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) =
      ENNReal.ofReal (3 * s6EndpointTVK * D.toReal) := by
    have he : ENNReal.ofReal (3 * (s6EndpointTVK * D.toReal)) =
        ENNReal.ofReal 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) :=
      ENNReal.ofReal_mul (by norm_num)
    simpa only [mul_assoc, ENNReal.ofReal_ofNat] using he.symm
  constructor
  · intro u hu
    have hqV : eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioi u) ≤
        ENNReal.ofReal (3 * s6EndpointTVK * D.toReal) :=
      ((le_add_of_nonneg_right bot_le).trans
        ((le_add_of_nonneg_right bot_le).trans (hout u hu))).trans_eq hVe
    have heq : EqOn (S.theta u)
        (fun v => S.lam u v * (S.alpha u v / S.lam u v - S.phi u v)) (Ioi u) := by
      intro v hv
      have hl : S.lam u v ≠ 0 := by
        have := (hgeom (u, v) ⟨hu, hv⟩).1
        change S.lam u v ≠ 0
        linarith only [this]
      dsimp only [Fields.theta]
      field_simp [hl]
    rw [eVariationOn.congr heq]
    apply invariant_variation_bound (V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal))
      (W := s4UniversalC * D ^ 2) (M := 24 * D.toReal) ?_ ?_ (hlV u hu) hqV
      (hphiout u hu)
    · intro v hv
      obtain ⟨hl0, hl1, _⟩ := hgeom (u, v) ⟨hu, hv⟩
      change |S.lam u v| ≤ 1
      rw [abs_of_nonneg (by linarith only [hl0] : 0 ≤ S.lam u v)]
      linarith only [hl1]
    · intro v hv
      have hl0 := (hgeom (u, v) ⟨hu, hv⟩).1
      have hlpos : 0 < S.lam u v := by linarith only [hl0]
      have hid : S.alpha u v / S.lam u v - S.phi u v =
          S.theta u v / S.lam u v := by
        dsimp only [Fields.theta]
        field_simp [hlpos.ne']
      rw [hid, abs_div, abs_of_pos hlpos]
      apply (div_le_iff₀ hlpos).2
      have hmul := mul_le_mul_of_nonneg_left hl0
        (show 0 ≤ 24 * D.toReal by positivity)
      have hθ := (hamp (u, v) ⟨hu, hv⟩).1
      nlinarith only [hmul, hθ, ENNReal.toReal_nonneg (a := D)]
  · intro v hv
    have hn0 := (hgeom (0, v) ⟨le_rfl, hv⟩).2.2.1
    have hnne : S.nu 0 v ≠ 0 := by linarith only [hn0]
    have hqcont : ContinuousWithinAt (fun u => S.beta u v / S.nu u v) (Ici 0) 0 :=
      ((right_scalar_derivatives_continuous h hD d (0, v) ⟨le_rfl, hv⟩).2).div
        ((right_expansions_continuous h hD d (0, v) ⟨le_rfl, hv⟩).2) hnne
    have hqV : eVariationOn (fun u => S.beta u v / S.nu u v) (Ico 0 v) ≤
        ENNReal.ofReal (3 * s6EndpointTVK * D.toReal) := by
      rw [eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hv hqcont]
      exact ((le_add_of_nonneg_right bot_le).trans
        ((le_add_of_nonneg_right bot_le).trans (hin v hv))).trans_eq hVe
    have heq : EqOn (fun u => S.zeta u v)
        (fun u => S.nu u v * (S.beta u v / S.nu u v - S.phi u v)) (Ico 0 v) := by
      intro u hu
      have hn0 := (hgeom (u, v) hu).2.2.1
      have hn : S.nu u v ≠ 0 := by linarith only [hn0]
      dsimp only [Fields.zeta]
      field_simp [hn]
    rw [eVariationOn.congr heq]
    apply invariant_variation_bound (V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal))
      (W := s4UniversalC * D ^ 2) (M := 24 * D.toReal) ?_ ?_ (hnV v hv) hqV
      (hphiin v hv)
    · intro u hu
      obtain ⟨_, _, hn0, hn1, _⟩ := hgeom (u, v) hu
      change |S.nu u v| ≤ 1
      rw [abs_of_nonpos (by linarith only [hn0] : S.nu u v ≤ 0)]
      linarith only [hn1]
    · intro u hu
      have hn0 := (hgeom (u, v) hu).2.2.1
      have hnpos : 0 < -S.nu u v := by linarith only [hn0]
      have hid : S.beta u v / S.nu u v - S.phi u v = S.zeta u v / S.nu u v := by
        dsimp only [Fields.zeta]
        field_simp [(neg_ne_zero.mp hnpos.ne')]
      rw [hid, abs_div, abs_of_neg (neg_pos.mp hnpos)]
      apply (div_le_iff₀ hnpos).2
      have hmul := mul_le_mul_of_nonneg_left hn0
        (show 0 ≤ 24 * D.toReal by positivity)
      have hζ := (hamp (u, v) hu).2
      nlinarith only [hmul, hζ]

/-- The canonical limit satisfies the exact frozen item 5. Its witness
uses only universal coefficients and the initial total variation. -/
theorem bv_item5
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ K : ℝ,
      (∀ u, eVariationOn (d.scalarRightFields.theta u)
        {v | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K) ∧
      ∀ v, eVariationOn (fun u => d.scalarRightFields.zeta u v)
        {u | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K := by
  let V := ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)
  let W := s4UniversalC * D ^ 2
  let K := (V + V) + ENNReal.ofReal (24 * D.toReal) * W
  have hW : W ≠ ∞ := ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  have hK : K ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW⟩
  obtain ⟨hout, hin⟩ := bv_invariant_variation h hD d
  refine ⟨K.toReal, ?_, ?_⟩ <;> rw [ENNReal.ofReal_toReal hK]
  · exact outgoing_section_bound hout
  · exact incoming_section_bound hin

end ChristodoulouBV

end
