module

public import ChristodoulouBV.Existence.AreaSectionLimitExceptional
import Mathlib.Tactic

/-!
# Common physical jump lines for the raw limit fields

On each off-axis rectangle, the mixed primitive bounds are uniform in
the longitudinal coordinate. They give the transverse Lipschitz control
which turns countably many BV discontinuity sets into one common set.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- A bounded interval density controls distances between arbitrary
points of its enclosing section, in either order. -/
theorem dist_le_of_interval_primitives
    {F q : ℝ → ℝ} {a b K : ℝ}
    (hp : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → x ≤ y → IntervalPrimitive F q x y)
    (hb : ∀ t ∈ Icc a b, |q t| ≤ K)
    {x z : ℝ} (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) :
    dist (F x) (F z) ≤ K * dist x z := by
  wlog hxz : x ≤ z generalizing x z
  · simpa only [dist_comm] using this hz hx (le_of_not_ge hxz)
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (F x) (F z), abs_sub_comm x z,
    abs_of_nonneg (sub_nonneg.mpr hxz)]
  exact (hp x z hx hz hxz).abs_sub_le hxz
    (fun t ht => hb t ⟨hx.1.trans ht.1, ht.2.trans hz.2⟩)

/-- The raw outgoing fields have common physical `v` jump lines on
every off-axis rectangle, simultaneously for every incoming coordinate.
This does not assert a common set after a mixing triangular chart. -/
theorem raw_outgoing_common_exceptional_set_on_rectangle
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {A B L R : ℝ}
    (hA : 0 ≤ A) (_hAB : A ≤ B) (hBL : B < L) (hLR : L ≤ R) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ v ∈ Ioo L R, v ∉ S →
      ∀ u ∈ Icc A B,
        ContinuousAt (d.rawFields.lam u) v ∧ ContinuousAt (d.rawFields.alpha u) v := by
  let X := Icc A B
  have hδ : 0 < L - B := sub_pos.mpr hBL
  have hM : 0 ≤ 6 * D.toReal + C :=
    add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (h 0).offset_nonneg
  have hmem (u : ℝ) (hu : u ∈ Icc A B) (v : ℝ) (hv : v ∈ Icc L R) :
      (u, v) ∈ globalDomain := ⟨hA.trans hu.1, hu.2.trans_lt (hBL.trans_le hv.1)⟩
  have hρ (u : ℝ) (hu : u ∈ Icc A B) (v : ℝ) (hv : v ∈ Icc L R) :
      |IsBVSolution.radiusCoeff d.rawFields u v| ≤ 9 / (L - B) :=
    d.raw_radius_coeff_bound h (hmem u hu v hv) hδ (by linarith only [hu.2, hv.1])
  have hρφ (u : ℝ) (hu : u ∈ Icc A B) (v : ℝ) (hv : v ∈ Icc L R) :
      |IsBVSolution.radiusCoeff d.rawFields u v * d.rawFields.phi u v| ≤
        (9 / (L - B)) * (6 * D.toReal + C) := by
    rw [abs_mul]
    exact mul_le_mul (hρ u hu v hv) (d.scalar_amplitude h (hmem u hu v hv))
      (abs_nonneg _) (div_nonneg (by norm_num) hδ.le)
  have hseg (v x z : ℝ) (hv : v ∈ Icc L R)
      (hx : x ∈ Icc A B) (hz : z ∈ Icc A B) (hxz : x ≤ z) :
      inSeg v x z ⊆ globalDomain := by
    rintro ⟨u, w⟩ ⟨hu, rfl⟩
    exact hmem u ⟨hx.1.trans hu.1, hu.2.trans hz.2⟩ _ hv
  have hlamBV (u : X) : BoundedVariationOn (d.rawFields.lam u) (Icc L R) := by
    have hb : BoundedVariationOn (d.lam u) (Ioi u) := ne_top_of_le_ne_top
      (ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD))
      ((expansions_limit h d).1 u (hA.trans u.property.1))
    apply hb.mono
    exact fun v hv => (u.property.2.trans_lt (hBL.trans_le hv.1))
  have hαBV (u : X) : BoundedVariationOn (d.rawFields.alpha u) (Icc L R) := by
    have hb : BoundedVariationOn (d.alpha u) (Ioi u) :=
      ne_top_of_le_ne_top (scalarVariationBound_ne_top hD C)
        ((alpha_beta_limit h d).2.1 u (hA.trans u.property.1))
    apply hb.mono
    exact fun v hv => (u.property.2.trans_lt (hBL.trans_le hv.1))
  have hlamLip (u z : X) (v : ℝ) (hv : v ∈ Icc L R) :
      dist (d.rawFields.lam u v) (d.rawFields.lam z v) ≤ (9 / (L - B)) * dist u z := by
    exact dist_le_of_interval_primitives
      (fun x z hx hz hxz => (raw_expansion_primitive_limit h d).1 v x z hxz
        (hseg v x z hv hx hz hxz))
      (fun t ht => hρ t ht v hv) u.property z.property
  have hαLip (u z : X) (v : ℝ) (hv : v ∈ Icc L R) :
      dist (d.rawFields.alpha u v) (d.rawFields.alpha z v) ≤
        ((9 / (L - B)) * (6 * D.toReal + C)) * dist u z := by
    exact dist_le_of_interval_primitives
      (fun x z hx hz hxz => (raw_alpha_beta_transport_limit h d).1 v x z hxz
        (hseg v x z hv hx hz hxz))
      (fun t ht => hρφ t ht v hv) u.property z.property
  obtain ⟨Slam, hSlam, hlam⟩ := exists_common_exceptional_set_on_interval hLR
    (div_nonneg (by norm_num) hδ.le) hlamBV hlamLip
  obtain ⟨Sα, hSα, hα⟩ := exists_common_exceptional_set_on_interval hLR
    (mul_nonneg (div_nonneg (by norm_num) hδ.le) hM) hαBV hαLip
  refine ⟨Slam ∪ Sα, hSlam.union hSα, fun v hv hvs u hu => ?_⟩
  exact ⟨hlam v hv (fun hm => hvs (Or.inl hm)) ⟨u, hu⟩,
    hα v hv (fun hm => hvs (Or.inr hm)) ⟨u, hu⟩⟩

/-- The incoming fields have common physical `u` jump lines on an
off-axis rectangle, simultaneously for every outgoing coordinate. -/
theorem raw_incoming_common_exceptional_set_on_rectangle
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {A B L R : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hBL : B < L) (_hLR : L ≤ R) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u ∈ Ioo A B, u ∉ S →
      ∀ v ∈ Icc L R,
        ContinuousAt (fun t => d.rawFields.nu t v) u ∧
          ContinuousAt (fun t => d.rawFields.beta t v) u := by
  let X := Icc L R
  have hδ : 0 < L - B := sub_pos.mpr hBL
  have hM : 0 ≤ 6 * D.toReal + C :=
    add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (h 0).offset_nonneg
  have hmem (u : ℝ) (hu : u ∈ Icc A B) (v : ℝ) (hv : v ∈ Icc L R) :
      (u, v) ∈ globalDomain := ⟨hA.trans hu.1, hu.2.trans_lt (hBL.trans_le hv.1)⟩
  have hρ (u : ℝ) (hu : u ∈ Icc A B) (v : ℝ) (hv : v ∈ Icc L R) :
      |IsBVSolution.radiusCoeff d.rawFields u v| ≤ 9 / (L - B) :=
    d.raw_radius_coeff_bound h (hmem u hu v hv) hδ (by linarith only [hu.2, hv.1])
  have hρφ (u : ℝ) (hu : u ∈ Icc A B) (v : ℝ) (hv : v ∈ Icc L R) :
      |IsBVSolution.radiusCoeff d.rawFields u v * d.rawFields.phi u v| ≤
        (9 / (L - B)) * (6 * D.toReal + C) := by
    rw [abs_mul]
    exact mul_le_mul (hρ u hu v hv) (d.scalar_amplitude h (hmem u hu v hv))
      (abs_nonneg _) (div_nonneg (by norm_num) hδ.le)
  have hseg (u x z : ℝ) (hu : u ∈ Icc A B)
      (hx : x ∈ Icc L R) (hz : z ∈ Icc L R) (hxz : x ≤ z) :
      outSeg u x z ⊆ globalDomain := by
    rintro ⟨w, v⟩ ⟨rfl, hv⟩
    exact hmem _ hu v ⟨hx.1.trans hv.1, hv.2.trans hz.2⟩
  have hνBV (v : X) : BoundedVariationOn (fun u => d.rawFields.nu u v) (Icc A B) := by
    have hb : BoundedVariationOn (fun u => d.nu u v) (Ico 0 v) := ne_top_of_le_ne_top
      (ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD))
      ((expansions_limit h d).2.1 v (hA.trans hAB |>.trans_lt hBL |>.trans_le v.property.1))
    apply hb.mono
    exact fun u hu => ⟨hA.trans hu.1, hu.2.trans_lt (hBL.trans_le v.property.1)⟩
  have hβBV (v : X) : BoundedVariationOn (fun u => d.rawFields.beta u v) (Icc A B) := by
    have hb : BoundedVariationOn (fun u => d.beta u v) (Ico 0 v) :=
      ne_top_of_le_ne_top (scalarVariationBound_ne_top hD C)
      ((alpha_beta_limit h d).2.2.1 v
        (hA.trans hAB |>.trans_lt hBL |>.trans_le v.property.1))
    apply hb.mono
    exact fun u hu => ⟨hA.trans hu.1, hu.2.trans_lt (hBL.trans_le v.property.1)⟩
  have hνLip (v z : X) (u : ℝ) (hu : u ∈ Icc A B) :
      dist (d.rawFields.nu u v) (d.rawFields.nu u z) ≤ (9 / (L - B)) * dist v z := by
    exact dist_le_of_interval_primitives
      (fun x z hx hz hxz => (raw_expansion_primitive_limit h d).2 u x z hxz
        (hseg u x z hu hx hz hxz))
      (fun t ht => hρ u hu t ht) v.property z.property
  have hβLip (v z : X) (u : ℝ) (hu : u ∈ Icc A B) :
      dist (d.rawFields.beta u v) (d.rawFields.beta u z) ≤
        ((9 / (L - B)) * (6 * D.toReal + C)) * dist v z := by
    exact dist_le_of_interval_primitives
      (fun x z hx hz hxz => (raw_alpha_beta_transport_limit h d).2 u x z hxz
        (hseg u x z hu hx hz hxz))
      (fun t ht => hρφ u hu t ht) v.property z.property
  obtain ⟨Sν, hSν, hν⟩ := exists_common_exceptional_set_on_interval hAB
    (div_nonneg (by norm_num) hδ.le) hνBV hνLip
  obtain ⟨Sβ, hSβ, hβ⟩ := exists_common_exceptional_set_on_interval hAB
    (mul_nonneg (div_nonneg (by norm_num) hδ.le) hM) hβBV hβLip
  refine ⟨Sν ∪ Sβ, hSν.union hSβ, fun u hu hus v hv => ?_⟩
  exact ⟨hν u hu (fun hm => hus (Or.inl hm)) ⟨v, hv⟩,
    hβ u hu (fun hm => hus (Or.inr hm)) ⟨v, hv⟩⟩

end ChristodoulouBV

end
