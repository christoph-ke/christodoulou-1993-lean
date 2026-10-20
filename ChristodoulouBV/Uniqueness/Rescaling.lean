module

public import ChristodoulouBV.Uniqueness.RescalingAxisVariation

/-!
# Rescaling of BV solutions and local scalar variation

The full frozen BV predicate is invariant under a translated positive affine
double-null chart. Local scalar variation on an augmented triangle is exactly
preserved by its normalization to unit scale.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Positive affine rescaling preserves every frozen BV clause, using the same
global lower bounds and variation constants. -/
theorem rescaled_isBVSolution {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    IsBVSolution (rescaledDomain U a h) (rescaledFields S a h) := by
  refine {
    solution := rescaled_isSolution hS.solution ha hh
    nu_bounded_below := ?_
    lam_bounded_below := ?_
    item1 := rescaled_item1 hS hh
    item2 := rescaled_item2 hS hh
    item3_ac_out := rescaled_item3_ac_out hS hh
    item3_ac_in := rescaled_item3_ac_in hS hh
    item3_variation := rescaled_item3_variation hS hh
    item4 := rescaled_item4 hS hh
    item5 := rescaled_item5 hS hh
    item6 := rescaled_item6 hS hh }
  · obtain ⟨N, hN⟩ := hS.nu_bounded_below
    exact ⟨N, fun p hp => hN _ hp.2⟩
  · obtain ⟨c, hc, hC⟩ := hS.lam_bounded_below
    exact ⟨c, hc, fun p hp => hC _ hp.2⟩

/-- The §3 outgoing scalar variation on a local open triangle. -/
noncomputable def localX (S : Fields) (a b : ℝ) : ENNReal :=
  ⨆ u ∈ Set.Ioo a b, eVariationOn (S.phi u) (Set.Ioo u b)

/-- The §3 incoming scalar variation on a local open triangle. -/
noncomputable def localY (S : Fields) (a b : ℝ) : ENNReal :=
  ⨆ v ∈ Set.Ioo a b,
    eVariationOn (fun u => S.phi u v) (Set.Ioo a v)

/-- The outgoing scalar variation of a single slice is exactly invariant. -/
theorem rescaled_outgoing_variation_eq (S : Fields) {a h : ℝ} (hh : 0 < h)
    (u b : ℝ) :
    eVariationOn ((rescaledFields S a h).phi u) (Set.Ioo u b) =
      eVariationOn (S.phi (affineCoordinate a h u))
        (Set.Ioo (affineCoordinate a h u) (affineCoordinate a h b)) := by
  have hc : Continuous (affineCoordinate a h) := by
    change Continuous (fun t : ℝ => a + h * t)
    fun_prop
  change eVariationOn
    ((S.phi (affineCoordinate a h u)) ∘ affineCoordinate a h)
      (Set.Ioo u b) = _
  rw [eVariationOn.comp_eq_of_monotoneOn
      (S.phi (affineCoordinate a h u)) (affineCoordinate a h)
      ((affineCoordinate_strictMono hh).monotone.monotoneOn _),
    hc.image_Ioo_of_strictMono (affineCoordinate_strictMono hh)]

/-- The incoming scalar variation of a single slice is exactly invariant. -/
theorem rescaled_incoming_variation_eq (S : Fields) {a h : ℝ} (hh : 0 < h)
    (v b : ℝ) :
    eVariationOn (fun u => (rescaledFields S a h).phi u v) (Set.Ioo b v) =
      eVariationOn (fun u => S.phi u (affineCoordinate a h v))
        (Set.Ioo (affineCoordinate a h b) (affineCoordinate a h v)) := by
  have hc : Continuous (affineCoordinate a h) := by
    change Continuous (fun t : ℝ => a + h * t)
    fun_prop
  change eVariationOn
    ((fun u => S.phi u (affineCoordinate a h v)) ∘ affineCoordinate a h)
      (Set.Ioo b v) = _
  rw [eVariationOn.comp_eq_of_monotoneOn
      (fun u => S.phi u (affineCoordinate a h v)) (affineCoordinate a h)
      ((affineCoordinate_strictMono hh).monotone.monotoneOn _),
    hc.image_Ioo_of_strictMono (affineCoordinate_strictMono hh)]

/-- Normalizing `(a,a+h)` to `(0,1)` preserves the §3 outgoing `X`. -/
theorem rescaled_localX (S : Fields) {a h : ℝ} (hh : 0 < h) :
    localX (rescaledFields S a h) 0 1 = localX S a (a + h) := by
  have hc : Continuous (affineCoordinate a h) := by
    change Continuous (fun t : ℝ => a + h * t)
    fun_prop
  unfold localX
  simp_rw [rescaled_outgoing_variation_eq S hh]
  rw [← iSup_image (f := affineCoordinate a h)
    (g := fun x => eVariationOn (S.phi x)
      (Set.Ioo x (affineCoordinate a h 1))) (t := Set.Ioo 0 1),
    hc.image_Ioo_of_strictMono (affineCoordinate_strictMono hh)]
  simp only [affineCoordinate, mul_zero, add_zero, mul_one]

/-- Normalizing `(a,a+h)` to `(0,1)` preserves the §3 incoming `Y`. -/
theorem rescaled_localY (S : Fields) {a h : ℝ} (hh : 0 < h) :
    localY (rescaledFields S a h) 0 1 = localY S a (a + h) := by
  have hc : Continuous (affineCoordinate a h) := by
    change Continuous (fun t : ℝ => a + h * t)
    fun_prop
  unfold localY
  simp_rw [rescaled_incoming_variation_eq S hh]
  rw [← iSup_image (f := affineCoordinate a h)
    (g := fun x => eVariationOn (fun u => S.phi u x)
      (Set.Ioo (affineCoordinate a h 0) x)) (t := Set.Ioo 0 1),
    hc.image_Ioo_of_strictMono (affineCoordinate_strictMono hh)]
  simp only [affineCoordinate, mul_zero, add_zero, mul_one]

/-- The positive affine chart on a pair of null coordinates. -/
def affinePair (a h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (affineCoordinate a h p.1, affineCoordinate a h p.2)

/-- The inverse chart on a pair of null coordinates. -/
noncomputable def inverseAffinePair (a h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 - a) / h, (p.2 - a) / h)

/-- The inverse chart followed by the affine chart is the identity. -/
theorem affinePair_inverse (a : ℝ) {h : ℝ} (hh : 0 < h) (p : ℝ × ℝ) :
    affinePair a h (inverseAffinePair a h p) = p := by
  rcases p with ⟨u, v⟩
  simp only [affinePair, inverseAffinePair, affineCoordinate]
  ext <;> field_simp [hh.ne'] <;> ring

/-- A full translated triangle normalizes to the augmented unit triangle. -/
theorem rescaledDomain_triangle (a : ℝ) {h : ℝ} (hh : 0 < h) :
    rescaledDomain (triangle a (a + h)) a h = triangle 0 1 := by
  ext p
  rcases p with ⟨u, v⟩
  constructor
  · intro hp
    have hpu : 0 ≤ u := hp.1
    have hpv : u < v :=
      (affineCoordinate_strictMono hh).lt_iff_lt.mp hp.2.2.1
    have hv1 : v < 1 :=
      (affineCoordinate_strictMono hh).lt_iff_lt.mp (by
        simpa only [affineCoordinate, mul_one] using hp.2.2.2)
    exact ⟨hpu, hpv, hv1⟩
  · intro hp
    refine ⟨hp.1, ?_⟩
    have hAu : a ≤ affineCoordinate a h u := by
      dsimp [affineCoordinate]
      nlinarith [mul_nonneg hh.le hp.1]
    have hAuv := affineCoordinate_strictMono (a := a) hh hp.2.1
    have hAv : affineCoordinate a h v < a + h := by
      simpa only [affineCoordinate, mul_one] using
        affineCoordinate_strictMono hh hp.2.2
    exact ⟨hAu, hAuv, hAv⟩

/-- The image of the augmented unit triangle is the translated triangle. -/
theorem affinePair_image_triangle (a : ℝ) {h : ℝ} (hh : 0 < h) :
    affinePair a h '' triangle 0 1 = triangle a (a + h) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : q ∈ rescaledDomain (triangle a (a + h)) a h := by
      rw [rescaledDomain_triangle a hh]
      exact hq
    exact hq'.2
  · intro hp
    refine ⟨inverseAffinePair a h p, ?_, affinePair_inverse a hh p⟩
    rw [← rescaledDomain_triangle a hh]
    have hnonneg : 0 ≤ (p.1 - a) / h :=
      div_nonneg (sub_nonneg.mpr hp.1) hh.le
    refine ⟨hnonneg, ?_⟩
    change affinePair a h (inverseAffinePair a h p) ∈ triangle a (a + h)
    rw [affinePair_inverse a hh p]
    exact hp

/-- Any scalar quantity composed with the chart has exactly the old range
over the corresponding augmented triangle. -/
theorem affinePair_image_values (f : ℝ → ℝ → ℝ) (a : ℝ) {h : ℝ}
    (hh : 0 < h) :
    (fun p : ℝ × ℝ => f (affineCoordinate a h p.1)
      (affineCoordinate a h p.2)) '' triangle 0 1 =
    (fun p : ℝ × ℝ => f p.1 p.2) '' triangle a (a + h) := by
  calc
    _ = (fun p : ℝ × ℝ => f p.1 p.2) ''
        (affinePair a h '' triangle 0 1) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [affinePair_image_triangle a hh]

/-- The outgoing expansion has the same range on the normalized triangle. -/
theorem rescaled_lam_image_triangle (S : Fields) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    (fun p : ℝ × ℝ => (rescaledFields S a h).lam p.1 p.2) '' triangle 0 1 =
    (fun p : ℝ × ℝ => S.lam p.1 p.2) '' triangle a (a + h) := by
  simpa only [rescaledFields] using affinePair_image_values S.lam a hh

/-- The incoming expansion has the same range on the normalized triangle. -/
theorem rescaled_nu_image_triangle (S : Fields) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    (fun p : ℝ × ℝ => (rescaledFields S a h).nu p.1 p.2) '' triangle 0 1 =
    (fun p : ℝ × ℝ => S.nu p.1 p.2) '' triangle a (a + h) := by
  simpa only [rescaledFields] using affinePair_image_values S.nu a hh

/-- The mass ratio has the same range on the normalized triangle. -/
theorem rescaled_mass_ratio_image_triangle (S : Fields) (a : ℝ)
    {h : ℝ} (hh : 0 < h) :
    (fun p : ℝ × ℝ =>
      2 * (rescaledFields S a h).m p.1 p.2 /
        (rescaledFields S a h).r p.1 p.2) '' triangle 0 1 =
    (fun p : ℝ × ℝ => 2 * S.m p.1 p.2 / S.r p.1 p.2) ''
      triangle a (a + h) := by
  have hfun : (fun p : ℝ × ℝ =>
      2 * (rescaledFields S a h).m p.1 p.2 /
        (rescaledFields S a h).r p.1 p.2) =
      (fun p : ℝ × ℝ =>
        2 * S.m (affineCoordinate a h p.1) (affineCoordinate a h p.2) /
          S.r (affineCoordinate a h p.1) (affineCoordinate a h p.2)) := by
    funext p
    exact rescaled_mass_ratio S hh p.1 p.2
  rw [hfun]
  exact affinePair_image_values (fun u v => 2 * S.m u v / S.r u v) a hh

/-- The outgoing scalar amplitude has the same range on the normalized triangle. -/
theorem rescaled_theta_image_triangle (S : Fields) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    (fun p : ℝ × ℝ => (rescaledFields S a h).theta p.1 p.2) '' triangle 0 1 =
    (fun p : ℝ × ℝ => S.theta p.1 p.2) '' triangle a (a + h) := by
  change (fun p : ℝ × ℝ => S.theta (affineCoordinate a h p.1)
    (affineCoordinate a h p.2)) '' triangle 0 1 = _
  exact affinePair_image_values S.theta a hh

/-- The incoming scalar amplitude has the same range on the normalized triangle. -/
theorem rescaled_zeta_image_triangle (S : Fields) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    (fun p : ℝ × ℝ => (rescaledFields S a h).zeta p.1 p.2) '' triangle 0 1 =
    (fun p : ℝ × ℝ => S.zeta p.1 p.2) '' triangle a (a + h) := by
  change (fun p : ℝ × ℝ => S.zeta (affineCoordinate a h p.1)
    (affineCoordinate a h p.2)) '' triangle 0 1 = _
  exact affinePair_image_values S.zeta a hh

/-- Restriction of a BV solution to a translated augmented triangle
normalizes to a BV solution on the augmented unit triangle. -/
theorem rescaled_triangle_isBVSolution {S : Fields} {a h : ℝ}
    (hS : IsBVSolution (triangle a (a + h)) S)
    (hh : 0 < h) :
    IsBVSolution (triangle 0 1) (rescaledFields S a h) := by
  have hp : (a, a + h / 2) ∈ triangle a (a + h) := by
    refine ⟨le_rfl, ?_, ?_⟩ <;> linarith
  have ha : 0 ≤ a := (hS.solution.development.wedge hp).1
  rw [← rescaledDomain_triangle a hh]
  exact rescaled_isBVSolution hS ha hh

/-- The four §3 scalar variation quantities of two solutions are preserved
simultaneously by normalization. -/
theorem rescaled_local_variations_pair (S₁ S₂ : Fields) {a h : ℝ} (hh : 0 < h) :
    localX (rescaledFields S₁ a h) 0 1 = localX S₁ a (a + h) ∧
    localY (rescaledFields S₁ a h) 0 1 = localY S₁ a (a + h) ∧
    localX (rescaledFields S₂ a h) 0 1 = localX S₂ a (a + h) ∧
    localY (rescaledFields S₂ a h) 0 1 = localY S₂ a (a + h) := by
  exact ⟨rescaled_localX S₁ hh, rescaled_localY S₁ hh,
    rescaled_localX S₂ hh, rescaled_localY S₂ hh⟩

/-- Equal radius and scalar data on the translated initial edge remain equal
on the normalized initial edge. -/
theorem rescaled_initial_data {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    {a h : ℝ}
    (hdata : ∀ v, (a, v) ∈ U₁ ∩ U₂ →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∀ v, (0, v) ∈ rescaledDomain U₁ a h ∩ rescaledDomain U₂ a h →
      (rescaledFields S₁ a h).r 0 v = (rescaledFields S₂ a h).r 0 v ∧
      (rescaledFields S₁ a h).phi 0 v = (rescaledFields S₂ a h).phi 0 v := by
  intro v hv
  have hmem : (a, affineCoordinate a h v) ∈ U₁ ∩ U₂ := by
    simpa only [affineCoordinate, mul_zero, add_zero] using
      (show (affineCoordinate a h 0, affineCoordinate a h v) ∈ U₁ ∩ U₂ from
        ⟨hv.1.2, hv.2.2⟩)
  obtain ⟨hr, hφ⟩ := hdata _ hmem
  exact ⟨by simpa only [rescaledFields, affineCoordinate, mul_zero, add_zero] using
    congrArg (fun x : ℝ => x / h) hr,
    by simpa only [rescaledFields, affineCoordinate, mul_zero, add_zero] using hφ⟩

end ChristodoulouBV.Uniqueness

end
