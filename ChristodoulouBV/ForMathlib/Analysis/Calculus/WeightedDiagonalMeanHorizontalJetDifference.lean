module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanHorizontalNumerator
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input horizontal first-jet estimate

The endpoint and centered-integrand lemmas yield the exact difference
coefficient for the horizontal derivative of a weighted diagonal error.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The horizontal first-jet difference bound in the interior of a unit-size
coordinate triangle. The coefficient matches the moving-endpoint quotient
estimate, while the proof uses only normalized fixed-interval integrals. -/
theorem abs_fderivWithin_weightedDiagonalError_horizontal_sub_le_of_jets
    {a b c C B L D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderiv₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = G₁ p)
    (hderiv₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = G₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    (_hGw₁U : ∀ p ∈ closedCoordTriangle a b, |Gw₁ p (1, 0)| ≤ L)
    (hGw₂U : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (1, 0)| ≤ L)
    (hG₁U : ∀ p ∈ closedCoordTriangle a b, |G₁ p (1, 0)| ≤ L)
    (hG₂U : ∀ p ∈ closedCoordTriangle a b, |G₂ p (1, 0)| ≤ L)
    (hG₁V : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hG₂V : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hGwUDiff : ∀ p ∈ closedCoordTriangle a b,
      |Gw₁ p (1, 0) - Gw₂ p (1, 0)| ≤ D)
    (hGUDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (1, 0) - G₂ p (1, 0)| ≤ D)
    (hGVDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (0, 1) - G₂ p (0, 1)| ≤ D)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L) (hD : 0 ≤ D)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalError w₁ f₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) +
          B + L * (1 + ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) + L + C) / c +
        (C * B + L * B + C * L) / c ^ 2) * D := by
  let K := closedCoordTriangle a b
  let d := p.2 - p.1
  let M := (B + C) / (2 * c) + C * B / (2 * c ^ 2)
  let Aφ := C * B + L * B + C * L
  let AΔ := B + C * M + B + L * (1 + M) + L + C
  let S : ℝ → ℝ × ℝ := diagonalSegment p
  let m₁ := weightedDiagonalMean w₁ f₁ p
  let m₂ := weightedDiagonalMean w₂ f₂ p
  let W₁ : ℝ → ℝ := fun t => w₁ (S t)
  let W₂ : ℝ → ℝ := fun t => w₂ (S t)
  let X₁ : ℝ → ℝ := fun t => Gw₁ (S t) (1, 0)
  let X₂ : ℝ → ℝ := fun t => Gw₂ (S t) (1, 0)
  let Z₁ : ℝ → ℝ := fun t => f₁ (S t) - m₁
  let Z₂ : ℝ → ℝ := fun t => f₂ (S t) - m₂
  let Y₁ : ℝ → ℝ := fun t => G₁ (S t) (1, 0)
  let Y₂ : ℝ → ℝ := fun t => G₂ (S t) (1, 0)
  let e₁ := m₁ - f₁ (p.1, p.1)
  let e₂ := m₂ - f₂ (p.1, p.1)
  let N₁ := weightedEndpointNumerator (w₁ (p.1, p.1)) e₁ d X₁ Z₁ W₁ Y₁
  let N₂ := weightedEndpointNumerator (w₂ (p.1, p.1)) e₂ d X₂ Z₂ W₂ Y₂
  let R₁ := ∫ t in (0 : ℝ)..1, W₁ t
  let R₂ := ∫ t in (0 : ℝ)..1, W₂ t
  have hpK : p ∈ K := by
    rw [← interior_closedCoordTriangle] at hp
    exact interior_subset hp
  have hpstrict : a < p.1 ∧ p.1 < p.2 ∧ p.2 < b := hp
  have hd : 0 < d := sub_pos.mpr hpstrict.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith [hsize]
  have hC : 0 ≤ C := (hc.le.trans (hweight₂ p hpK).1).trans (hweight₂ p hpK).2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hseg : ContinuousOn S (Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (p.1, p.1 + t * (p.2 - p.1))) (Icc 0 1)
    fun_prop
  have hmap : MapsTo S (Icc (0 : ℝ) 1) K :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hpK ht
  have hjet₁ : ∀ z ∈ K, HasFDerivWithinAt f₁ (G₁ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₁ hG₁ hdf₁ hderiv₁ hz
  have hjet₂ : ∀ z ∈ K, HasFDerivWithinAt f₂ (G₂ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₂ hG₂ hdf₂ hderiv₂ hz
  let Gdiff : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z => G₁ z - G₂ z
  have hjetdiff : ∀ z ∈ K,
      HasFDerivWithinAt (f₁ - f₂) (Gdiff z) K z := by
    intro z hz
    exact (hjet₁ z hz).sub (hjet₂ z hz)
  have hGdiffV : ∀ z ∈ K, |Gdiff z (0, 1)| ≤ D := by
    intro z hz
    simpa only [Gdiff, sub_apply] using hGVDiff z hz
  have hHdiff : |weightedDiagonalError w₁ f₁ p -
      weightedDiagonalError w₂ f₂ p| ≤ M * d * D := by
    exact abs_weightedDiagonalError_sub_le_of_jets hc hD
      hw₁ hw₂ hf₁ hf₂ (fun z hz => (hweight₁ z hz).1) hweight₂
      hwdiff hjet₁ hjet₂ hG₁V hG₂V hGVDiff
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le
  have he₁ : |e₁| ≤ B * d :=
    abs_weightedDiagonalMean_sub_lower_le_of_jet hw₁ hf₁
      (fun z hz => (hweight₁ z hz).1) hc hB hjet₁ hG₁V
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le
  have he₂ : |e₂| ≤ B * d :=
    abs_weightedDiagonalMean_sub_lower_le_of_jet hw₂ hf₂
      (fun z hz => (hweight₂ z hz).1) hc hB hjet₂ hG₂V
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le
  have heDiff : |e₁ - e₂| ≤ M * d * D :=
    abs_weightedDiagonalMean_sub_lower_sub_le_of_jets hc hD
      hw₁ hw₂ hf₁ hf₂ (fun z hz => (hweight₁ z hz).1)
      hweight₂ hwdiff hjet₁ hjet₂ hG₁V hG₂V hGVDiff
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le
  have hZ₁ : ∀ t ∈ Icc (0 : ℝ) 1, |Z₁ t| ≤ B * d := by
    intro t ht
    have h := abs_weightedDiagonalMean_sub_segment_le_of_jet hw₁ hf₁
      (fun z hz => (hweight₁ z hz).1) hc hB hjet₁ hG₁V
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le ht
    simpa only [Z₁, m₁, S, d, abs_sub_comm] using h
  have hZ₂ : ∀ t ∈ Icc (0 : ℝ) 1, |Z₂ t| ≤ B * d := by
    intro t ht
    have h := abs_weightedDiagonalMean_sub_segment_le_of_jet hw₂ hf₂
      (fun z hz => (hweight₂ z hz).1) hc hB hjet₂ hG₂V
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le ht
    simpa only [Z₂, m₂, S, d, abs_sub_comm] using h
  have hZDiff : ∀ t ∈ Icc (0 : ℝ) 1,
      |Z₁ t - Z₂ t| ≤ (1 + M) * d * D := by
    intro t ht
    exact abs_centered_weightedDiagonalMean_sub_segment_sub_le hD
      hjetdiff hGdiffV hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le ht hHdiff
  have hR₁ : c ≤ R₁ := integral_diagonalSegment_weight_ge hw₁
    (fun z hz => (hweight₁ z hz).1) hpK
  have hR₂ : c ≤ R₂ := integral_diagonalSegment_weight_ge hw₂
    (fun z hz => (hweight₂ z hz).1) hpK
  have hRDiff : |R₁ - R₂| ≤ D := by
    have hw₁i : IntervalIntegrable W₁ volume 0 1 :=
      (hw₁.comp hseg hmap).intervalIntegrable_of_Icc (by norm_num)
    have hw₂i : IntervalIntegrable W₂ volume 0 1 :=
      (hw₂.comp hseg hmap).intervalIntegrable_of_Icc (by norm_num)
    change |(∫ t in (0 : ℝ)..1, W₁ t) -
      (∫ t in (0 : ℝ)..1, W₂ t)| ≤ D
    rw [← intervalIntegral.integral_sub hw₁i hw₂i]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := D)
      (f := fun t => W₁ t - W₂ t) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
          exact ⟨ht.1.le, ht.2⟩
        simpa only [Real.norm_eq_abs] using hwdiff _ (hmap ht'))
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  have hI₁ : IntervalIntegrable
      (fun t => X₁ t * Z₁ t + W₁ t * Y₁ t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (((hGw₁.comp hseg hmap).clm_apply continuousOn_const).mul
      ((hf₁.comp hseg hmap).sub continuousOn_const)).add
      ((hw₁.comp hseg hmap).mul
        ((hG₁.comp hseg hmap).clm_apply continuousOn_const))
  have hI₂ : IntervalIntegrable
      (fun t => X₂ t * Z₂ t + W₂ t * Y₂ t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (((hGw₂.comp hseg hmap).clm_apply continuousOn_const).mul
      ((hf₂.comp hseg hmap).sub continuousOn_const)).add
      ((hw₂.comp hseg hmap).mul
        ((hG₂.comp hseg hmap).clm_apply continuousOn_const))
  have hN₂ : |N₂| ≤ Aφ := by
    exact abs_weightedEndpointNumerator_le hd hdle hB hC hL
      (by
        rw [abs_of_nonneg (hc.le.trans (hweight₂ _ (by
          exact ⟨hpstrict.1.le, le_rfl, by linarith [hpstrict.2.1, hpstrict.2.2]⟩)).1)]
        exact (hweight₂ _ (by
          exact ⟨hpstrict.1.le, le_rfl, by linarith [hpstrict.2.1, hpstrict.2.2]⟩)).2)
      he₂
      (fun t ht => hGw₂U _ (hmap ht)) hZ₂
      (fun t ht => by
        rw [abs_of_nonneg (hc.le.trans (hweight₂ _ (hmap ht)).1)]
        exact (hweight₂ _ (hmap ht)).2)
      (fun t ht => hG₂U _ (hmap ht))
  have hNDiff : |N₁ - N₂| ≤ AΔ * D := by
    apply abs_weightedEndpointNumerator_sub_le hd hdle hB hC hL hM hD
    · have hdiag : (p.1, p.1) ∈ K :=
        ⟨hpstrict.1.le, le_rfl, by linarith [hpstrict.2.1, hpstrict.2.2]⟩
      rw [abs_of_nonneg (hc.le.trans (hweight₂ _ hdiag).1)]
      exact (hweight₂ _ hdiag).2
    · exact hwdiff _
        ⟨hpstrict.1.le, le_rfl, by linarith [hpstrict.2.1, hpstrict.2.2]⟩
    · exact he₁
    · exact heDiff
    · exact fun t ht => hGw₂U _ (hmap ht)
    · exact fun t ht => hGwUDiff _ (hmap ht)
    · exact hZ₁
    · exact hZDiff
    · intro t ht
      rw [abs_of_nonneg (hc.le.trans (hweight₂ _ (hmap ht)).1)]
      exact (hweight₂ _ (hmap ht)).2
    · exact fun t ht => hwdiff _ (hmap ht)
    · exact fun t ht => hG₁U _ (hmap ht)
    · exact fun t ht => hGUDiff _ (hmap ht)
    · exact hI₁
    · exact hI₂
  have hQ : |N₁ / R₁ - N₂ / R₂| ≤
      (AΔ / c + Aφ / c ^ 2) * D := by
    have h := abs_div_sub_div_le hc hR₁ hR₂ hNDiff hRDiff hN₂
    convert h using 1 <;> ring
  have hformula₁ := fderivWithin_weightedDiagonalError_horizontal_eq_endpoint
    hab hw₁ hf₁ hGw₁ hG₁ hdw₁ hdf₁ hderivw₁ hderiv₁
    (fun z hz => (hweight₁ z hz).1) hc hp
  have hformula₂ := fderivWithin_weightedDiagonalError_horizontal_eq_endpoint
    hab hw₂ hf₂ hGw₂ hG₂ hdw₂ hdf₂ hderivw₂ hderiv₂
    (fun z hz => (hweight₂ z hz).1) hc hp
  have hform₁ : (fderivWithin ℝ (weightedDiagonalError w₁ f₁) K p) (1, 0) =
      G₁ p (1, 0) - N₁ / R₁ := by
    simpa only [N₁, R₁, weightedEndpointNumerator, e₁, d, X₁, Z₁, W₁, Y₁,
      m₁, S] using hformula₁
  have hform₂ : (fderivWithin ℝ (weightedDiagonalError w₂ f₂) K p) (1, 0) =
      G₂ p (1, 0) - N₂ / R₂ := by
    simpa only [N₂, R₂, weightedEndpointNumerator, e₂, d, X₂, Z₂, W₂, Y₂,
      m₂, S] using hformula₂
  rw [hform₁, hform₂]
  have hid : (G₁ p (1, 0) - N₁ / R₁) - (G₂ p (1, 0) - N₂ / R₂) =
      (G₁ p (1, 0) - G₂ p (1, 0)) - (N₁ / R₁ - N₂ / R₂) := by ring
  rw [hid]
  have htri : |(G₁ p (1, 0) - G₂ p (1, 0)) - (N₁ / R₁ - N₂ / R₂)| ≤
      |G₁ p (1, 0) - G₂ p (1, 0)| + |N₁ / R₁ - N₂ / R₂| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (G₁ p (1, 0) - G₂ p (1, 0)) 0 (N₁ / R₁ - N₂ / R₂)
  calc
    _ ≤ |G₁ p (1, 0) - G₂ p (1, 0)| + |N₁ / R₁ - N₂ / R₂| := htri
    _ ≤ D + (AΔ / c + Aφ / c ^ 2) * D := add_le_add (hGUDiff p hpK) hQ
    _ = (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) +
          B + L * (1 + ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) + L + C) / c +
        (C * B + L * B + C * L) / c ^ 2) * D := by dsimp [AΔ, Aφ, M]; ring

/-- A two-input horizontal jet bound extends from the interior to the entire
closed coordinate triangle. -/
theorem abs_fderivWithin_horizontal_sub_le_of_interior
    {a b D : ℝ} (hab : a < b) {F₁ F₂ : ℝ × ℝ → ℝ}
    (hC1₁ : ContDiffOn ℝ 1 F₁ (closedCoordTriangle a b))
    (hC1₂ : ContDiffOn ℝ 1 F₂ (closedCoordTriangle a b))
    (hinterior : ∀ p ∈ interior (closedCoordTriangle a b),
      |(fderivWithin ℝ F₁ (closedCoordTriangle a b) p) (1, 0) -
        (fderivWithin ℝ F₂ (closedCoordTriangle a b) p) (1, 0)| ≤ D)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ F₁ (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ F₂ (closedCoordTriangle a b) p) (1, 0)| ≤ D := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont₁ : ContinuousOn (fun z => (fderivWithin ℝ F₁ K z) (1, 0)) K :=
    (hC1₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hcont₂ : ContinuousOn (fun z => (fderivWithin ℝ F₂ K z) (1, 0)) K :=
    (hC1₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hcont : ContinuousOn (fun z =>
      |(fderivWithin ℝ F₁ K z) (1, 0) -
        (fderivWithin ℝ F₂ K z) (1, 0)|) K :=
    (hcont₁.sub hcont₂).abs
  have hclosure : closure (interior K) = K := by
    rw [interior_closedCoordTriangle, closure_openCoordTriangle hab]
  change p ∈ K at hp
  rw [← hclosure] at hp
  have hcont' : ContinuousOn (fun z =>
      |(fderivWithin ℝ F₁ K z) (1, 0) -
        (fderivWithin ℝ F₂ K z) (1, 0)|) (closure (interior K)) := by
    rw [hclosure]
    exact hcont
  have hinside : ∀ z ∈ interior K,
      |(fderivWithin ℝ F₁ K z) (1, 0) -
        (fderivWithin ℝ F₂ K z) (1, 0)| ≤ D := hinterior
  exact le_on_closure hinside hcont' continuousOn_const hp

/-- The exact two-input horizontal first-jet difference bound holds on the
entire closed coordinate triangle. -/
theorem abs_fderivWithin_weightedDiagonalError_horizontal_sub_le
    {a b c C B L D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderiv₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = G₁ p)
    (hderiv₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = G₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    (hGw₁U : ∀ p ∈ closedCoordTriangle a b, |Gw₁ p (1, 0)| ≤ L)
    (hGw₂U : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (1, 0)| ≤ L)
    (hG₁U : ∀ p ∈ closedCoordTriangle a b, |G₁ p (1, 0)| ≤ L)
    (hG₂U : ∀ p ∈ closedCoordTriangle a b, |G₂ p (1, 0)| ≤ L)
    (hG₁V : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hG₂V : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hGwUDiff : ∀ p ∈ closedCoordTriangle a b,
      |Gw₁ p (1, 0) - Gw₂ p (1, 0)| ≤ D)
    (hGUDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (1, 0) - G₂ p (1, 0)| ≤ D)
    (hGVDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (0, 1) - G₂ p (0, 1)| ≤ D)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L) (hD : 0 ≤ D)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalError w₁ f₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) +
          B + L * (1 + ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) + L + C) / c +
        (C * B + L * B + C * L) / c ^ 2) * D := by
  have hC1₁ := contDiffOn_weightedDiagonalError hab hw₁ hf₁ hGw₁ hG₁
    hdw₁ hdf₁ hderivw₁ hderiv₁ (fun z hz => (hweight₁ z hz).1) hc
  have hC1₂ := contDiffOn_weightedDiagonalError hab hw₂ hf₂ hGw₂ hG₂
    hdw₂ hdf₂ hderivw₂ hderiv₂ (fun z hz => (hweight₂ z hz).1) hc
  apply abs_fderivWithin_horizontal_sub_le_of_interior hab hC1₁ hC1₂ _ hp
  intro z hz
  exact abs_fderivWithin_weightedDiagonalError_horizontal_sub_le_of_jets hab hsize
    hw₁ hw₂ hf₁ hf₂ hGw₁ hGw₂ hG₁ hG₂ hdw₁ hdw₂ hdf₁ hdf₂
    hderivw₁ hderivw₂ hderiv₁ hderiv₂ hweight₁ hweight₂ hwdiff
    hGw₁U hGw₂U hG₁U hG₂U hG₁V hG₂V hGwUDiff hGUDiff hGVDiff
    hc hB hL hD (by rwa [interior_closedCoordTriangle] at hz)

end intervalIntegral

end
