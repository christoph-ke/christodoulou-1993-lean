module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointValue
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Endpoint derivatives of the Picard primitives

The horizontal and vertical endpoint derivatives hold at every point of the
closed triangle, including its edges.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace ChristodoulouBV.AxisPicard

/-- FTC for a horizontal primitive of a kernel continuous on the closed axis
triangle, including both endpoints of the admissible horizontal interval. -/
theorem hasDerivWithinAt_horizontal_integral_upper
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    HasDerivWithinAt (fun t => ∫ s in a..t, k (s, v))
      (k (u, v)) (Icc a v) u := by
  have hslice : ContinuousOn (fun s => k (s, v)) (Icc a v) :=
    hk.comp (continuous_id.prodMk continuous_const).continuousOn (by
      intro s hs
      change a ≤ s ∧ s ≤ v ∧ v ≤ b
      exact ⟨hs.1, hs.2, hvb⟩)
  have hsub : Icc a u ⊆ Icc a v := Icc_subset_Icc le_rfl huv
  have hint : IntervalIntegrable (fun s => k (s, v)) volume a u :=
    (hslice.mono hsub).intervalIntegrable_of_Icc hau
  have huI : u ∈ Icc a v := ⟨hau, huv⟩
  let _ : Fact (u ∈ Icc a v) := ⟨huI⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hslice.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u)
    (hslice u huI)

/-- A horizontal primitive of a continuous triangle kernel is continuous
through the outgoing edge and the diagonal. -/
theorem continuousOn_horizontal_integral {a b : ℝ}
    {k : ℝ × ℝ → ℝ} (hk : ContinuousOn k (closedCoordTriangle a b)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in a..p.1, k (s, p.2))
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let fK : C(K, ℝ) := ⟨_, hk.domRestrict⟩
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq (isClosed_closedCoordTriangle a b)
  have hFeq : ∀ z ∈ K, F z = k z := by
    intro z hz
    have h := congrArg (fun H : C(K, ℝ) => H ⟨z, hz⟩) hF
    simpa [fK] using h
  have hsegcont : Continuous (fun pt : (ℝ × ℝ) × ℝ =>
      (a + pt.2 * (pt.1.1 - a), pt.1.2)) := by fun_prop
  have hintcont : Continuous (fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..1, F (a + t * (p.1 - a), p.2)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact F.continuous.comp hsegcont
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (p.1 - a) * ∫ t in (0 : ℝ)..1,
        F (a + t * (p.1 - a), p.2)) K := by
    exact (continuous_fst.sub continuous_const).continuousOn.mul
      hintcont.continuousOn
  apply hcont.congr
  intro p hp
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (a + t * (p.1 - a), p.2) ∈ K := by
    have hd : 0 ≤ p.1 - a := sub_nonneg.mpr hp.1
    have hlo : 0 ≤ t * (p.1 - a) := mul_nonneg ht.1 hd
    have hhi : t * (p.1 - a) ≤ p.1 - a := by
      nlinarith only [ht.2, hd]
    change a ≤ a + t * (p.1 - a) ∧
      a + t * (p.1 - a) ≤ p.2 ∧ p.2 ≤ b
    exact ⟨by linarith only [hlo], by linarith only [hhi, hp.2.1], hp.2.2⟩
  have hsame : (∫ t in (0 : ℝ)..1,
      F (a + t * (p.1 - a), p.2)) =
      ∫ t in (0 : ℝ)..1, k (a + t * (p.1 - a), p.2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    exact hFeq _ (hsegment t htI)
  have hsubst := intervalIntegral.smul_integral_comp_add_mul
    (f := fun s : ℝ => k (s, p.2))
    (a := (0 : ℝ)) (b := 1) (p.1 - a) a
  change (∫ s in a..p.1, k (s, p.2)) =
    (p.1 - a) * ∫ t in (0 : ℝ)..1,
      F (a + t * (p.1 - a), p.2)
  rw [hsame]
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsubst.symm

/-- Differentiating a horizontal primitive in its transverse coordinate at
an interior parameter uses a rectangle contained in the axis triangle. -/
theorem hasDerivAt_horizontal_integral_transverse
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt k (G p) (closedCoordTriangle a b) p)
    {u v : ℝ} (hau : a ≤ u) (huv : u < v) (hvb : v < b) :
    HasDerivAt (fun t => ∫ s in a..u, k (s, t))
      (∫ s in a..u, G (s, v) (0, 1)) v := by
  have hrect : Icc u b ×ˢ Icc a u ⊆
      {p : ℝ × ℝ | (p.2, p.1) ∈ closedCoordTriangle a b} := by
    intro p hp
    have hx : p.1 ∈ Icc u b := hp.1
    have hs : p.2 ∈ Icc a u := hp.2
    change a ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ b
    exact ⟨hs.1, hs.2.trans hx.1, hx.2⟩
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.2, p.1))
      (Icc u b ×ˢ Icc a u) (closedCoordTriangle a b) :=
    fun p hp => hrect hp
  have hkrect : ContinuousOn (fun p : ℝ × ℝ => k (p.2, p.1))
      (Icc u b ×ˢ Icc a u) :=
    hk.comp (continuous_snd.prodMk continuous_fst).continuousOn hmap
  have hGrect : ContinuousOn (fun p : ℝ × ℝ => G (p.2, p.1) (0, 1))
      (Icc u b ×ˢ Icc a u) :=
    (hG.comp (continuous_snd.prodMk continuous_fst).continuousOn hmap).clm_apply
      continuousOn_const
  have hderiv : ∀ x ∈ Ioo u b, ∀ s ∈ Icc a u,
      HasDerivAt (fun y => k (s, y)) (G (s, x) (0, 1)) x := by
    intro x hx s hs
    have hsx : (s, x) ∈ closedCoordTriangle a b := by
      change a ≤ s ∧ s ≤ x ∧ x ≤ b
      exact ⟨hs.1, hs.2.trans hx.1.le, hx.2.le⟩
    have hpath : HasDerivAt (fun y : ℝ => (s, y)) (0, 1) x := by
      simpa using (hasDerivAt_const x s).prodMk (hasDerivAt_id x)
    have hevent : ∀ᶠ y in 𝓝 x, (s, y) ∈ closedCoordTriangle a b := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      change a ≤ s ∧ s ≤ y ∧ y ≤ b
      exact ⟨hs.1, hs.2.trans hy.1.le, hy.2.le⟩
    simpa only [Function.comp_def] using
      (hjet (s, x) hsx).comp_hasDerivAt x hpath hevent
  exact intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle_banach
    ⟨huv, hvb⟩ ⟨hau, le_refl u⟩ hkrect hGrect hderiv

/-- The outgoing Picard primitive has horizontal derivative equal to the
input gravitational coefficient throughout the closed triangle. -/
theorem Box.picard_lam_horizontal_deriv {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    HasDerivWithinAt
      (fun t => (x.1.toTriple.picard a g hEdge).lam (t, v))
      (x.1.toTriple.gravitational (u, v)) (Icc a v) u := by
  have hk := (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn
  have h := hasDerivWithinAt_horizontal_integral_upper hk hau huv hvb
  convert (((hasDerivAt_const u (g v)).hasDerivWithinAt).add h) using 1
  · ext t
    simp only [Triple.picard, Pi.add_apply]
  · simp only [zero_add]

/-- The scalar Picard primitive has horizontal derivative equal to the input
scalar source throughout the closed triangle. -/
theorem Box.picard_h_horizontal_deriv {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    HasDerivWithinAt
      (fun t => (x.1.toTriple.picard a g hEdge).h (t, v))
      (x.1.toTriple.scalarSource (u, v)) (Icc a v) u := by
  have hq := (x.picard_coefficients_c1 hab hM hsmall).2.continuousOn
  have h := hasDerivWithinAt_horizontal_integral_upper hq hau huv hvb
  convert (((hasDerivAt_const u (hEdge v)).hasDerivWithinAt).add h) using 1
  · ext t
    simp only [Triple.picard, Pi.add_apply]
  · simp only [zero_add]

/-- The incoming Picard primitive has vertical derivative equal to the input
gravitational coefficient throughout the closed triangle. -/
theorem Box.picard_nu_vertical_deriv {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    HasDerivWithinAt
      (fun t => (x.1.toTriple.picard a g hEdge).nu (u, t))
      (x.1.toTriple.gravitational (u, v)) (Icc u b) v := by
  have hk := (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn
  have h := intervalIntegral.hasDerivWithinAt_integral_upper_of_triangle_continuous
    hk hau (le_refl u) huv hvb
  convert (((hasDerivAt_const v
    (-(x.1.toTriple.picard a g hEdge).lam (u, u))).hasDerivWithinAt).add h) using 1
  · ext t
    simp only [Triple.picard, Pi.add_apply]
  · simp only [zero_add]

end ChristodoulouBV.AxisPicard

end
