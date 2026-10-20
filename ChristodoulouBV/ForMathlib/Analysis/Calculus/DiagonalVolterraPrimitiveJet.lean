module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraQuotientBox
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartialBanach
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# First jets of vertical Volterra primitives

The primitive of a continuous first jet on a coordinate triangle can be
differentiated in its three scalar parameters. The first-coordinate formula
uses a rectangle contained in the triangle, so no extension across its
diagonal is required.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The closed three-coordinate domain for a vertical Volterra primitive. -/
@[expose] def closedVolterraTriple (a b : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ p.2 ∧ p.2 ≤ b}

/-- Differentiation under the integral sign in the first coordinate of a
vertical primitive. The relative derivative includes `u=w` whenever the
available horizontal interval `[a,w]` has positive length. -/
theorem hasDerivWithinAt_integral_first_of_triangle_jet
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt k (G p) (closedCoordTriangle a b) p)
    {u w v : ℝ} (haw : a < w) (hu : a ≤ u) (huw : u ≤ w)
    (hwv : w ≤ v) (hv : v ≤ b) :
    HasDerivWithinAt (fun x => ∫ s in w..v, k (x, s))
      (∫ s in w..v, G (u, s) (1, 0)) (Icc a w) u := by
  have huI : u ∈ Icc a w := ⟨hu, huw⟩
  have hvI : v ∈ Icc w v := ⟨hwv, le_rfl⟩
  have hrect : Icc a w ×ˢ Icc w v ⊆ closedCoordTriangle a b := by
    intro p hp
    have hx : p.1 ∈ Icc a w := hp.1
    have hs : p.2 ∈ Icc w v := hp.2
    exact ⟨hx.1, hx.2.trans hs.1, hs.2.trans hv⟩
  have hkrect : ContinuousOn k (Icc a w ×ˢ Icc w v) := hk.mono hrect
  have hGrect : ContinuousOn (fun p => G p (1, 0))
      (Icc a w ×ˢ Icc w v) :=
    (hG.mono hrect).clm_apply continuousOn_const
  have hderiv : ∀ x ∈ Ioo a w, ∀ s ∈ Icc w v,
      HasDerivAt (fun y => k (y, s)) (G (x, s) (1, 0)) x := by
    intro x hx s hs
    have hxs : (x, s) ∈ closedCoordTriangle a b :=
      ⟨hx.1.le, hx.2.le.trans hs.1, hs.2.trans hv⟩
    have hpath : HasDerivAt (fun y : ℝ => (y, s)) (1, 0) x := by
      simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x s)
    have hevent : ∀ᶠ y in 𝓝 x, (y, s) ∈ closedCoordTriangle a b := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact ⟨hy.1.le, hy.2.le.trans hs.1, hs.2.trans hv⟩
    simpa only [Function.comp_def] using
      (hjet (x, s) hxs).comp_hasDerivAt x hpath hevent
  exact hasDerivWithinAt_integral_of_continuousOn_rectangle_banach
    haw huI hvI hkrect hGrect hderiv

/-- FTC gives the upper-endpoint derivative of a vertical primitive at all
points of its closed admissible interval, including both endpoints. -/
theorem hasDerivWithinAt_integral_upper_of_triangle_continuous
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    {u w v : ℝ} (hu : a ≤ u) (huw : u ≤ w)
    (hwv : w ≤ v) (hv : v ≤ b) :
    HasDerivWithinAt (fun y => ∫ s in w..y, k (u, s))
      (k (u, v)) (Icc w b) v := by
  have hslice : ContinuousOn (fun s => k (u, s)) (Icc w b) :=
    hk.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro s hs
      exact ⟨hu, huw.trans hs.1, hs.2⟩)
  have hsub : Icc w v ⊆ Icc w b := Icc_subset_Icc le_rfl hv
  have hint : IntervalIntegrable (fun s => k (u, s)) volume w v :=
    (hslice.mono hsub).intervalIntegrable_of_Icc hwv
  have hvI : v ∈ Icc w b := ⟨hwv, hv⟩
  let _ : Fact (v ∈ Icc w b) := ⟨hvI⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hslice.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v)
    (hslice v hvI)

/-- FTC gives the negative lower-endpoint derivative of a vertical primitive
on the whole closed interval of admissible lower endpoints. -/
theorem hasDerivWithinAt_integral_lower_of_triangle_continuous
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    {u w v : ℝ} (hu : a ≤ u) (huw : u ≤ w)
    (hwv : w ≤ v) (hv : v ≤ b) :
    HasDerivWithinAt (fun y => ∫ s in y..v, k (u, s))
      (-k (u, w)) (Icc u v) w := by
  have hslice : ContinuousOn (fun s => k (u, s)) (Icc u v) :=
    hk.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro s hs
      exact ⟨hu, hs.1, hs.2.trans hv⟩)
  have hsub : Icc w v ⊆ Icc u v := Icc_subset_Icc huw le_rfl
  have hint : IntervalIntegrable (fun s => k (u, s)) volume w v :=
    (hslice.mono hsub).intervalIntegrable_of_Icc hwv
  have hwI : w ∈ Icc u v := ⟨huw, hwv⟩
  let _ : Fact (w ∈ Icc u v) := ⟨hwI⟩
  exact intervalIntegral.integral_hasDerivWithinAt_left hint
    (hslice.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc w)
    (hslice w hwI)

/-- The continuous first-coordinate candidate for a vertical primitive on
its closed three-coordinate domain. -/
@[expose] noncomputable def verticalVolterraFirstJet
    (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ∫ s in p.1.2..p.2, G (p.1.1, s) (1, 0)

/-- All three coordinate-jet candidates of a vertical primitive vary
continuously over the closed Volterra triple. -/
theorem continuousOn_verticalVolterraPrimitive_jets
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b)) :
    ContinuousOn (verticalVolterraFirstJet G) (closedVolterraTriple a b) ∧
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ => -k (p.1.1, p.1.2))
      (closedVolterraTriple a b) ∧
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ => k (p.1.1, p.2))
      (closedVolterraTriple a b) := by
  let T := closedVolterraTriple a b
  let K := closedCoordTriangle a b
  have hmapLower : MapsTo (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2)) T K := by
    intro p hp
    have hcoord : a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ p.2 ∧ p.2 ≤ b := hp
    exact ⟨hcoord.1, hcoord.2.1, hcoord.2.2.1.trans hcoord.2.2.2⟩
  have hmapUpper : MapsTo (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2)) T K := by
    intro p hp
    have hcoord : a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ p.2 ∧ p.2 ≤ b := hp
    exact ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2.1, hcoord.2.2.2⟩
  have hmapSegment (p : (ℝ × ℝ) × ℝ) (hp : p ∈ T)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (p.1.1, p.1.2 + t * (p.2 - p.1.2)) ∈ K := by
    have hcoord : a ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ p.2 ∧ p.2 ≤ b := hp
    have hd : 0 ≤ p.2 - p.1.2 := sub_nonneg.mpr hcoord.2.2.1
    have hlow : 0 ≤ t * (p.2 - p.1.2) := mul_nonneg ht.1 hd
    have hhigh : t * (p.2 - p.1.2) ≤ p.2 - p.1.2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hd]
    exact ⟨hcoord.1, by linarith, by linarith⟩
  have hGu : ContinuousOn (fun z => G z (1, 0)) K :=
    hG.clm_apply continuousOn_const
  let fK : C(K, ℝ) := ⟨_, hGu.domRestrict⟩
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq (isClosed_closedCoordTriangle a b)
  have hFeq : ∀ z ∈ K, F z = G z (1, 0) := by
    intro z hz
    have h := congrArg (fun H : C(K, ℝ) => H ⟨z, hz⟩) hF
    simpa [fK] using h
  have hsegcont : Continuous (fun pt : ((ℝ × ℝ) × ℝ) × ℝ =>
      (pt.1.1.1, pt.1.1.2 + pt.2 * (pt.1.2 - pt.1.1.2))) := by
    fun_prop
  have hintcont : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      ∫ t in (0 : ℝ)..1,
        F (p.1.1, p.1.2 + t * (p.2 - p.1.2))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact F.continuous.comp hsegcont
  have hgap : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.2 - p.1.2) T := by
    fun_prop
  have hcont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (p.2 - p.1.2) *
        ∫ t in (0 : ℝ)..1,
          F (p.1.1, p.1.2 + t * (p.2 - p.1.2))) T :=
    hgap.mul hintcont.continuousOn
  have hfirst : ContinuousOn (verticalVolterraFirstJet G) T := by
    apply hcont.congr
    intro p hp
    have hsubst := intervalIntegral.smul_integral_comp_add_mul
      (f := fun s : ℝ => G (p.1.1, s) (1, 0))
      (a := (0 : ℝ)) (b := 1) (p.2 - p.1.2) p.1.2
    have hsame : (∫ t in (0 : ℝ)..1,
        F (p.1.1, p.1.2 + t * (p.2 - p.1.2))) =
        ∫ t in (0 : ℝ)..1,
          G (p.1.1, p.1.2 + t * (p.2 - p.1.2)) (1, 0) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      exact hFeq _ (hmapSegment p hp t ht')
    change verticalVolterraFirstJet G p =
      (p.2 - p.1.2) *
        ∫ t in (0 : ℝ)..1, F (p.1.1, p.1.2 + t * (p.2 - p.1.2))
    rw [hsame]
    simpa [verticalVolterraFirstJet, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hsubst.symm
  have hlowcont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (p.1.1, p.1.2)) T := by fun_prop
  have hupcont : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (p.1.1, p.2)) T := by fun_prop
  exact ⟨hfirst, (hk.comp hlowcont hmapLower).neg,
    hk.comp hupcont hmapUpper⟩

/-- The vertical primitive itself is continuous in all three parameters on
the closed Volterra domain. -/
theorem continuousOn_verticalVolterraPrimitive
    {a b : ℝ} {k : ℝ × ℝ → ℝ}
    (hk : ContinuousOn k (closedCoordTriangle a b)) :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      ∫ s in p.1.2..p.2, k (p.1.1, s)) (closedVolterraTriple a b) := by
  let P : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z => (k z) • P
  have hG : ContinuousOn G (closedCoordTriangle a b) :=
    hk.smul continuousOn_const
  have h := (continuousOn_verticalVolterraPrimitive_jets hk hG).1
  apply h.congr
  intro p hp
  change (∫ s in p.1.2..p.2, k (p.1.1, s)) =
    verticalVolterraFirstJet G p
  apply intervalIntegral.integral_congr
  intro s hs
  simp [G, P]

/-- The weighted diagonal Volterra primitive and its three candidate
coordinate jets are continuous across all faces of the closed triple. -/
theorem continuousOn_weightedDiagonalVolterraPrimitive_jets
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) :
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      weightedDiagonalVolterraPrimitive w f p.1.1 p.1.2 p.2)
      (closedVolterraTriple a b) ∧
    ContinuousOn
      (verticalVolterraFirstJet
        (fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
          (closedCoordTriangle a b))) (closedVolterraTriple a b) ∧
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      -weightedDiagonalQuotientKernel w f (p.1.1, p.1.2))
      (closedVolterraTriple a b) ∧
    ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      weightedDiagonalQuotientKernel w f (p.1.1, p.2))
      (closedVolterraTriple a b) := by
  let K := closedCoordTriangle a b
  have hk : ContinuousOn (weightedDiagonalQuotientKernel w f) K :=
    continuousOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc
  have hC1 := contDiffOn_weightedDiagonalQuotientKernel hab
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG := hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hjet := continuousOn_verticalVolterraPrimitive_jets hk hG
  refine ⟨?_, hjet.1, hjet.2.1, hjet.2.2⟩
  simpa only [weightedDiagonalVolterraPrimitive] using
    (continuousOn_verticalVolterraPrimitive hk)

/-- The first-coordinate derivative of the weighted diagonal Volterra
primitive is the integral of the horizontal quotient-kernel jet. -/
theorem hasDerivWithinAt_weightedDiagonalVolterraPrimitive_first
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c)
    {u lower upper : ℝ} (halower : a < lower)
    (hu : a ≤ u) (hulower : u ≤ lower)
    (hlowerupper : lower ≤ upper) (hupper : upper ≤ b) :
    HasDerivWithinAt
      (fun x => weightedDiagonalVolterraPrimitive w f x lower upper)
      (verticalVolterraFirstJet
        (fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
          (closedCoordTriangle a b)) ((u, lower), upper))
      (Icc a lower) u := by
  let K := closedCoordTriangle a b
  have hC1 := contDiffOn_weightedDiagonalQuotientKernel hab
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG : ContinuousOn
      (fderivWithin ℝ (weightedDiagonalQuotientKernel w f) K) K :=
    hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hjet : ∀ p ∈ K,
      HasFDerivWithinAt (weightedDiagonalQuotientKernel w f)
        (fderivWithin ℝ (weightedDiagonalQuotientKernel w f) K p) K p := by
    intro p hp
    exact ((hC1.differentiableOn (by norm_num)) p hp).hasFDerivWithinAt
  have h := hasDerivWithinAt_integral_first_of_triangle_jet
    (continuousOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc)
    hG hjet halower hu hulower hlowerupper hupper
  simpa only [weightedDiagonalVolterraPrimitive, verticalVolterraFirstJet] using h

/-- The upper-endpoint derivative of the weighted diagonal Volterra primitive
is the quotient kernel itself. -/
theorem hasDerivWithinAt_weightedDiagonalVolterraPrimitive_upper
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c)
    {u lower upper : ℝ} (hu : a ≤ u) (hulower : u ≤ lower)
    (hlowerupper : lower ≤ upper) (hupper : upper ≤ b) :
    HasDerivWithinAt
      (fun y => weightedDiagonalVolterraPrimitive w f u lower y)
      (weightedDiagonalQuotientKernel w f (u, upper)) (Icc lower b) upper := by
  exact hasDerivWithinAt_integral_upper_of_triangle_continuous
    (continuousOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc)
    hu hulower hlowerupper hupper

/-- The lower-endpoint derivative of the weighted diagonal Volterra
primitive is minus the quotient kernel at that endpoint. -/
theorem hasDerivWithinAt_weightedDiagonalVolterraPrimitive_lower
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c)
    {u lower upper : ℝ} (hu : a ≤ u) (hulower : u ≤ lower)
    (hlowerupper : lower ≤ upper) (hupper : upper ≤ b) :
    HasDerivWithinAt
      (fun y => weightedDiagonalVolterraPrimitive w f u y upper)
      (-weightedDiagonalQuotientKernel w f (u, lower)) (Icc u upper) lower := by
  exact hasDerivWithinAt_integral_lower_of_triangle_continuous
    (continuousOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc)
    hu hulower hlowerupper hupper

end intervalIntegral

end
