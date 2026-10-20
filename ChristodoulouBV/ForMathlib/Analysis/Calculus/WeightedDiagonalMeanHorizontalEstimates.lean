module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanHorizontalCalculus
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Bounds for horizontal derivatives of weighted diagonal means

The exact endpoint formula gives first-derivative estimates on a bounded jet box.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The exact horizontal derivative bound for the weighted error on the
interior of a unit-size coordinate triangle. -/
theorem abs_fderivWithin_weightedDiagonalError_horizontal_le_of_jets
    {a b c C B L : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
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
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hGwU : ∀ p ∈ closedCoordTriangle a b, |Gw p (1, 0)| ≤ L)
    (hGfU : ∀ p ∈ closedCoordTriangle a b, |Gf p (1, 0)| ≤ L)
    (hGfV : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) p) (1, 0)| ≤
      L + (C * B + L * B + C * L) / c := by
  let d := p.2 - p.1
  let D := ∫ t in (0 : ℝ)..1, w (diagonalSegment p t)
  let m := weightedDiagonalMean w f p
  let A : ℝ → ℝ := fun t =>
    Gw (diagonalSegment p t) (1, 0) * (f (diagonalSegment p t) - m) +
      w (diagonalSegment p t) * Gf (diagonalSegment p t) (1, 0)
  let I := ∫ t in (0 : ℝ)..1, A t
  have hpK : p ∈ closedCoordTriangle a b := by
    rw [← interior_closedCoordTriangle] at hp
    exact interior_subset hp
  have hpstrict : a < p.1 ∧ p.1 < p.2 ∧ p.2 < b := hp
  have hd : 0 < d := sub_pos.mpr hpstrict.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith [hsize]
  have hC : 0 ≤ C :=
    (hc.le.trans (hweight p hpK).1).trans (hweight p hpK).2
  have hD : c ≤ D := integral_diagonalSegment_weight_ge hw
    (fun z hz => (hweight z hz).1) hpK
  have hDpos : 0 < D := hc.trans_le hD
  have hjetf : ∀ z ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf z) (closedCoordTriangle a b) z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf hGf hdf hderivf hz
  have hlower : |m - f (p.1, p.1)| ≤ B * d := by
    exact abs_weightedDiagonalMean_sub_lower_le_of_jet hw hf
      (fun z hz => (hweight z hz).1) hc hB hjetf hGfV
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      diagonalSegment p t ∈ closedCoordTriangle a b :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hpK ht
  have hApoint : ∀ t ∈ Icc (0 : ℝ) 1,
      |A t| ≤ L * B * d + C * L := by
    intro t ht
    have hmean := abs_weightedDiagonalMean_sub_segment_le_of_jet hw hf
      (fun z hz => (hweight z hz).1) hc hB hjetf hGfV
      hpstrict.1.le hpstrict.2.1.le hpstrict.2.2.le ht
    have hmean' : |f (diagonalSegment p t) - m| ≤ B * d := by
      simpa only [abs_sub_comm, m, d] using hmean
    have hwbound : |w (diagonalSegment p t)| ≤ C := by
      rw [abs_of_nonneg (hc.le.trans (hweight _ (hseg t ht)).1)]
      exact (hweight _ (hseg t ht)).2
    have hfirst : |Gw (diagonalSegment p t) (1, 0) *
        (f (diagonalSegment p t) - m)| ≤ L * (B * d) := by
      rw [abs_mul]
      exact mul_le_mul (hGwU _ (hseg t ht)) hmean'
        (abs_nonneg _) hL
    have hsecond : |w (diagonalSegment p t) *
        Gf (diagonalSegment p t) (1, 0)| ≤ C * L := by
      rw [abs_mul]
      exact mul_le_mul hwbound (hGfU _ (hseg t ht)) (abs_nonneg _) hC
    calc
      |A t| ≤ |Gw (diagonalSegment p t) (1, 0) *
            (f (diagonalSegment p t) - m)| +
          |w (diagonalSegment p t) * Gf (diagonalSegment p t) (1, 0)| :=
        abs_add_le _ _
      _ ≤ L * (B * d) + C * L := add_le_add hfirst hsecond
      _ = L * B * d + C * L := by ring
  have hI : |I| ≤ L * B * d + C * L := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := L * B * d + C * L)
      (f := A) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
          exact ⟨ht.1.le, ht.2⟩
        simpa only [Real.norm_eq_abs] using hApoint t ht')
    simpa only [I, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  have hend : |w (p.1, p.1) * (m - f (p.1, p.1)) / d| ≤ C * B := by
    have hdiag : (p.1, p.1) ∈ closedCoordTriangle a b :=
      ⟨hpstrict.1.le, le_rfl, by linarith [hpstrict.2.1, hpstrict.2.2]⟩
    have hw0 : |w (p.1, p.1)| ≤ C := by
      rw [abs_of_nonneg (hc.le.trans (hweight _ hdiag).1)]
      exact (hweight _ hdiag).2
    rw [abs_div, abs_mul, abs_of_pos hd]
    have hnum := mul_le_mul hw0 hlower (abs_nonneg _) hC
    have hnum' : |w (p.1, p.1)| * |m - f (p.1, p.1)| ≤ C * B * d := by
      calc
        _ ≤ C * (B * d) := hnum
        _ = C * B * d := by ring
    exact (div_le_iff₀ hd).2 (by nlinarith [hnum'])
  have hAbound : |w (p.1, p.1) * (m - f (p.1, p.1)) / d + I| ≤
      C * B + L * B + C * L := by
    calc
      _ ≤ |w (p.1, p.1) * (m - f (p.1, p.1)) / d| + |I| := abs_add_le _ _
      _ ≤ C * B + (L * B * d + C * L) := add_le_add hend hI
      _ ≤ C * B + L * B + C * L := by
        nlinarith [mul_le_mul_of_nonneg_left hdle (mul_nonneg hL hB)]
  rw [fderivWithin_weightedDiagonalError_horizontal_eq_endpoint hab
    hw hf hGw hGf hdw hdf hderivw hderivf
    (fun z hz => (hweight z hz).1) hc hp]
  change |Gf p (1, 0) - (w (p.1, p.1) * (m - f (p.1, p.1)) / d + I) / D| ≤ _
  have hquot : |(w (p.1, p.1) * (m - f (p.1, p.1)) / d + I) / D| ≤
      (C * B + L * B + C * L) / c := by
    rw [abs_div, abs_of_pos hDpos]
    have hnum : 0 ≤ C * B + L * B + C * L := by positivity
    calc
      _ ≤ (C * B + L * B + C * L) / D :=
        div_le_div_of_nonneg_right hAbound hDpos.le
      _ ≤ (C * B + L * B + C * L) / c :=
        div_le_div_of_nonneg_left hnum hc hD
  have htri : |Gf p (1, 0) -
      (w (p.1, p.1) * (m - f (p.1, p.1)) / d + I) / D| ≤
      |Gf p (1, 0)| +
        |(w (p.1, p.1) * (m - f (p.1, p.1)) / d + I) / D| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (Gf p (1, 0)) 0
        ((w (p.1, p.1) * (m - f (p.1, p.1)) / d + I) / D)
  calc
    _ ≤ |Gf p (1, 0)| +
        |(w (p.1, p.1) * (m - f (p.1, p.1)) / d + I) / D| := htri
    _ ≤ L + (C * B + L * B + C * L) / c :=
      add_le_add (hGfU p hpK) hquot

/-- A bound for the horizontal component of a continuous first jet extends
from the interior to the closed coordinate triangle. -/
theorem abs_fderivWithin_horizontal_le_of_interior
    {a b M : ℝ} (hab : a < b) {F : ℝ × ℝ → ℝ}
    (hC1 : ContDiffOn ℝ 1 F (closedCoordTriangle a b))
    (hinterior : ∀ p ∈ interior (closedCoordTriangle a b),
      |(fderivWithin ℝ F (closedCoordTriangle a b) p) (1, 0)| ≤ M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ F (closedCoordTriangle a b) p) (1, 0)| ≤ M := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont : ContinuousOn
      (fun z => |(fderivWithin ℝ F K z) (1, 0)|) K :=
    ((hC1.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).abs
  have hclosure : closure (interior K) = K := by
    rw [interior_closedCoordTriangle, closure_openCoordTriangle hab]
  change p ∈ K at hp
  rw [← hclosure] at hp
  have hcont' : ContinuousOn (fun z => |(fderivWithin ℝ F K z) (1, 0)|)
      (closure (interior K)) := by
    rw [hclosure]
    exact hcont
  have hinside : ∀ z ∈ interior K,
      |(fderivWithin ℝ F K z) (1, 0)| ≤ M := hinterior
  exact le_on_closure hinside hcont' continuousOn_const hp

/-- The exact horizontal derivative bound extends to all three closed edges
and both vertices of a unit-size coordinate triangle. -/
theorem abs_fderivWithin_weightedDiagonalError_horizontal_le
    {a b c C B L : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
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
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hGwU : ∀ p ∈ closedCoordTriangle a b, |Gw p (1, 0)| ≤ L)
    (hGfU : ∀ p ∈ closedCoordTriangle a b, |Gf p (1, 0)| ≤ L)
    (hGfV : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalError w f) (closedCoordTriangle a b) p) (1, 0)| ≤
      L + (C * B + L * B + C * L) / c := by
  have hC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf (fun z hz => (hweight z hz).1) hc
  apply abs_fderivWithin_horizontal_le_of_interior hab hC1 _ hp
  intro z hz
  exact abs_fderivWithin_weightedDiagonalError_horizontal_le_of_jets hab hsize
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hGwU hGfU hGfV
    hc hB hL (by rwa [interior_closedCoordTriangle] at hz)


end intervalIntegral

end
