module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxisCoefficients
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Attenuated Volterra integral of a positive weighted diagonal mean

The amplitude identities connect the general attenuated Volterra calculus to
the quadratic and quotient kernels of a weighted diagonal mean.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The attenuated integral formed from the quadratic and quotient kernels
of a weighted diagonal mean. -/
@[expose] noncomputable def weightedDiagonalAttenuatedVolterra
    (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  attenuatedVolterraIntegral
    (weightedDiagonalQuadraticKernel w f)
    (weightedDiagonalQuotientKernel w f) p.1 p.2

/-- The weighted attenuated integral vanishes on the diagonal. -/
@[simp] theorem weightedDiagonalAttenuatedVolterra_diag
    (w f : ℝ × ℝ → ℝ) (u : ℝ) :
    weightedDiagonalAttenuatedVolterra w f (u, u) = 0 := by
  simp [weightedDiagonalAttenuatedVolterra]

/-- Under continuous first-jet data, the weighted attenuated integral has
continuous first jets through both sides of the compact diagonal. -/
theorem contDiffOn_weightedDiagonalAttenuatedVolterra
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
    ContDiffOn ℝ 1 (weightedDiagonalAttenuatedVolterra w f)
      (closedCoordTriangle a b) := by
  have hj := contDiffOn_weightedDiagonalQuadraticKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hk := contDiffOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  exact contDiffOn_attenuatedVolterraIntegral hab hj hk

/-- A nonnegative weight makes its attenuated quadratic Volterra integral
nonnegative throughout the closed triangle. -/
theorem weightedDiagonalAttenuatedVolterra_nonneg
    {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u v : ℝ}
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    0 ≤ weightedDiagonalAttenuatedVolterra w f (u, v) := by
  change 0 ≤ ∫ s in u..v,
    weightedDiagonalQuadraticKernel w f (u, s) *
      Real.exp (-(∫ t in s..v, weightedDiagonalQuotientKernel w f (u, t)))
  apply intervalIntegral.integral_nonneg huv
  intro s hs
  exact mul_nonneg
    (weightedDiagonalQuadraticKernel_nonneg
      (hc.le.trans (hweight (u, s) ⟨hu, hs.1, hs.2.trans hv⟩)))
    (Real.exp_pos _).le

/-- The weighted attenuated integral obeys the Volterra ODE in its upper
coordinate, also at the diagonal and at the triangle boundary. -/
theorem fderivWithin_weightedDiagonalAttenuatedVolterra_vertical
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
    (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalAttenuatedVolterra w f)
      (closedCoordTriangle a b) p) (0, 1) =
        weightedDiagonalQuadraticKernel w f p -
          weightedDiagonalQuotientKernel w f p *
            weightedDiagonalAttenuatedVolterra w f p := by
  have hj := contDiffOn_weightedDiagonalQuadraticKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hk := contDiffOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  exact fderivWithin_attenuatedVolterraIntegral_vertical hab hj hk hp

/-- The horizontal first jet is the attenuated integral of the source jet
minus the source times the attenuation jet, on the whole closed triangle. -/
theorem fderivWithin_weightedDiagonalAttenuatedVolterra_horizontal
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
    (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalAttenuatedVolterra w f)
      (closedCoordTriangle a b) p) (1, 0) =
      ∫ s in p.1..p.2,
        Real.exp (-(∫ t in s..p.2,
          weightedDiagonalQuotientKernel w f (p.1, t))) *
          ((fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
              (closedCoordTriangle a b) (p.1, s)) (1, 0) -
            weightedDiagonalQuadraticKernel w f (p.1, s) *
              (∫ t in s..p.2,
                (fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
                  (closedCoordTriangle a b) (p.1, t)) (1, 0))) := by
  have hj := contDiffOn_weightedDiagonalQuadraticKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hk := contDiffOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hdiag : ∀ x ∈ Icc a b,
      weightedDiagonalQuadraticKernel w f (x, x) = 0 := by
    intro x hx
    exact weightedDiagonalQuadraticKernel_diag
      (ne_of_gt (hc.trans_le (hweight (x, x) ⟨hx.1, le_rfl, hx.2⟩)))
  exact fderivWithin_attenuatedVolterraIntegral_horizontal hab hj hk hdiag hp

/-- The weighted source amplitude and its horizontal-jet amplitude have
the diagonal values that determine all three axis coefficients. -/
theorem weightedDiagonalAttenuatedVolterra_uniform_axis
    {a b c J₀ J₁ K₀ K₁ : ℝ} (hab : a < b)
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
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hjbound : ∀ p ∈ closedCoordTriangle a b,
      weightedDiagonalQuadraticKernel w f p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hjubound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
        (closedCoordTriangle a b) p) (1, 0)| ≤ J₁ * (p.2 - p.1))
    (hkbound : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ weightedDiagonalQuotientKernel w f p ∧
        weightedDiagonalQuotientKernel w f p ≤ K₀ * (p.2 - p.1))
    (hkubound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
        (closedCoordTriangle a b) p) (1, 0)| ≤ K₁) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |weightedDiagonalAttenuatedVolterra w f (u, v) -
          w (u, u) * (Gf (u, u) (0, 1)) ^ 2 * (v - u) ^ 3 / 12| ≤
            ε * (v - u) ^ 3 ∧
        |(fderivWithin ℝ (weightedDiagonalAttenuatedVolterra w f)
            (closedCoordTriangle a b) (u, v)) (0, 1) -
          w (u, u) * (Gf (u, u) (0, 1)) ^ 2 * (v - u) ^ 2 / 4| ≤
            ε * (v - u) ^ 2 ∧
        |(fderivWithin ℝ (weightedDiagonalAttenuatedVolterra w f)
            (closedCoordTriangle a b) (u, v)) (1, 0) +
          w (u, u) * (Gf (u, u) (0, 1)) ^ 2 * (v - u) ^ 2 / 4| ≤
            ε * (v - u) ^ 2 := by
  let K := closedCoordTriangle a b
  let H := weightedDiagonalError w f
  let Φ := verticalJetMean (fderivWithin ℝ H K)
  let j := weightedDiagonalQuadraticKernel w f
  let k := weightedDiagonalQuotientKernel w f
  let A : ℝ × ℝ → ℝ := fun p => w p * Φ p ^ 2
  let B : ℝ × ℝ → ℝ := fun p =>
    (p.2 - p.1) * Gw p (1, 0) * Φ p ^ 2 +
      2 * w p * Φ p * (fderivWithin ℝ H K p) (1, 0)
  have hHC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hj := contDiffOn_weightedDiagonalQuadraticKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hk := contDiffOn_weightedDiagonalQuotientKernel hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hHjet : ContinuousOn (fderivWithin ℝ H K) K :=
    hHC1.continuousOn_fderivWithin hunique (by norm_num)
  have hΦ : ContinuousOn Φ K := continuousOn_verticalJetMean hHjet
  have hA : ContinuousOn A K := hw.mul (hΦ.pow 2)
  have hB : ContinuousOn B K := by
    have hgap : ContinuousOn (fun p : ℝ × ℝ => p.2 - p.1) K := by fun_prop
    have hGwU : ContinuousOn (fun p => Gw p (1, 0)) K :=
      hGw.clm_apply continuousOn_const
    have hHU : ContinuousOn (fun p => (fderivWithin ℝ H K p) (1, 0)) K :=
      hHjet.clm_apply continuousOn_const
    exact ((hgap.mul hGwU).mul (hΦ.pow 2)).add
      (((continuousOn_const.mul hw).mul hΦ).mul hHU)
  have hjetw : ∀ p ∈ K, HasFDerivWithinAt w (Gw p) K p := by
    intro p hp
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hw hGw hdw hderivw hp
  have hfactor : ∀ p ∈ K, H p = (p.2 - p.1) * Φ p := by
    intro p hp
    exact weightedDiagonalError_eq_gap_mul_verticalJetMean hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc hp
  have hsource : ∀ p ∈ K,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2 ∧
        j p = (p.2 - p.1) ^ 2 * A p := by
    intro p hp
    refine ⟨weightedDiagonalQuadraticKernel_nonneg
      (hc.le.trans (hweight p hp)), hjbound p hp, ?_⟩
    change w p * H p ^ 2 = (p.2 - p.1) ^ 2 * (w p * Φ p ^ 2)
    rw [hfactor p hp]
    ring
  have hjet : ∀ p ∈ K,
      |(fderivWithin ℝ j K p) (1, 0)| ≤ J₁ * (p.2 - p.1) ∧
      (fderivWithin ℝ j K p) (1, 0) = (p.2 - p.1) * B p := by
    intro p hp
    refine ⟨hjubound p hp, ?_⟩
    have hprod := fderivWithin_weightedDiagonalQuadraticKernel_apply hab
      hjetw hHC1 hp (e := (1, 0))
    change (fderivWithin ℝ j K p) (1, 0) = _
    have hfactor' : weightedDiagonalError w f p = (p.2 - p.1) * Φ p :=
      hfactor p hp
    rw [hprod, hfactor']
    dsimp [B]
    ring
  have hdiag : ∀ x ∈ Icc a b, j (x, x) = 0 := by
    intro x hx
    exact weightedDiagonalQuadraticKernel_diag
      (ne_of_gt (hc.trans_le (hweight (x, x) ⟨hx.1, le_rfl, hx.2⟩)))
  have hAdiag : ∀ x ∈ Icc a b,
      A (x, x) = w (x, x) * (Gf (x, x) (0, 1)) ^ 2 / 4 := by
    intro x hx
    have hcoords := weightedDiagonalMean_diag_coordinate_derivatives hab
      hw hf hGw hGf hdw hdf hderivw hderivf hweight hc hx.1 hx.2
    have hΦdiag : Φ (x, x) = Gf (x, x) (0, 1) / 2 := by
      change verticalJetMean (fderivWithin ℝ H K) (x, x) = _
      rw [verticalJetMean_diag]
      exact hcoords.2.2.1
    change w (x, x) * Φ (x, x) ^ 2 = _
    rw [hΦdiag]
    ring
  have hBdiag : ∀ x ∈ Icc a b,
      B (x, x) = -w (x, x) * (Gf (x, x) (0, 1)) ^ 2 / 2 := by
    intro x hx
    have hcoords := weightedDiagonalMean_diag_coordinate_derivatives hab
      hw hf hGw hGf hdw hdf hderivw hderivf hweight hc hx.1 hx.2
    have hΦdiag : Φ (x, x) = Gf (x, x) (0, 1) / 2 := by
      change verticalJetMean (fderivWithin ℝ H K) (x, x) = _
      rw [verticalJetMean_diag]
      exact hcoords.2.2.1
    have hHu : (fderivWithin ℝ H K (x, x)) (1, 0) =
        -Gf (x, x) (0, 1) / 2 := hcoords.2.2.2
    change (x - x) * Gw (x, x) (1, 0) * Φ (x, x) ^ 2 +
      2 * w (x, x) * Φ (x, x) *
        (fderivWithin ℝ H K (x, x)) (1, 0) = _
    rw [sub_self, zero_mul, zero_mul, zero_add, hΦdiag, hHu]
    ring
  have hres := attenuatedVolterraIntegral_uniform_axis_coefficients
    (weight := w) (h := fun p => Gf p (0, 1))
    hab hj hk hA hB hdiag hJ₀ hJ₁ hK₀ hK₁ hsource hkbound hjet
    hkubound hAdiag hBdiag
  exact hres

end intervalIntegral

end
