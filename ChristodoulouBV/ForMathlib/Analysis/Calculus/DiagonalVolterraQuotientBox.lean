module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraRadiusJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input estimates for diagonal quotient kernels

The quotient derivative is normalized by the coordinate gap before applying
the scalar two-input quotient estimate. This gives a bound uniform to the
diagonal with the five terms of the ordinary quotient-rule difference.
-/

public section

open Set

namespace intervalIntegral

/-- The uniform first-coordinate derivative coefficient for the quotient
kernel. -/
@[expose] noncomputable def weightedDiagonalQuotientDerivativeCoefficient
    (c C B L R : ℝ) : ℝ :=
  weightedDiagonalQuadraticDerivativeCoefficient c C B L / c +
    weightedDiagonalQuadraticValueCoefficient C B * R / c ^ 2

/-- The two-input value coefficient for the quotient kernel. -/
@[expose] noncomputable def weightedDiagonalQuotientValueDifferenceCoefficient
    (c C B : ℝ) : ℝ :=
  weightedDiagonalQuadraticValueDifferenceCoefficient c C B / c +
    weightedDiagonalQuadraticValueCoefficient C B / c ^ 2

/-- The two-input first-coordinate derivative coefficient for the quotient
kernel; its five summands are the five quotient-rule subtraction terms. -/
@[expose] noncomputable def weightedDiagonalQuotientDerivativeDifferenceCoefficient
    (c C B L R RΔ : ℝ) : ℝ :=
  let j₀ := weightedDiagonalQuadraticValueCoefficient C B
  let j₁ := weightedDiagonalQuadraticDerivativeCoefficient c C B L
  let jΔ₀ := weightedDiagonalQuadraticValueDifferenceCoefficient c C B
  let jΔ₁ := weightedDiagonalQuadraticDerivativeDifferenceCoefficient c C B L
  jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * R / c ^ 2 +
    j₀ * RΔ / c ^ 2 + 2 * j₀ * R / c ^ 3

/-- A gap-scaled two-input quotient derivative estimate, obtained by
normalizing numerator, its derivative, and the denominator by the powers of
the gap with which they vanish. -/
theorem abs_quotientJet_sub_le_of_gap_bounds
    {c d j₀ j₁ jΔ₀ jΔ₁ R RΔ D : ℝ}
    {r₁ r₂ J₁ J₂ P₁ P₂ S₁ S₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hj₀ : 0 ≤ j₀) (hj₁ : 0 ≤ j₁)
    (hjΔ₀ : 0 ≤ jΔ₀) (hjΔ₁ : 0 ≤ jΔ₁)
    (hR : 0 ≤ R) (hRΔ : 0 ≤ RΔ) (hD : 0 ≤ D)
    (hr₁ : c * d ≤ r₁) (hr₂ : c * d ≤ r₂)
    (hrdiff : |r₁ - r₂| ≤ d * D)
    (hJ₂ : |J₂| ≤ j₀ * d ^ 2)
    (hJdiff : |J₁ - J₂| ≤ jΔ₀ * d ^ 2 * D)
    (hP₂ : |P₂| ≤ j₁ * d)
    (hPdiff : |P₁ - P₂| ≤ jΔ₁ * d * D)
    (hS₁ : |S₁| ≤ R) (hS₂ : |S₂| ≤ R)
    (hSdiff : |S₁ - S₂| ≤ RΔ * D) :
    |(P₁ / r₁ - J₁ * S₁ / r₁ ^ 2) -
      (P₂ / r₂ - J₂ * S₂ / r₂ ^ 2)| ≤
      (jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * R / c ^ 2 +
        j₀ * RΔ / c ^ 2 + 2 * j₀ * R / c ^ 3) * D := by
  have hρ₁ : c ≤ r₁ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₁])
  have hρ₂ : c ≤ r₂ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₂])
  have hρdiff : |r₁ / d - r₂ / d| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hrdiff)
  have hJ₂' : |J₂ / d ^ 2| ≤ j₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hJ₂])
  have hJdiff' : |J₁ / d ^ 2 - J₂ / d ^ 2| ≤ jΔ₀ * D := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hJdiff])
  have hP₂' : |P₂ / d| ≤ j₁ := by
    rw [abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by nlinarith only [hP₂])
  have hPdiff' : |P₁ / d - P₂ / d| ≤ jΔ₁ * D := by
    rw [← sub_div, abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by nlinarith only [hPdiff])
  have h := abs_quotientJet_sub_le hc hj₀ hj₁ hjΔ₀ hjΔ₁
    hR hRΔ hD hρ₁ hρ₂ hρdiff hJ₂' hJdiff' hP₂' hPdiff'
    hS₁ hS₂ hSdiff
  have hnorm : ∀ r J P S : ℝ, r ≠ 0 →
      (P / d) / (r / d) - (J / d ^ 2) * S / (r / d) ^ 2 =
        P / r - J * S / r ^ 2 := by
    intro r J P S hr
    field_simp [hd.ne', hr]
  rw [hnorm r₁ J₁ P₁ S₁ (ne_of_gt ((mul_pos hc hd).trans_le hr₁)),
    hnorm r₂ J₂ P₂ S₂ (ne_of_gt ((mul_pos hc hd).trans_le hr₂))] at h
  exact h

/-- The relative first jets of two extended diagonal quotient kernels obey
the five-term quotient coefficient at every point strictly above the diagonal. -/
theorem abs_fderivWithin_weightedDiagonalQuotientKernel_sub_le_of_bounds
    {a b c j₀ j₁ jΔ₀ jΔ₁ R RΔ D : ℝ} (hab : a < b)
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ Gf₁ Gf₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hGf₁ : ContinuousOn Gf₁ (closedCoordTriangle a b))
    (hGf₂ : ContinuousOn Gf₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderivf₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = Gf₁ p)
    (hderivf₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = Gf₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p)
    (hc : 0 < c) (hj₀ : 0 ≤ j₀) (hj₁ : 0 ≤ j₁)
    (hjΔ₀ : 0 ≤ jΔ₀) (hjΔ₁ : 0 ≤ jΔ₁)
    (hR : 0 ≤ R) (hRΔ : 0 ≤ RΔ) (hD : 0 ≤ D)
    {p e : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) (hpdiag : p.1 < p.2)
    (hj₂ : |weightedDiagonalQuadraticKernel w₂ f₂ p| ≤
      j₀ * (p.2 - p.1) ^ 2)
    (hjdiff : |weightedDiagonalQuadraticKernel w₁ f₁ p -
      weightedDiagonalQuadraticKernel w₂ f₂ p| ≤
      jΔ₀ * (p.2 - p.1) ^ 2 * D)
    (hji₂ : |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w₂ f₂)
      (closedCoordTriangle a b) p) e| ≤ j₁ * (p.2 - p.1))
    (hjidiff : |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w₁ f₁)
        (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ (weightedDiagonalQuadraticKernel w₂ f₂)
        (closedCoordTriangle a b) p) e| ≤
      jΔ₁ * (p.2 - p.1) * D)
    (hrdiff : |weightedDiagonalRadius w₁ p -
      weightedDiagonalRadius w₂ p| ≤ (p.2 - p.1) * D)
    (hri₁ : |(fderivWithin ℝ (weightedDiagonalRadius w₁)
      (closedCoordTriangle a b) p) e| ≤ R)
    (hri₂ : |(fderivWithin ℝ (weightedDiagonalRadius w₂)
      (closedCoordTriangle a b) p) e| ≤ R)
    (hridiff : |(fderivWithin ℝ (weightedDiagonalRadius w₁)
        (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ (weightedDiagonalRadius w₂)
        (closedCoordTriangle a b) p) e| ≤ RΔ * D) :
    |(fderivWithin ℝ (weightedDiagonalQuotientKernel w₁ f₁)
        (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ (weightedDiagonalQuotientKernel w₂ f₂)
        (closedCoordTriangle a b) p) e| ≤
      (jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * R / c ^ 2 +
        j₀ * RΔ / c ^ 2 + 2 * j₀ * R / c ^ 3) * D := by
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
    exact hp
  have hr₁ : c * (p.2 - p.1) ≤ weightedDiagonalRadius w₁ p :=
    mul_sub_le_weightedDiagonalRadius hw₁ hweight₁ hcoord.1 hpdiag.le hcoord.2.2
  have hr₂ : c * (p.2 - p.1) ≤ weightedDiagonalRadius w₂ p :=
    mul_sub_le_weightedDiagonalRadius hw₂ hweight₂ hcoord.1 hpdiag.le hcoord.2.2
  rw [fderivWithin_weightedDiagonalQuotientKernel_apply_off_diag hab
      hw₁ hf₁ hGw₁ hGf₁ hdw₁ hdf₁ hderivw₁ hderivf₁ hweight₁ hc hp hpdiag,
    fderivWithin_weightedDiagonalQuotientKernel_apply_off_diag hab
      hw₂ hf₂ hGw₂ hGf₂ hdw₂ hdf₂ hderivw₂ hderivf₂ hweight₂ hc hp hpdiag]
  exact abs_quotientJet_sub_le_of_gap_bounds hc (sub_pos.mpr hpdiag)
    hj₀ hj₁ hjΔ₀ hjΔ₁ hR hRΔ hD hr₁ hr₂ hrdiff
    hj₂ hjdiff hji₂ hjidiff hri₁ hri₂ hridiff

private theorem le_on_closedCoordTriangle_of_le_interior
    {a b : ℝ} (hab : a < b)
    {F G : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (closedCoordTriangle a b))
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hle : ∀ p ∈ interior (closedCoordTriangle a b), F p ≤ G p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) : F p ≤ G p := by
  let K := closedCoordTriangle a b
  have hEq : EqOn (fun z => |F z - G z| + (F z - G z))
      (fun _ => 0) (interior K) := by
    intro z hz
    simp [abs_of_nonpos (sub_nonpos.mpr (hle z hz))]
  have hcont : ContinuousOn (fun z => |F z - G z| + (F z - G z)) K :=
    (hF.sub hG).abs.add (hF.sub hG)
  have hclosure : K ⊆ closure (interior K) := by
    rw [interior_closedCoordTriangle, closure_openCoordTriangle hab]
  have h := (hEq.of_subset_closure hcont continuousOn_const interior_subset hclosure) hp
  have hn := abs_nonneg (F p - G p)
  linarith only [h, hn]

/-- On a positive three-jet box, the quotient kernel has the two-input
value and coordinate derivative estimates with the coefficients of the
product and quotient ledgers. -/
theorem weightedDiagonalQuotientKernel_difference_bounds_threeJetDistanceOn
    {a b c C B L D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ g₁ g₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hg₁ : ContinuousOn g₁ (closedCoordTriangle a b))
    (hg₂ : ContinuousOn g₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hGg₁ : ContinuousOn Gg₁ (closedCoordTriangle a b))
    (hGg₂ : ContinuousOn Gg₂ (closedCoordTriangle a b))
    (hGf₁ : ContinuousOn Gf₁ (closedCoordTriangle a b))
    (hGf₂ : ContinuousOn Gf₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderivf₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = Gf₁ p)
    (hderivf₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = Gf₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hGw₁U : ∀ p ∈ closedCoordTriangle a b, |Gw₁ p (1, 0)| ≤ L)
    (hGw₂U : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (1, 0)| ≤ L)
    (hGw₂V : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (0, 1)| ≤ L)
    (hGf₁U : ∀ p ∈ closedCoordTriangle a b, |Gf₁ p (1, 0)| ≤ L)
    (hGf₂U : ∀ p ∈ closedCoordTriangle a b, |Gf₂ p (1, 0)| ≤ L)
    (hGf₁V : ∀ p ∈ closedCoordTriangle a b, |Gf₁ p (0, 1)| ≤ B)
    (hGf₂V : ∀ p ∈ closedCoordTriangle a b, |Gf₂ p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hD : D = threeJetDistanceOn (closedCoordTriangle a b)
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |weightedDiagonalQuotientKernel w₁ f₁ p -
      weightedDiagonalQuotientKernel w₂ f₂ p| ≤
      weightedDiagonalQuotientValueDifferenceCoefficient c C B *
        (p.2 - p.1) * D ∧
    |(fderivWithin ℝ (weightedDiagonalQuotientKernel w₁ f₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalQuotientKernel w₂ f₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      weightedDiagonalQuotientDerivativeDifferenceCoefficient
        c C B L (C + L) 2 * D ∧
    |(fderivWithin ℝ (weightedDiagonalQuotientKernel w₁ f₁)
        (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalQuotientKernel w₂ f₂)
        (closedCoordTriangle a b) p) (0, 1)| ≤
      weightedDiagonalQuotientDerivativeDifferenceCoefficient
        c C B L (C + L) 2 * D := by
  let K := closedCoordTriangle a b
  let j₀ := weightedDiagonalQuadraticValueCoefficient C B
  let j₁ := weightedDiagonalQuadraticDerivativeCoefficient c C B L
  let jΔ₀ := weightedDiagonalQuadraticValueDifferenceCoefficient c C B
  let jΔ₁ := weightedDiagonalQuadraticDerivativeDifferenceCoefficient c C B L
  let R := C + L
  have hC : 0 ≤ C := (hc.le.trans (hweight₁ p hp).1).trans (hweight₁ p hp).2
  have hM : 0 ≤ weightedDiagonalErrorValueDifferenceCoefficient c C B := by
    dsimp [weightedDiagonalErrorValueDifferenceCoefficient]
    positivity
  have hH₁ : 0 ≤ weightedDiagonalErrorDerivativeCoefficient c C B L := by
    dsimp [weightedDiagonalErrorDerivativeCoefficient]
    positivity
  have hN : 0 ≤ weightedDiagonalErrorDerivativeDifferenceCoefficient c C B L := by
    dsimp [weightedDiagonalErrorDerivativeDifferenceCoefficient]
    positivity
  have hj₀ : 0 ≤ j₀ := by dsimp [j₀, weightedDiagonalQuadraticValueCoefficient]; positivity
  have hj₁ : 0 ≤ j₁ := by
    dsimp [j₁, weightedDiagonalQuadraticDerivativeCoefficient]
    positivity
  have hjΔ₀ : 0 ≤ jΔ₀ := by
    dsimp [jΔ₀, weightedDiagonalQuadraticValueDifferenceCoefficient]
    positivity
  have hjΔ₁ : 0 ≤ jΔ₁ := by
    dsimp [jΔ₁, weightedDiagonalQuadraticDerivativeDifferenceCoefficient]
    positivity
  have hR : 0 ≤ R := add_nonneg hC hL
  have hK : IsCompact K := isCompact_closedCoordTriangle a b
  have hne : K.Nonempty := by
    refine ⟨(a, a), ?_⟩
    exact ⟨le_rfl, le_rfl, hab.le⟩
  have hDw : coordinateJetDistanceOn K w₁ w₂ Gw₁ Gw₂ ≤ D := by
    rw [hD]
    exact coordinateJetDistanceOn_first_le_threeJetDistanceOn K
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂
  have hDnonneg : 0 ≤ D :=
    (coordinateJetDistanceOn_nonneg hK hne hw₁ hw₂ hGw₁ hGw₂).trans hDw
  have hj₂ := weightedDiagonalQuadraticKernel_bounds_on_jetBox hab hsize
    hw₂ hf₂ hGw₂ hGf₂ hdw₂ hdf₂ hderivw₂ hderivf₂
    hweight₂ hGw₂U hGw₂V hGf₂U hGf₂V hc hB hL hp
  have hjdiff := weightedDiagonalQuadraticKernel_difference_bounds_threeJetDistanceOn
    hab hsize hw₁ hw₂ hg₁ hg₂ hf₁ hf₂ hGw₁ hGw₂ hGg₁ hGg₂ hGf₁ hGf₂
    hdw₁ hdw₂ hdf₁ hdf₂ hderivw₁ hderivw₂ hderivf₁ hderivf₂
    hweight₁ hweight₂ hGw₁U hGw₂U hGw₂V hGf₁U hGf₂U hGf₁V hGf₂V
    hc hB hL hD hp
  have hrdiff := weightedDiagonalRadius_difference_bounds_threeJetDistanceOn
    hab hsize hw₁ hw₂ hGw₁ hGw₂ hdw₁ hdw₂ hderivw₁ hderivw₂ hD hp
  have hweightabs (w : ℝ × ℝ → ℝ)
      (hb : ∀ z ∈ K, c ≤ w z ∧ w z ≤ C) : ∀ z ∈ K, |w z| ≤ C := by
    intro z hz
    rw [abs_of_nonneg (hc.le.trans (hb z hz).1)]
    exact (hb z hz).2
  have hri₁ := abs_fderivWithin_weightedDiagonalRadius_apply_le hab
    hw₁ hGw₁ hdw₁ hderivw₁ (hweightabs w₁ hweight₁) hGw₁U hp
  have hri₂ := abs_fderivWithin_weightedDiagonalRadius_apply_le hab
    hw₂ hGw₂ hdw₂ hderivw₂ (hweightabs w₂ hweight₂) hGw₂U hp
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
    exact hp
  have hdle : p.2 - p.1 ≤ 1 := by linarith
  have hri₁u : |(fderivWithin ℝ (weightedDiagonalRadius w₁) K p) (1, 0)| ≤ R :=
    hri₁.1.trans (by dsimp [R]; nlinarith only [hL, hdle])
  have hri₂u : |(fderivWithin ℝ (weightedDiagonalRadius w₂) K p) (1, 0)| ≤ R :=
    hri₂.1.trans (by dsimp [R]; nlinarith only [hL, hdle])
  have hri₁v : |(fderivWithin ℝ (weightedDiagonalRadius w₁) K p) (0, 1)| ≤ R :=
    hri₁.2.trans (by dsimp [R]; linarith only [hL])
  have hri₂v : |(fderivWithin ℝ (weightedDiagonalRadius w₂) K p) (0, 1)| ≤ R :=
    hri₂.2.trans (by dsimp [R]; linarith only [hL])
  have hval : |weightedDiagonalQuotientKernel w₁ f₁ p -
      weightedDiagonalQuotientKernel w₂ f₂ p| ≤
      weightedDiagonalQuotientValueDifferenceCoefficient c C B *
        (p.2 - p.1) * D := by
    by_cases hpdiag : p.1 < p.2
    · have h := abs_weightedDiagonalQuotientKernel_sub_le_of_bounds
        hw₁ hw₂ (fun z hz => (hweight₁ z hz).1)
        (fun z hz => (hweight₂ z hz).1) hc hp hpdiag
        hj₂.1 hjdiff.1 hrdiff.1
      simpa only [weightedDiagonalQuotientValueDifferenceCoefficient,
        j₀, jΔ₀] using h
    · have heq : p.1 = p.2 := le_antisymm hcoord.2.1 (le_of_not_gt hpdiag)
      have hz : weightedDiagonalQuotientKernel w₁ f₁ p = 0 ∧
          weightedDiagonalQuotientKernel w₂ f₂ p = 0 := by
        rcases p with ⟨u, v⟩
        simp only at heq
        subst v
        exact ⟨weightedDiagonalQuotientKernel_diag w₁ f₁ u,
          weightedDiagonalQuotientKernel_diag w₂ f₂ u⟩
      rw [hz.1, hz.2, sub_self, abs_zero, heq, sub_self, mul_zero, zero_mul]
  have hcont₁ := contDiffOn_weightedDiagonalQuotientKernel hab
    hw₁ hf₁ hGw₁ hGf₁ hdw₁ hdf₁ hderivw₁ hderivf₁
    (fun z hz => (hweight₁ z hz).1) hc
  have hcont₂ := contDiffOn_weightedDiagonalQuotientKernel hab
    hw₂ hf₂ hGw₂ hGf₂ hdw₂ hdf₂ hderivw₂ hderivf₂
    (fun z hz => (hweight₂ z hz).1) hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjetcont₁ := hcont₁.continuousOn_fderivWithin hunique (by norm_num)
  have hjetcont₂ := hcont₂.continuousOn_fderivWithin hunique (by norm_num)
  have hderiv (e : ℝ × ℝ) (he : e = (1, 0) ∨ e = (0, 1)) :
      |(fderivWithin ℝ (weightedDiagonalQuotientKernel w₁ f₁) K p) e -
        (fderivWithin ℝ (weightedDiagonalQuotientKernel w₂ f₂) K p) e| ≤
          weightedDiagonalQuotientDerivativeDifferenceCoefficient
            c C B L R 2 * D := by
    apply le_on_closedCoordTriangle_of_le_interior hab
      ((hjetcont₁.clm_apply continuousOn_const).sub
        (hjetcont₂.clm_apply continuousOn_const)).abs continuousOn_const
      ?_ hp
    intro z hz
    have hzK : z ∈ K := interior_subset hz
    have hzstrict : z.1 < z.2 := by
      have hzo : z ∈ openCoordTriangle a b := by
        simpa only [interior_closedCoordTriangle] using hz
      exact hzo.2.1
    have hj₂z := weightedDiagonalQuadraticKernel_bounds_on_jetBox hab hsize
      hw₂ hf₂ hGw₂ hGf₂ hdw₂ hdf₂ hderivw₂ hderivf₂
      hweight₂ hGw₂U hGw₂V hGf₂U hGf₂V hc hB hL hzK
    have hjdz := weightedDiagonalQuadraticKernel_difference_bounds_threeJetDistanceOn
      hab hsize hw₁ hw₂ hg₁ hg₂ hf₁ hf₂ hGw₁ hGw₂ hGg₁ hGg₂ hGf₁ hGf₂
      hdw₁ hdw₂ hdf₁ hdf₂ hderivw₁ hderivw₂ hderivf₁ hderivf₂
      hweight₁ hweight₂ hGw₁U hGw₂U hGw₂V hGf₁U hGf₂U hGf₁V hGf₂V
      hc hB hL hD hzK
    have hrdz := weightedDiagonalRadius_difference_bounds_threeJetDistanceOn
      hab hsize hw₁ hw₂ hGw₁ hGw₂ hdw₁ hdw₂ hderivw₁ hderivw₂ hD hzK
    have hri₁z := abs_fderivWithin_weightedDiagonalRadius_apply_le hab
      hw₁ hGw₁ hdw₁ hderivw₁ (hweightabs w₁ hweight₁) hGw₁U hzK
    have hri₂z := abs_fderivWithin_weightedDiagonalRadius_apply_le hab
      hw₂ hGw₂ hdw₂ hderivw₂ (hweightabs w₂ hweight₂) hGw₂U hzK
    have hzcoord : a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := by
      change a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b at hzK
      exact hzK
    have hzdle : z.2 - z.1 ≤ 1 := by linarith
    have hRuz₁ : |(fderivWithin ℝ (weightedDiagonalRadius w₁) K z) (1, 0)| ≤ R :=
      hri₁z.1.trans (by dsimp [R]; nlinarith only [hL, hzdle])
    have hRuz₂ : |(fderivWithin ℝ (weightedDiagonalRadius w₂) K z) (1, 0)| ≤ R :=
      hri₂z.1.trans (by dsimp [R]; nlinarith only [hL, hzdle])
    have hRvz₁ : |(fderivWithin ℝ (weightedDiagonalRadius w₁) K z) (0, 1)| ≤ R :=
      hri₁z.2.trans (by dsimp [R]; linarith only [hL])
    have hRvz₂ : |(fderivWithin ℝ (weightedDiagonalRadius w₂) K z) (0, 1)| ≤ R :=
      hri₂z.2.trans (by dsimp [R]; linarith only [hL])
    rcases he with rfl | rfl
    · have h := abs_fderivWithin_weightedDiagonalQuotientKernel_sub_le_of_bounds
        hab hw₁ hw₂ hf₁ hf₂ hGw₁ hGw₂ hGf₁ hGf₂ hdw₁ hdw₂ hdf₁ hdf₂
        hderivw₁ hderivw₂ hderivf₁ hderivf₂
        (fun y hy => (hweight₁ y hy).1) (fun y hy => (hweight₂ y hy).1)
        hc hj₀ hj₁ hjΔ₀ hjΔ₁ hR (by norm_num : (0 : ℝ) ≤ 2) hDnonneg
        hzK hzstrict hj₂z.1 hjdz.1 hj₂z.2.1 hjdz.2.1 hrdz.1
        hRuz₁ hRuz₂ hrdz.2.1
      simpa only [Pi.sub_apply, weightedDiagonalQuotientDerivativeDifferenceCoefficient,
        j₀, j₁, jΔ₀, jΔ₁, R] using h
    · have hRdv : |(fderivWithin ℝ (weightedDiagonalRadius w₁) K z) (0, 1) -
        (fderivWithin ℝ (weightedDiagonalRadius w₂) K z) (0, 1)| ≤ 2 * D := by
        linarith only [hrdz.2.2, hDnonneg]
      have h := abs_fderivWithin_weightedDiagonalQuotientKernel_sub_le_of_bounds
        hab hw₁ hw₂ hf₁ hf₂ hGw₁ hGw₂ hGf₁ hGf₂ hdw₁ hdw₂ hdf₁ hdf₂
        hderivw₁ hderivw₂ hderivf₁ hderivf₂
        (fun y hy => (hweight₁ y hy).1) (fun y hy => (hweight₂ y hy).1)
        hc hj₀ hj₁ hjΔ₀ hjΔ₁ hR (by norm_num : (0 : ℝ) ≤ 2) hDnonneg
        hzK hzstrict hj₂z.1 hjdz.1 hj₂z.2.2 hjdz.2.2 hrdz.1
        hRvz₁ hRvz₂ hRdv
      simpa only [Pi.sub_apply, weightedDiagonalQuotientDerivativeDifferenceCoefficient,
        j₀, j₁, jΔ₀, jΔ₁, R] using h
  refine ⟨hval, ?_, ?_⟩
  · exact hderiv (1, 0) (Or.inl rfl)
  · exact hderiv (0, 1) (Or.inr rfl)

/-- Both coordinate derivatives of the extended quotient kernel satisfy
the first-jet coefficient on the full closed triangle. -/
theorem weightedDiagonalQuotientKernel_derivative_bounds_on_jetBox
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
    (hGwV : ∀ p ∈ closedCoordTriangle a b, |Gw p (0, 1)| ≤ L)
    (hGfU : ∀ p ∈ closedCoordTriangle a b, |Gf p (1, 0)| ≤ L)
    (hGfV : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p) (1, 0)| ≤
      weightedDiagonalQuotientDerivativeCoefficient c C B L (C + L) ∧
    |(fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p) (0, 1)| ≤
      weightedDiagonalQuotientDerivativeCoefficient c C B L (C + L) := by
  let K := closedCoordTriangle a b
  have hC : 0 ≤ C := (hc.le.trans (hweight p hp).1).trans (hweight p hp).2
  have hwabs : ∀ z ∈ K, |w z| ≤ C := by
    intro z hz
    rw [abs_of_nonneg (hc.le.trans (hweight z hz).1)]
    exact (hweight z hz).2
  have hcont := (contDiffOn_weightedDiagonalQuotientKernel hab
    hw hf hGw hGf hdw hdf hderivw hderivf (fun z hz => (hweight z hz).1) hc)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjetcont := hcont.continuousOn_fderivWithin hunique (by norm_num)
  have hderiv (e : ℝ × ℝ) (he : e = (1, 0) ∨ e = (0, 1)) :
      |(fderivWithin ℝ (weightedDiagonalQuotientKernel w f) K p) e| ≤
        weightedDiagonalQuotientDerivativeCoefficient c C B L (C + L) := by
    apply le_on_closedCoordTriangle_of_le_interior hab
      (hjetcont.clm_apply continuousOn_const).abs continuousOn_const ?_ hp
    intro z hz
    have hzK : z ∈ K := interior_subset hz
    have hzstrict : z.1 < z.2 := by
      have hzo : z ∈ openCoordTriangle a b := by
        simpa only [interior_closedCoordTriangle] using hz
      exact hzo.2.1
    have hcoord : a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b := by
      change a ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ b at hzK
      exact hzK
    have hdle : z.2 - z.1 ≤ 1 := by linarith
    have hj := weightedDiagonalQuadraticKernel_bounds_on_jetBox hab hsize
      hw hf hGw hGf hdw hdf hderivw hderivf hweight
      hGwU hGwV hGfU hGfV hc hB hL hzK
    have hr := abs_fderivWithin_weightedDiagonalRadius_apply_le hab
      hw hGw hdw hderivw hwabs hGwU hzK
    have hru : |(fderivWithin ℝ (weightedDiagonalRadius w) K z) (1, 0)| ≤ C + L :=
      hr.1.trans (by nlinarith only [hL, hdle])
    have hrv : |(fderivWithin ℝ (weightedDiagonalRadius w) K z) (0, 1)| ≤ C + L :=
      hr.2.trans (by linarith only [hL])
    rcases he with rfl | rfl
    · have h := abs_fderivWithin_weightedDiagonalQuotientKernel_apply_le_of_bounds
        hab hw hf hGw hGf hdw hdf hderivw hderivf
        (fun y hy => (hweight y hy).1) hc hzK hzstrict hj.1 hj.2.1 hru
      simpa only [weightedDiagonalQuotientDerivativeCoefficient,
        weightedDiagonalQuadraticValueCoefficient,
        weightedDiagonalQuadraticDerivativeCoefficient] using h
    · have h := abs_fderivWithin_weightedDiagonalQuotientKernel_apply_le_of_bounds
        hab hw hf hGw hGf hdw hdf hderivw hderivf
        (fun y hy => (hweight y hy).1) hc hzK hzstrict hj.1 hj.2.2 hrv
      simpa only [weightedDiagonalQuotientDerivativeCoefficient,
        weightedDiagonalQuadraticValueCoefficient,
        weightedDiagonalQuadraticDerivativeCoefficient] using h
  exact ⟨hderiv (1, 0) (Or.inl rfl), hderiv (0, 1) (Or.inr rfl)⟩

end intervalIntegral

end
