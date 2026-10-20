module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Regular products of removable rational coefficients

Once the cubic-over-square quotient has a continuous first jet, the remaining
coefficients are ordinary products and reciprocals on the closed triangle.
-/

public section

open Set

namespace intervalIntegral

/-- A general rational coefficient formed from a cubic-over-square quotient,
two regular factors, and the complementary cubic-over-linear quotient. -/
@[expose] noncomputable def rationalCubicCoefficient
    (J r w z : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  cubicSquaredQuotient J r p *
    (w p * z p / (1 - cubicLinearQuotient J r p))

/-- A general source coefficient obtained by multiplying the rational cubic
coefficient by a regular factor divided by a nonzero weight. -/
@[expose] noncomputable def rationalCubicSource
    (J r w z H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  rationalCubicCoefficient J r w z p * (-H p / w p)

/-- A nonvanishing complementary denominator makes the rational cubic
coefficient `C¹` on the closed triangle. -/
theorem contDiffOn_rationalCubicCoefficient
    {a b : ℝ} {J r w z : ℝ × ℝ → ℝ}
    (hA : ContDiffOn ℝ 1 (cubicSquaredQuotient J r)
      (closedCoordTriangle a b))
    (hμ : ContDiffOn ℝ 1 (cubicLinearQuotient J r)
      (closedCoordTriangle a b))
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hz : ContDiffOn ℝ 1 z (closedCoordTriangle a b))
    (hden : ∀ p ∈ closedCoordTriangle a b,
      1 - cubicLinearQuotient J r p ≠ 0) :
    ContDiffOn ℝ 1 (rationalCubicCoefficient J r w z)
      (closedCoordTriangle a b) := by
  have hB : ContDiffOn ℝ 1
      (fun p => w p * z p / (1 - cubicLinearQuotient J r p))
      (closedCoordTriangle a b) :=
    (hw.mul hz).div (contDiffOn_const.sub hμ) hden
  exact hA.mul hB

/-- The rational cubic coefficient vanishes on the diagonal. -/
@[simp] theorem rationalCubicCoefficient_diag
    (J r w z : ℝ × ℝ → ℝ) (u : ℝ) :
    rationalCubicCoefficient J r w z (u, u) = 0 := by
  simp [rationalCubicCoefficient, cubicSquaredQuotient]

/-- When the regular factors have opposite diagonal values, the first jet
of the rational cubic coefficient is minus the square of that value times
the first jet of the cubic-over-square quotient. -/
theorem fderivWithin_rationalCubicCoefficient_diag
    {a b : ℝ} {J r w z : ℝ × ℝ → ℝ} {u l : ℝ}
    (hab : a < b) (hu : u ∈ Icc a b)
    (hA : ContDiffOn ℝ 1 (cubicSquaredQuotient J r)
      (closedCoordTriangle a b))
    (hμ : ContDiffOn ℝ 1 (cubicLinearQuotient J r)
      (closedCoordTriangle a b))
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hz : ContDiffOn ℝ 1 z (closedCoordTriangle a b))
    (hden : ∀ p ∈ closedCoordTriangle a b,
      1 - cubicLinearQuotient J r p ≠ 0)
    (hwdiag : w (u, u) = l) (hzdiag : z (u, u) = -l) :
    fderivWithin ℝ (rationalCubicCoefficient J r w z)
      (closedCoordTriangle a b) (u, u) =
        (-l ^ 2) • fderivWithin ℝ (cubicSquaredQuotient J r)
          (closedCoordTriangle a b) (u, u) := by
  let K := closedCoordTriangle a b
  let A := cubicSquaredQuotient J r
  let B : ℝ × ℝ → ℝ :=
    fun p => w p * z p / (1 - cubicLinearQuotient J r p)
  have hB : ContDiffOn ℝ 1 B K :=
    (hw.mul hz).div (contDiffOn_const.sub hμ) hden
  have hdiag : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have huDiff : UniqueDiffWithinAt ℝ K (u, u) :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab))
      (u, u) hdiag
  change fderivWithin ℝ (fun p => A p * B p) K (u, u) = _
  rw [fderivWithin_fun_mul huDiff
    ((hA.differentiableOn (by norm_num)) (u, u) hdiag)
    ((hB.differentiableOn (by norm_num)) (u, u) hdiag)]
  have hAz : A (u, u) = 0 := by simp [A, cubicSquaredQuotient]
  have hμz : cubicLinearQuotient J r (u, u) = 0 := by
    simp [cubicLinearQuotient]
  have hBz : B (u, u) = -l ^ 2 := by
    simp [B, hwdiag, hzdiag, hμz]
    ring
  change cubicSquaredQuotient J r (u, u) = 0 at hAz
  rw [hAz, hBz, zero_smul, zero_add]

/-- The diagonal coordinate jets of the rational cubic coefficient have
the opposite signs dictated by the cubic numerator expansion. -/
theorem rationalCubicCoefficient_axis_coordinates
    {a b : ℝ} {J r w z U ρ : ℝ × ℝ → ℝ}
    {V Gr : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    {u l b₀ : ℝ}
    (hab : a < b) (hu : u ∈ Icc a b)
    (hA : ContDiffOn ℝ 1 (cubicSquaredQuotient J r)
      (closedCoordTriangle a b))
    (hμ : ContDiffOn ℝ 1 (cubicLinearQuotient J r)
      (closedCoordTriangle a b))
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hz : ContDiffOn ℝ 1 z (closedCoordTriangle a b))
    (hden : ∀ p ∈ closedCoordTriangle a b,
      1 - cubicLinearQuotient J r p ≠ 0)
    (hAjet : fderivWithin ℝ (cubicSquaredQuotient J r)
      (closedCoordTriangle a b) (u, u) =
        cubicSquaredQuotientJet U ρ V Gr (u, u))
    (hl : l ≠ 0)
    (hwdiag : w (u, u) = l) (hzdiag : z (u, u) = -l)
    (hρ : ρ (u, u) = l)
    (hU : U (u, u) = l * b₀ ^ 2 / 12)
    (hVu : V (u, u) (1, 0) = -(l * b₀ ^ 2 / 4))
    (hVv : V (u, u) (0, 1) = l * b₀ ^ 2 / 4)
    (hGru : Gr (u, u) (1, 0) = -l)
    (hGrv : Gr (u, u) (0, 1) = l) :
    (fderivWithin ℝ (rationalCubicCoefficient J r w z)
      (closedCoordTriangle a b) (u, u)) (1, 0) =
        l * b₀ ^ 2 / 12 ∧
      (fderivWithin ℝ (rationalCubicCoefficient J r w z)
      (closedCoordTriangle a b) (u, u)) (0, 1) =
        -(l * b₀ ^ 2 / 12) := by
  have hK := fderivWithin_rationalCubicCoefficient_diag
    hab hu hA hμ hw hz hden hwdiag hzdiag
  have hAs := cubicSquaredQuotientJet_axis hl hρ hU hVu hVv hGru hGrv
  rw [hAjet] at hK
  constructor
  · have h := congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (1, 0)) hK
    simp only [smul_apply, smul_eq_mul, hAs.1] at h
    convert h using 1
    field_simp [hl]
  · have h := congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (0, 1)) hK
    simp only [smul_apply, smul_eq_mul, hAs.2] at h
    convert h using 1
    field_simp [hl]

/-- Dividing the source factor by a nonzero weight preserves `C¹`
regularity of the rational source coefficient. -/
theorem contDiffOn_rationalCubicSource
    {a b : ℝ} {J r w z H : ℝ × ℝ → ℝ}
    (hK : ContDiffOn ℝ 1 (rationalCubicCoefficient J r w z)
      (closedCoordTriangle a b))
    (hH : ContDiffOn ℝ 1 H (closedCoordTriangle a b))
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hwne : ∀ p ∈ closedCoordTriangle a b, w p ≠ 0) :
    ContDiffOn ℝ 1 (rationalCubicSource J r w z H)
      (closedCoordTriangle a b) := by
  have hB : ContDiffOn ℝ 1 (fun p => -H p / w p)
      (closedCoordTriangle a b) := hH.neg.div hw hwne
  exact hK.mul hB

/-- If the extra source factor vanishes on the diagonal, the rational source
and its full relative first jet vanish there. -/
theorem rationalCubicSource_diag_jet
    {a b : ℝ} {J r w z H : ℝ × ℝ → ℝ} {u : ℝ}
    (hab : a < b) (hu : u ∈ Icc a b)
    (hK : ContDiffOn ℝ 1 (rationalCubicCoefficient J r w z)
      (closedCoordTriangle a b))
    (hH : ContDiffOn ℝ 1 H (closedCoordTriangle a b))
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hwne : ∀ p ∈ closedCoordTriangle a b, w p ≠ 0)
    (hHdiag : H (u, u) = 0) :
    rationalCubicSource J r w z H (u, u) = 0 ∧
      fderivWithin ℝ (rationalCubicSource J r w z H)
        (closedCoordTriangle a b) (u, u) = 0 := by
  let K := closedCoordTriangle a b
  let C := rationalCubicCoefficient J r w z
  let B : ℝ × ℝ → ℝ := fun p => -H p / w p
  have hB : ContDiffOn ℝ 1 B K := hH.neg.div hw hwne
  have hdiag : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hBz : B (u, u) = 0 := by simp [B, hHdiag]
  constructor
  · simp [rationalCubicSource]
  · have huDiff : UniqueDiffWithinAt ℝ K (u, u) :=
      (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab))
        (u, u) hdiag
    change fderivWithin ℝ (fun p => C p * B p) K (u, u) = 0
    rw [fderivWithin_fun_mul huDiff
      ((hK.differentiableOn (by norm_num)) (u, u) hdiag)
      ((hB.differentiableOn (by norm_num)) (u, u) hdiag)]
    simp [hBz]

end intervalIntegral

end
