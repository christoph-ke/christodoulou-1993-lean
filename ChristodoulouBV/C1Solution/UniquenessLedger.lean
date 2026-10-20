module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsReciprocal
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsLedger
import ChristodoulouBV.ForMathlib.Gronwall.Integral
import Mathlib.Tactic

/-!
# Arbitrary-bound constants for C¹ uniqueness

The constants in the outgoing two-input calculation are kept in dependency
order. In particular, `Kd` is determined before `Wdv`, which uses the
outgoing equation for `ν`. The bounds are for a triangle of width at most
`τ`, with `τ ≥ 1`; they make no small-data assumption.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- Explicit constants for the outgoing two-input coefficient calculation.
The suffix `0` bounds a value after its indicated gap power, `v` bounds its
outgoing jet, `d` bounds a value difference, and `dv` a jet difference. -/
structure UniquenessLedgerConstants where
  H0 : ℝ
  Hv : ℝ
  Hd : ℝ
  Hdv : ℝ
  j0 : ℝ
  jv : ℝ
  jd : ℝ
  jdv : ℝ
  k0 : ℝ
  kv : ℝ
  kd : ℝ
  kdv : ℝ
  J0 : ℝ
  Jv : ℝ
  Jd : ℝ
  Jdv : ℝ
  mu0 : ℝ
  muv : ℝ
  mud : ℝ
  mudv : ℝ
  A0 : ℝ
  Av : ℝ
  Ad : ℝ
  Adv : ℝ
  W0 : ℝ
  Wd : ℝ
  Wv : ℝ
  Wdv : ℝ
  Z0 : ℝ
  Zv : ℝ
  Zd : ℝ
  Zdv : ℝ
  K0 : ℝ
  Kd : ℝ
  Kv : ℝ
  Kdv : ℝ
  P0 : ℝ
  Pv : ℝ
  Pd : ℝ
  Pdv : ℝ
  Qd : ℝ
  Qdv : ℝ
  A1 : ℝ

/-- The exact coarse coefficients audited for (U). `c` bounds `λ` below,
`C,V,L,B` bound `λ, |ν|, |λ_v|, |h_v|`, and `ε` bounds `1-μ` below. -/
@[expose] noncomputable def uniquenessLedgerConstants
    (c C V L B ε τ : ℝ) : UniquenessLedgerConstants := Id.run do
  let H0 := B
  let Hv := B + C * B / c
  let Hd := (B + C) / (2 * c) + C * B / (2 * c ^ 2)
  let Hdv := 1 + (B + C * Hd) / c + C * B / c ^ 2
  let j0 := C * B ^ 2
  let jv := L * B ^ 2 * τ + 2 * C * B * Hv
  let jd := B ^ 2 + 2 * C * B * Hd
  let jdv := B ^ 2 * τ + 2 * L * B * Hd * τ +
    2 * (B * Hv + C * Hd * Hv + C * B * Hdv)
  let k0 := j0 / c
  let kv := jv / c + j0 * C / c ^ 2
  let kd := jd / c + j0 / c ^ 2
  let kdv := jdv / c + jv / c ^ 2 + jd * C / c ^ 2 +
    j0 / c ^ 2 + 2 * j0 * C / c ^ 3
  let J0 := j0 / 3
  let Jd := jd / 3 + j0 * kd * τ ^ 2 / 6
  let Jv := j0 + k0 * J0 * τ ^ 2
  let Jdv := jd + (kd * J0 + k0 * Jd) * τ ^ 2
  let mu0 := J0 / c
  let muv := Jv / c + J0 * C / c ^ 2
  let mud := Jd / c + J0 / c ^ 2
  let mudv := Jdv / c + Jv / c ^ 2 + Jd * C / c ^ 2 +
    J0 / c ^ 2 + 2 * J0 * C / c ^ 3
  let A0 := J0 / c ^ 2
  let Av := Jv / c ^ 2 + 2 * J0 * C / c ^ 3
  let Ad := Jd / c ^ 2 + 2 * J0 / c ^ 3
  let Adv := Jdv / c ^ 2 + 2 * Jv / c ^ 3 + 2 * Jd * C / c ^ 3 +
    2 * J0 / c ^ 3 + 6 * J0 * C / c ^ 4
  let W0 := C * V
  let Wd := V + C
  let Z0 := 1 / ε
  let Zv := muv / ε ^ 2
  let Zd := mud / ε ^ 2
  let Zdv := mudv / ε ^ 2 + 2 * muv * mud * τ ^ 2 / ε ^ 3
  let K0 := A0 * W0 * Z0
  let Kd := Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd * τ ^ 2
  let Wv := L * V + C * K0 * τ
  let Wdv := V + L + K0 * τ + C * Kd * τ
  let Kv := Av * W0 * Z0 + A0 * Wv * Z0 * τ + A0 * W0 * Zv * τ ^ 2
  let Kdv := τ ^ 3 *
    (Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * Zd +
     Ad * Wv * Z0 + A0 * Wdv * Z0 + A0 * Wv * Zd +
     Ad * W0 * Zv + A0 * Wd * Zv + A0 * W0 * Zdv)
  let P0 := K0 * B
  let Pv := Kv * B + K0 * Hv
  let Pd := Kd * B + K0 * Hd
  let Pdv := Kdv * B + Kv * Hd + Kd * Hv + K0 * Hdv
  let Qd := Pd / c + P0 / c ^ 2
  let Qdv := Pdv / c + Pv / c ^ 2 + Pd * L * τ / c ^ 2 +
    P0 * τ / c ^ 2 + 2 * P0 * L * τ / c ^ 3
  return {
    H0, Hv, Hd, Hdv, j0, jv, jd, jdv, k0, kv, kd, kdv,
    J0, Jv, Jd, Jdv, mu0, muv, mud, mudv, A0, Av, Ad, Adv,
    W0, Wd, Wv, Wdv, Z0, Zv, Zd, Zdv, K0, Kd, Kv, Kdv,
    P0, Pv, Pd, Pdv, Qd, Qdv,
    A1 := Kd * τ + Qd * τ ^ 2 + Kdv + Qdv * τ }

/-- The acyclic value estimate for `K_g=A W Z`. It is established before
using `ν_v=K_g` to estimate the outgoing jet of `W=λν`. The three terms on the
right correspond to the changed `A`, `W`, and `Z` factors. -/
theorem mixed_coefficient_value_difference
    {d E τ A0 Ad W0 Wd Z0 Zd : ℝ}
    {a₁ a₂ w₁ w₂ z₁ z₂ : ℝ}
    (hd : 0 ≤ d) (hdτ : d ≤ τ) (hτ : 1 ≤ τ) (hE : 0 ≤ E)
    (hA0 : 0 ≤ A0) (hAd : 0 ≤ Ad)
    (hW0 : 0 ≤ W0) (hWd : 0 ≤ Wd) (hZd : 0 ≤ Zd)
    (ha₂ : |a₂| ≤ A0 * d)
    (had : |a₁ - a₂| ≤ Ad * d * E)
    (hw₁ : |w₁| ≤ W0) (hw₂ : |w₂| ≤ W0)
    (hwd : |w₁ - w₂| ≤ Wd * E)
    (hz₁ : |z₁| ≤ Z0)
    (hzd : |z₁ - z₂| ≤ Zd * d ^ 2 * E) :
    |a₁ * w₁ * z₁ - a₂ * w₂ * z₂| ≤
      (Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd * τ ^ 2) * d * E := by
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hdsq : d ^ 2 ≤ τ ^ 2 := by nlinarith only [hd, hdτ, hτ0]
  have h := intervalIntegral.abs_triple_mul_sub_le
    (mul_nonneg hA0 hd) hW0
    (mul_nonneg (mul_nonneg hAd hd) hE)
    (mul_nonneg hWd hE)
    ha₂ hw₁ hw₂ hz₁ had hwd hzd
  calc
    _ ≤ (Ad * d * E) * W0 * Z0 +
        (A0 * d) * (Wd * E) * Z0 +
        (A0 * d) * W0 * (Zd * d ^ 2 * E) := h
    _ ≤ (Ad * d * E) * W0 * Z0 +
        (A0 * d) * (Wd * E) * Z0 +
        (A0 * d) * W0 * (Zd * τ ^ 2 * E) := by
          have hlast : Zd * d ^ 2 * E ≤ Zd * τ ^ 2 * E := by
            gcongr
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hlast
              (mul_nonneg (mul_nonneg hA0 hd) hW0)) _
    _ = _ := by ring

/-- The four terms in the outgoing jet difference of `W=λν`, after
substituting `ν_v=K_g`. The `Kd` input is the already established value
coefficient for `ΔK_g`, so this estimate is acyclic. -/
theorem lam_nu_product_jet_difference
    {d E τ C V L K0 Kd : ℝ}
    {lam₁ lam₂ nu₁ nu₂ Li₁ Li₂ K₁ K₂ : ℝ}
    (hdτ : d ≤ τ) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hK0 : 0 ≤ K0) (hKd : 0 ≤ Kd)
    (hnu₁ : |nu₁| ≤ V)
    (hLi₂ : |Li₂| ≤ L) (hLidiff : |Li₁ - Li₂| ≤ E)
    (hnudiff : |nu₁ - nu₂| ≤ E)
    (hlam₂ : |lam₂| ≤ C) (hlamdiff : |lam₁ - lam₂| ≤ E)
    (hK₁ : |K₁| ≤ K0 * d) (hKdiff : |K₁ - K₂| ≤ Kd * d * E) :
    |(Li₁ * nu₁ + lam₁ * K₁) - (Li₂ * nu₂ + lam₂ * K₂)| ≤
      (V + L + K0 * τ + C * Kd * τ) * E := by
  have hid : (Li₁ * nu₁ + lam₁ * K₁) - (Li₂ * nu₂ + lam₂ * K₂) =
      (Li₁ - Li₂) * nu₁ + Li₂ * (nu₁ - nu₂) +
        (lam₁ - lam₂) * K₁ + lam₂ * (K₁ - K₂) := by ring
  rw [hid]
  have h₁ : |(Li₁ - Li₂) * nu₁| ≤ E * V := by
    rw [abs_mul]
    exact mul_le_mul hLidiff hnu₁ (abs_nonneg _) hE
  have h₂ : |Li₂ * (nu₁ - nu₂)| ≤ L * E := by
    rw [abs_mul]
    exact mul_le_mul hLi₂ hnudiff (abs_nonneg _) hL
  have h₃ : |(lam₁ - lam₂) * K₁| ≤ E * (K0 * τ) := by
    rw [abs_mul]
    exact mul_le_mul hlamdiff (hK₁.trans (mul_le_mul_of_nonneg_left hdτ hK0))
      (abs_nonneg _) hE
  have h₄ : |lam₂ * (K₁ - K₂)| ≤ C * (Kd * τ * E) := by
    rw [abs_mul]
    have hKdτ : Kd * d * E ≤ Kd * τ * E := by gcongr
    exact mul_le_mul hlam₂ (hKdiff.trans hKdτ) (abs_nonneg _) hC
  calc
    _ ≤ |(Li₁ - Li₂) * nu₁ + Li₂ * (nu₁ - nu₂) +
          (lam₁ - lam₂) * K₁| + |lam₂ * (K₁ - K₂)| := abs_add_le _ _
    _ ≤ (|(Li₁ - Li₂) * nu₁| + |Li₂ * (nu₁ - nu₂)| +
          |(lam₁ - lam₂) * K₁|) + |lam₂ * (K₁ - K₂)| := by
      gcongr
      calc
        _ ≤ |(Li₁ - Li₂) * nu₁ + Li₂ * (nu₁ - nu₂)| +
            |(lam₁ - lam₂) * K₁| := abs_add_le _ _
        _ ≤ (|(Li₁ - Li₂) * nu₁| + |Li₂ * (nu₁ - nu₂)|) +
            |(lam₁ - lam₂) * K₁| := by gcongr; exact abs_add_le _ _
    _ ≤ E * V + L * E + E * (K0 * τ) + C * (Kd * τ * E) := by
      exact add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = _ := by ring

/-- The nine product-rule terms for the outgoing jet of `K_g=A W Z`.
The factor `τ³` absorbs every gap power after applying the unit-width
three-factor estimate to `d/τ`. -/
theorem mixed_coefficient_jet_difference
    {d E τ A0 Av Ad Adv W0 Wv Wd Wdv Z0 Zv Zd Zdv : ℝ}
    {a₁ a₂ ai₁ ai₂ w₁ w₂ wi₁ wi₂ z₁ z₂ zi₁ zi₂ : ℝ}
    (hd : 0 ≤ d) (hdτ : d ≤ τ) (hτ : 1 ≤ τ) (hE : 0 ≤ E)
    (hA0 : 0 ≤ A0) (hAv : 0 ≤ Av)
    (hAd : 0 ≤ Ad) (hAdv : 0 ≤ Adv)
    (hW0 : 0 ≤ W0) (hWv : 0 ≤ Wv)
    (hWd : 0 ≤ Wd) (hWdv : 0 ≤ Wdv)
    (hZ0 : 0 ≤ Z0) (hZv : 0 ≤ Zv) (hZd : 0 ≤ Zd) (hZdv : 0 ≤ Zdv)
    (ha₂ : |a₂| ≤ A0 * d)
    (had : |a₁ - a₂| ≤ Ad * d * E)
    (hai₂ : |ai₂| ≤ Av)
    (haid : |ai₁ - ai₂| ≤ Adv * E)
    (hw₁ : |w₁| ≤ W0) (hw₂ : |w₂| ≤ W0)
    (hwd : |w₁ - w₂| ≤ Wd * E)
    (hwi₁ : |wi₁| ≤ Wv) (hwi₂ : |wi₂| ≤ Wv)
    (hwid : |wi₁ - wi₂| ≤ Wdv * E)
    (hz₁ : |z₁| ≤ Z0)
    (hzd : |z₁ - z₂| ≤ Zd * d ^ 2 * E)
    (hzi₁ : |zi₁| ≤ Zv * d)
    (hzid : |zi₁ - zi₂| ≤ Zdv * d * E) :
    |(ai₁ * w₁ * z₁ + a₁ * wi₁ * z₁ + a₁ * w₁ * zi₁) -
      (ai₂ * w₂ * z₂ + a₂ * wi₂ * z₂ + a₂ * w₂ * zi₂)| ≤
      τ ^ 3 *
        (Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * Zd +
         Ad * Wv * Z0 + A0 * Wdv * Z0 + A0 * Wv * Zd +
         Ad * W0 * Zv + A0 * Wd * Zv + A0 * W0 * Zdv) * E := by
  have hτpos : 0 < τ := by linarith only [hτ]
  let t := d / τ
  have ht0 : 0 ≤ t := div_nonneg hd hτpos.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hτpos).mpr (by simpa only [one_mul] using hdτ)
  have hgap : τ * t = d := by
    dsimp [t]
    field_simp [hτpos.ne']
  have ha₂' : |a₂| ≤ (A0 * τ) * t := by
    calc _ ≤ A0 * d := ha₂
         _ = (A0 * τ) * t := by rw [← hgap]; ring
  have had' : |a₁ - a₂| ≤ (Ad * τ) * t * E := by
    calc _ ≤ Ad * d * E := had
         _ = (Ad * τ) * t * E := by rw [← hgap]; ring
  have hzd' : |z₁ - z₂| ≤ (Zd * τ ^ 2) * t ^ 2 * E := by
    calc _ ≤ Zd * d ^ 2 * E := hzd
         _ = (Zd * τ ^ 2) * t ^ 2 * E := by rw [← hgap]; ring
  have hzi₁' : |zi₁| ≤ (Zv * τ) * t := by
    calc _ ≤ Zv * d := hzi₁
         _ = (Zv * τ) * t := by rw [← hgap]; ring
  have hzid' : |zi₁ - zi₂| ≤ (Zdv * τ) * t * E := by
    calc _ ≤ Zdv * d * E := hzid
         _ = (Zdv * τ) * t * E := by rw [← hgap]; ring
  have h := intervalIntegral.abs_tripleProductJet_sub_le_of_gap_bounds
    ht0 ht1 hE (mul_nonneg hA0 hτpos.le) hAv
    (mul_nonneg hAd hτpos.le) hAdv hW0 hWv hWd hWdv
    (mul_nonneg hZv hτpos.le)
    (mul_nonneg hZd (sq_nonneg τ)) (mul_nonneg hZdv hτpos.le)
    ha₂' had' hai₂ haid hw₁ hw₂ hwd hwi₁ hwi₂ hwid
    hz₁ hzd' hzi₁' hzid'
  have hτsq : τ ^ 2 ≤ τ ^ 3 := by nlinarith only [hτ, sq_nonneg τ]
  have hτle : τ ≤ τ ^ 3 := by nlinarith only [hτ, hτsq]
  have h1le : (1 : ℝ) ≤ τ ^ 3 := by nlinarith only [hτ, hτle]
  calc
    _ ≤ (Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * (Zd * τ ^ 2) +
         (Ad * τ) * Wv * Z0 + (A0 * τ) * Wdv * Z0 +
           (A0 * τ) * Wv * (Zd * τ ^ 2) +
         (Ad * τ) * W0 * (Zv * τ) + (A0 * τ) * Wd * (Zv * τ) +
           (A0 * τ) * W0 * (Zdv * τ)) * E := h
    _ ≤ τ ^ 3 *
        (Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * Zd +
         Ad * Wv * Z0 + A0 * Wdv * Z0 + A0 * Wv * Zd +
         Ad * W0 * Zv + A0 * Wd * Zv + A0 * W0 * Zdv) * E := by
      apply mul_le_mul_of_nonneg_right ?_ hE
      calc
        _ = Adv * W0 * Z0 * 1 + Av * Wd * Z0 * 1 +
            Av * W0 * Zd * τ ^ 2 + Ad * Wv * Z0 * τ +
            A0 * Wdv * Z0 * τ + A0 * Wv * Zd * τ ^ 3 +
            Ad * W0 * Zv * τ ^ 2 + A0 * Wd * Zv * τ ^ 2 +
            A0 * W0 * Zdv * τ ^ 2 := by ring
        _ ≤ Adv * W0 * Z0 * τ ^ 3 + Av * Wd * Z0 * τ ^ 3 +
            Av * W0 * Zd * τ ^ 3 + Ad * Wv * Z0 * τ ^ 3 +
            A0 * Wdv * Z0 * τ ^ 3 + A0 * Wv * Zd * τ ^ 3 +
            Ad * W0 * Zv * τ ^ 3 + A0 * Wd * Zv * τ ^ 3 +
            A0 * W0 * Zdv * τ ^ 3 := by
              gcongr
        _ = _ := by ring

/-- The three product-rule terms of one outgoing `K_g` jet, with the
unscaled `τ` powers of the audited `Kv` coefficient. -/
theorem mixed_coefficient_jet_bound
    {d τ A0 Av W0 Wv Z0 Zv : ℝ}
    {a ai w wi z zi : ℝ}
    (hd : 0 ≤ d) (hdτ : d ≤ τ)
    (hA0 : 0 ≤ A0) (hAv : 0 ≤ Av)
    (hW0 : 0 ≤ W0) (hWv : 0 ≤ Wv) (hZv : 0 ≤ Zv)
    (ha : |a| ≤ A0 * d) (hai : |ai| ≤ Av)
    (hw : |w| ≤ W0) (hwi : |wi| ≤ Wv)
    (hz : |z| ≤ Z0) (hzi : |zi| ≤ Zv * d) :
    |ai * w * z + a * wi * z + a * w * zi| ≤
      Av * W0 * Z0 + A0 * Wv * Z0 * τ + A0 * W0 * Zv * τ ^ 2 := by
  have h := intervalIntegral.abs_tripleProductJet_le
    (mul_nonneg hA0 hd) hW0 hAv hWv ha hai hw hwi hz hzi
  have hτ0 : 0 ≤ τ := hd.trans hdτ
  have hdsq : d ^ 2 ≤ τ ^ 2 := by nlinarith only [hd, hdτ, hτ0]
  have hterm₂ : (A0 * d) * Wv * Z0 ≤ A0 * Wv * Z0 * τ := by
    have hcoef : 0 ≤ A0 * Wv * Z0 := by
      have hZ0 : 0 ≤ Z0 := (abs_nonneg z).trans hz
      positivity
    nlinarith only [mul_le_mul_of_nonneg_left hdτ hcoef]
  have hterm₃ : (A0 * d) * W0 * (Zv * d) ≤ A0 * W0 * Zv * τ ^ 2 := by
    have hcoef : 0 ≤ A0 * W0 * Zv := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hdsq hcoef]
  calc
    _ ≤ Av * W0 * Z0 + (A0 * d) * Wv * Z0 +
        (A0 * d) * W0 * (Zv * d) := h
    _ ≤ Av * W0 * Z0 + A0 * Wv * Z0 * τ +
        A0 * W0 * Zv * τ ^ 2 := by
          exact add_le_add (add_le_add_right hterm₂ _) hterm₃

/-- The five quotient-rule terms for the outgoing jet of `Q=-P/λ`, where
`P=K_g H` vanishes quadratically. The sign of `Q` cancels in a two-input
absolute difference. -/
theorem source_coefficient_jet_difference
    {c d E τ P0 Pv Pd Pdv L : ℝ}
    {lam₁ lam₂ P₁ P₂ Pi₁ Pi₂ Li₁ Li₂ : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hdτ : d ≤ τ) (hτ : 1 ≤ τ)
    (hE : 0 ≤ E) (hP0 : 0 ≤ P0) (hPv : 0 ≤ Pv)
    (hPd : 0 ≤ Pd) (hPdv : 0 ≤ Pdv) (hL : 0 ≤ L)
    (hlam₁ : c ≤ lam₁) (hlam₂ : c ≤ lam₂)
    (hlamdiff : |lam₁ - lam₂| ≤ E)
    (hP₂ : |P₂| ≤ P0 * d ^ 2)
    (hPdiff : |P₁ - P₂| ≤ Pd * d ^ 2 * E)
    (hPi₂ : |Pi₂| ≤ Pv * d)
    (hPidiff : |Pi₁ - Pi₂| ≤ Pdv * d * E)
    (hLi₁ : |Li₁| ≤ L) (hLi₂ : |Li₂| ≤ L)
    (hLidiff : |Li₁ - Li₂| ≤ E) :
    |(Pi₁ / lam₁ - P₁ * Li₁ / lam₁ ^ 2) -
      (Pi₂ / lam₂ - P₂ * Li₂ / lam₂ ^ 2)| ≤
      (Pdv / c + Pv / c ^ 2 + Pd * L * τ / c ^ 2 +
        P0 * τ / c ^ 2 + 2 * P0 * L * τ / c ^ 3) * d * E := by
  have hτpos : 0 < τ := by linarith only [hτ]
  let t := d / τ
  have ht0 : 0 ≤ t := div_nonneg hd hτpos.le
  have ht1 : t ≤ 1 := (div_le_iff₀ hτpos).mpr (by simpa only [one_mul] using hdτ)
  have hgap : τ * t = d := by
    dsimp [t]
    field_simp [hτpos.ne']
  have hP₂' : |P₂| ≤ (P0 * τ ^ 2) * t ^ 2 := by
    calc _ ≤ P0 * d ^ 2 := hP₂
         _ = (P0 * τ ^ 2) * t ^ 2 := by rw [← hgap]; ring
  have hPdiff' : |P₁ - P₂| ≤ (Pd * τ ^ 2) * t ^ 2 * E := by
    calc _ ≤ Pd * d ^ 2 * E := hPdiff
         _ = (Pd * τ ^ 2) * t ^ 2 * E := by rw [← hgap]; ring
  have hPi₂' : |Pi₂| ≤ (Pv * τ) * t := by
    calc _ ≤ Pv * d := hPi₂
         _ = (Pv * τ) * t := by rw [← hgap]; ring
  have hPidiff' : |Pi₁ - Pi₂| ≤ (Pdv * τ) * t * E := by
    calc _ ≤ Pdv * d * E := hPidiff
         _ = (Pdv * τ) * t * E := by rw [← hgap]; ring
  have h := intervalIntegral.abs_quotientJet_sub_le_of_quadratic_gap_bounds
    hc ht0 ht1 hE (mul_nonneg hP0 (sq_nonneg τ))
    (mul_nonneg hPv hτpos.le) (mul_nonneg hPd (sq_nonneg τ))
    (mul_nonneg hPdv hτpos.le) hL (by norm_num : (0 : ℝ) ≤ 1)
    hlam₁ hlam₂ hlamdiff hP₂' hPdiff' hPi₂' hPidiff'
    hLi₁ hLi₂ (by simpa only [one_mul] using hLidiff)
  convert h using 1
  rw [← hgap]
  ring

/-- The complete two-factor `P=K_gH` and quotient `Q=-P/λ` rows. The
four `P_v` difference terms feed the five `Q_v` difference terms, with the
exact arbitrary-width coefficients of the factor estimates. -/
theorem source_coefficient_difference_of_factor_bounds
    {c d E τ K0 Kv Kd Kdv B Hv Hd Hdv L : ℝ}
    {k₁ k₂ ki₁ ki₂ h₁ h₂ hi₁ hi₂ lam₁ lam₂ Li₁ Li₂ : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hdτ : d ≤ τ) (hτ : 1 ≤ τ)
    (hE : 0 ≤ E) (hK0 : 0 ≤ K0) (hKv : 0 ≤ Kv)
    (hKd : 0 ≤ Kd) (hKdv : 0 ≤ Kdv)
    (hB : 0 ≤ B) (hHv : 0 ≤ Hv) (hHd : 0 ≤ Hd)
    (hHdv : 0 ≤ Hdv) (hL : 0 ≤ L)
    (hk₂ : |k₂| ≤ K0 * d)
    (hkd : |k₁ - k₂| ≤ Kd * d * E)
    (hki₂ : |ki₂| ≤ Kv)
    (hkid : |ki₁ - ki₂| ≤ Kdv * E)
    (hh₁ : |h₁| ≤ B * d) (hh₂ : |h₂| ≤ B * d)
    (hhd : |h₁ - h₂| ≤ Hd * d * E)
    (hhi₁ : |hi₁| ≤ Hv) (hhi₂ : |hi₂| ≤ Hv)
    (hhid : |hi₁ - hi₂| ≤ Hdv * E)
    (hlam₁ : c ≤ lam₁) (hlam₂ : c ≤ lam₂)
    (hlamdiff : |lam₁ - lam₂| ≤ E)
    (hLi₁ : |Li₁| ≤ L) (hLi₂ : |Li₂| ≤ L)
    (hLidiff : |Li₁ - Li₂| ≤ E) :
    let P0 := K0 * B
    let Pv := Kv * B + K0 * Hv
    let Pd := Kd * B + K0 * Hd
    let Pdv := Kdv * B + Kv * Hd + Kd * Hv + K0 * Hdv
    |-(k₁ * h₁) / lam₁ - -(k₂ * h₂) / lam₂| ≤
      (Pd / c + P0 / c ^ 2) * d ^ 2 * E ∧
    |(-(ki₁ * h₁ + k₁ * hi₁) / lam₁ +
        (k₁ * h₁) * Li₁ / lam₁ ^ 2) -
      (-(ki₂ * h₂ + k₂ * hi₂) / lam₂ +
        (k₂ * h₂) * Li₂ / lam₂ ^ 2)| ≤
      (Pdv / c + Pv / c ^ 2 + Pd * L * τ / c ^ 2 +
        P0 * τ / c ^ 2 + 2 * P0 * L * τ / c ^ 3) * d * E := by
  dsimp only
  let P0 := K0 * B
  let Pv := Kv * B + K0 * Hv
  let Pd := Kd * B + K0 * Hd
  let Pdv := Kdv * B + Kv * Hd + Kd * Hv + K0 * Hdv
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  have hPv : 0 ≤ Pv := by dsimp [Pv]; positivity
  have hPd : 0 ≤ Pd := by dsimp [Pd]; positivity
  have hPdv : 0 ≤ Pdv := by dsimp [Pdv]; positivity
  have hP₂ : |k₂ * h₂| ≤ P0 * d ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (K0 * d) * (B * d) :=
        mul_le_mul hk₂ hh₂ (abs_nonneg _) (mul_nonneg hK0 hd)
      _ = P0 * d ^ 2 := by dsimp [P0]; ring
  have hPd' : |k₁ * h₁ - k₂ * h₂| ≤ Pd * d ^ 2 * E := by
    simpa only [Pd] using
      intervalIntegral.abs_mul_sub_mul_le_of_linear_gap_bounds
        hd hE hK0 hKd hk₂ hkd hh₁ hhd
  have hPi₂ : |ki₂ * h₂ + k₂ * hi₂| ≤ Pv * d := by
    have h₁' : |ki₂ * h₂| ≤ Kv * (B * d) := by
      rw [abs_mul]
      exact mul_le_mul hki₂ hh₂ (abs_nonneg _) hKv
    have h₂' : |k₂ * hi₂| ≤ (K0 * d) * Hv := by
      rw [abs_mul]
      exact mul_le_mul hk₂ hhi₂ (abs_nonneg _) (mul_nonneg hK0 hd)
    calc
      _ ≤ |ki₂ * h₂| + |k₂ * hi₂| := abs_add_le _ _
      _ ≤ Kv * (B * d) + (K0 * d) * Hv := add_le_add h₁' h₂'
      _ = Pv * d := by dsimp [Pv]; ring
  have hPdv' : |(ki₁ * h₁ + k₁ * hi₁) -
      (ki₂ * h₂ + k₂ * hi₂)| ≤ Pdv * d * E := by
    simpa only [Pdv] using
      intervalIntegral.abs_productJet_sub_le_of_linear_gap_bounds
        hd hE hK0 hKd hk₂ hkd hki₂ hkid hh₁ hhd hhi₁ hhid
  constructor
  · have h := intervalIntegral.abs_div_sub_div_le_of_quadratic_gap_bounds
      hc hlam₁ hlam₂ hlamdiff hP₂ hPd'
    have heq : -(k₁ * h₁) / lam₁ - -(k₂ * h₂) / lam₂ =
        -((k₁ * h₁) / lam₁ - (k₂ * h₂) / lam₂) := by ring
    rw [heq, abs_neg]
    exact h
  · have h := source_coefficient_jet_difference hc hd hdτ hτ hE
      hP0 hPv hPd hPdv hL hlam₁ hlam₂ hlamdiff
      hP₂ hPd' hPi₂ hPdv' hLi₁ hLi₂ hLidiff
    have heq :
        (-(ki₁ * h₁ + k₁ * hi₁) / lam₁ +
          (k₁ * h₁) * Li₁ / lam₁ ^ 2) -
        (-(ki₂ * h₂ + k₂ * hi₂) / lam₂ +
          (k₂ * h₂) * Li₂ / lam₂ ^ 2) =
        -(((ki₁ * h₁ + k₁ * hi₁) / lam₁ -
          (k₁ * h₁) * Li₁ / lam₁ ^ 2) -
          ((ki₂ * h₂ + k₂ * hi₂) / lam₂ -
          (k₂ * h₂) * Li₂ / lam₂ ^ 2)) := by ring
    rw [heq, abs_neg]
    exact h

/-- The final pointwise arithmetic of the arbitrary-width coefficient
ledger. The `Kd`, `Qd`, `Kdv`, and `Qdv` bounds retain their gap powers until
this step, where `d≤τ` produces the explicit constant `A₁`. -/
theorem four_coefficient_difference_bound
    {d E τ Kd Qd Kdv Qdv : ℝ}
    {K₁ K₂ Q₁ Q₂ Ki₁ Ki₂ Qi₁ Qi₂ : ℝ}
    (hd : 0 ≤ d) (hdτ : d ≤ τ) (hE : 0 ≤ E)
    (hKd : 0 ≤ Kd) (hQd : 0 ≤ Qd) (hQdv : 0 ≤ Qdv)
    (hK : |K₁ - K₂| ≤ Kd * d * E)
    (hQ : |Q₁ - Q₂| ≤ Qd * d ^ 2 * E)
    (hKi : |Ki₁ - Ki₂| ≤ Kdv * E)
    (hQi : |Qi₁ - Qi₂| ≤ Qdv * d * E) :
    |K₁ - K₂| + |Q₁ - Q₂| + |Ki₁ - Ki₂| + |Qi₁ - Qi₂| ≤
      (Kd * τ + Qd * τ ^ 2 + Kdv + Qdv * τ) * E := by
  have hτ0 : 0 ≤ τ := hd.trans hdτ
  have hdsq : d ^ 2 ≤ τ ^ 2 := by nlinarith only [hd, hdτ, hτ0]
  have h₁ : Kd * d * E ≤ Kd * τ * E := by gcongr
  have h₂ : Qd * d ^ 2 * E ≤ Qd * τ ^ 2 * E := by gcongr
  have h₃ : Qdv * d * E ≤ Qdv * τ * E := by gcongr
  calc
    _ ≤ Kd * d * E + Qd * d ^ 2 * E + Kdv * E + Qdv * d * E := by
      exact add_le_add (add_le_add (add_le_add hK hQ) hKi) hQi
    _ ≤ Kd * τ * E + Qd * τ ^ 2 * E + Kdv * E + Qdv * τ * E := by
      exact add_le_add (add_le_add (add_le_add h₁ h₂) le_rfl) h₃
    _ = _ := by ring

/-- The outgoing-ray scalar Gronwall step. This is the exact factor used to
eliminate the `ν` difference from the four-field comparison. -/
theorem outgoing_nu_bound_of_volterra
    {u b τ D Kd : ℝ} {n : ℝ → ℝ}
    (hub : u ≤ b) (hτ : 1 ≤ τ) (hwidth : b - u ≤ τ)
    (hD : 0 ≤ D) (hKd : 0 ≤ Kd)
    (hn : ContinuousOn n (Icc u b))
    (hineq : ∀ v ∈ Icc u b,
      n v ≤ D + Kd * τ * ∫ s in u..v, (D + n s)) :
    n b ≤ (2 * Real.exp (Kd * τ ^ 2) - 1) * D := by
  let g : ℝ → ℝ := fun v => D + n v
  have hgcont : ContinuousOn g (Icc u b) :=
    continuousOn_const.add hn
  have hgint : IntervalIntegrable g volume u b :=
    hgcont.intervalIntegrable_of_Icc hub
  have hkint : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume u b :=
    intervalIntegrable_const
  have hkgint : IntervalIntegrable (fun s : ℝ => (1 : ℝ) * g s)
      volume u b := by simpa only [one_mul] using hgint
  have hB : 0 ≤ Kd * τ := mul_nonneg hKd (by linarith only [hτ])
  have hbound := intervalIntegral.le_mul_exp_integral_of_le_integral_const_mul
    (a := u) (b := b) (A := 2 * D) (B := Kd * τ)
    (k := fun _ => (1 : ℝ)) (h := g) hub hB hkint hkgint
    (fun _ _ => by norm_num)
    (fun v hv => by
      have h := hineq v hv
      simp only [one_mul]
      change D + n v ≤ 2 * D + Kd * τ * ∫ s in u..v, g s
      linarith only [h])
  have hb : b ∈ Icc u b := ⟨hub, le_rfl⟩
  have hgb := hbound b hb
  have hintegral : (∫ _s in u..b, (1 : ℝ)) = b - u := by simp
  rw [hintegral] at hgb
  have hexparg : Kd * τ * (b - u) ≤ Kd * τ ^ 2 := by
    have hτ0 : 0 ≤ τ := by linarith only [hτ]
    nlinarith only [mul_le_mul_of_nonneg_left hwidth (mul_nonneg hKd hτ0)]
  have hexp : Real.exp (Kd * τ * (b - u)) ≤ Real.exp (Kd * τ ^ 2) :=
    Real.exp_le_exp.mpr hexparg
  have hmul : 2 * D * Real.exp (Kd * τ * (b - u)) ≤
      2 * D * Real.exp (Kd * τ ^ 2) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  change D + n b ≤ 2 * D * Real.exp (Kd * τ * (b - u)) at hgb
  calc
    n b ≤ 2 * D * Real.exp (Kd * τ * (b - u)) - D := by
      linarith only [hgb]
    _ ≤ 2 * D * Real.exp (Kd * τ ^ 2) - D := by
      linarith only [hmul]
    _ = (2 * Real.exp (Kd * τ ^ 2) - 1) * D := by ring

end ChristodoulouBV.C1Solution

end
