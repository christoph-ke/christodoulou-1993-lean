module

public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Order.Interval.Set.ProjIcc
public import ChristodoulouBV.ForMathlib.BoundedVariation.ExtendIcc

/-!
# Local Stieltjes measures on a compact real interval

A function of bounded variation on a closed interval is extended constantly outside that
interval. Its global vector measure then gives a finite signed Stieltjes measure on the interval.
The extension preserves the exact variation, including the costs of unusual endpoint values.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace BoundedVariationOn

/-- The Stieltjes vector measure on `[a,b]`, with constant extension on both sides.
An atom at `b` records the left jump into `f b`; an atom at `a` records the
right jump away from `f a`. -/
noncomputable def localStieltjes {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) : VectorMeasure ℝ ℝ :=
  ((extendIcc_boundedVariationOn hab hf).vectorMeasure).restrict (Icc a b)

/-- The local Stieltjes measure only depends on values inside the closed interval. -/
theorem localStieltjes_congr {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hg : BoundedVariationOn g (Icc a b))
    (hfg : EqOn f g (Icc a b)) :
    localStieltjes hab hf = localStieltjes hab hg := by
  have hext : Function.extendIcc f hab = Function.extendIcc g hab := by
    funext x
    exact hfg (Set.projIcc a b hab x).property
  simp only [localStieltjes, hext]

/-- The total variation of the local measure is bounded by the original interval variation. -/
theorem localStieltjes_variation_univ_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) :
    (localStieltjes hab hf).variation univ ≤ eVariationOn f (Icc a b) := by
  let h := extendIcc_boundedVariationOn hab hf
  calc
    (localStieltjes hab hf).variation univ = h.vectorMeasure.variation (Icc a b) := by
      simp [localStieltjes, VectorMeasure.variation_restrict measurableSet_Icc]
    _ ≤ h.vectorMeasure.variation univ := measure_mono (subset_univ _)
    _ ≤ eVariationOn (Function.extendIcc f hab) univ := h.variation_vectorMeasure_univ_le
    _ = eVariationOn f (Icc a b) := eVariationOn_extendIcc hab

/-- The variation bound also applies to each measurable subinterval of `[a,b]`. -/
theorem localStieltjes_variation_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (s : Set ℝ) :
    (localStieltjes hab hf).variation s ≤ eVariationOn f (Icc a b) :=
  (measure_mono (subset_univ s)).trans (localStieltjes_variation_univ_le hab hf)

/-- On a subinterval, the local measure has the global right-limit increment formula. -/
theorem localStieltjes_Ioc {f : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) :
    localStieltjes hab hf (Ioc c d) =
      (Function.extendIcc f hab).rightLim d - (Function.extendIcc f hab).rightLim c := by
  have hs : Ioc c d ⊆ Icc a b := by
    intro x hx
    exact ⟨hac.trans hx.1.le, hx.2.trans hdb⟩
  rw [localStieltjes, VectorMeasure.restrict_eq_self
    (v := (extendIcc_boundedVariationOn hab hf).vectorMeasure)
    measurableSet_Icc measurableSet_Ioc hs]
  exact (extendIcc_boundedVariationOn hab hf).vectorMeasure_Ioc hcd

/-- The local measure of a closed subinterval is the increment between the extension's
right limit at its right endpoint and left limit at its left endpoint. -/
theorem localStieltjes_Icc {f : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) :
    localStieltjes hab hf (Icc c d) =
      (Function.extendIcc f hab).rightLim d - (Function.extendIcc f hab).leftLim c := by
  have hs : Icc c d ⊆ Icc a b := by
    intro x hx
    exact ⟨hac.trans hx.1, hx.2.trans hdb⟩
  rw [localStieltjes, VectorMeasure.restrict_eq_self
    (v := (extendIcc_boundedVariationOn hab hf).vectorMeasure)
    measurableSet_Icc measurableSet_Icc hs]
  exact (extendIcc_boundedVariationOn hab hf).vectorMeasure_Icc hcd

/-- At a point of the interval, the atom is the jump of the extended function. -/
theorem localStieltjes_singleton {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hx : x ∈ Icc a b) :
    localStieltjes hab hf {x} =
      (Function.extendIcc f hab).rightLim x - (Function.extendIcc f hab).leftLim x := by
  have hs : ({x} : Set ℝ) ⊆ Icc a b := by simpa using hx
  rw [localStieltjes, VectorMeasure.restrict_eq_self
    (v := (extendIcc_boundedVariationOn hab hf).vectorMeasure)
    measurableSet_Icc (measurableSet_singleton x) hs]
  exact (extendIcc_boundedVariationOn hab hf).vectorMeasure_singleton

/-- Strictly before the right endpoint, the extension has the same right limit as `f`. -/
theorem rightLim_extendIcc_of_lt {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hax : a ≤ x) (hxb : x < b) :
    (Function.extendIcc f hab).rightLim x = f.rightLim x := by
  have hev : f =ᶠ[𝓝[>] x] Function.extendIcc f hab := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb)] with y hxy hyb
    exact (extendIcc_of_mem hab ⟨hax.trans hxy.le, hyb.le⟩).symm
  have hlim := (extendIcc_boundedVariationOn hab hf).tendsto_rightLim x
  exact (rightLim_eq_of_tendsto (hlim.congr' hev.symm)).symm

/-- Strictly after the left endpoint, the extension has the same left limit as `f`. -/
theorem leftLim_extendIcc_of_gt {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hax : a < x) (hxb : x ≤ b) :
    (Function.extendIcc f hab).leftLim x = f.leftLim x := by
  have hev : f =ᶠ[𝓝[<] x] Function.extendIcc f hab := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hax)] with y hyx hay
    exact (extendIcc_of_mem hab ⟨hay.le, hyx.le.trans hxb⟩).symm
  have hlim := (extendIcc_boundedVariationOn hab hf).tendsto_leftLim x
  exact (leftLim_eq_of_tendsto (hlim.congr' hev.symm)).symm

/-- The extension's left limit at `a` is its constant left value. -/
theorem leftLim_extendIcc_left {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (Function.extendIcc f hab).leftLim a = f a := by
  have hev : Function.extendIcc f hab =ᶠ[𝓝[<] a] fun _ => f a := by
    filter_upwards [self_mem_nhdsWithin] with y hya
    exact extendIcc_of_le_left hab hya.le
  exact leftLim_eq_of_tendsto (tendsto_const_nhds.congr' hev.symm)

/-- The extension's right limit at `b` is its constant right value. -/
theorem rightLim_extendIcc_right {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (Function.extendIcc f hab).rightLim b = f b := by
  have hev : Function.extendIcc f hab =ᶠ[𝓝[>] b] fun _ => f b := by
    filter_upwards [self_mem_nhdsWithin] with y hby
    exact extendIcc_of_right_le hab hby.le
  exact rightLim_eq_of_tendsto (tendsto_const_nhds.congr' hev.symm)

/-- On an interval strictly below `b`, the measure is the increment of the right limits of `f`. -/
theorem localStieltjes_Ioc_lt {f : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d < b) :
    localStieltjes hab hf (Ioc c d) = f.rightLim d - f.rightLim c := by
  rw [localStieltjes_Ioc hab hf hac hcd hdb.le,
    rightLim_extendIcc_of_lt hab hf (hac.trans hcd) hdb,
    rightLim_extendIcc_of_lt hab hf hac (hcd.trans_lt hdb)]

/-- At the right endpoint, the measure records the value `f b`, not a right limit of `f`. -/
theorem localStieltjes_Ioc_right {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) (hac : a ≤ c) (hcb : c < b) :
    localStieltjes hab hf (Ioc c b) = f b - f.rightLim c := by
  rw [localStieltjes_Ioc hab hf hac hcb.le le_rfl,
    rightLim_extendIcc_right hab, rightLim_extendIcc_of_lt hab hf hac hcb]

/-- The left endpoint atom is the jump from `f a` to its right limit when `a < b`. -/
theorem localStieltjes_singleton_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Icc a b)) :
    localStieltjes hab.le hf {a} = f.rightLim a - f a := by
  rw [localStieltjes_singleton hab.le hf ⟨le_rfl, hab.le⟩,
    rightLim_extendIcc_of_lt hab.le hf le_rfl hab, leftLim_extendIcc_left hab.le]

/-- The right endpoint atom is the jump from the left limit into `f b`. -/
theorem localStieltjes_singleton_right {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Icc a b)) :
    localStieltjes hab.le hf {b} = f b - f.leftLim b := by
  rw [localStieltjes_singleton hab.le hf ⟨hab.le, le_rfl⟩,
    rightLim_extendIcc_right hab.le,
    leftLim_extendIcc_of_gt hab.le hf hab le_rfl]

/-- A uniform bound on an integrand controls its integral against the local Stieltjes measure.
This applies in particular to both `Ioc` and `Icc` subintervals. -/
theorem enorm_setIntegral_localStieltjes_le {f h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b))
    {s : Set ℝ} {C : ℝ≥0∞} (hC : ∀ x ∈ s, ‖h x‖ₑ ≤ C) :
    ‖∫ᵛ x in s, h x ∂•localStieltjes hab hf‖ₑ ≤
      C * eVariationOn f (Icc a b) := by
  calc
    ‖∫ᵛ x in s, h x ∂•localStieltjes hab hf‖ₑ ≤
        C * ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ *
          (localStieltjes hab hf).variation s :=
      VectorMeasure.enorm_setIntegral_le_of_enorm_le_const hC
    _ ≤ C * 1 * (localStieltjes hab hf).variation s := by
      gcongr
      exact ContinuousLinearMap.opENorm_lsmul_le
    _ ≤ C * 1 * eVariationOn f (Icc a b) := by
      gcongr
      exact localStieltjes_variation_le hab hf s
    _ = C * eVariationOn f (Icc a b) := by simp

/-- Integrating over a subset of `[a,b]` agrees with integrating against the global measure
of the constant extension. -/
theorem setIntegral_localStieltjes_eq {f h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b))
    {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Icc a b) :
    (∫ᵛ x in s, h x ∂•localStieltjes hab hf) =
      ∫ᵛ x in s, h x ∂•(extendIcc_boundedVariationOn hab hf).vectorMeasure := by
  simp only [localStieltjes, VectorMeasure.restrict_restrict
    (v := (extendIcc_boundedVariationOn hab hf).vectorMeasure) hs measurableSet_Icc,
    Set.inter_eq_left.mpr hsub]

/-- Integration by parts for the local Stieltjes measures on `[a,b]`.
The one-sided representatives make the formula valid in the presence of jumps. -/
theorem setIntegral_Icc_localStieltjes_ibp {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b))
    (hg : BoundedVariationOn g (Icc a b)) :
    (∫ᵛ x in Icc a b, (Function.extendIcc f hab).leftLim x ∂•localStieltjes hab hg) =
      f b • g b - f a • g a -
        ∫ᵛ x in Icc a b, (Function.extendIcc g hab).rightLim x ∂<•localStieltjes hab hf := by
  have h := (extendIcc_boundedVariationOn hab hf).setIntegral_Icc_leftLim_smul_vectorMeasure_eq_sub
    (extendIcc_boundedVariationOn hab hg) hab
  rw [rightLim_extendIcc_right hab, rightLim_extendIcc_right hab,
    leftLim_extendIcc_left hab, leftLim_extendIcc_left hab] at h
  simpa only [localStieltjes,
    VectorMeasure.restrict_restrict
      (v := (extendIcc_boundedVariationOn hab hf).vectorMeasure)
      measurableSet_Icc measurableSet_Icc,
    VectorMeasure.restrict_restrict
      (v := (extendIcc_boundedVariationOn hab hg).vectorMeasure)
      measurableSet_Icc measurableSet_Icc,
    Set.inter_self] using h

/-- Integration by parts on `(a,b]`; the omitted left atom changes the boundary term to
the right limits at `a`. -/
theorem setIntegral_Ioc_localStieltjes_ibp {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : BoundedVariationOn f (Icc a b))
    (hg : BoundedVariationOn g (Icc a b)) :
    (∫ᵛ x in Ioc a b, (Function.extendIcc f hab.le).leftLim x ∂•localStieltjes hab.le hg) =
      f b • g b - f.rightLim a • g.rightLim a -
        ∫ᵛ x in Ioc a b, (Function.extendIcc g hab.le).rightLim x ∂<•localStieltjes hab.le hf := by
  have h :=
    (extendIcc_boundedVariationOn hab.le hf).setIntegral_Ioc_leftLim_smul_vectorMeasure_eq_sub
      (extendIcc_boundedVariationOn hab.le hg) hab.le
  rw [rightLim_extendIcc_right hab.le, rightLim_extendIcc_right hab.le,
    rightLim_extendIcc_of_lt hab.le hf le_rfl hab,
    rightLim_extendIcc_of_lt hab.le hg le_rfl hab] at h
  have hss : Ioc a b ∩ Icc a b = Ioc a b := Set.inter_eq_left.mpr Ioc_subset_Icc_self
  simpa only [localStieltjes,
    VectorMeasure.restrict_restrict
      (v := (extendIcc_boundedVariationOn hab.le hf).vectorMeasure)
      measurableSet_Ioc measurableSet_Icc,
    VectorMeasure.restrict_restrict
      (v := (extendIcc_boundedVariationOn hab.le hg).vectorMeasure)
      measurableSet_Ioc measurableSet_Icc,
    hss] using h

/-- The constant extension of an absolutely continuous function is continuous. -/
theorem continuous_extendIcc_of_absolutelyContinuousOnInterval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    Continuous (Function.extendIcc f hab) := by
  have hcont : ContinuousOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.continuousOn
  exact (continuous_IccExtend_iff (h := hab)).2 hcont.domRestrict

/-- For absolutely continuous data, the local Stieltjes mass of an interval is the integral
of the ordinary derivative. The right endpoint is included. -/
theorem localStieltjes_Ioc_eq_integral_deriv {f : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    localStieltjes (f := f) hab
      (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn)
      (Ioc c d) = ∫ x in c..d, deriv f x := by
  let hfbv : BoundedVariationOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.boundedVariationOn
  have hc := continuous_extendIcc_of_absolutelyContinuousOnInterval hab hf
  have hcdc : (Function.extendIcc f hab).rightLim c = f c := by
    rw [hc.continuousAt.continuousWithinAt.rightLim_eq]
    exact extendIcc_of_mem hab ⟨hac, hcd.trans hdb⟩
  have hcdd : (Function.extendIcc f hab).rightLim d = f d := by
    rw [hc.continuousAt.continuousWithinAt.rightLim_eq]
    exact extendIcc_of_mem hab ⟨hac.trans hcd, hdb⟩
  have hfac : AbsolutelyContinuousOnInterval f c d :=
    hf.mono (by simpa only [uIcc_of_le hcd, uIcc_of_le hab] using
      (Icc_subset_Icc hac hdb))
  change localStieltjes hab hfbv (Ioc c d) = _
  rw [localStieltjes_Ioc hab hfbv hac hcd hdb, hcdd, hcdc]
  exact hfac.integral_deriv_eq_sub.symm

/-- The same derivative formula holds for a closed subinterval: absolute continuity removes
the left endpoint atom. -/
theorem localStieltjes_Icc_eq_integral_deriv {f : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    localStieltjes (f := f) hab
      (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn)
      (Icc c d) = ∫ x in c..d, deriv f x := by
  let hfbv : BoundedVariationOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.boundedVariationOn
  have hc := continuous_extendIcc_of_absolutelyContinuousOnInterval hab hf
  have hcdc : (Function.extendIcc f hab).leftLim c = f c := by
    rw [hc.continuousAt.continuousWithinAt.leftLim_eq]
    exact extendIcc_of_mem hab ⟨hac, hcd.trans hdb⟩
  have hcdd : (Function.extendIcc f hab).rightLim d = f d := by
    rw [hc.continuousAt.continuousWithinAt.rightLim_eq]
    exact extendIcc_of_mem hab ⟨hac.trans hcd, hdb⟩
  have hfac : AbsolutelyContinuousOnInterval f c d :=
    hf.mono (by simpa only [uIcc_of_le hcd, uIcc_of_le hab] using
      (Icc_subset_Icc hac hdb))
  change localStieltjes hab hfbv (Icc c d) = _
  rw [localStieltjes_Icc hab hfbv hac hcd hdb, hcdd, hcdc]
  exact hfac.integral_deriv_eq_sub.symm

/-- An absolutely continuous function has no left endpoint atom. -/
theorem localStieltjes_singleton_left_eq_zero_of_absolutelyContinuousOnInterval
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    localStieltjes (f := f) hab
      (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn) {a} = 0 := by
  have h := localStieltjes_Icc_eq_integral_deriv hab hf le_rfl le_rfl hab
  simpa using h

/-- The signed derivative-density measure on a compact interval. If the derivative is not
integrable, `withDensity` uses its standard zero fallback. -/
noncomputable def localDerivMeasure (f : ℝ → ℝ) (a b : ℝ) : VectorMeasure ℝ ℝ :=
  (((volume.restrict (Icc a b)).toSignedMeasure.withDensity (deriv f)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip).restrict (Icc a b))

/-- On a closed subinterval, the derivative-density measure integrates the derivative. -/
theorem localDerivMeasure_Icc {f : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    localDerivMeasure f a b (Icc c d) = ∫ x in c..d, deriv f x := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hderiv : IntegrableOn (deriv f) (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv
  have hvm : μ.toSignedMeasure.Integrable (deriv f) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure,
      IntegrableOn, μ] using hderiv
  have hsub : Icc c d ⊆ Icc a b := by
    intro x hx
    exact ⟨hac.trans hx.1, hx.2.trans hdb⟩
  unfold localDerivMeasure
  rw [VectorMeasure.restrict_eq_self
      (v := μ.toSignedMeasure.withDensity (deriv f)
        (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      measurableSet_Icc measurableSet_Icc hsub,
    VectorMeasure.withDensity_apply hvm]
  change (∫ᵛ x, deriv f x ∂<•(μ.toSignedMeasure.restrict (Icc c d))) = _
  rw [VectorMeasure.restrict_toSignedMeasure measurableSet_Icc,
    VectorMeasure.integral_toSignedMeasure]
  change (∫ x, deriv f x ∂(volume.restrict (Icc a b)).restrict (Icc c d)) = _
  rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.mpr hsub]
  simpa only [← restrict_Ioc_eq_restrict_Icc] using
    (intervalIntegral.integral_of_le hcd).symm

private theorem restrict_eq_of_Icc_subinterval (μ ν : VectorMeasure ℝ ℝ) {a b : ℝ}
    (h : ∀ c d, a ≤ c → c ≤ d → d ≤ b →
      (μ.restrict (Icc a b)) (Icc c d) = (ν.restrict (Icc a b)) (Icc c d)) :
    μ.restrict (Icc a b) = ν.restrict (Icc a b) := by
  apply VectorMeasure.ext_of_Icc
  intro c d hcd
  rw [VectorMeasure.restrict_apply μ measurableSet_Icc measurableSet_Icc,
    VectorMeasure.restrict_apply ν measurableSet_Icc measurableSet_Icc,
    Icc_inter_Icc, max_comm c a, min_comm d b]
  by_cases hmn : max a c ≤ min b d
  · have hs : Icc (max a c) (min b d) ⊆ Icc a b := by
      intro x hx
      exact ⟨le_trans (le_max_left a c) hx.1, hx.2.trans (min_le_left b d)⟩
    have hh := h (max a c) (min b d) (le_max_left a c) hmn (min_le_left b d)
    rw [VectorMeasure.restrict_eq_self μ measurableSet_Icc measurableSet_Icc hs,
      VectorMeasure.restrict_eq_self ν measurableSet_Icc measurableSet_Icc hs] at hh
    exact hh
  · have hempty : Icc (max a c) (min b d) = ∅ := by
      exact Icc_eq_empty_of_lt (lt_of_not_ge hmn)
    simp [hempty]

/-- For absolutely continuous data, the local Stieltjes vector measure is the signed
Lebesgue measure with density `deriv f` on `[a,b]`. This equality yields the corresponding
integral identity for every bounded measurable integrand. -/
theorem localStieltjes_eq_localDerivMeasure {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    localStieltjes (f := f) hab
      (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn) =
        localDerivMeasure f a b := by
  let hfbv : BoundedVariationOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.boundedVariationOn
  change ((extendIcc_boundedVariationOn hab hfbv).vectorMeasure).restrict (Icc a b) =
    (((volume.restrict (Icc a b)).toSignedMeasure.withDensity (deriv f)
      (ContinuousLinearMap.lsmul ℝ ℝ).flip).restrict (Icc a b))
  apply restrict_eq_of_Icc_subinterval _ _
  intro c d hac hcd hdb
  change localStieltjes hab hfbv (Icc c d) = localDerivMeasure f a b (Icc c d)
  exact (localStieltjes_Icc_eq_integral_deriv hab hf hac hcd hdb).trans
    (localDerivMeasure_Icc hab hf hac hcd hdb).symm

/-- The local derivative measure is Mathlib's vector-valued density of restricted Lebesgue
measure, restricted once more to the defining interval. -/
theorem localDerivMeasure_eq_withDensityᵥ {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntegrableOn (deriv f) (Icc a b) volume) :
    localDerivMeasure f a b =
      ((volume.restrict (Icc a b)).withDensityᵥ (deriv f)).restrict (Icc a b) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hderiv : Integrable (deriv f) μ := by simpa only [IntegrableOn, μ] using hf
  have hvm : μ.toSignedMeasure.Integrable (deriv f) := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hderiv
  apply VectorMeasure.ext
  intro s hs
  unfold localDerivMeasure
  rw [VectorMeasure.restrict_apply
      (v := μ.toSignedMeasure.withDensity (deriv f)
        (ContinuousLinearMap.lsmul ℝ ℝ).flip)
      measurableSet_Icc hs,
    VectorMeasure.restrict_apply
      (v := μ.withDensityᵥ (deriv f)) measurableSet_Icc hs,
    VectorMeasure.withDensity_apply hvm,
    withDensityᵥ_apply hderiv (hs.inter measurableSet_Icc)]
  change (∫ᵛ x, deriv f x ∂<•(μ.toSignedMeasure.restrict (s ∩ Icc a b))) = _
  rw [VectorMeasure.restrict_toSignedMeasure (hs.inter measurableSet_Icc),
    VectorMeasure.integral_toSignedMeasure]

/-- An absolutely continuous function's local Stieltjes measure is the signed derivative
density of Lebesgue measure on the compact interval. -/
theorem localStieltjes_eq_withDensityᵥ {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    localStieltjes (f := f) hab
      (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn) =
      ((volume.restrict (Icc a b)).withDensityᵥ (deriv f)).restrict (Icc a b) := by
  rw [localStieltjes_eq_localDerivMeasure hab hf]
  exact localDerivMeasure_eq_withDensityᵥ
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv)

end BoundedVariationOn
