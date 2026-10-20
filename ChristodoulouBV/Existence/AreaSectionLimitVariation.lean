module

public import ChristodoulouBV.Existence.AreaSectionLimitSmoothCalculus
public import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
public import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.Tactic

/-!
# Uniform variation bounds on compact area sections

The BV factor is controlled by the smooth approximants' natural section bounds, including
the initial incoming endpoint. The other factor is absolutely continuous
with the bounded mixed scalar density. Their pointwise product and
integral primitive therefore have a bound uniform in the smooth index.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- A common finite BV bound for the four second components on compact
physical sections. The scalar offset is retained in this local bound. -/
@[expose] noncomputable def areaSectionFieldVariationBound (D : ℝ≥0∞) (C : ℝ) : ℝ≥0∞ :=
  s4UniversalC * D ^ 2 +
    (ENNReal.ofReal (1 / (1 / 3 : ℝ)) * scalarVariationBound D C +
      ENNReal.ofReal ((4 * D.toReal + C) / (1 / 3 : ℝ) ^ 2) * (s4UniversalC * D ^ 2))

/-- The local BV bound is finite whenever the datum variation is finite. -/
theorem area_section_field_variation_bound_ne_top {D : ℝ≥0∞} (hD : D ≠ ∞) (C : ℝ) :
    areaSectionFieldVariationBound D C ≠ ∞ := by
  have hV : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  exact ENNReal.add_ne_top.mpr ⟨hV, ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (scalarVariationBound_ne_top hD C),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV⟩⟩

/-- Uniform BV control of the actual second component of every smooth
area section on any admissible compact physical interval. -/
theorem SmoothSolutionBounds.area_section_g_variation_bound
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z A B : ℝ}
    (hab : A ≤ B) (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain) :
    eVariationOn (fun t => areaSectionG k
      (areaSectionCoefficients S (areaPhysicalPoint k z t))) (Icc A B) ≤
        areaSectionFieldVariationBound D C := by
  have hD : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hC := h.offset_nonneg
  have hA := hs ⟨le_rfl, hab⟩
  cases k with
  | phiAlphaLam =>
    change (z, A) ∈ globalDomain at hA
    have hsub : Icc A B ⊆ Ioi z := fun t ht => (hs ht).2
    have hl := (eVariationOn.mono (S.lam z) hsub).trans ((h.variation_out z hA.1).2)
    have hα := (eVariationOn.mono (S.alpha z) hsub).trans (h.raw_variation_out z hA.1)
    have hd := eVariationOn.div_le_of_abs_ge (c := (1 / 3 : ℝ)) (M := 4 * D.toReal + C)
      (f := S.alpha z) (g := S.lam z) (s := Icc A B) (by norm_num)
      (fun t ht => ((h.geometry (z, t) (hs ht)).1).trans (le_abs_self _))
      (fun t ht => by have hb := h.amplitudes.alpha (z, t) (hs ht); linarith only [hb, hD, hC])
    have hd' := hd.trans (add_le_add (mul_le_mul_of_nonneg_left hα bot_le)
      (mul_le_mul_of_nonneg_left hl bot_le))
    have hout := hd'.trans (le_add_of_nonneg_left (a :=
      ENNReal.ofReal (1 / (1 / 3 : ℝ)) * scalarVariationBound D C +
      ENNReal.ofReal ((4 * D.toReal + C) / (1 / 3 : ℝ) ^ 2) * (s4UniversalC * D ^ 2))
        (b := s4UniversalC * D ^ 2) bot_le)
    change eVariationOn (fun t => S.alpha z t * (S.lam z t)⁻¹) (Icc A B) ≤ _
    simpa only [div_eq_mul_inv, areaSectionFieldVariationBound, scalarVariationBound] using hout
  | lamPhi =>
    change (z, A) ∈ globalDomain at hA
    have hsub : Icc A B ⊆ Ioi z := fun t ht => (hs ht).2
    exact ((eVariationOn.mono (S.lam z) hsub).trans ((h.variation_out z hA.1).2)).trans
      (le_add_of_nonneg_right bot_le)
  | phiBetaNu =>
    change (A, z) ∈ globalDomain at hA
    have hz : 0 < z := hA.1.trans_lt hA.2
    have hsub : Icc A B ⊆ Ico 0 z := fun t ht => hs ht
    have hn := (eVariationOn.mono (fun t => S.nu t z) hsub).trans (h.variation_nu_initial_edge hz)
    have hβ := (eVariationOn.mono (fun t => S.beta t z) hsub).trans
      (h.variation_beta_initial_edge hz)
    have hd := eVariationOn.div_le_of_abs_ge (c := (1 / 3 : ℝ)) (M := 4 * D.toReal + C)
      (f := fun t => S.beta t z) (g := fun t => S.nu t z) (s := Icc A B) (by norm_num)
      (fun t ht => by
        have hb := (h.geometry (t, z) (hs ht)).2.2.1
        rw [abs_of_nonpos (by linarith only [hb])]
        exact hb)
      (fun t ht => by have hb := h.amplitudes.beta (t, z) (hs ht); linarith only [hb, hC])
    have hd' := hd.trans (add_le_add (mul_le_mul_of_nonneg_left hβ bot_le)
      (mul_le_mul_of_nonneg_left hn bot_le))
    have hout := hd'.trans (le_add_of_nonneg_left (a :=
      ENNReal.ofReal (1 / (1 / 3 : ℝ)) * scalarVariationBound D C +
      ENNReal.ofReal ((4 * D.toReal + C) / (1 / 3 : ℝ) ^ 2) * (s4UniversalC * D ^ 2))
        (b := s4UniversalC * D ^ 2) bot_le)
    change eVariationOn (fun t => S.beta t z * (S.nu t z)⁻¹) (Icc A B) ≤ _
    simpa only [div_eq_mul_inv, areaSectionFieldVariationBound, scalarVariationBound] using hout
  | nuPhi =>
    change (A, z) ∈ globalDomain at hA
    have hz : 0 < z := hA.1.trans_lt hA.2
    have hsub : Icc A B ⊆ Ico 0 z := fun t ht => hs ht
    exact ((eVariationOn.mono (fun t => S.nu t z) hsub).trans
      (h.variation_nu_initial_edge hz)).trans (le_add_of_nonneg_right bot_le)

private theorem ac_variation_le_of_ae_bound
    {f p : ℝ → ℝ} {A B M : ℝ} (hab : A ≤ B)
    (hf : AbsolutelyContinuousOnInterval f A B)
    (hfp : ∀ᵐ t ∂volume, t ∈ Icc A B → deriv f t = p t)
    (hp : ∀ t ∈ Icc A B, |p t| ≤ M) :
    eVariationOn f (Icc A B) ≤ ENNReal.ofReal (M * (B - A)) := by
  rw [hf.eVariationOn_eq_integral_abs_deriv hab]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ t in A..B, |deriv f t|) ≤ ∫ _t in A..B, M := by
      apply intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv.abs
        intervalIntegrable_const
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae hfp] with t ht hpt
      rw [hpt ht]
      exact hp t ht
    _ = M * (B - A) := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem integral_variation_le_of_bound
    {q : ℝ → ℝ} {A B b M : ℝ} (hab : A ≤ B) (hb : b ∈ Icc A B)
    (hq : IntervalIntegrable q volume A B) (hbound : ∀ t ∈ Icc A B, |q t| ≤ M) :
    eVariationOn (fun x => ∫ t in b..x, q t) (Icc A B) ≤ ENNReal.ofReal (M * (B - A)) := by
  have hint (x y : ℝ) (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
      IntervalIntegrable q volume x y :=
    hq.mono_set (by simpa only [uIcc_of_le hab] using uIcc_subset_Icc hx hy)
  rw [IntervalIntegrable.eVariationOn_eq_integral_abs hab hq (by
    intro x hx
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hint b A hb ⟨le_rfl, hab⟩) (hint A x ⟨le_rfl, hab⟩ hx)).symm)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ t in A..B, |q t|) ≤ ∫ _t in A..B, M :=
      intervalIntegral.integral_mono_on hab hq.abs intervalIntegrable_const hbound
    _ = M * (B - A) := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem smooth_area_f_ac_ae
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z A B : ℝ}
    (hab : A ≤ B) (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain) :
    AbsolutelyContinuousOnInterval
      (fun t => areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t))) A B ∧
      ∀ᵐ t ∂volume, t ∈ Icc A B →
        deriv (fun t => areaSectionF k
          (areaSectionCoefficients S (areaPhysicalPoint k z t))) t =
          areaSectionP (areaSectionCoefficients S (areaPhysicalPoint k z t)) := by
  cases hki : k.incoming with
  | false =>
    have hseg : outSeg z A B ⊆ globalDomain := by
      rintro ⟨u, v⟩ ⟨rfl, hv⟩
      simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using hs hv
    have heq : (fun t => areaSectionF k
        (areaSectionCoefficients S (areaPhysicalPoint k z t))) =
        (fun t => S.zeta z t / S.r z t) := by
      funext t
      simp only [areaSectionF, areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      change (S.beta z t - S.nu z t * S.phi z t) * (S.r z t)⁻¹ = _
      rw [Fields.zeta, div_eq_mul_inv]
    rw [heq]
    simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using
      h.outgoing_mixed_scalar_density hab hseg
  | true =>
    have hseg : inSeg z A B ⊆ globalDomain := by
      rintro ⟨u, v⟩ ⟨hu, rfl⟩
      simpa only [areaPhysicalPoint, hki, ite_true] using hs hu
    have heq : (fun t => areaSectionF k
        (areaSectionCoefficients S (areaPhysicalPoint k z t))) =
        (fun t => S.theta t z / S.r t z) := by
      funext t
      simp only [areaSectionF, areaPhysicalPoint, hki, ite_true]
      change (S.alpha t z - S.lam t z * S.phi t z) * (S.r t z)⁻¹ = _
      rw [Fields.theta, div_eq_mul_inv]
    rw [heq]
    simpa only [areaPhysicalPoint, hki, ite_true] using
      h.incoming_mixed_scalar_density hab hseg

/-- A uniform bound for the variation of a smooth physical primitive,
derived from its four algebraic majorants and the smooth BV bounds. -/
theorem SmoothSolutionBounds.area_physical_primitive_variation_bound
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z b A B : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    {F G P Q : ℝ}
    (hF : ∀ t ∈ Icc A B, |areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t))| ≤ F)
    (hG : ∀ t ∈ Icc A B, |areaSectionG k (areaSectionCoefficients S (areaPhysicalPoint k z t))| ≤ G)
    (hP : ∀ t ∈ Icc A B, |areaSectionP (areaSectionCoefficients S (areaPhysicalPoint k z t))| ≤ P)
    (hQ : ∀ t ∈ Icc A B,
      |areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k z t))| ≤ Q) :
    eVariationOn (areaPhysicalPrimitive k S z b) (Icc A B) ≤
      ENNReal.ofReal F * areaSectionFieldVariationBound D C +
        ENNReal.ofReal G * ENNReal.ofReal (P * (B - A)) +
          ENNReal.ofReal (Q * (B - A)) := by
  let f := fun t => areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  let g := fun t => areaSectionG k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  let q := fun t => areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  have hvar_g := h.area_section_g_variation_bound k hab hs
  obtain ⟨hfAC, hfDeriv⟩ := smooth_area_f_ac_ae h k hab hs
  have hvar_f := ac_variation_le_of_ae_bound hab hfAC hfDeriv hP
  have hqcont : ContinuousOn q (Icc A B) :=
    (area_section_q_continuous k).continuousOn.comp
      (h.area_section_coefficients_continuousOn.comp
        ((area_physical_point_continuous k).comp
          (continuous_const.prodMk continuous_id)).continuousOn hs)
      (fun _ _ => mem_univ _)
  have hvar_q := integral_variation_le_of_bound hab hb (hqcont.intervalIntegrable_of_Icc hab) hQ
  have hprod := (eVariationOn.mul_le_of_abs_le hF hG).trans
    (add_le_add (mul_le_mul_of_nonneg_left hvar_g bot_le) (mul_le_mul_of_nonneg_left hvar_f bot_le))
  have heq : areaPhysicalPrimitive k S z b =
      (fun t => f t * g t - f b * g b) - (fun x => ∫ t in b..x, q t) := rfl
  rw [heq]
  apply (eVariationOn.sub_le _ _ _).trans
  have hconst : eVariationOn (fun t => f t * g t - f b * g b) (Icc A B) =
      eVariationOn (f * g) (Icc A B) := by
    simpa only [sub_eq_add_neg, Pi.mul_apply] using
      eVariationOn.add_const (f * g) (-(f b * g b)) (Icc A B)
  rw [hconst]
  exact add_le_add hprod hvar_q

end ChristodoulouBV

end
