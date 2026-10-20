module

public import Mathlib.Analysis.ODE.Gronwall
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Characteristic jets of Goursat integral solutions

The fundamental theorem of calculus gives relative characteristic derivatives at every point
of a closed rectangle, including its edges and corners. The transverse derivatives require
an additional argument and are not asserted here.
-/

public section

open Set intervalIntegral MeasureTheory

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An integral equation with a continuous integrand has its prescribed relative derivative
at every point of a closed interval, including both endpoints. -/
theorem hasDerivWithinAt_of_eq_integral_on_Icc
    {a b : ℝ} (g f : ℝ → E) (d : E)
    (hf : ContinuousOn f (Icc a b))
    (heq : ∀ t ∈ Icc a b, g t = d + ∫ s in a..t, f s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt g (f t) (Icc a b) t := by
  have hint : IntervalIntegrable f volume a t :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hprim : HasDerivWithinAt (fun x => ∫ s in a..x, f s)
      (f t) (Icc a b) t :=
    @integral_hasDerivWithinAt_right E _ _ _ f a t hint
      (Icc a b) (Icc a b) (@FTCFilter.nhdsIcc t a b ⟨ht⟩)
      (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hf t ht)
  have hsum : HasDerivWithinAt
      (fun x => d + ∫ s in a..x, f s) (f t) (Icc a b) t := by
    convert (hasDerivWithinAt_const (s := Icc a b) (x := t) (c := d)).add hprim using 1
    simp
  exact hsum.congr (fun x hx => heq x hx) (heq t ht)

/-- A continuous linear Volterra equation has the Grönwall bound with its actual
initial value and source bound. -/
theorem norm_le_gronwallBound_of_linear_volterra
    {a b : ℝ} (hab : a ≤ b) (z h : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (d : E) (P B κ : ℝ)
    (hz : ContinuousOn z (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hP : ‖d‖ ≤ P)
    (hB : ∀ s ∈ Icc a b, ‖h s‖ ≤ B)
    (hκ : ∀ s ∈ Icc a b, ‖A s‖ ≤ κ)
    (heq : ∀ t ∈ Icc a b, z t = d + ∫ s in a..t, A s (z s) + h s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖z t‖ ≤ gronwallBound P κ B (t - a) := by
  have hfield : ContinuousOn (fun s => A s (z s) + h s) (Icc a b) :=
    (hA.clm_apply hz).add hh
  have hderiv : ∀ s ∈ Icc a b,
      HasDerivWithinAt z (A s (z s) + h s) (Icc a b) s := by
    intro s hs
    exact hasDerivWithinAt_of_eq_integral_on_Icc z
      (fun x => A x (z x) + h x) d hfield heq hs
  have hright : ∀ s ∈ Ico a b,
      HasDerivWithinAt z (A s (z s) + h s) (Ici s) s := by
    intro s hs
    exact (hderiv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)
  have hinitial : z a = d := by
    simpa only [integral_same, add_zero] using heq a ⟨le_rfl, hab⟩
  have hbound : ∀ s ∈ Ico a b,
      ‖A s (z s) + h s‖ ≤ κ * ‖z s‖ + B := by
    intro s hs
    have hs' := Ico_subset_Icc_self hs
    calc
      ‖A s (z s) + h s‖ ≤ ‖A s (z s)‖ + ‖h s‖ := norm_add_le _ _
      _ ≤ ‖A s‖ * ‖z s‖ + B :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (hB s hs')
      _ ≤ κ * ‖z s‖ + B :=
        add_le_add (mul_le_mul_of_nonneg_right (hκ s hs') (norm_nonneg _)) le_rfl
  exact norm_le_gronwallBound_of_norm_deriv_right_le hz hright
    (by simpa only [hinitial] using hP) hbound t ht

end intervalIntegral

/-- The Grönwall bound is at most the initial bound plus the accumulated source,
multiplied by the exponential growth factor. -/
theorem gronwallBound_le_add_mul_exp (P B κ x : ℝ) (hB : 0 ≤ B) (hκ : 0 ≤ κ) :
    gronwallBound P κ B x ≤ (P + B * x) * Real.exp (κ * x) := by
  by_cases hκ0 : κ = 0
  · subst κ
    simp only [gronwallBound_K0, zero_mul, Real.exp_zero, mul_one]
    exact le_rfl
  rw [gronwallBound_of_K_ne_0 hκ0]
  have hmain : Real.exp (κ * x) - 1 ≤ (κ * x) * Real.exp (κ * x) := by
    have h := Real.add_one_le_exp (-(κ * x))
    have hmul : (-(κ * x) + 1) * Real.exp (κ * x) ≤ 1 := by
      calc
        _ ≤ Real.exp (-(κ * x)) * Real.exp (κ * x) :=
          mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith
  calc
    P * Real.exp (κ * x) + B / κ * (Real.exp (κ * x) - 1)
        ≤ P * Real.exp (κ * x) + B / κ * ((κ * x) * Real.exp (κ * x)) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hmain (div_nonneg hB hκ))
    _ = (P + B * x) * Real.exp (κ * x) := by field_simp

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The explicit exponential estimate for a continuous linear Volterra equation. -/
theorem norm_le_add_mul_exp_of_linear_volterra
    {a b : ℝ} (hab : a ≤ b) (z h : ℝ → E) (A : ℝ → E →L[ℝ] E)
    (d : E) (P B κ : ℝ)
    (hz : ContinuousOn z (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hP : ‖d‖ ≤ P) (hB0 : 0 ≤ B) (hκ0 : 0 ≤ κ)
    (hB : ∀ s ∈ Icc a b, ‖h s‖ ≤ B)
    (hκ : ∀ s ∈ Icc a b, ‖A s‖ ≤ κ)
    (heq : ∀ t ∈ Icc a b, z t = d + ∫ s in a..t, A s (z s) + h s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖z t‖ ≤ (P + B * (t - a)) * Real.exp (κ * (t - a)) :=
  (norm_le_gronwallBound_of_linear_volterra hab z h A d P B κ hz hh hA
    hP hB hκ heq ht).trans
    (gronwallBound_le_add_mul_exp P B κ (t - a) hB0 hκ0)

end intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The right-hand side of the first Goursat equation is a continuous field on the
closed rectangle when the solution remains in the domain of continuity. -/
theorem continuousOn_first_characteristic_field
    (u₀ u₁ v₀ v₁ : ℝ) (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ) :
    ContinuousOn (fun p => fX p (X p, Y p)) (rectangle u₀ u₁ v₀ v₁) := by
  apply hfX.comp ((continuous_id.prodMk (hX.prodMk hY)).continuousOn)
  intro p hp
  exact ⟨hp, hball p hp⟩

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The first characteristic derivative exists relative to the horizontal closed interval
at every rectangle point, including all edges and corners. -/
theorem hasDerivWithinAt_first_of_integral_equation_on_ball
    (u₀ u₁ v₀ v₁ : ℝ)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (x₀ : ℝ → E)
    (fX : ℝ × ℝ → E × F → E) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)))
    {u v : ℝ} (huI : u ∈ Icc u₀ u₁) (hvI : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt (fun s => X (s, v))
      (fX (u, v) (X (u, v), Y (u, v))) (Icc u₀ u₁) u := by
  have hfield := continuousOn_first_characteristic_field
    u₀ u₁ v₀ v₁ X Y fX hX hY c ρ hfX hball
  have hslice : ContinuousOn
      (fun s => fX (s, v) (X (s, v), Y (s, v))) (Icc u₀ u₁) :=
    hfield.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => by
        simpa only [rectangle] using
          (show (s, v) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨hs, hvI⟩))
  exact intervalIntegral.hasDerivWithinAt_of_eq_integral_on_Icc
    (fun s => X (s, v))
    (fun s => fX (s, v) (X (s, v), Y (s, v))) (x₀ v) hslice
    (fun s hs => heq (s, v) (by
      simpa only [rectangle] using
        (show (s, v) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨hs, hvI⟩))) huI

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The right-hand side of the second Goursat equation is continuous on the rectangle
when the solution remains in its domain of continuity. -/
theorem continuousOn_second_characteristic_field
    (u₀ u₁ v₀ v₁ : ℝ) (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (fY : ℝ × ℝ → E × F → F) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ) :
    ContinuousOn (fun p => fY p (X p, Y p)) (rectangle u₀ u₁ v₀ v₁) := by
  apply hfY.comp ((continuous_id.prodMk (hX.prodMk hY)).continuousOn)
  intro p hp
  exact ⟨hp, hball p hp⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The second characteristic derivative exists relative to the vertical closed interval
at every rectangle point, including all edges and corners. -/
theorem hasDerivWithinAt_second_of_integral_equation_on_ball
    (u₀ u₁ v₀ v₁ : ℝ)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (y₀ : ℝ → F)
    (fY : ℝ × ℝ → E × F → F) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    {u v : ℝ} (huI : u ∈ Icc u₀ u₁) (hvI : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt (fun t => Y (u, t))
      (fY (u, v) (X (u, v), Y (u, v))) (Icc v₀ v₁) v := by
  have hfield := continuousOn_second_characteristic_field
    u₀ u₁ v₀ v₁ X Y fY hX hY c ρ hfY hball
  have hslice : ContinuousOn
      (fun t => fY (u, t) (X (u, t), Y (u, t))) (Icc v₀ v₁) :=
    hfield.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => by
        simpa only [rectangle] using
          (show (u, t) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨huI, ht⟩))
  exact intervalIntegral.hasDerivWithinAt_of_eq_integral_on_Icc
    (fun t => Y (u, t))
    (fun t => fY (u, t) (X (u, t), Y (u, t))) (y₀ u) hslice
    (fun t ht => heq (u, t) (by
      simpa only [rectangle] using
        (show (u, t) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨huI, ht⟩))) hvI

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The actual horizontal relative derivative of the first unknown is continuous on a
nondegenerate closed rectangle. -/
theorem continuousOn_derivWithin_first_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ < u₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (x₀ : ℝ → E)
    (fX : ℝ × ℝ → E × F → E) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2))) :
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin (fun s => X (s, p.2)) (Icc u₀ u₁) p.1)
      (rectangle u₀ u₁ v₀ v₁) := by
  apply (continuousOn_first_characteristic_field
    u₀ u₁ v₀ v₁ X Y fX hX hY c ρ hfX hball).congr
  intro p hp
  exact (hasDerivWithinAt_first_of_integral_equation_on_ball
    u₀ u₁ v₀ v₁ X Y x₀ fX hX hY c ρ hfX hball heq hp.1 hp.2).derivWithin
      ((uniqueDiffOn_Icc hu) p.1 hp.1)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The actual vertical relative derivative of the second unknown is continuous on a
nondegenerate closed rectangle. -/
theorem continuousOn_derivWithin_second_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hv : v₀ < v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (y₀ : ℝ → F)
    (fY : ℝ × ℝ → E × F → F) (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t))) :
    ContinuousOn
      (fun p : ℝ × ℝ => derivWithin (fun t => Y (p.1, t)) (Icc v₀ v₁) p.2)
      (rectangle u₀ u₁ v₀ v₁) := by
  apply (continuousOn_second_characteristic_field
    u₀ u₁ v₀ v₁ X Y fY hX hY c ρ hfY hball).congr
  intro p hp
  exact (hasDerivWithinAt_second_of_integral_equation_on_ball
    u₀ u₁ v₀ v₁ X Y y₀ fY hX hY c ρ hfY hball heq hp.1 hp.2).derivWithin
      ((uniqueDiffOn_Icc hv) p.2 hp.2)

omit [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The first unknown equals its prescribed datum on the left edge. -/
theorem first_eq_datum_on_left_edge
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (x₀ : ℝ → E)
    (fX : ℝ × ℝ → E × F → E)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)))
    {v : ℝ} (hv : v ∈ Icc v₀ v₁) : X (u₀, v) = x₀ v := by
  have hp : (u₀, v) ∈ rectangle u₀ u₁ v₀ v₁ := by
    simpa only [rectangle] using
      (show (u₀, v) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨⟨le_rfl, hu⟩, hv⟩)
  simpa only [integral_same, add_zero] using heq (u₀, v) hp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [CompleteSpace F] in
/-- The second unknown equals its prescribed datum on the bottom edge. -/
theorem second_eq_datum_on_bottom_edge
    (u₀ u₁ v₀ v₁ : ℝ) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (y₀ : ℝ → F)
    (fY : ℝ × ℝ → E × F → F)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    {u : ℝ} (hu : u ∈ Icc u₀ u₁) : Y (u, v₀) = y₀ u := by
  have hp : (u, v₀) ∈ rectangle u₀ u₁ v₀ v₁ := by
    simpa only [rectangle] using
      (show (u, v₀) ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁ from ⟨hu, ⟨le_rfl, hv⟩⟩)
  simpa only [integral_same, add_zero] using heq (u, v₀) hp

omit [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- On the left edge, the relative transverse derivative of the first unknown is the
relative derivative of its prescribed datum; this includes both left corners. -/
theorem hasDerivWithinAt_first_on_left_edge
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (x₀ : ℝ → E)
    (fX : ℝ × ℝ → E × F → E)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)))
    {v : ℝ} (hv : v ∈ Icc v₀ v₁) {dx : E}
    (hdatum : HasDerivWithinAt x₀ dx (Icc v₀ v₁) v) :
    HasDerivWithinAt (fun t => X (u₀, t)) dx (Icc v₀ v₁) v := by
  exact hdatum.congr
    (fun t ht => first_eq_datum_on_left_edge
      u₀ u₁ v₀ v₁ hu X Y x₀ fX heq ht)
    (first_eq_datum_on_left_edge u₀ u₁ v₀ v₁ hu X Y x₀ fX heq hv)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [CompleteSpace F] in
/-- On the bottom edge, the relative transverse derivative of the second unknown is the
relative derivative of its prescribed datum; this includes both bottom corners. -/
theorem hasDerivWithinAt_second_on_bottom_edge
    (u₀ u₁ v₀ v₁ : ℝ) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F) (y₀ : ℝ → F)
    (fY : ℝ × ℝ → E × F → F)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    {u : ℝ} (hu : u ∈ Icc u₀ u₁) {dy : F}
    (hdatum : HasDerivWithinAt y₀ dy (Icc u₀ u₁) u) :
    HasDerivWithinAt (fun s => Y (s, v₀)) dy (Icc u₀ u₁) u := by
  exact hdatum.congr
    (fun s hs => second_eq_datum_on_bottom_edge
      u₀ u₁ v₀ v₁ hv X Y y₀ fY heq hs)
    (second_eq_datum_on_bottom_edge u₀ u₁ v₀ v₁ hv X Y y₀ fY heq hu)

end Goursat

end
