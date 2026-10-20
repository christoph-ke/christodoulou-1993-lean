module

public import Mathlib
public import ChristodoulouBV.ForMathlib.ODE.Goursat
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Goursat equations on arbitrary rectangles

An exponential change of scale makes the characteristic Picard operator a
contraction on a rectangle of any finite size.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The integral of an exponential of an affine function. -/
theorem integral_exp_mul_add (K a b c : ℝ) (hK : 0 < K) :
    (∫ s in a..b, Real.exp (K * (s + c))) =
      (Real.exp (K * (b + c)) - Real.exp (K * (a + c))) / K := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => Real.exp (K * (t + c)) / K)
        (Real.exp (K * (x + c))) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => K * (t + c)) K x := by
      convert ((hasDerivAt_id x).const_add c).const_mul K using 1
      · funext t
        simp only [id_eq]
        ring
      · ring
    convert ((Real.hasDerivAt_exp (K * (x + c))).comp x hlin).div_const K using 1
    · ext t; rfl
    · field_simp
  have h := intervalIntegral.integral_deriv_eq_sub'
    (fun t : ℝ => Real.exp (K * (t + c)) / K)
    (funext fun x => (hderiv x).deriv)
    (fun x _ => (hderiv x).differentiableAt)
    (by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (K * (t + c))) (uIcc a b))
  convert h using 1; ring

/-- An exponential bound for the difference of two ordered interval integrals. -/
theorem norm_integral_sub_le_exp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b c K C : ℝ} (hab : a ≤ b) (hK : 0 < K) (hC : 0 ≤ C)
    (f g : ℝ → G) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hfg : ∀ s ∈ Icc a b, ‖f s - g s‖ ≤ C * Real.exp (K * (s + c))) :
    ‖(∫ s in a..b, f s) - ∫ s in a..b, g s‖ ≤
      C / K * Real.exp (K * (b + c)) := by
  rw [← intervalIntegral.integral_sub hf hg]
  have hbound : ∀ᵐ s : ℝ, s ∈ Ioc a b →
      ‖f s - g s‖ ≤ C * Real.exp (K * (s + c)) :=
    Filter.Eventually.of_forall (fun s hs => hfg s ⟨hs.1.le, hs.2⟩)
  have hint : IntervalIntegrable (fun s : ℝ => C * Real.exp (K * (s + c)))
      MeasureTheory.volume a b := (by fun_prop : Continuous
        (fun s : ℝ => C * Real.exp (K * (s + c)))).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le hab hbound hint
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_add K a b c hK] at h
  calc
    _ ≤ C * ((Real.exp (K * (b + c)) - Real.exp (K * (a + c))) / K) := h
    _ ≤ C / K * Real.exp (K * (b + c)) := by
      have : 0 ≤ Real.exp (K * (a + c)) := (Real.exp_pos _).le
      calc
        _ ≤ C * (Real.exp (K * (b + c)) / K) := by
          gcongr
          exact sub_le_self _ this
        _ = _ := by ring

/-- Multiply a continuous rectangle-valued function by an exponential weight. -/
private noncomputable def expScale (u₀ u₁ v₀ v₁ K : ℝ)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    C(rectangle u₀ u₁ v₀ v₁, E × F) :=
  ⟨fun p => Real.exp (K * (p.1.1 + p.1.2)) • w p,
    (by fun_prop : Continuous (fun p : rectangle u₀ u₁ v₀ v₁ =>
      Real.exp (K * (p.1.1 + p.1.2)) • w p))⟩

/-- Exponential scaling is inverted by negating the exponent. -/
private theorem expScale_neg_expScale (u₀ u₁ v₀ v₁ K : ℝ)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    expScale u₀ u₁ v₀ v₁ (-K) (expScale u₀ u₁ v₀ v₁ K w) = w := by
  apply ContinuousMap.ext
  intro p
  change Real.exp (-K * (p.1.1 + p.1.2)) •
    (Real.exp (K * (p.1.1 + p.1.2)) • w p) = w p
  rw [smul_smul, ← Real.exp_add]
  have : -K * (p.1.1 + p.1.2) + K * (p.1.1 + p.1.2) = 0 := by ring
  simp only [this, Real.exp_zero, one_smul]

/-- Scaling by `-K` is the inverse of scaling by `K`. -/
private theorem expScale_expScale_neg (u₀ u₁ v₀ v₁ K : ℝ)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    expScale u₀ u₁ v₀ v₁ K (expScale u₀ u₁ v₀ v₁ (-K) w) = w := by
  simpa only [neg_neg] using expScale_neg_expScale u₀ u₁ v₀ v₁ (-K) w

/-- The characteristic Picard operator conjugated by exponential scaling. -/
private noncomputable def expPicard (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) (K : ℝ)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    C(rectangle u₀ u₁ v₀ v₁, E × F) :=
  expScale u₀ u₁ v₀ v₁ (-K)
    (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
      (expScale u₀ u₁ v₀ v₁ K w))

/-- Scaling converts a sup-distance bound into a pointwise exponential bound. -/
private theorem dist_expScale_apply_le (u₀ u₁ v₀ v₁ K : ℝ)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (p : rectangle u₀ u₁ v₀ v₁) :
    dist (expScale u₀ u₁ v₀ v₁ K w p) (expScale u₀ u₁ v₀ v₁ K z p) ≤
      Real.exp (K * (p.1.1 + p.1.2)) * dist w z := by
  change dist (Real.exp (K * (p.1.1 + p.1.2)) • w p)
    (Real.exp (K * (p.1.1 + p.1.2)) • z p) ≤ _
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist p) (Real.exp_pos _).le

/-- The exponentially conjugated Picard operator is Lipschitz with constant `κ / K`. -/
private theorem dist_expPicard_le (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) (K : ℝ) (hK : 0 < K)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F)) :
    dist (expPicard u₀ u₁ v₀ v₁ hu hv K x₀ y₀ fX fY hx₀ hy₀ hfX hfY w)
      (expPicard u₀ u₁ v₀ v₁ hu hv K x₀ y₀ fX fY hx₀ hy₀ hfX hfY z) ≤
      ((κ : ℝ) / K) * dist w z := by
  let W := expScale u₀ u₁ v₀ v₁ K w
  let Z := expScale u₀ u₁ v₀ v₁ K z
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  have hC : 0 ≤ (κ : ℝ) * dist w z :=
    mul_nonneg κ.coe_nonneg dist_nonneg
  have hpoint (p : rectangle u₀ u₁ v₀ v₁) :
      dist (expScale u₀ u₁ v₀ v₁ (-K) (T W) p)
        (expScale u₀ u₁ v₀ v₁ (-K) (T Z) p) ≤
        ((κ : ℝ) / K) * dist w z := by
    have hp : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2
    have hpX : ‖(T W p).1 - (T Z p).1‖ ≤
        ((κ : ℝ) * dist w z) / K * Real.exp (K * (p.1.1 + p.1.2)) := by
      have hfw : Continuous (fun s : ℝ => fX (s, p.1.2)
          (W (clippedPoint hu hv (s, p.1.2)))) :=
        continuous_comp_clippedPoint hu hv fX hfX W
          (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
      have hfz : Continuous (fun s : ℝ => fX (s, p.1.2)
          (Z (clippedPoint hu hv (s, p.1.2)))) :=
        continuous_comp_clippedPoint hu hv fX hfX Z
          (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
      have hfg : ∀ s ∈ Icc u₀ p.1.1,
          ‖fX (s, p.1.2) (W (clippedPoint hu hv (s, p.1.2))) -
            fX (s, p.1.2) (Z (clippedPoint hu hv (s, p.1.2)))‖ ≤
            ((κ : ℝ) * dist w z) * Real.exp (K * (s + p.1.2)) := by
        intro s hs
        rw [← dist_eq_norm]
        have h := (hLX (s, p.1.2) _ _).trans (mul_le_mul_of_nonneg_left
          (dist_expScale_apply_le u₀ u₁ v₀ v₁ K w z
            (clippedPoint hu hv (s, p.1.2))) κ.coe_nonneg)
        have hsI : s ∈ Icc u₀ u₁ := ⟨hs.1, hs.2.trans hp.1.2⟩
        simpa only [W, Z, clippedPoint, clip_eq_self hsI,
          clip_eq_self hp.2, mul_comm (Real.exp (K * (s + p.1.2))) (dist w z),
          ← mul_assoc] using h
      have h := norm_integral_sub_le_exp hp.1.1 hK hC _ _
        (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _) hfg
      simpa only [T, picard_apply, add_sub_add_left_eq_sub] using h
    have hpY : ‖(T W p).2 - (T Z p).2‖ ≤
        ((κ : ℝ) * dist w z) / K * Real.exp (K * (p.1.1 + p.1.2)) := by
      have hfw : Continuous (fun t : ℝ => fY (p.1.1, t)
          (W (clippedPoint hu hv (p.1.1, t)))) :=
        continuous_comp_clippedPoint hu hv fY hfY W
          (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
      have hfz : Continuous (fun t : ℝ => fY (p.1.1, t)
          (Z (clippedPoint hu hv (p.1.1, t)))) :=
        continuous_comp_clippedPoint hu hv fY hfY Z
          (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
      have hfg : ∀ t ∈ Icc v₀ p.1.2,
          ‖fY (p.1.1, t) (W (clippedPoint hu hv (p.1.1, t))) -
            fY (p.1.1, t) (Z (clippedPoint hu hv (p.1.1, t)))‖ ≤
            ((κ : ℝ) * dist w z) * Real.exp (K * (t + p.1.1)) := by
        intro t ht
        rw [← dist_eq_norm]
        have h := (hLY (p.1.1, t) _ _).trans (mul_le_mul_of_nonneg_left
          (dist_expScale_apply_le u₀ u₁ v₀ v₁ K w z
            (clippedPoint hu hv (p.1.1, t))) κ.coe_nonneg)
        have htI : t ∈ Icc v₀ v₁ := ⟨ht.1, ht.2.trans hp.2.2⟩
        simpa only [W, Z, clippedPoint, clip_eq_self hp.1, clip_eq_self htI,
          add_comm t p.1.1, mul_comm (Real.exp (K * (p.1.1 + t))) (dist w z),
          ← mul_assoc] using h
      have h := norm_integral_sub_le_exp hp.2.1 hK hC _ _
        (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _) hfg
      simpa only [T, picard_apply, add_sub_add_left_eq_sub, add_comm p.1.2 p.1.1] using h
    change dist (Real.exp (-K * (p.1.1 + p.1.2)) • T W p)
      (Real.exp (-K * (p.1.1 + p.1.2)) • T Z p) ≤ _
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← dist_eq_norm, Prod.dist_eq]
    have hmax : max (dist (T W p).1 (T Z p).1)
        (dist (T W p).2 (T Z p).2) ≤
        ((κ : ℝ) * dist w z) / K * Real.exp (K * (p.1.1 + p.1.2)) := by
      apply max_le
      · simpa only [dist_eq_norm] using hpX
      · simpa only [dist_eq_norm] using hpY
    calc
      _ ≤ Real.exp (-K * (p.1.1 + p.1.2)) *
          (((κ : ℝ) * dist w z) / K * Real.exp (K * (p.1.1 + p.1.2))) :=
        mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
      _ = ((κ : ℝ) / K) * dist w z := by
        rw [mul_comm (Real.exp (-K * _)) _, mul_assoc, ← Real.exp_add]
        have : K * (p.1.1 + p.1.2) + -K * (p.1.1 + p.1.2) = 0 := by ring
        simp only [this, Real.exp_zero, mul_one]
        ring
  apply (ContinuousMap.dist_le (mul_nonneg (div_nonneg κ.coe_nonneg hK.le) dist_nonneg)).2
  intro p
  exact hpoint p

/-- Any exponent larger than the Lipschitz constant gives a contraction. -/
private theorem contractingWith_expPicard (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) (K : ℝ) (hK : 0 < K)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hκK : (κ : ℝ) < K) :
    ContractingWith (⟨(κ : ℝ) / K, div_nonneg κ.coe_nonneg hK.le⟩ : NNReal)
      (expPicard u₀ u₁ v₀ v₁ hu hv K x₀ y₀ fX fY hx₀ hy₀ hfX hfY) := by
  constructor
  · exact (div_lt_one hK).2 hκK
  · apply LipschitzWith.of_dist_le_mul
    intro w z
    exact dist_expPicard_le u₀ u₁ v₀ v₁ hu hv K hK x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY κ hLX hLY w z

/-- A continuous solution of the Goursat integral equations exists on every finite rectangle. -/
theorem exists_continuous_solution_global [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b) :
    ∃ w : C(rectangle u₀ u₁ v₀ v₁, E × F),
      ∀ p : rectangle u₀ u₁ v₀ v₁,
        w p =
          (x₀ p.1.2 + ∫ s in u₀..p.1.1,
              fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))),
           y₀ p.1.1 + ∫ t in v₀..p.1.2,
              fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) := by
  let K : ℝ := (κ : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hκK : (κ : ℝ) < K := by dsimp [K]; linarith
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  let S := expPicard u₀ u₁ v₀ v₁ hu hv K x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  have hS := contractingWith_expPicard u₀ u₁ v₀ v₁ hu hv K hK
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY κ hLX hLY hκK
  obtain ⟨z, hz, _, _⟩ := hS.exists_fixedPoint (ContinuousMap.const _ (0, 0)) (by simp)
  let w := expScale u₀ u₁ v₀ v₁ K z
  have hw : Function.IsFixedPt T w := by
    have h := congrArg (expScale u₀ u₁ v₀ v₁ K) hz
    change expScale u₀ u₁ v₀ v₁ K
      (expScale u₀ u₁ v₀ v₁ (-K) (T w)) = w at h
    rwa [expScale_expScale_neg] at h
  refine ⟨w, fun p => ?_⟩
  calc
    w p = T w p := congrArg (fun q : C(rectangle u₀ u₁ v₀ v₁, E × F) => q p) hw.symm
    _ = _ := picard_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w p

/-- Two continuous fixed points of the Goursat Picard operator agree on any rectangle. -/
theorem fixedPoint_unique_picard_global (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w)
    (hz : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) z) :
    w = z := by
  let K : ℝ := (κ : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hκK : (κ : ℝ) < K := by dsimp [K]; linarith
  let S := expPicard u₀ u₁ v₀ v₁ hu hv K x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  have hS := contractingWith_expPicard u₀ u₁ v₀ v₁ hu hv K hK
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY κ hLX hLY hκK
  have hwS : Function.IsFixedPt S (expScale u₀ u₁ v₀ v₁ (-K) w) := by
    change expScale u₀ u₁ v₀ v₁ (-K)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
        (expScale u₀ u₁ v₀ v₁ K (expScale u₀ u₁ v₀ v₁ (-K) w))) = _
    rw [expScale_expScale_neg]
    exact congrArg (expScale u₀ u₁ v₀ v₁ (-K)) hw
  have hzS : Function.IsFixedPt S (expScale u₀ u₁ v₀ v₁ (-K) z) := by
    change expScale u₀ u₁ v₀ v₁ (-K)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
        (expScale u₀ u₁ v₀ v₁ K (expScale u₀ u₁ v₀ v₁ (-K) z))) = _
    rw [expScale_expScale_neg]
    exact congrArg (expScale u₀ u₁ v₀ v₁ (-K)) hz
  have h := hS.fixedPoint_unique' hwS hzS
  have h' := congrArg (expScale u₀ u₁ v₀ v₁ K) h
  simpa only [expScale_expScale_neg] using h'

/-- Global existence in the ordinary two-component integral formulation. -/
theorem exists_continuous_solution_on_rectangle_global [CompleteSpace E] [CompleteSpace F]
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
      Continuous X ∧ Continuous Y ∧
      ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)) := by
  obtain ⟨w, hw⟩ := exists_continuous_solution_global u₀ u₁ v₀ v₁ hu hv
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY κ hLX hLY
  let X : ℝ × ℝ → E := fun p => (w (clippedPoint hu hv p)).1
  let Y : ℝ × ℝ → F := fun p => (w (clippedPoint hu hv p)).2
  refine ⟨X, Y, (w.continuous.comp (continuous_clippedPoint hu hv)).fst,
    (w.continuous.comp (continuous_clippedPoint hu hv)).snd, ?_⟩
  intro p hp
  let q : rectangle u₀ u₁ v₀ v₁ := ⟨p, hp⟩
  have hq : clippedPoint hu hv p = q := clippedPoint_eq_self hu hv q
  have h := hw q
  dsimp [X, Y] at ⊢
  rw [hq]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Continuous solutions of the Goursat integral equations agree on any rectangle. -/
theorem eq_on_rectangle_of_integral_equations_global
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X X' : ℝ × ℝ → E) (Y Y' : ℝ × ℝ → F)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hX : ContinuousOn X (rectangle u₀ u₁ v₀ v₁))
    (hY : ContinuousOn Y (rectangle u₀ u₁ v₀ v₁))
    (hX' : ContinuousOn X' (rectangle u₀ u₁ v₀ v₁))
    (hY' : ContinuousOn Y' (rectangle u₀ u₁ v₀ v₁))
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (heq' : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X' p = x₀ p.2 + ∫ s in u₀..p.1, fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
      Y' p = y₀ p.1 + ∫ t in v₀..p.2, fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) :
    ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p := by
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX).prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY)⟩
  let z : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X' p.1, Y' p.1),
      (continuousOn_iff_continuous_domRestrict.mp hX').prodMk
        (continuousOn_iff_continuous_domRestrict.mp hY')⟩
  have hw := isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv
    X Y x₀ y₀ fX fY hX hY hx₀ hy₀ hfX hfY heq
  have hz := isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv
    X' Y' x₀ y₀ fX fY hX' hY' hx₀ hy₀ hfX hfY heq'
  have h : w = z := fixedPoint_unique_picard_global u₀ u₁ v₀ v₁ hu hv
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY κ hLX hLY w z hw hz
  intro p hp
  exact Prod.mk.inj (congrArg (fun q : C(rectangle u₀ u₁ v₀ v₁, E × F) => q ⟨p, hp⟩) h)

/-- Continuous dependence on the two edge functions on an arbitrary rectangle. -/
theorem dist_solutions_le_global (u₀ u₁ v₀ v₁ : ℝ)
    (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁) (K : ℝ) (hK : 0 < K)
    (x₀ x₀' : ℝ → E) (y₀ y₀' : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hx₀' : Continuous x₀') (hy₀' : Continuous y₀')
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (κ : NNReal)
    (hLX : ∀ q a b, dist (fX q a) (fX q b) ≤ (κ : ℝ) * dist a b)
    (hLY : ∀ q a b, dist (fY q a) (fY q b) ≤ (κ : ℝ) * dist a b)
    (hκK : (κ : ℝ) < K)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdataX : ∀ v ∈ Icc v₀ v₁, dist (x₀ v) (x₀' v) ≤ A)
    (hdataY : ∀ u ∈ Icc u₀ u₁, dist (y₀ u) (y₀' u) ≤ B)
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w)
    (hz : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀' y₀' fX fY hx₀' hy₀' hfX hfY) z) :
    dist w z ≤ Real.exp (K * (u₁ + v₁)) *
      (Real.exp (-K * (u₀ + v₀)) * max A B / (1 - (κ : ℝ) / K)) := by
  let S := expPicard u₀ u₁ v₀ v₁ hu hv K x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  let S' := expPicard u₀ u₁ v₀ v₁ hu hv K x₀' y₀' fX fY hx₀' hy₀' hfX hfY
  let W := expScale u₀ u₁ v₀ v₁ (-K) w
  let Z := expScale u₀ u₁ v₀ v₁ (-K) z
  have hW : Function.IsFixedPt S W := by
    change expScale u₀ u₁ v₀ v₁ (-K)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
        (expScale u₀ u₁ v₀ v₁ K W)) = W
    rw [expScale_expScale_neg]
    exact congrArg (expScale u₀ u₁ v₀ v₁ (-K)) hw
  have hZ : Function.IsFixedPt S' Z := by
    change expScale u₀ u₁ v₀ v₁ (-K)
      (picard u₀ u₁ v₀ v₁ hu hv x₀' y₀' fX fY hx₀' hy₀' hfX hfY
        (expScale u₀ u₁ v₀ v₁ K Z)) = Z
    rw [expScale_expScale_neg]
    exact congrArg (expScale u₀ u₁ v₀ v₁ (-K)) hz
  have hS := contractingWith_expPicard u₀ u₁ v₀ v₁ hu hv K hK
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY κ hLX hLY hκK
  have hq : (κ : ℝ) / K < 1 := (div_lt_one hK).2 hκK
  have hden : 0 < 1 - (κ : ℝ) / K := sub_pos.mpr hq
  have hM : 0 ≤ max A B := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]
      exact hB
    · rw [max_eq_left h]
      exact hA
  have hD : 0 ≤ Real.exp (-K * (u₀ + v₀)) * max A B :=
    mul_nonneg (Real.exp_pos _).le hM
  have hSdist : dist W Z ≤
      Real.exp (-K * (u₀ + v₀)) * max A B / (1 - (κ : ℝ) / K) := by
    apply hS.dist_fixedPoint_fixedPoint_of_dist_le' S' hW hZ
    intro q
    apply (ContinuousMap.dist_le hD).2
    intro p
    have hp : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2
    have hsum₀ : u₀ + v₀ ≤ p.1.1 + p.1.2 := add_le_add hp.1.1 hp.2.1
    have hExp : Real.exp (-K * (p.1.1 + p.1.2)) ≤
        Real.exp (-K * (u₀ + v₀)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hsum₀)]
    have hdata : dist (x₀ p.1.2, y₀ p.1.1) (x₀' p.1.2, y₀' p.1.1) ≤
        max A B := by
      rw [Prod.dist_eq]
      exact max_le (le_trans (hdataX _ hp.2) (le_max_left _ _))
        (le_trans (hdataY _ hp.1) (le_max_right _ _))
    have hpoint : dist (S q p) (S' q p) =
        Real.exp (-K * (p.1.1 + p.1.2)) *
          dist (x₀ p.1.2, y₀ p.1.1) (x₀' p.1.2, y₀' p.1.1) := by
      change dist (Real.exp (-K * (p.1.1 + p.1.2)) •
          (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
            (expScale u₀ u₁ v₀ v₁ K q) p))
        (Real.exp (-K * (p.1.1 + p.1.2)) •
          (picard u₀ u₁ v₀ v₁ hu hv x₀' y₀' fX fY hx₀' hy₀' hfX hfY
            (expScale u₀ u₁ v₀ v₁ K q) p)) = _
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), ← dist_eq_norm,
        picard_apply, picard_apply]
      congr 1
      rw [Prod.dist_eq, Prod.dist_eq]
      simp only [dist_eq_norm, add_sub_add_right_eq_sub]
    rw [hpoint]
    exact (mul_le_mul_of_nonneg_left hdata (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right hExp hM)
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le
    (div_nonneg hD hden.le))).2
  intro p
  have hp : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
    simpa only [rectangle, mem_prod] using p.2
  have hsum₁ : p.1.1 + p.1.2 ≤ u₁ + v₁ := add_le_add hp.1.2 hp.2.2
  have hExp : Real.exp (K * (p.1.1 + p.1.2)) ≤ Real.exp (K * (u₁ + v₁)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hsum₁)]
  calc
    dist (w p) (z p) =
        dist (expScale u₀ u₁ v₀ v₁ K W p) (expScale u₀ u₁ v₀ v₁ K Z p) := by
      simp only [W, Z, expScale_expScale_neg]
    _ ≤ Real.exp (K * (p.1.1 + p.1.2)) * dist W Z :=
      dist_expScale_apply_le u₀ u₁ v₀ v₁ K W Z p
    _ ≤ Real.exp (K * (u₁ + v₁)) *
        (Real.exp (-K * (u₀ + v₀)) * max A B / (1 - (κ : ℝ) / K)) := by
      exact (mul_le_mul_of_nonneg_left hSdist (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right hExp (div_nonneg hD hden.le))

end Goursat

end
