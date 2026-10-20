module

public import Mathlib.Topology.MetricSpace.Contracting
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Regular
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Picard iterates on a closed Goursat rectangle

The initial mixed trace and every Picard iterate remain in the state ball under the
full-trace margin. A contraction on that ball then gives uniform convergence to any
fixed point in the ball. The statements use globally continuous nonlinearities; a
later local extension can supply these from data on a neighborhood of the ball.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Metric

/-- Iterates of a map contracting on an invariant set converge to a fixed point in
that set, without assuming that the ambient space or the invariant set is complete. -/
theorem tendsto_iterate_of_contractingOn {α : Type*} [PseudoMetricSpace α]
    (T : α → α) (S : Set α) (x w : α) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : x ∈ S) (hw : w ∈ S) (hT : MapsTo T S S)
    (hcontract : ∀ y ∈ S, ∀ z ∈ S, dist (T y) (T z) ≤ q * dist y z)
    (hfixed : T w = w) :
    Tendsto (fun n : ℕ => T^[n] x) atTop (𝓝 w) := by
  have hmem : ∀ n : ℕ, T^[n] x ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hT ih
  apply Metric.tendsto_of_dist_succ_le_error_add_contracting hq0 hq1
    (e := fun _ => (0 : ℝ)) tendsto_const_nhds
  intro n
  simpa only [Function.iterate_succ_apply', hfixed, zero_add] using
    hcontract (T^[n] x) (hmem n) w hw

end Metric

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The mixed characteristic trace as a continuous map on the rectangle. -/
@[expose] noncomputable def picardBase (u₀ u₁ v₀ v₁ : ℝ)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀) :
    C(rectangle u₀ u₁ v₀ v₁, E × F) :=
  ⟨fun p => (x₀ p.1.2, y₀ p.1.1),
    ((hx₀.comp continuous_snd).prodMk (hy₀.comp continuous_fst)).comp
      continuous_subtype_val⟩

/-- Iterates of the characteristic Picard operator, starting from the full mixed
trace `(x₀(v), y₀(u))`. -/
@[expose] noncomputable def picardIterate
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (n : ℕ) : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
  (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY)^[n]
    (picardBase u₀ u₁ v₀ v₁ x₀ y₀ hx₀ hy₀)

/-- The zeroth Picard iterate is the mixed edge trace. -/
theorem picardIterate_zero
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry) :
    picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY 0 =
      picardBase u₀ u₁ v₀ v₁ x₀ y₀ hx₀ hy₀ := by
  simp [picardIterate]

/-- The zeroth iterate evaluates to the full mixed characteristic trace. -/
theorem picardIterate_zero_apply
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (p : rectangle u₀ u₁ v₀ v₁) :
    picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY 0 p = (x₀ p.1.2, y₀ p.1.1) := by
  rw [picardIterate_zero]
  rfl

/-- Each next Picard iterate is the Picard image of the preceding iterate. -/
theorem picardIterate_succ
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (n : ℕ) :
    picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY (n + 1) =
      picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
        (picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY n) := by
  simp [picardIterate, Function.iterate_succ_apply']

/-- The next iterate satisfies the two characteristic integral formulas with
the preceding iterate in the integrands. -/
theorem picardIterate_succ_apply
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (n : ℕ) (p : rectangle u₀ u₁ v₀ v₁) :
    picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY (n + 1) p =
      (x₀ p.1.2 + ∫ s in u₀..p.1.1,
        fX (s, p.1.2) (picardIterate u₀ u₁ v₀ v₁ hu hv
          x₀ y₀ fX fY hx₀ hy₀ hfX hfY n
            (clippedPoint hu hv (s, p.1.2))),
       y₀ p.1.1 + ∫ t in v₀..p.1.2,
        fY (p.1.1, t) (picardIterate u₀ u₁ v₀ v₁ hu hv
          x₀ y₀ fX fY hx₀ hy₀ hfX hfY n
            (clippedPoint hu hv (p.1.1, t)))) := by
  rw [picardIterate_succ]
  exact picard_apply u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY _ p

/-- The full-trace margin keeps the Picard image of every ball-valued continuous
map in the same state ball. -/
theorem picard_mem_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ r M : ℝ) (hM : 0 ≤ M)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : ∀ p, dist (w p) c ≤ ρ) (p : rectangle u₀ u₁ v₀ v₁) :
    dist (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w p) c ≤ ρ := by
  have hIX : ‖∫ s in u₀..p.1.1,
      fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))‖ ≤
      M * (p.1.1 - u₀) := by
    have hb : ∀ s ∈ Set.uIoc u₀ p.1.1,
        ‖fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))‖ ≤ M := by
      intro s hs
      have hsI : s ∈ Icc u₀ u₁ :=
        Set.uIcc_subset_Icc ⟨le_rfl, hu⟩ p.2.1 (Set.uIoc_subset_uIcc hs)
      exact hMX (s, p.1.2) (pair_mem_rectangle hsI p.2.2) _ (hw _)
    simpa [abs_of_nonneg (sub_nonneg.mpr p.2.1.1)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := u₀) (b := p.1.1) (C := M)
        (f := fun s => fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))) hb)
  have hIY : ‖∫ t in v₀..p.1.2,
      fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))‖ ≤
      M * (p.1.2 - v₀) := by
    have hb : ∀ t ∈ Set.uIoc v₀ p.1.2,
        ‖fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))‖ ≤ M := by
      intro t ht
      have htI : t ∈ Icc v₀ v₁ :=
        Set.uIcc_subset_Icc ⟨le_rfl, hv⟩ p.2.2 (Set.uIoc_subset_uIcc ht)
      exact hMY (p.1.1, t) (pair_mem_rectangle p.2.1 htI) _ (hw _)
    simpa [abs_of_nonneg (sub_nonneg.mpr p.2.2.1)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := v₀) (b := p.1.2) (C := M)
        (f := fun t => fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) hb)
  have hX : dist
      (x₀ p.1.2 + ∫ s in u₀..p.1.1,
        fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))))
      (x₀ p.1.2) ≤ M * max (u₁ - u₀) (v₁ - v₀) := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hIX.trans (mul_le_mul_of_nonneg_left
      (le_max_of_le_left (sub_le_sub_right p.2.1.2 _)) hM)
  have hY : dist
      (y₀ p.1.1 + ∫ t in v₀..p.1.2,
        fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t))))
      (y₀ p.1.1) ≤ M * max (u₁ - u₀) (v₁ - v₀) := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hIY.trans (mul_le_mul_of_nonneg_left
      (le_max_of_le_right (sub_le_sub_right p.2.2.2 _)) hM)
  rw [picard_apply]
  calc
    dist _ c ≤ dist _ (x₀ p.1.2, y₀ p.1.1) +
      dist (x₀ p.1.2, y₀ p.1.1) c := dist_triangle _ _ _
    _ ≤ M * max (u₁ - u₀) (v₁ - v₀) + r := by
      rw [Prod.dist_eq]
      exact add_le_add (max_le hX hY) (hdata p.1 p.2)
    _ = r + M * max (u₁ - u₀) (v₁ - v₀) := add_comm _ _
    _ ≤ ρ := hsize

/-- Every Picard iterate stays in the state ball under the full mixed-trace
margin, including the zeroth iterate. -/
theorem picardIterate_mem_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ r M : ℝ) (hM : 0 ≤ M)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (n : ℕ) (p : rectangle u₀ u₁ v₀ v₁) :
    dist (picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY n p) c ≤ ρ := by
  have hr : r ≤ ρ := by
    have hnonneg : 0 ≤ M * max (u₁ - u₀) (v₁ - v₀) :=
      mul_nonneg hM (le_max_of_le_left (sub_nonneg.mpr hu))
    linarith only [hsize, hnonneg]
  induction n generalizing p with
  | zero =>
      rw [picardIterate_zero]
      exact (hdata p.1 p.2).trans hr
  | succ n ih =>
      rw [picardIterate_succ]
      exact picard_mem_ball u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀
        hfX hfY c ρ r M hM hdata hMX hMY hsize _ ih p

/-- On ball-valued continuous maps, the Picard operator is Lipschitz with the
characteristic length times the state Lipschitz constant. -/
theorem dist_picard_le_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ : ℝ) (κ : NNReal)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z')
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z')
    (w z : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hw : ∀ p, dist (w p) c ≤ ρ) (hz : ∀ p, dist (z p) c ≤ ρ) :
    dist (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY w)
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY z) ≤
      ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * dist w z := by
  apply (ContinuousMap.dist_le (mul_nonneg
    (mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu))) dist_nonneg)).2
  intro p
  rw [Prod.dist_eq]
  apply max_le
  · have hfw : Continuous (fun s : ℝ =>
        fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2)))) :=
      continuous_comp_clippedPoint hu hv fX hfX w
        (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
    have hfz : Continuous (fun s : ℝ =>
        fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2)))) :=
      continuous_comp_clippedPoint hu hv fX hfX z
        (fun s => (s, p.1.2)) (continuous_id.prodMk continuous_const)
    have hbound : ∀ s ∈ Icc u₀ p.1.1,
        ‖fX (s, p.1.2) (w (clippedPoint hu hv (s, p.1.2))) -
          fX (s, p.1.2) (z (clippedPoint hu hv (s, p.1.2)))‖ ≤
          (κ : ℝ) * dist w z := by
      intro s hs
      rw [← dist_eq_norm]
      have hsI : s ∈ Icc u₀ u₁ := ⟨hs.1, hs.2.trans p.2.1.2⟩
      exact (hLX (s, p.1.2) (pair_mem_rectangle hsI p.2.2) _ _
        (hw _) (hz _)).trans
          (mul_le_mul_of_nonneg_left
            (ContinuousMap.dist_apply_le_dist (clippedPoint hu hv (s, p.1.2)))
            κ.coe_nonneg)
    have h := norm_integral_sub_le_of_norm_sub_le p.2.1.1 _ _
      (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _) hbound
    simp only [picard_apply, dist_eq_norm, add_sub_add_left_eq_sub] at ⊢
    simp only [dist_eq_norm] at h
    calc
      _ ≤ ((κ : ℝ) * ‖w - z‖) * (p.1.1 - u₀) := h
      _ ≤ ((κ : ℝ) * ‖w - z‖) * max (u₁ - u₀) (v₁ - v₀) := by
        gcongr
        exact le_max_of_le_left (sub_le_sub_right p.2.1.2 _)
      _ = ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * ‖w - z‖ := by ring
  · have hfw : Continuous (fun t : ℝ =>
        fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t)))) :=
      continuous_comp_clippedPoint hu hv fY hfY w
        (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
    have hfz : Continuous (fun t : ℝ =>
        fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t)))) :=
      continuous_comp_clippedPoint hu hv fY hfY z
        (fun t => (p.1.1, t)) (continuous_const.prodMk continuous_id)
    have hbound : ∀ t ∈ Icc v₀ p.1.2,
        ‖fY (p.1.1, t) (w (clippedPoint hu hv (p.1.1, t))) -
          fY (p.1.1, t) (z (clippedPoint hu hv (p.1.1, t)))‖ ≤
          (κ : ℝ) * dist w z := by
      intro t ht
      rw [← dist_eq_norm]
      have htI : t ∈ Icc v₀ v₁ := ⟨ht.1, ht.2.trans p.2.2.2⟩
      exact (hLY (p.1.1, t) (pair_mem_rectangle p.2.1 htI) _ _
        (hw _) (hz _)).trans
          (mul_le_mul_of_nonneg_left
            (ContinuousMap.dist_apply_le_dist (clippedPoint hu hv (p.1.1, t)))
            κ.coe_nonneg)
    have h := norm_integral_sub_le_of_norm_sub_le p.2.2.1 _ _
      (hfw.intervalIntegrable _ _) (hfz.intervalIntegrable _ _) hbound
    simp only [picard_apply, dist_eq_norm, add_sub_add_left_eq_sub] at ⊢
    simp only [dist_eq_norm] at h
    calc
      _ ≤ ((κ : ℝ) * ‖w - z‖) * (p.1.2 - v₀) := h
      _ ≤ ((κ : ℝ) * ‖w - z‖) * max (u₁ - u₀) (v₁ - v₀) := by
        gcongr
        exact le_max_of_le_right (sub_le_sub_right p.2.2.2 _)
      _ = ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * ‖w - z‖ := by ring

/-- The ball-preserving Picard iterates converge uniformly on the rectangle to
any ball-valued fixed point of the Picard operator. -/
theorem tendsto_picardIterate_of_fixedPoint_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ r M : ℝ) (hM : 0 ≤ M) (κ : NNReal)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z')
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z')
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (w : C(rectangle u₀ u₁ v₀ v₁, E × F))
    (hwball : ∀ p, dist (w p) c ≤ ρ)
    (hfixed : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w) :
    Tendsto (picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY) atTop (𝓝 w) := by
  let S : Set (C(rectangle u₀ u₁ v₀ v₁, E × F)) :=
    {z | ∀ p, dist (z p) c ≤ ρ}
  let T := picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY
  have hr : r ≤ ρ := by
    have hnonneg : 0 ≤ M * max (u₁ - u₀) (v₁ - v₀) :=
      mul_nonneg hM (le_max_of_le_left (sub_nonneg.mpr hu))
    linarith only [hsize, hnonneg]
  have hbase : picardBase u₀ u₁ v₀ v₁ x₀ y₀ hx₀ hy₀ ∈ S := by
    intro p
    exact (hdata p.1 p.2).trans hr
  have hT : MapsTo T S S := by
    intro z hz p
    exact picard_mem_ball u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY c ρ r M hM hdata hMX hMY hsize z hz p
  have hc : ∀ z ∈ S, ∀ z' ∈ S,
      dist (T z) (T z') ≤
        ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀)) * dist z z' := by
    intro z hz z' hz'
    exact dist_picard_le_on_ball u₀ u₁ v₀ v₁ hu hv x₀ y₀
      fX fY hx₀ hy₀ hfX hfY c ρ κ hLX hLY z z' hz hz'
  exact Metric.tendsto_iterate_of_contractingOn T S
    (picardBase u₀ u₁ v₀ v₁ x₀ y₀ hx₀ hy₀) w
    ((κ : ℝ) * max (u₁ - u₀) (v₁ - v₀))
    (mul_nonneg κ.coe_nonneg (le_max_of_le_left (sub_nonneg.mpr hu)))
    hsmall hbase hwball hT hc hfixed

/-- Picard iterates converge uniformly to a ball-valued continuous solution of
the Goursat integral equations. -/
theorem tendsto_picardIterate_of_integral_equations_on_ball
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hfX : Continuous fX.uncurry) (hfY : Continuous fY.uncurry)
    (c : E × F) (ρ r M : ℝ) (hM : 0 ≤ M) (κ : NNReal)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z')
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z')
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t))) :
    Tendsto (picardIterate u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY
      hx₀ hy₀ hfX hfY) atTop
      (𝓝 (⟨fun p : rectangle u₀ u₁ v₀ v₁ => (X p.1, Y p.1),
        ((hX.prodMk hY).comp continuous_subtype_val)⟩ :
        C(rectangle u₀ u₁ v₀ v₁, E × F))) := by
  let w : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1), (hX.prodMk hY).comp continuous_subtype_val⟩
  have hfixed : Function.IsFixedPt
      (picard u₀ u₁ v₀ v₁ hu hv x₀ y₀ fX fY hx₀ hy₀ hfX hfY) w := by
    exact isFixedPt_picard_of_integral_equations u₀ u₁ v₀ v₁ hu hv
      X Y x₀ y₀ fX fY hX.continuousOn hY.continuousOn
      hx₀ hy₀ hfX hfY heq
  exact tendsto_picardIterate_of_fixedPoint_on_ball u₀ u₁ v₀ v₁ hu hv
    x₀ y₀ fX fY hx₀ hy₀ hfX hfY c ρ r M hM κ hdata hMX hMY
    hLX hLY hsize hsmall w (fun p => hball p.1 p.2) hfixed

end Goursat

end
