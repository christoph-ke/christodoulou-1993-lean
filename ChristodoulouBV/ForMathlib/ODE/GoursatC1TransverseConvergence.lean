module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseInduction
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Stability of linear Volterra recursions on a rectangle

A short characteristic integral contracts the unknown continuous field.
Convergence of the forcing field then implies uniform convergence of the
nonautonomous iterates to a solution of the limiting Volterra equation.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform convergence of a horizontal linear Volterra recursion under
uniform convergence of its forcing evaluated at the limiting solution. -/
theorem tendsto_of_linear_horizontal_volterra_recursion
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (d : ℝ → E) (κ : NNReal)
    (A : ℕ → C(rectangle u₀ u₁ v₀ v₁, E →L[ℝ] E))
    (J : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (P : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (A_lim : C(rectangle u₀ u₁ v₀ v₁, E →L[ℝ] E))
    (J_lim P_lim : C(rectangle u₀ u₁ v₀ v₁, E))
    (hA : ∀ n p, ‖A n p‖ ≤ (κ : ℝ))
    (hJ : Tendsto J atTop (𝓝 J_lim))
    (hsmall : (κ : ℝ) * (u₁ - u₀) < 1)
    (hrec : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      P (n + 1) p = d p.1.2 + ∫ s in u₀..p.1.1,
        A n (clippedPoint hu hv (s, p.1.2))
          (P n (clippedPoint hu hv (s, p.1.2))) +
        J n (clippedPoint hu hv (s, p.1.2)))
    (hlim : ∀ p : rectangle u₀ u₁ v₀ v₁,
      P_lim p = d p.1.2 + ∫ s in u₀..p.1.1,
        A_lim (clippedPoint hu hv (s, p.1.2))
          (P_lim (clippedPoint hu hv (s, p.1.2))) +
        J_lim (clippedPoint hu hv (s, p.1.2)))
    (hAconv : Tendsto A atTop (𝓝 A_lim)) :
    Tendsto P atTop (𝓝 P_lim) := by
  let R := rectangle u₀ u₁ v₀ v₁
  let V : ℕ → C(R, E) := fun n =>
    ⟨fun p => A n p (P_lim p) + J n p,
      ((A n).continuous.clm_apply P_lim.continuous).add (J n).continuous⟩
  let V_lim : C(R, E) :=
    ⟨fun p => A_lim p (P_lim p) + J_lim p,
      (A_lim.continuous.clm_apply P_lim.continuous).add J_lim.continuous⟩
  have hV : Tendsto V atTop (𝓝 V_lim) := by
    have hbound : ∀ n, dist (V n) V_lim ≤
        dist (A n) A_lim * ‖P_lim‖ + dist (J n) J_lim := by
      intro n
      apply (ContinuousMap.dist_le (add_nonneg
        (mul_nonneg dist_nonneg (norm_nonneg _)) dist_nonneg)).2
      intro p
      change dist (A n p (P_lim p) + J n p)
        (A_lim p (P_lim p) + J_lim p) ≤ _
      have hApoint : ‖(A n p - A_lim p) (P_lim p)‖ ≤
          dist (A n) A_lim * ‖P_lim‖ := by
        calc
          ‖(A n p - A_lim p) (P_lim p)‖ ≤ ‖A n p - A_lim p‖ * ‖P_lim p‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ dist (A n) A_lim * ‖P_lim‖ := by
            gcongr
            · rw [← dist_eq_norm]
              exact (ContinuousMap.dist_apply_le_dist p :
                dist (A n p) (A_lim p) ≤ dist (A n) A_lim)
            · exact ContinuousMap.norm_coe_le_norm P_lim p
      have hJpoint : ‖J n p - J_lim p‖ ≤ dist (J n) J_lim := by
        rw [← dist_eq_norm]
        exact (ContinuousMap.dist_apply_le_dist p :
          dist (J n p) (J_lim p) ≤ dist (J n) J_lim)
      calc
        dist (A n p (P_lim p) + J n p) (A_lim p (P_lim p) + J_lim p) =
            ‖(A n p - A_lim p) (P_lim p) + (J n p - J_lim p)‖ := by
              rw [dist_eq_norm, sub_apply]
              congr 1
              abel
        _ ≤ ‖(A n p - A_lim p) (P_lim p)‖ + ‖J n p - J_lim p‖ := norm_add_le _ _
        _ ≤ dist (A n) A_lim * ‖P_lim‖ + dist (J n) J_lim := add_le_add hApoint hJpoint
    have herror : Tendsto (fun n => dist (A n) A_lim * ‖P_lim‖ + dist (J n) J_lim)
        atTop (𝓝 0) := by
      simpa only [zero_mul, zero_add] using
        ((tendsto_iff_dist_tendsto_zero.mp hAconv).mul
          tendsto_const_nhds).add
          (tendsto_iff_dist_tendsto_zero.mp hJ)
    exact tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun n => dist_nonneg) hbound herror)
  have hq0 : 0 ≤ (κ : ℝ) * (u₁ - u₀) :=
    mul_nonneg κ.coe_nonneg (sub_nonneg.mpr hu)
  apply Metric.tendsto_of_dist_succ_le_error_add_contracting hq0 hsmall
    (e := fun n => (u₁ - u₀) * dist (V n) V_lim)
    (by simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_iff_dist_tendsto_zero.mp hV)))
  intro n
  suffices h : dist (P (n + 1)) P_lim ≤
      ((κ : ℝ) * (u₁ - u₀)) * dist (P n) P_lim +
      (u₁ - u₀) * dist (V n) V_lim by
    simpa only [add_comm] using h
  apply (ContinuousMap.dist_le (add_nonneg
    (mul_nonneg hq0 dist_nonneg)
    (mul_nonneg (sub_nonneg.mpr hu) dist_nonneg))).2
  intro p
  rw [hrec n p, hlim p, dist_eq_norm, add_sub_add_left_eq_sub]
  let γ : ℝ → rectangle u₀ u₁ v₀ v₁ :=
    fun s => clippedPoint hu hv (s, p.1.2)
  have hγ : Continuous γ :=
    (continuous_clippedPoint hu hv).comp
      (continuous_id.prodMk continuous_const)
  have hf : Continuous (fun s : ℝ =>
      A n (clippedPoint hu hv (s, p.1.2))
        (P n (clippedPoint hu hv (s, p.1.2))) +
      J n (clippedPoint hu hv (s, p.1.2))) := by
    exact (((A n).continuous.comp hγ).clm_apply
      ((P n).continuous.comp hγ)).add ((J n).continuous.comp hγ)
  have hg : Continuous (fun s : ℝ =>
      A_lim (clippedPoint hu hv (s, p.1.2))
        (P_lim (clippedPoint hu hv (s, p.1.2))) +
      J_lim (clippedPoint hu hv (s, p.1.2))) := by
    exact ((A_lim.continuous.comp hγ).clm_apply
      (P_lim.continuous.comp hγ)).add (J_lim.continuous.comp hγ)
  have hbound : ∀ s ∈ Icc u₀ p.1.1,
      ‖(A n (clippedPoint hu hv (s, p.1.2))
          (P n (clippedPoint hu hv (s, p.1.2))) +
        J n (clippedPoint hu hv (s, p.1.2))) -
        (A_lim (clippedPoint hu hv (s, p.1.2))
          (P_lim (clippedPoint hu hv (s, p.1.2))) +
        J_lim (clippedPoint hu hv (s, p.1.2)))‖ ≤
        (κ : ℝ) * dist (P n) P_lim + dist (V n) V_lim := by
    intro s hs
    let q := clippedPoint hu hv (s, p.1.2)
    have hAq : ‖A n q (P n q - P_lim q)‖ ≤ (κ : ℝ) * dist (P n) P_lim := by
      calc
        ‖A n q (P n q - P_lim q)‖ ≤ ‖A n q‖ * ‖P n q - P_lim q‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (κ : ℝ) * dist (P n) P_lim := by
          gcongr
          · exact hA n q
          · simpa only [dist_eq_norm] using
              (ContinuousMap.dist_apply_le_dist q :
                dist (P n q) (P_lim q) ≤ dist (P n) P_lim)
    have hVq : ‖V n q - V_lim q‖ ≤ dist (V n) V_lim := by
      rw [← dist_eq_norm]
      exact (ContinuousMap.dist_apply_le_dist q :
        dist (V n q) (V_lim q) ≤ dist (V n) V_lim)
    change ‖(A n q (P n q) + J n q) - (A_lim q (P_lim q) + J_lim q)‖ ≤ _
    calc
      _ = ‖A n q (P n q - P_lim q) + (V n q - V_lim q)‖ := by
        change ‖A n q (P n q) + J n q -
          (A_lim q (P_lim q) + J_lim q)‖ =
          ‖A n q (P n q - P_lim q) +
            ((A n q (P_lim q) + J n q) -
              (A_lim q (P_lim q) + J_lim q))‖
        rw [map_sub]
        congr 1
        abel
      _ ≤ ‖A n q (P n q - P_lim q)‖ + ‖V n q - V_lim q‖ := norm_add_le _ _
      _ ≤ (κ : ℝ) * dist (P n) P_lim + dist (V n) V_lim := add_le_add hAq hVq
  have hint := norm_integral_sub_le_of_norm_sub_le p.2.1.1 _ _
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) hbound
  calc
    _ ≤ ((κ : ℝ) * dist (P n) P_lim + dist (V n) V_lim) * (p.1.1 - u₀) := hint
    _ ≤ ((κ : ℝ) * dist (P n) P_lim + dist (V n) V_lim) * (u₁ - u₀) := by
      gcongr
      exact p.2.1.2
    _ = ((κ : ℝ) * (u₁ - u₀)) * dist (P n) P_lim +
        (u₁ - u₀) * dist (V n) V_lim := by ring

end Goursat

end
