module

public import Mathlib.Topology.CompactOpen
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Jets
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Limits of integral identities for characteristic Picard iterates

The integral identity, rather than a theorem about limits of derivatives, transfers a
continuous jet through a uniform limit of approximations.  The result is stated for
continuous maps on one compact interval and is independent of a particular ODE.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Sup-norm convergence of continuous integrands on a compact interval passes through
integration up to any fixed point of that interval. -/
theorem tendsto_integral_of_tendsto_continuousMap
    {a b : ℝ} (hab : a ≤ b)
    (g : ℕ → C(Icc a b, E)) (G : C(Icc a b, E))
    (hg : Tendsto g atTop (𝓝 G)) {t : ℝ} (ht : t ∈ Icc a b) :
    Tendsto (fun n => ∫ s in a..t, g n ⟨Goursat.clip a b s,
      Goursat.clip_mem_Icc hab s⟩) atTop
      (𝓝 (∫ s in a..t, G ⟨Goursat.clip a b s,
        Goursat.clip_mem_Icc hab s⟩)) := by
  have hclip : Continuous (fun s : ℝ =>
      (⟨Goursat.clip a b s, Goursat.clip_mem_Icc hab s⟩ : Icc a b)) :=
    Continuous.subtype_mk (Goursat.continuous_clip a b) _
  have hnorm (n : ℕ) :
      ‖(∫ s in a..t, g n ⟨Goursat.clip a b s,
          Goursat.clip_mem_Icc hab s⟩) -
        ∫ s in a..t, G ⟨Goursat.clip a b s,
          Goursat.clip_mem_Icc hab s⟩‖ ≤
        dist (g n) G * (t - a) := by
    apply Goursat.norm_integral_sub_le_of_norm_sub_le ht.1
    · exact ((g n).continuous.comp hclip).intervalIntegrable a t
    · exact (G.continuous.comp hclip).intervalIntegrable a t
    · intro s _
      rw [← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist _
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => hnorm n)
  have hdist : Tendsto (fun n => dist (g n) G) atTop (𝓝 (0 : ℝ)) := by
    simpa only [dist_self] using hg.dist (tendsto_const_nhds (x := G))
  simpa only [zero_mul] using hdist.mul_const (t - a)

/-- A uniformly convergent sequence of continuous primitives whose integrands also
converge uniformly has the expected relative derivative on the whole closed interval.
No derivative-limit theorem is used: the integral identities pass to the limit first. -/
theorem hasDerivWithinAt_of_tendsto_integral_eq
    [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    (f g : ℕ → C(Icc a b, E)) (F G : C(Icc a b, E))
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G))
    (heq : ∀ n (t : ℝ) (ht : t ∈ Icc a b),
      f n ⟨t, ht⟩ = f n ⟨a, ⟨le_rfl, hab⟩⟩ +
        ∫ s in a..t, g n ⟨Goursat.clip a b s,
          Goursat.clip_mem_Icc hab s⟩)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => F ⟨Goursat.clip a b s,
      Goursat.clip_mem_Icc hab s⟩) (G ⟨t, ht⟩) (Icc a b) t := by
  let fExt : ℝ → E := fun s => F ⟨Goursat.clip a b s,
    Goursat.clip_mem_Icc hab s⟩
  let gExt : ℝ → E := fun s => G ⟨Goursat.clip a b s,
    Goursat.clip_mem_Icc hab s⟩
  have hclip : Continuous (fun s : ℝ =>
      (⟨Goursat.clip a b s, Goursat.clip_mem_Icc hab s⟩ : Icc a b)) :=
    Continuous.subtype_mk (Goursat.continuous_clip a b) _
  have hgExt : ContinuousOn gExt (Icc a b) :=
    (G.continuous.comp hclip).continuousOn
  have hlimEq (x : ℝ) (hx : x ∈ Icc a b) :
      F ⟨x, hx⟩ = F ⟨a, ⟨le_rfl, hab⟩⟩ + ∫ s in a..x, gExt s := by
    have hleft : Tendsto (fun n => f n ⟨x, hx⟩) atTop
        (𝓝 (F ⟨x, hx⟩)) := by
      simpa only [Function.comp_def] using
        ((continuous_eval_const (⟨x, hx⟩ : Icc a b)).tendsto F).comp hf
    have hbase : Tendsto (fun n => f n ⟨a, ⟨le_rfl, hab⟩⟩) atTop
        (𝓝 (F ⟨a, ⟨le_rfl, hab⟩⟩)) := by
      simpa only [Function.comp_def] using
        ((continuous_eval_const (⟨a, ⟨le_rfl, hab⟩⟩ : Icc a b)).tendsto F).comp hf
    have hintegral := tendsto_integral_of_tendsto_continuousMap hab g G hg hx
    have hright : Tendsto (fun n => f n ⟨x, hx⟩) atTop
        (𝓝 (F ⟨a, ⟨le_rfl, hab⟩⟩ + ∫ s in a..x, gExt s)) := by
      convert hbase.add hintegral using 1
      funext n
      exact heq n x hx
    exact tendsto_nhds_unique hleft hright
  have heqExt (x : ℝ) (hx : x ∈ Icc a b) :
      fExt x = F ⟨a, ⟨le_rfl, hab⟩⟩ + ∫ s in a..x, gExt s := by
    simpa only [fExt, Goursat.clip_eq_self hx] using hlimEq x hx
  have h := hasDerivWithinAt_of_eq_integral_on_Icc fExt gExt
    (F ⟨a, ⟨le_rfl, hab⟩⟩) hgExt heqExt ht
  simpa only [gExt, Goursat.clip_eq_self ht] using h

end intervalIntegral

namespace Real

/-- A nonnegative sequence tends to zero when each next term is bounded by a
vanishing error plus a fixed strict contraction of the current term. -/
theorem tendsto_zero_of_le_error_add_contracting
    {a e : ℕ → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : ∀ n, 0 ≤ a n) (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ n, a (n + 1) ≤ e n + q * a n) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hδ : 0 < ε * (1 - q) / 2 := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp he _ hδ)
  have hbound (k : ℕ) : a (N + k) ≤ q ^ k * a N + ε / 2 := by
    induction k with
    | zero =>
      simp only [add_zero, pow_zero, one_mul]
      linarith
    | succ k ih =>
      have heN : e (N + k) < ε * (1 - q) / 2 := by
        have h := hN (N + k) (Nat.le_add_right N k)
        have : dist (e (N + k)) 0 = |e (N + k)| := by simp
        rw [this] at h
        exact lt_of_le_of_lt (le_abs_self _) h
      calc
        a (N + (k + 1)) = a ((N + k) + 1) := by simp only [Nat.add_assoc]
        _ ≤ e (N + k) + q * a (N + k) := hrec _
        _ ≤ ε * (1 - q) / 2 + q * (q ^ k * a N + ε / 2) := by
          exact add_le_add (le_of_lt heN) (mul_le_mul_of_nonneg_left ih hq0)
        _ = q ^ (k + 1) * a N + ε / 2 := by ring
  have hpow : Tendsto (fun k : ℕ => q ^ k * a N) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (a N)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hpow (ε / 2) (by positivity)
  refine ⟨N + K, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : N ≤ n)
  have hk : K ≤ k := by omega
  have hsmall : q ^ k * a N < ε / 2 := by
    have h := hK k hk
    have : dist (q ^ k * a N) 0 = |q ^ k * a N| := by simp
    rw [this] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have htotal : a (N + k) < ε := by linarith only [hbound k, hsmall]
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (ha0 (N + k))] using htotal

end Real

namespace Metric

/-- Approximate iterates converge to a point when their one-step error vanishes and
their distance to that point satisfies a fixed contraction estimate. -/
theorem tendsto_of_dist_succ_le_error_add_contracting
    {α : Type*} [PseudoMetricSpace α] {z : ℕ → α} {w : α}
    {e : ℕ → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ n, dist (z (n + 1)) w ≤ e n + q * dist (z n) w) :
    Tendsto z atTop (𝓝 w) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact Real.tendsto_zero_of_le_error_add_contracting hq0 hq1
    (fun n => dist_nonneg) he hrec

end Metric

end
