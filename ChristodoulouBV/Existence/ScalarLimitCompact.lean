module

public import ChristodoulouBV.Existence.ScalarLimitCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Scalar-radius convergence up to the axis

Uniform Lipschitz extensions recover convergence on closed triangles from
the already selected existence subsequence. No new extraction is performed.
The natural scalar-radius extension assigns zero on the axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The nonnegative axis belongs to the closure of the global development. -/
theorem nonnegative_axis_mem_closure_globalDomain {x : ℝ} (hx : 0 ≤ x) :
    (x, x) ∈ closure globalDomain := by
  apply mem_closure_of_tendsto
    (((continuous_const.prodMk continuous_id).tendsto x).mono_left
      (show 𝓝[>] x ≤ 𝓝 x from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ⟨hx, ht⟩

private theorem scalar_bound_on_closure {F R : (ℝ × ℝ) → ℝ} {M : ℝ}
    (hF : Continuous F) (hR : Continuous R)
    (hb : ∀ p ∈ globalDomain, |F p| ≤ M * |R p|) :
    ∀ p ∈ closure globalDomain, |F p| ≤ M * |R p| :=
  closure_minimal hb (isClosed_le hF.abs (continuous_const.mul hR.abs))

/-- The selected scalar radius vanishes on every nonnegative axis point. -/
theorem RadiusLimitData.scalarRadius_axis
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {x : ℝ} (hx : 0 ≤ x) : d.scalarRadius (x, x) = 0 := by
  have hb : ∀ p ∈ globalDomain,
      |d.scalarRadius p| ≤ (6 * D.toReal + C) * |d.radius p| := by
    intro p hp
    rw [← d.radius_mul_scalar h hp, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (d.scalar_amplitude h hp) (abs_nonneg _)
  have hx' := scalar_bound_on_closure d.scalarRadius_continuous d.radius_continuous hb
    (x, x) (nonnegative_axis_mem_closure_globalDomain hx)
  rw [d.radius_axis h hx, abs_zero, mul_zero] at hx'
  exact abs_nonpos_iff.mp hx'

/-- The scalar radius with its natural zero trace on the axis. -/
@[expose] noncomputable def scalarRadiusWithAxis (S : Fields) (p : ℝ × ℝ) : ℝ :=
  if p.1 = p.2 then 0 else S.r p.1 p.2 * S.phi p.1 p.2

private theorem uniform_on_compact_of_lipschitz_pointwise
    {E : ℕ → (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → ℝ} {L : ℝ≥0}
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hE : ∀ n, LipschitzWith L (E n))
    (hlim : ∀ p ∈ K, Tendsto (fun n => E n p) atTop (𝓝 (F p))) :
    TendstoUniformlyOn E F atTop K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heq : Equicontinuous (fun n (p : K) => E n p) :=
    (LipschitzWith.uniformEquicontinuous _ L
      (fun n => by simpa only [mul_one, Function.comp_def] using
        (hE n).comp (LipschitzWith.subtype_val K))).equicontinuous
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (heq.tendsto_uniformFun_iff_pi atTop (fun p : K => F p)).mpr
  exact tendsto_pi_nhds.mpr (fun p => hlim p p.property)

/-- Scalar-radius convergence is uniform on every closed finite triangle,
with the initial edge and zero-axis trace included. -/
theorem RadiusLimitData.scalarRadius_uniform_on_closed_triangle
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) (b : ℝ) :
    TendstoUniformlyOn (fun n => scalarRadiusWithAxis (T (d.subsequence n)))
      d.scalarRadius atTop (closedCoordTriangle 0 b) := by
  choose E hE hEq using fun n => ((h (d.subsequence n)).scalar_radius_lipschitz).extend_real
  have heq : Equicontinuous E :=
    (LipschitzWith.uniformEquicontinuous E
      ⟨2 * (4 * D.toReal + C), mul_nonneg (by norm_num)
        (add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (h 0).offset_nonneg)⟩
      hE).equicontinuous
  have hclosed := heq.isClosed_setOfPred_tendsto d.scalarRadius_continuous (l := atTop)
  have hlim : ∀ p ∈ closure globalDomain,
      Tendsto (fun n => E n p) atTop (𝓝 (d.scalarRadius p)) := by
    apply closure_minimal ?_ hclosed
    intro p hp
    exact (d.scalarRadius_limit.tendsto_at hp).congr'
      (Eventually.of_forall (fun n => hEq n hp))
  have haxis (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : E n (x, x) = 0 := by
    have hb : ∀ p ∈ globalDomain,
        |E n p| ≤ (6 * D.toReal + C) * |d.radiusExtension n p| := by
      intro p hp
      rw [← hEq n hp, ← d.radiusExtension_eq n hp, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        ((h (d.subsequence n)).amplitudes.phi p hp) (abs_nonneg _)
    have hx' := scalar_bound_on_closure (hE n).continuous
      (d.radiusExtension_continuous n) hb (x, x)
      (nonnegative_axis_mem_closure_globalDomain hx)
    rw [d.radiusExtension_axis h n hx, abs_zero, mul_zero] at hx'
    exact abs_nonpos_iff.mp hx'
  have hK : closedCoordTriangle 0 b ⊆ closure globalDomain := by
    intro p hp
    rcases eq_or_lt_of_le hp.2.1 with he | he
    · have hpEq : p = (p.1, p.1) := Prod.ext rfl he.symm
      rw [hpEq]
      exact nonnegative_axis_mem_closure_globalDomain hp.1
    · exact subset_closure ⟨hp.1, he⟩
  have hc := uniform_on_compact_of_lipschitz_pointwise
    (L := ⟨2 * (4 * D.toReal + C), mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (h 0).offset_nonneg)⟩)
    (isCompact_closedCoordTriangle 0 b) hE (fun p hp => hlim p (hK hp))
  apply hc.congr
  refine Eventually.of_forall (fun n p hp => ?_)
  by_cases he : p.1 = p.2
  · have hpEq : p = (p.1, p.1) := Prod.ext rfl he.symm
    have hz : E n p = 0 := (congrArg (E n) hpEq).trans (haxis n p.1 hp.1)
    simpa only [scalarRadiusWithAxis, ite_eq_left he] using hz
  · rw [scalarRadiusWithAxis, ite_eq_right he]
    exact (hEq n ⟨hp.1, lt_of_le_of_ne hp.2.1 he⟩).symm

end ChristodoulouBV

end
