module

public import ChristodoulouBV.Existence.RadiusLimitCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Radius primitives and the axis trace of the limit

The limiting equations are the exact frozen interval identities, rather
than pointwise differentiability assertions at jumps.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Dominated convergence passes a bounded sequence of interval primitives
to its endpoint and density limits. -/
theorem interval_primitive_limit {f g : ℕ → ℝ → ℝ} {F G : ℝ → ℝ}
    {a b M : ℝ} (hab : a ≤ b) (hprim : ∀ n, IntervalPrimitive (f n) (g n) a b)
    (hbound : ∀ n t, t ∈ Icc a b → |g n t| ≤ M)
    (ha : Tendsto (fun n => f n a) atTop (𝓝 (F a)))
    (hb : Tendsto (fun n => f n b) atTop (𝓝 (F b)))
    (hg : ∀ t ∈ Icc a b, Tendsto (fun n => g n t) atTop (𝓝 (G t)))
    (hG : IntervalIntegrable G volume a b) : IntervalPrimitive F G a b := by
  have hi : Tendsto (fun n => ∫ t in a..b, g n t) atTop (𝓝 (∫ t in a..b, G t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => M)
    · exact Eventually.of_forall (fun n => by
        simpa only [uIoc_of_le hab] using (hprim n).1.aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun t ht => by
        rw [uIoc_of_le hab] at ht
        exact hbound n t ⟨ht.1.le, ht.2⟩))
    · exact intervalIntegrable_const
    · exact Eventually.of_forall (fun t ht => by
        rw [uIoc_of_le hab] at ht
        exact hg t ⟨ht.1.le, ht.2⟩)
  refine ⟨hG, tendsto_nhds_unique (hb.sub ha) ?_⟩
  exact hi.congr' (Eventually.of_forall (fun n => (hprim n).2.symm))

/-- Both exact frozen radius primitives pass to the single shared existence limit on
every closed null segment of the global development. -/
theorem radius_primitive_limit {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (fun v => d.radius (u, v)) (d.lam u) a b) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.radius (u, v)) (fun u => d.nu u v) a b) := by
  have hV : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  obtain ⟨hlamvar, hνvar, _⟩ := expansions_limit h d
  constructor
  · intro u a b hab hs
    have haU : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    have hbU : (u, b) ∈ globalDomain := hs ⟨rfl, ⟨hab, le_rfl⟩⟩
    have hBV : BoundedVariationOn (d.lam u) (Ioi u) :=
      ne_of_lt ((hlamvar u haU.1).trans_lt hV)
    apply interval_primitive_limit hab
      (fun n => (h (d.subsequence n)).solution.solution.radius_out u a b hab hs)
      (M := 1)
    · intro n t ht
      obtain ⟨hl, hu⟩ := (h (d.subsequence n)).amplitudes.lam (u, t) (hs ⟨rfl, ht⟩)
      rw [abs_of_nonneg (by linarith only [hl])]
      exact hu.trans (by norm_num)
    · exact d.radius_limit.tendsto_at haU
    · exact d.radius_limit.tendsto_at hbU
    · intro t ht
      exact d.lam_limit (u, t) (hs ⟨rfl, ht⟩)
    · apply hBV.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)).2
  · intro v a b hab hs
    have haU : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
    have hbU : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
    have hBV : BoundedVariationOn (fun u => d.nu u v) (Ico 0 v) :=
      ne_of_lt ((hνvar v (haU.1.trans_lt haU.2)).trans_lt hV)
    apply interval_primitive_limit hab
      (fun n => (h (d.subsequence n)).solution.solution.radius_in v a b hab hs)
      (M := 1)
    · intro n t ht
      obtain ⟨hl, hu⟩ := (h (d.subsequence n)).amplitudes.nu (t, v) (hs ⟨ht, rfl⟩)
      rw [abs_of_nonpos (by linarith only [hu])]
      linarith only [hl]
    · exact d.radius_limit.tendsto_at haU
    · exact d.radius_limit.tendsto_at hbU
    · intro t ht
      exact d.nu_limit (t, v) (hs ⟨ht, rfl⟩)
    · apply hBV.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (show (t, v) ∈ globalDomain from hs ⟨ht, rfl⟩)

/-- The natural radius extension assigns the zero trace on the axis. -/
@[expose] noncomputable def radiusWithAxis (S : Fields) (p : ℝ × ℝ) : ℝ :=
  if p.1 = p.2 then 0 else S.r p.1 p.2

/-- Every continuous smooth-radius extension has zero value on the axis. -/
theorem RadiusLimitData.radiusExtension_axis
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : d.radiusExtension n (x, x) = 0 := by
  let H := (h (d.subsequence n)).solution.solution
  have hp : (x, x + 1) ∈ globalDomain := ⟨hx, lt_add_one x⟩
  have htrace : Tendsto ((T (d.subsequence n)).r x) (𝓝[>] x) (𝓝 (0 : ℝ)) := by
    simpa only [H.development.axis_filter_eq hp] using
      H.radius_axis x (H.development.axis_mem hp)
  have he : Tendsto (fun t => d.radiusExtension n (x, t)) (𝓝[>] x) (𝓝 (0 : ℝ)) := by
    apply htrace.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact d.radiusExtension_eq n (show (x, t) ∈ globalDomain from ⟨hx, ht⟩)
  have hc : Continuous (fun t => d.radiusExtension n (x, t)) :=
    (d.radiusExtension_continuous n).comp (continuous_const.prodMk continuous_id)
  exact tendsto_nhds_unique ((hc.tendsto x).mono_left nhdsWithin_le_nhds) he

/-- The continuous limiting radius has zero axis values. -/
theorem RadiusLimitData.radius_axis
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {x : ℝ} (hx : 0 ≤ x) : d.radius (x, x) = 0 := by
  have hl := d.radiusExtension_limit.tendstoLocallyUniformlyOn.tendsto_at
    (mem_univ (x, x))
  have hz : Tendsto (fun n => d.radiusExtension n (x, x)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [d.radiusExtension_axis h _ hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hl hz

/-- Radius convergence is uniform on each closed triangle, including the
initial edge and the zero-radius axis, after the natural axis extension. -/
theorem RadiusLimitData.radius_uniform_on_closed_triangle
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) (b : ℝ) :
    TendstoUniformlyOn (fun n => radiusWithAxis (T (d.subsequence n))) d.radius atTop
      (closedCoordTriangle 0 b) := by
  have hc := tendstoLocallyUniformly_iff_forall_isCompact.mp d.radiusExtension_limit
    _ (isCompact_closedCoordTriangle 0 b)
  intro V hV
  filter_upwards [hc V hV] with n hn p hp
  have heq : radiusWithAxis (T (d.subsequence n)) p = d.radiusExtension n p := by
    by_cases he : p.1 = p.2
    · rw [radiusWithAxis, ite_eq_left he]
      exact (d.radiusExtension_axis h n hp.1).symm.trans
        (congrArg (d.radiusExtension n) (Prod.ext rfl he))
    · rw [radiusWithAxis, ite_eq_right he]
      exact d.radiusExtension_eq n ⟨hp.1, lt_of_le_of_ne hp.2.1 he⟩
  rw [heq]
  exact hn p hp

/-- The exact initial-radius gauge survives the joint selection. -/
theorem RadiusLimitData.initial_radius
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {v : ℝ} (hv : 0 < v) : d.radius (0, v) = v / 2 := by
  apply tendsto_nhds_unique (d.radius_limit.tendsto_at ⟨le_rfl, hv⟩)
  have he (n : ℕ) := ((h (d.subsequence n)).initial_data v hv).1
  simpa only [he] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => v / 2) atTop (𝓝 (v / 2)))

end ChristodoulouBV

end
