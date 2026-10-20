module

public import ChristodoulouBV.Existence.ScalarLimit
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Tactic

/-!
# Mass geometry on the shared existence subsequence

The mass was selected together with the other six fields on the common existence subsequence. This
module uses that selection without extracting again. The quantitative
geometry implies nonnegative mass, its zero axis trace, and locally
uniform convergence of the mass ratio away from the axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The limiting mass is nonnegative and satisfies the universal radius
bound at every point, including the initial edge. -/
theorem RadiusLimitData.mass_bounds
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    0 ≤ d.mass p ∧ 2 * d.mass p ≤ d.radius p / 3 := by
  have hr := d.radius_pos h hp
  obtain ⟨hlo, hhi⟩ := d.mass_geometry h p hp
  have hq0 : 0 ≤ 2 * d.mass p / d.radius p := by linarith only [hhi]
  have hq1 : 2 * d.mass p / d.radius p ≤ 1 / 3 := by linarith only [hlo]
  have hm0 := (le_div_iff₀ hr).mp hq0
  have hm1 := (div_le_iff₀ hr).mp hq1
  constructor <;> linarith only [hm0, hm1]

/-- The continuous selected mass has zero value on every nonnegative
axis point, independently of the smooth fields' assigned axis values. -/
theorem RadiusLimitData.mass_axis
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {x : ℝ} (hx : 0 ≤ x) : d.mass (x, x) = 0 := by
  have hclosed : IsClosed {p | 0 ≤ d.mass p ∧ 2 * d.mass p ≤ d.radius p / 3} :=
    (isClosed_le continuous_const d.mass_continuous).inter
      (isClosed_le (continuous_const.mul d.mass_continuous)
        (d.radius_continuous.div_const 3))
  have hb := closure_minimal (fun p hp => d.mass_bounds h hp) hclosed
    (nonnegative_axis_mem_closure_globalDomain hx)
  change 0 ≤ d.mass (x, x) ∧ 2 * d.mass (x, x) ≤ d.radius (x, x) / 3 at hb
  rw [d.radius_axis h hx] at hb
  linarith only [hb.1, hb.2]

/-- The selected mass satisfies the precise one-sided axis-limit clause
of the frozen solution predicate, for the canonical scalar fields. -/
theorem mass_axis_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    ∀ x ∈ adjacentAxis globalDomain,
      Tendsto (d.scalarRightFields.m x)
        (nhdsWithin x (Ioi x) ⊓ principal {v | (x, v) ∈ globalDomain}) (𝓝 (0 : ℝ)) := by
  intro x hx
  change Tendsto (fun v => d.mass (x, v)) _ (𝓝 (0 : ℝ))
  have hx0 : 0 ≤ x := by
    have hcl : (x, x) ∈ closure globalDomain := hx
    rw [s6_closure_globalDomain] at hcl
    exact hcl.1
  have hc : Continuous (fun v => d.mass (x, v)) :=
    d.mass_continuous.comp (continuous_const.prodMk continuous_id)
  have ht : Tendsto (fun v => d.mass (x, v))
      (𝓝[>] x ⊓ principal {v | (x, v) ∈ globalDomain}) (𝓝 (d.mass (x, x))) :=
    (hc.tendsto x).mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  simpa only [d.mass_axis h hx0] using ht

/-- The off-axis mass ratios converge locally uniformly on the same
subsequence. The radius floor controls their denominator. -/
theorem RadiusLimitData.mass_ratio_locally_uniform
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => 2 * (T (d.subsequence n)).m p.1 p.2 /
        (T (d.subsequence n)).r p.1 p.2)
      (fun p => 2 * d.mass p / d.radius p) atTop globalDomain := by
  have hr0 := fun p hp => (d.radius_pos h (p := p) hp).ne'
  have hi := d.radius_limit.fun_inv₀ d.radius_continuous.continuousOn hr0
  have hm := d.mass_limit.fun_mul₀ hi d.mass_continuous.continuousOn
    (d.radius_continuous.continuousOn.inv₀ hr0)
  have htwo : TendstoLocallyUniformlyOn
      (fun (_ : ℕ) (_ : ℝ × ℝ) => (2 : ℝ)) (fun _ => 2) atTop globalDomain :=
    (tendsto_const_nhds.tendstoUniformlyOn_const globalDomain).tendstoLocallyUniformlyOn
  have hprod := htwo.fun_mul₀ hm continuousOn_const
    (d.mass_continuous.continuousOn.mul
      (d.radius_continuous.continuousOn.inv₀ hr0))
  simpa only [div_eq_mul_inv, mul_assoc] using hprod

/-- Mass compactness and its axis and geometry consequences, all on
the shared existence subsequence. -/
theorem mass_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞) :
    let d := radiusLimitData h hD
    StrictMono d.subsequence ∧ Continuous d.mass ∧
      TendstoLocallyUniformlyOn
        (fun n (p : ℝ × ℝ) => (T (d.subsequence n)).m p.1 p.2)
        d.mass atTop globalDomain ∧
      (∀ x : ℝ, 0 ≤ x → d.mass (x, x) = 0) ∧
      TendstoLocallyUniformlyOn
        (fun n (p : ℝ × ℝ) => 2 * (T (d.subsequence n)).m p.1 p.2 /
          (T (d.subsequence n)).r p.1 p.2)
        (fun p => 2 * d.mass p / d.radius p) atTop globalDomain ∧
      ∀ p ∈ globalDomain, 0 ≤ d.mass p ∧ 2 * d.mass p ≤ d.radius p / 3 ∧
        0 ≤ 2 * d.mass p / d.radius p ∧ 2 * d.mass p / d.radius p ≤ 1 / 3 := by
  let d := radiusLimitData h hD
  refine ⟨d.strictMono, d.mass_continuous, d.mass_limit,
    fun _ hx => d.mass_axis h hx, d.mass_ratio_locally_uniform h, ?_⟩
  intro p hp
  obtain ⟨hm0, hm1⟩ := d.mass_bounds h hp
  obtain ⟨hq0, hq1⟩ := d.mass_geometry h p hp
  exact ⟨hm0, hm1, by linarith only [hq1], by linarith only [hq0]⟩

end ChristodoulouBV

end
