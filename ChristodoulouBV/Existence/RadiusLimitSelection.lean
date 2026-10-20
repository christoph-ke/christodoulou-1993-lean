module

public import ChristodoulouBV.Existence.RadiusLimitCompact
public import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives
import Mathlib.Tactic

/-!
# A common selection for the radius construction

The scalar-radius and mass compactness selections are performed here as well,
so subsequent radius limit constructions need no further subsequence extraction.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The three compact limits on a single subsequence. The extension of each
smooth radius agrees on the whole global development, including `u = 0`.
The scalar radius and mass are selected simultaneously for the scalar and mass limit constructions. -/
structure SmoothCompactLimits (T : ℕ → Fields) where
  /-- The common increasing index map. -/
  subsequence : ℕ → ℕ
  /-- Strict increase of the selected indices. -/
  strictMono : StrictMono subsequence
  /-- A continuous extension of the limiting radius. -/
  radius : (ℝ × ℝ) → ℝ
  /-- A continuous extension of the limiting scalar radius. -/
  scalarRadius : (ℝ × ℝ) → ℝ
  /-- A continuous extension of the limiting mass. -/
  mass : (ℝ × ℝ) → ℝ
  /-- Continuity of the radius, including the axis. -/
  radius_continuous : Continuous radius
  /-- Continuity of the scalar radius. -/
  scalarRadius_continuous : Continuous scalarRadius
  /-- Continuity of the mass. -/
  mass_continuous : Continuous mass
  /-- Radius convergence on the off-axis global development. -/
  radius_limit : TendstoLocallyUniformlyOn
    (fun n (p : ℝ × ℝ) => (T (subsequence n)).r p.1 p.2) radius atTop globalDomain
  /-- Scalar-radius convergence on the same subsequence. -/
  scalarRadius_limit : TendstoLocallyUniformlyOn
    (fun n (p : ℝ × ℝ) => (T (subsequence n)).r p.1 p.2 *
      (T (subsequence n)).phi p.1 p.2) scalarRadius atTop globalDomain
  /-- Mass convergence on the same subsequence. -/
  mass_limit : TendstoLocallyUniformlyOn
    (fun n (p : ℝ × ℝ) => (T (subsequence n)).m p.1 p.2) mass atTop globalDomain
  /-- The extended smooth radii, with their natural traces on the axis. -/
  radiusExtension : ℕ → (ℝ × ℝ) → ℝ
  /-- Continuity of every radius extension. -/
  radiusExtension_continuous : ∀ n, Continuous (radiusExtension n)
  /-- The extensions agree with the selected fields at every admissible point. -/
  radiusExtension_eq : ∀ n, EqOn
    (fun p : ℝ × ℝ => (T (subsequence n)).r p.1 p.2) (radiusExtension n) globalDomain
  /-- Uniform convergence on all compact sets, in particular closed triangles. -/
  radiusExtension_limit : TendstoLocallyUniformly radiusExtension radius atTop

/-- Locally uniform convergence on a set survives passage to a subsequence. -/
theorem locally_uniform_on_comp_strictMono {X : Type*} [TopologicalSpace X]
    {f : ℕ → X → ℝ} {g : X → ℝ} {U : Set X}
    (h : TendstoLocallyUniformlyOn f g atTop U) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    TendstoLocallyUniformlyOn (fun n => f (σ n)) g atTop U := by
  intro V hV x hx
  obtain ⟨t, ht, hevent⟩ := h V hV x hx
  exact ⟨t, ht, hσ.tendsto_atTop.eventually hevent⟩

/-- Reindex the compact limits during the single joint selection. -/
@[expose] def SmoothCompactLimits.subseq {T : ℕ → Fields}
    (c : SmoothCompactLimits T) {τ : ℕ → ℕ} (hτ : StrictMono τ) : SmoothCompactLimits T where
  subsequence := c.subsequence ∘ τ
  strictMono := c.strictMono.comp hτ
  radius := c.radius
  scalarRadius := c.scalarRadius
  mass := c.mass
  radius_continuous := c.radius_continuous
  scalarRadius_continuous := c.scalarRadius_continuous
  mass_continuous := c.mass_continuous
  radius_limit := locally_uniform_on_comp_strictMono c.radius_limit hτ
  scalarRadius_limit := locally_uniform_on_comp_strictMono c.scalarRadius_limit hτ
  mass_limit := locally_uniform_on_comp_strictMono c.mass_limit hτ
  radiusExtension := fun n => c.radiusExtension (τ n)
  radiusExtension_continuous := fun n => c.radiusExtension_continuous (τ n)
  radiusExtension_eq := fun n => c.radiusExtension_eq (τ n)
  radiusExtension_limit := locally_uniform_comp_strictMono c.radiusExtension_limit hτ

/-- Restrict locally uniform convergence to a set where the approximants agree. -/
theorem locally_uniform_on_of_eqOn {X : Type*} [TopologicalSpace X]
    {f g : ℕ → X → ℝ} {F : X → ℝ} {U : Set X}
    (h : TendstoLocallyUniformly f F atTop) (heq : ∀ n, EqOn (g n) (f n) U) :
    TendstoLocallyUniformlyOn g F atTop U := by
  intro V hV x hx
  obtain ⟨t, ht, hevent⟩ := h V hV x
  refine ⟨t ∩ U, inter_mem (mem_nhdsWithin_of_mem_nhds ht) self_mem_nhdsWithin, ?_⟩
  filter_upwards [hevent] with n hn y hy
  obtain ⟨hy, hyU⟩ := hy
  rw [heq n hyU]
  exact hn y hy

/-- Joint compactness of radius, scalar radius, and mass for any uniformly bounded smooth approximation
sequence. All three are selected before the sectionwise Helly selection. -/
theorem exists_smooth_compact_limits {a : ℕ → ℝ → ℝ}
    {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) :
    Nonempty (SmoothCompactLimits T) := by
  have hC : 0 ≤ C := (h 0).offset_nonneg
  have hr (n : ℕ) : |(T n).r 0 1| ≤ (1 : ℝ) := by
    rw [((h n).initial_data 1 zero_lt_one).1]
    norm_num
  obtain ⟨σ, R, E, hσ, hR, hE, hER, _, _⟩ :=
    ascoli_on_closed_triangle_exhaustion (fun n => (h n).radius_lipschitz) hr
  have hψ (n : ℕ) : |(T (σ n)).r 0 1 * (T (σ n)).phi 0 1| ≤ 6 * D.toReal + C := by
    rw [((h (σ n)).initial_data 1 zero_lt_one).1, abs_mul]
    have ht := (h (σ n)).amplitudes.phi (0, 1) ⟨le_rfl, zero_lt_one⟩
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hn := abs_nonneg ((T (σ n)).phi 0 1)
    linarith only [ht, hn]
  obtain ⟨τ, P, Eψ, hτ, hP, hEψ, hEP, _, _⟩ :=
    ascoli_on_closed_triangle_exhaustion
      (f := fun n (p : ℝ × ℝ) => (T (σ n)).r p.1 p.2 * (T (σ n)).phi p.1 p.2)
      (L := ⟨2 * (4 * D.toReal + C), mul_nonneg (by norm_num)
        (add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) hC)⟩)
      (fun n => (h (σ n)).scalar_radius_lipschitz) hψ
  have hm (n : ℕ) : |(T (σ (τ n))).m 0 1| ≤ (1 : ℝ) := by
    obtain ⟨_, _, _, _, hlo, hhi⟩ :=
      (h (σ (τ n))).geometry (0, 1) ⟨le_rfl, zero_lt_one⟩
    rw [((h (σ (τ n))).initial_data 1 zero_lt_one).1] at hlo hhi
    norm_num only [div_div, div_one] at hlo hhi
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hhi]
  obtain ⟨υ, M, Em, hυ, hM, hEm, hEM, _, _⟩ :=
    ascoli_on_closed_triangle_exhaustion
      (f := fun n (p : ℝ × ℝ) => (T (σ (τ n))).m p.1 p.2)
      (L := ⟨2 * (100 * D.toReal ^ 2), by positivity⟩)
      (fun n => (h (σ (τ n))).mass_lipschitz) hm
  have hER' := locally_uniform_comp_strictMono
    (locally_uniform_comp_strictMono hER hτ) hυ
  have hEP' := locally_uniform_comp_strictMono hEP hυ
  exact ⟨{
    subsequence := σ ∘ τ ∘ υ
    strictMono := hσ.comp (hτ.comp hυ)
    radius := R
    scalarRadius := P
    mass := M
    radius_continuous := hR
    scalarRadius_continuous := hP
    mass_continuous := hM
    radius_limit := locally_uniform_on_of_eqOn hER' (fun n => (hE _).2)
    scalarRadius_limit := locally_uniform_on_of_eqOn hEP' (fun n => (hEψ _).2)
    mass_limit := locally_uniform_on_of_eqOn hEM (fun n => (hEm _).2)
    radiusExtension := fun n => E (σ (τ (υ n)))
    radiusExtension_continuous := fun n => (hE (σ (τ (υ n)))).1.continuous
    radiusExtension_eq := fun n => (hE (σ (τ (υ n)))).2
    radiusExtension_limit := hER' }⟩

end ChristodoulouBV

end
