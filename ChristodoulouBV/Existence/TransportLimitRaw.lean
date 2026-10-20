module

public import ChristodoulouBV.Existence.MassLimit
import Mathlib.Tactic

/-!
# Mixed transport primitives of the raw limits

The four remaining frozen equations pass along the common existence subsequence.
The mixed radius density has the universal off-axis bound `9 / gap`;
the scalar density retains the smooth approximants' scalar offset in its amplitude bound.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Convergence of the four fields in the mixed radius density implies
convergence of that density when the limiting denominators are positive. -/
theorem radius_coeff_tendsto {S : ℕ → Fields} {F : Fields} {p : ℝ × ℝ}
    (hr : Tendsto (fun n => (S n).r p.1 p.2) atTop (𝓝 (F.r p.1 p.2)))
    (hm : Tendsto (fun n => (S n).m p.1 p.2) atTop (𝓝 (F.m p.1 p.2)))
    (hl : Tendsto (fun n => (S n).lam p.1 p.2) atTop (𝓝 (F.lam p.1 p.2)))
    (hn : Tendsto (fun n => (S n).nu p.1 p.2) atTop (𝓝 (F.nu p.1 p.2)))
    (hr0 : 0 < F.r p.1 p.2) (hq0 : 0 < 1 - 2 * F.m p.1 p.2 / F.r p.1 p.2) :
    Tendsto (fun n => IsBVSolution.radiusCoeff (S n) p.1 p.2) atTop
      (𝓝 (IsBVSolution.radiusCoeff F p.1 p.2)) := by
  have hμ := ((tendsto_const_nhds (x := (2 : ℝ))).mul hm).div hr hr0.ne'
  exact ((hμ.mul hl).mul hn).div ((tendsto_const_nhds.sub hμ).mul hr)
    (mul_pos hq0 hr0).ne'

/-- The raw mixed radius density converges at every domain point along
exactly the shared seven-field selection. -/
theorem RadiusLimitData.raw_radius_coeff_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun n => IsBVSolution.radiusCoeff (T (d.subsequence n)) p.1 p.2) atTop
      (𝓝 (IsBVSolution.radiusCoeff d.rawFields p.1 p.2)) := by
  apply radius_coeff_tendsto (d.radius_limit.tendsto_at hp) (d.mass_limit.tendsto_at hp)
    (d.lam_limit p hp) (d.nu_limit p hp) (d.radius_pos h hp)
  exact lt_of_lt_of_le (by norm_num) (d.mass_geometry h p hp).1

/-- The universal mixed-density bound passes to the raw fields, with any
positive lower bound for the coordinate gap. -/
theorem RadiusLimitData.raw_radius_coeff_bound
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) {δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ p.2 - p.1) :
    |IsBVSolution.radiusCoeff d.rawFields p.1 p.2| ≤ 9 / δ := by
  exact le_of_tendsto (d.raw_radius_coeff_limit h hp).abs
    (Eventually.of_forall (fun n =>
      (h (d.subsequence n)).mixed_radius_bound hp hδ hgap))

/-- Both mixed expansion primitives hold for the raw pointwise limits,
on every closed null segment, including the initial edge. -/
theorem raw_expansion_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.rawFields.lam u v)
        (fun u => IsBVSolution.radiusCoeff d.rawFields u v) a b) ∧
    ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.rawFields.nu u)
        (IsBVSolution.radiusCoeff d.rawFields u) a b := by
  constructor
  · intro v a b hab hs
    have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.lam_in v a b hab hs)
      (M := 9 / (v - b))
    · intro n t ht
      exact (h (d.subsequence n)).mixed_radius_bound (p := (t, v)) (hs ⟨ht, rfl⟩)
        (sub_pos.mpr hp.2) (by linarith only [ht.2])
    · exact d.lam_limit (a, v) (hs ⟨⟨le_rfl, hab⟩, rfl⟩)
    · exact d.lam_limit (b, v) hp
    · exact Eventually.of_forall (fun t ht =>
        d.raw_radius_coeff_limit h (p := (t, v)) (hs ⟨ht, rfl⟩))
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.nu_out u a b hab hs)
      (M := 9 / (a - u))
    · intro n t ht
      exact (h (d.subsequence n)).mixed_radius_bound (p := (u, t)) (hs ⟨rfl, ht⟩)
        (sub_pos.mpr hp.2) (by linarith only [ht.1])
    · exact d.nu_limit (u, a) hp
    · exact d.nu_limit (u, b) (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)
    · exact Eventually.of_forall (fun t ht =>
        d.raw_radius_coeff_limit h (p := (u, t)) (hs ⟨rfl, ht⟩))

/-- The two scalar mixed primitives also pass to the raw limits. Their
majorant retains the fixed datum's scalar offset, with universal coefficients. -/
theorem raw_alpha_beta_transport_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.rawFields.alpha u v)
        (fun u => IsBVSolution.radiusCoeff d.rawFields u v * d.rawFields.phi u v) a b) ∧
    ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.rawFields.beta u)
        (fun v => IsBVSolution.radiusCoeff d.rawFields u v * d.rawFields.phi u v) a b := by
  constructor
  · intro v a b hab hs
    have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.alpha_in v a b hab hs)
      (M := (9 / (v - b)) * (6 * D.toReal + C))
    · intro n t ht
      rw [abs_mul]
      exact mul_le_mul
        ((h (d.subsequence n)).mixed_radius_bound (p := (t, v)) (hs ⟨ht, rfl⟩)
          (sub_pos.mpr hp.2) (by linarith only [ht.2]))
        ((h (d.subsequence n)).amplitudes.phi (t, v) (hs ⟨ht, rfl⟩))
        (abs_nonneg _) (div_nonneg (by norm_num) (sub_pos.mpr hp.2).le)
    · exact d.alpha_limit (a, v) (hs ⟨⟨le_rfl, hab⟩, rfl⟩)
    · exact d.alpha_limit (b, v) hp
    · exact Eventually.of_forall (fun t ht =>
        (d.raw_radius_coeff_limit h (p := (t, v)) (hs ⟨ht, rfl⟩)).mul
          (d.scalar_locally_uniform h |>.tendsto_at (a := (t, v)) (hs ⟨ht, rfl⟩)))
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    apply interval_primitive_limit_ae hab
      (fun n => (h (d.subsequence n)).solution.solution.beta_out u a b hab hs)
      (M := (9 / (a - u)) * (6 * D.toReal + C))
    · intro n t ht
      rw [abs_mul]
      exact mul_le_mul
        ((h (d.subsequence n)).mixed_radius_bound (p := (u, t)) (hs ⟨rfl, ht⟩)
          (sub_pos.mpr hp.2) (by linarith only [ht.1]))
        ((h (d.subsequence n)).amplitudes.phi (u, t) (hs ⟨rfl, ht⟩))
        (abs_nonneg _) (div_nonneg (by norm_num) (sub_pos.mpr hp.2).le)
    · exact d.beta_limit (u, a) hp
    · exact d.beta_limit (u, b) (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)
    · exact Eventually.of_forall (fun t ht =>
        (d.raw_radius_coeff_limit h (p := (u, t)) (hs ⟨rfl, ht⟩)).mul
          (d.scalar_locally_uniform h |>.tendsto_at (a := (u, t)) (hs ⟨rfl, ht⟩)))

end ChristodoulouBV

end
