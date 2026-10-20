module

public import ChristodoulouBV.Existence.TransportLimitTrace
import Mathlib.Tactic

/-!
# Mixed primitives for the canonical representatives

The simultaneous right translation of the raw solution has the same gap
from the axis on each translated null segment. Dominated convergence in
this spatial parameter proves all four remaining primitives for the
single canonical record `RadiusLimitData.scalarRightFields`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Translate an interval primitive, including its endpoint identity. -/
theorem IntervalPrimitive.translate {F g : ℝ → ℝ} {a b e : ℝ}
    (hp : IntervalPrimitive F g (a + e) (b + e)) :
    IntervalPrimitive (fun t => F (t + e)) (fun t => g (t + e)) a b := by
  refine ⟨(IntervalIntegrable.comp_add_right_iff (f := g) (a := a) (b := b)
    (c := e)).mpr hp.1, ?_⟩
  rw [intervalIntegral.integral_comp_add_right]
  exact hp.2

private theorem transportShift_inSeg {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) (n : ℕ) :
    inSeg (v + transportStep n) (a + transportStep n) (b + transportStep n) ⊆
      globalDomain := by
  have haU : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
  have hbU : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
  rintro ⟨x, y⟩ ⟨hx, rfl⟩
  exact ⟨(add_nonneg haU.1 (transport_step_pos n).le).trans hx.1,
    by linarith only [hx.2, hbU.2]⟩

private theorem transportShift_outSeg {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) (n : ℕ) :
    outSeg (u + transportStep n) (a + transportStep n) (b + transportStep n) ⊆
      globalDomain := by
  have haU : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  rintro ⟨x, y⟩ ⟨rfl, hy⟩
  exact ⟨add_nonneg haU.1 (transport_step_pos n).le,
    by linarith only [haU.2, hy.1]⟩

/-- The simultaneously translated mixed density tends to the exact
canonical density at every domain point. -/
theorem transport_shift_radius_coeff_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun n => IsBVSolution.radiusCoeff (transportShiftFields d.rawFields n)
      p.1 p.2) atTop (𝓝 (IsBVSolution.radiusCoeff d.scalarRightFields p.1 p.2)) := by
  obtain ⟨hr, _, hm, hl, hn, _, _⟩ := transport_shift_fields_limit h hD d hp
  apply radius_coeff_tendsto hr hm hl hn (d.radius_pos h hp)
  exact lt_of_lt_of_le (by norm_num) (d.mass_geometry h p hp).1

/-- The simultaneous translation preserves the universal off-axis
majorant because it preserves the coordinate gap exactly. -/
theorem transport_shift_radius_coeff_bound
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) {δ : ℝ} (hδ : 0 < δ)
    (hgap : δ ≤ p.2 - p.1) (n : ℕ) :
    |IsBVSolution.radiusCoeff (transportShiftFields d.rawFields n) p.1 p.2| ≤ 9 / δ := by
  exact d.raw_radius_coeff_bound h (transport_shift_mem hp n) hδ (by
    simpa only [add_sub_add_right_eq_sub] using hgap)

/-- The incoming λ and outgoing ν primitives hold for the canonical
representatives at every closed null segment. No all-point derivative assertion at jumps is made. -/
theorem expansion_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.scalarRightFields.lam u v)
        (fun u => IsBVSolution.radiusCoeff d.scalarRightFields u v) a b) ∧
    ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.scalarRightFields.nu u)
        (IsBVSolution.radiusCoeff d.scalarRightFields u) a b := by
  obtain ⟨hlprim, hnprim⟩ := raw_expansion_primitive_limit h d
  have ht := fun p hp => transport_shift_fields_limit h hD d (p := p) hp
  constructor
  · intro v a b hab hs
    have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
    apply interval_primitive_limit_ae hab (fun n =>
      (hlprim (v + transportStep n) (a + transportStep n) (b + transportStep n)
        (by linarith only [hab]) (transportShift_inSeg hab hs n)).translate)
      (M := 9 / (v - b))
    · intro n t ht
      exact transport_shift_radius_coeff_bound h d (p := (t, v)) (hs ⟨ht, rfl⟩)
        (sub_pos.mpr hp.2) (by linarith only [ht.2]) n
    · exact (ht (a, v) (hs ⟨⟨le_rfl, hab⟩, rfl⟩)).2.2.2.1
    · exact (ht (b, v) hp).2.2.2.1
    · exact Eventually.of_forall (fun t ht =>
        transport_shift_radius_coeff_limit h hD d (p := (t, v)) (hs ⟨ht, rfl⟩))
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    apply interval_primitive_limit_ae hab (fun n =>
      (hnprim (u + transportStep n) (a + transportStep n) (b + transportStep n)
        (by linarith only [hab]) (transportShift_outSeg hab hs n)).translate)
      (M := 9 / (a - u))
    · intro n t ht
      exact transport_shift_radius_coeff_bound h d (p := (u, t)) (hs ⟨rfl, ht⟩)
        (sub_pos.mpr hp.2) (by linarith only [ht.1]) n
    · exact (ht (u, a) hp).2.2.2.2.1
    · exact (ht (u, b) (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)).2.2.2.2.1
    · exact Eventually.of_forall (fun t ht =>
        transport_shift_radius_coeff_limit h hD d (p := (u, t)) (hs ⟨rfl, ht⟩))

/-- The incoming α and outgoing β primitives hold for the same canonical
fields. The finite scalar
offset is retained in the dominating function. -/
theorem alpha_beta_transport_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.scalarRightFields.alpha u v)
        (fun u => IsBVSolution.radiusCoeff d.scalarRightFields u v *
          d.scalarRightFields.phi u v) a b) ∧
    ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.scalarRightFields.beta u)
        (fun v => IsBVSolution.radiusCoeff d.scalarRightFields u v *
          d.scalarRightFields.phi u v) a b := by
  obtain ⟨hαprim, hβprim⟩ := raw_alpha_beta_transport_limit h d
  have ht := fun p hp => transport_shift_fields_limit h hD d (p := p) hp
  constructor
  · intro v a b hab hs
    have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
    apply interval_primitive_limit_ae hab (fun n =>
      (hαprim (v + transportStep n) (a + transportStep n) (b + transportStep n)
        (by linarith only [hab]) (transportShift_inSeg hab hs n)).translate)
      (M := (9 / (v - b)) * (6 * D.toReal + C))
    · intro n t ht
      rw [abs_mul]
      exact mul_le_mul
        (transport_shift_radius_coeff_bound h d (p := (t, v)) (hs ⟨ht, rfl⟩)
          (sub_pos.mpr hp.2) (by linarith only [ht.2]) n)
        (d.scalar_amplitude h (transport_shift_mem (p := (t, v)) (hs ⟨ht, rfl⟩) n))
        (abs_nonneg _) (div_nonneg (by norm_num) (sub_pos.mpr hp.2).le)
    · exact (ht (a, v) (hs ⟨⟨le_rfl, hab⟩, rfl⟩)).2.2.2.2.2.1
    · exact (ht (b, v) hp).2.2.2.2.2.1
    · exact Eventually.of_forall (fun t ht =>
        (transport_shift_radius_coeff_limit h hD d (p := (t, v)) (hs ⟨ht, rfl⟩)).mul
          (transport_shift_fields_limit h hD d (p := (t, v)) (hs ⟨ht, rfl⟩)).2.1)
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    apply interval_primitive_limit_ae hab (fun n =>
      (hβprim (u + transportStep n) (a + transportStep n) (b + transportStep n)
        (by linarith only [hab]) (transportShift_outSeg hab hs n)).translate)
      (M := (9 / (a - u)) * (6 * D.toReal + C))
    · intro n t ht
      rw [abs_mul]
      exact mul_le_mul
        (transport_shift_radius_coeff_bound h d (p := (u, t)) (hs ⟨rfl, ht⟩)
          (sub_pos.mpr hp.2) (by linarith only [ht.1]) n)
        (d.scalar_amplitude h (transport_shift_mem (p := (u, t)) (hs ⟨rfl, ht⟩) n))
        (abs_nonneg _) (div_nonneg (by norm_num) (sub_pos.mpr hp.2).le)
    · exact (ht (u, a) hp).2.2.2.2.2.2
    · exact (ht (u, b) (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)).2.2.2.2.2.2
    · exact Eventually.of_forall (fun t ht =>
        (transport_shift_radius_coeff_limit h hD d (p := (u, t)) (hs ⟨rfl, ht⟩)).mul
          (transport_shift_fields_limit h hD d (p := (u, t)) (hs ⟨rfl, ht⟩)).2.1)

end ChristodoulouBV

end
