module

public import ChristodoulouBV.Existence.ScalarLimitRepresentatives
import Mathlib.Tactic

/-!
# The scalar right-representative fields

The canonical representatives are separate from the raw fields that retain
arbitrary initial datum values. For right-continuous initial data the
canonical outgoing representative has the same literal initial trace.
All four extra canonical right-continuity clauses hold for this one field record.
Stability of the remaining mixed equations is proved in the transport limit and final representative constructions.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The radius limit right expansions together with the right scalar derivatives,
on the same selected scalar, radius and mass carrier. -/
@[expose] noncomputable def RadiusLimitData.scalarRightFields {T : ℕ → Fields}
    (d : RadiusLimitData T) : Fields :=
  { d.rightFields with alpha := d.rightAlpha, beta := d.rightBeta }

/-- Right-continuous initial data keep their exact point values under
canonical right-v scalar-derivative selection. -/
theorem data_trace_limit_of_right_continuous
    {alpha₀ : ℝ → ℝ} {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n))
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a n v) atTop (𝓝 (alpha₀ v)))
    (hrc : ∀ v, 0 < v → ContinuousWithinAt alpha₀ (Ici v) v)
    (d : RadiusLimitData T) :
    ∀ v, 0 < v → d.scalarRightFields.r 0 v = v / 2 ∧
      d.scalarRightFields.alpha 0 v = alpha₀ v := by
  intro v hv
  refine ⟨d.initial_radius h hv, ?_⟩
  apply rightLim_eq_of_tendsto
  apply ((hrc v hv).mono Ioi_subset_Ici_self).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (data_trace_limit h hpoint d t (hv.trans ht)).2.symm

/-- The same canonical fields satisfy the four canonical right-continuity
clauses for λ, θ, ν and ζ at every domain point. -/
theorem scalar_right_fields_rightBV
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) : RightBVFields globalDomain d.scalarRightFields := by
  have hexp := right_expansions_continuous h hD d
  have hscalar := right_scalar_derivatives_continuous h hD d
  have hφ := d.scalar_continuousOn h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hexp p hp).1.mono (fun _ ht => ht.1)
  · intro p hp
    have hφout : ContinuousWithinAt (d.rawFields.phi p.1)
        {w | p.2 ≤ w ∧ (p.1, w) ∈ globalDomain} p.2 := by
      exact (hφ.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ ht => ht.2)) p.2 ⟨le_rfl, hp⟩
    exact ((hscalar p hp).1.mono (fun _ ht => ht.1)).sub
      (((hexp p hp).1.mono (fun _ ht => ht.1)).mul hφout)
  · intro p hp
    exact (hexp p hp).2.mono (fun _ ht => ht.1)
  · intro p hp
    have hφin : ContinuousWithinAt (fun u => d.rawFields.phi u p.2)
        {s | p.1 ≤ s ∧ (s, p.2) ∈ globalDomain} p.1 := by
      exact (hφ.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ht.2)) p.1 ⟨le_rfl, hp⟩
    exact ((hscalar p hp).2.mono (fun _ ht => ht.1)).sub
      (((hexp p hp).2.mono (fun _ ht => ht.1)).mul hφin)

/-- Both scalar primitives in the frozen `r * φ` shape hold for the
canonical field record, on every closed null segment. -/
theorem scalar_right_fields_primitives
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (fun v => d.scalarRightFields.r u v * d.scalarRightFields.phi u v)
        (d.scalarRightFields.alpha u) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.scalarRightFields.r u v * d.scalarRightFields.phi u v)
        (fun u => d.scalarRightFields.beta u v) a b := by
  obtain ⟨hout, hin⟩ := right_scalar_radius_primitive_limit h hD d
  constructor
  · intro u a b hab hs
    obtain ⟨hi, he⟩ := hout u a b hab hs
    refine ⟨hi, ?_⟩
    change d.radius (u, b) * d.rawFields.phi u b -
      d.radius (u, a) * d.rawFields.phi u a = _
    rw [d.radius_mul_scalar h (p := (u, b)) (hs ⟨rfl, ⟨hab, le_rfl⟩⟩),
      d.radius_mul_scalar h (p := (u, a)) (hs ⟨rfl, ⟨le_rfl, hab⟩⟩)]
    exact he
  · intro v a b hab hs
    obtain ⟨hi, he⟩ := hin v a b hab hs
    refine ⟨hi, ?_⟩
    change d.radius (b, v) * d.rawFields.phi b v -
      d.radius (a, v) * d.rawFields.phi a v = _
    rw [d.radius_mul_scalar h (p := (b, v)) (hs ⟨⟨hab, le_rfl⟩, rfl⟩),
      d.radius_mul_scalar h (p := (a, v)) (hs ⟨⟨le_rfl, hab⟩, rfl⟩)]
    exact he

/-- All six universal geometry bounds refer to the same canonical scalar
field record used for the initial trace and canonical right-continuity clauses. -/
theorem scalar_right_fields_geometry
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ d.scalarRightFields.lam p.1 p.2 ∧
      d.scalarRightFields.lam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -d.scalarRightFields.nu p.1 p.2 ∧
      -d.scalarRightFields.nu p.1 p.2 ≤ 2 / 3 ∧
      (2 / 3 : ℝ) ≤ 1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ∧
      1 - 2 * d.scalarRightFields.m p.1 p.2 / d.scalarRightFields.r p.1 p.2 ≤ 1 :=
  radius_limit_geometry h hD d

end ChristodoulouBV

end
