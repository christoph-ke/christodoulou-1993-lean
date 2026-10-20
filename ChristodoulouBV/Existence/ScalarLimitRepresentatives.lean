module

public import ChristodoulouBV.Existence.ScalarLimitPrimitives
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Right representatives of the scalar derivative limits

Raw limits preserve arbitrary datum values. Their canonical right traces
have the canonical representative conventions: right-v α and right-u β.
Convergence to these traces is sectionwise almost everywhere, while raw
convergence remains pointwise everywhere.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The canonical right-v representative of the outgoing scalar derivative. -/
@[expose] noncomputable def RadiusLimitData.rightAlpha {T : ℕ → Fields}
    (d : RadiusLimitData T) (u : ℝ) : ℝ → ℝ := (d.alpha u).rightLim

/-- The canonical right-u representative of the incoming scalar derivative. -/
@[expose] noncomputable def RadiusLimitData.rightBeta {T : ℕ → Fields}
    (d : RadiusLimitData T) (u v : ℝ) : ℝ := (fun s => d.beta s v).rightLim u

/-- Both canonical scalar derivative representatives are continuous from
the right at every point, including the initial edge. -/
theorem right_scalar_derivatives_continuous
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      ContinuousWithinAt (d.rightAlpha p.1) (Ici p.2) p.2 ∧
      ContinuousWithinAt (fun u => d.rightBeta u p.2) (Ici p.1) p.1 := by
  have hV := lt_top_iff_ne_top.mpr (scalarVariationBound_ne_top hD C)
  obtain ⟨_, hlam, hnu, _⟩ := alpha_beta_limit h d
  intro p hp
  have hlamBV : BoundedVariationOn (d.alpha p.1) (Ioi p.1) :=
    ne_of_lt ((hlam p.1 hp.1).trans_lt hV)
  have hν : BoundedVariationOn (fun u => d.beta u p.2) (Ico 0 p.2) :=
    ne_of_lt ((hnu p.2 (hp.1.trans_lt hp.2)).trans_lt hV)
  constructor
  · apply continuousWithinAt_rightLim_Ici
    apply tendsto_rightLim_of_tendsto
    have ht := hlamBV.exists_tendsto_right p.2
    have he : Ioi p.1 ∩ Ioi p.2 = Ioi p.2 :=
      inter_eq_right.mpr (Ioi_subset_Ioi hp.2.le)
    simpa only [he] using ht
  · exact continuousWithinAt_rightLim_Ici
      (tendsto_rightLim_of_tendsto (hν.exists_tendsto_right_Ico hp))

/-- Right representatives retain the raw variation bound with its offset,
including the initial endpoint of the incoming section. -/
theorem right_scalar_derivatives_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → eVariationOn (d.rightAlpha u) (Ioi u) ≤ scalarVariationBound D C) ∧
    ∀ v, 0 < v → eVariationOn (fun u => d.rightBeta u v) (Ico 0 v) ≤ scalarVariationBound D C := by
  obtain ⟨_, hlam, hnu, _⟩ := alpha_beta_limit h d
  constructor
  · intro u hu
    exact (eVariationOn.eVariationOn_rightLim_le isOpen_Ioi).trans (hlam u hu)
  · intro v hv
    rw [eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hv
      (right_scalar_derivatives_continuous h hD d (0, v) ⟨le_rfl, hv⟩).2]
    exact (eVariationOn.eVariationOn_rightLim_le isOpen_Ioo).trans
      ((eVariationOn.mono _ Ioo_subset_Ico_self).trans (hnu v hv))

/-- The same smooth subsequence converges to the canonical scalar
derivatives almost everywhere on every closed null segment. -/
theorem right_scalar_derivatives_segment_ae_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      ∀ᵐ t : ℝ, t ∈ Icc a b →
        Tendsto (fun n => (T (d.subsequence n)).alpha u t) atTop (𝓝 (d.rightAlpha u t))) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      ∀ᵐ t : ℝ, t ∈ Icc a b →
        Tendsto (fun n => (T (d.subsequence n)).beta t v) atTop (𝓝 (d.rightBeta t v)) := by
  have hV := lt_top_iff_ne_top.mpr (scalarVariationBound_ne_top hD C)
  obtain ⟨_, hlam, hnu, _⟩ := alpha_beta_limit h d
  constructor
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    have hBV := BoundedVariationOn.mono
      (ne_of_lt ((hlam u hp.1).trans_lt hV) : BoundedVariationOn (d.alpha u) (Ioi u))
      (fun t ht => (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)).2)
    filter_upwards [rightLim_ae_eq_on_interval hab hBV] with t ht htI
    change Tendsto _ _ (𝓝 ((d.alpha u).rightLim t))
    rw [ht htI]
    exact d.alpha_limit (u, t) (hs ⟨rfl, htI⟩)
  · intro v a b hab hs
    have hp : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
    have hBV := BoundedVariationOn.mono
      (ne_of_lt ((hnu v (hp.1.trans_lt hp.2)).trans_lt hV) :
        BoundedVariationOn (fun u => d.beta u v) (Ico 0 v))
      (fun t ht => (show (t, v) ∈ globalDomain from hs ⟨ht, rfl⟩))
    filter_upwards [rightLim_ae_eq_on_interval hab hBV] with t ht htI
    change Tendsto _ _ (𝓝 ((fun u => d.beta u v).rightLim t))
    rw [ht htI]
    exact d.beta_limit (t, v) (hs ⟨htI, rfl⟩)

/-- The canonical right scalar derivatives satisfy both exact
scalar-radius interval primitives. -/
theorem right_scalar_radius_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (fun v => d.scalarRadius (u, v)) (d.rightAlpha u) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.scalarRadius (u, v)) (fun u => d.rightBeta u v) a b := by
  have hV := lt_top_iff_ne_top.mpr (scalarVariationBound_ne_top hD C)
  obtain ⟨_, hlam, hnu, _⟩ := alpha_beta_limit h d
  obtain ⟨hout, hin⟩ := scalar_radius_primitive_limit h hD d
  constructor
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    apply interval_primitive_rightLim hab (hout u a b hab hs)
    exact BoundedVariationOn.mono
      (ne_of_lt ((hlam u hp.1).trans_lt hV) : BoundedVariationOn (d.alpha u) (Ioi u))
      (fun t ht => (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)).2)
  · intro v a b hab hs
    have hp : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
    apply interval_primitive_rightLim hab (hin v a b hab hs)
    exact BoundedVariationOn.mono
      (ne_of_lt ((hnu v (hp.1.trans_lt hp.2)).trans_lt hV) :
        BoundedVariationOn (fun u => d.beta u v) (Ico 0 v))
      (fun t ht => (show (t, v) ∈ globalDomain from hs ⟨ht, rfl⟩))

end ChristodoulouBV

end
