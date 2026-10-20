module

public import ChristodoulouBV.Existence.RadiusLimitPrimitives
public import ChristodoulouBV.ForMathlib.BoundedVariation.ExtendIcc
import Mathlib.Tactic

/-!
# Right representatives of the expansion limits

The raw Helly limits preserve pointwise convergence. Their right traces give
the right-v λ and right-u ν representatives required by the quantitative existence construction. Both radius
primitives hold for these representatives. Stability of the remaining
equations and scalar representatives is proved in the final representative construction.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The right-v representative of the outgoing expansion limit. -/
@[expose] noncomputable def RadiusLimitData.rightLam {T : ℕ → Fields}
    (d : RadiusLimitData T) (u : ℝ) : ℝ → ℝ := (d.lam u).rightLim

/-- The right-u representative of the incoming expansion limit. -/
@[expose] noncomputable def RadiusLimitData.rightNu {T : ℕ → Fields}
    (d : RadiusLimitData T) (u v : ℝ) : ℝ := (fun s => d.nu s v).rightLim u

/-- A BV function on a closed interval agrees almost everywhere there
with its right-limit representative. -/
theorem rightLim_ae_eq_on_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) :
    ∀ᵐ x : ℝ, x ∈ Icc a b → f.rightLim x = f x := by
  let E := Function.extendIcc f hab
  have hE : BoundedVariationOn E univ :=
    BoundedVariationOn.extendIcc_boundedVariationOn hab hf
  filter_upwards [hE.countable_not_continuousAt.ae_notMem volume,
    volume.ae_ne a, volume.ae_ne b] with x hx hxa hxb hxI
  have hxE : ContinuousAt E x := Classical.not_not.mp hx
  have hxi : x ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hxI.1 hxa.symm, lt_of_le_of_ne hxI.2 hxb⟩
  have he : f =ᶠ[𝓝 x] E := by
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
    exact (BoundedVariationOn.extendIcc_of_mem hab ⟨hy.1.le, hy.2.le⟩).symm
  exact (hxE.congr_of_eventuallyEq he).continuousWithinAt.rightLim_eq

/-- Taking the right representative of a BV density preserves its exact
interval primitive, including the interval endpoints. -/
theorem interval_primitive_rightLim {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : IntervalPrimitive F f a b) (hf : BoundedVariationOn f (Icc a b)) :
    IntervalPrimitive F f.rightLim a b := by
  have hae : ∀ᵐ x : ℝ, x ∈ uIoc a b → f.rightLim x = f x := by
    filter_upwards [rightLim_ae_eq_on_interval hab hf] with x hx hxI
    rw [uIoc_of_le hab] at hxI
    exact hx ⟨hxI.1.le, hxI.2⟩
  refine ⟨?_, ?_⟩
  · apply hp.1.congr_ae
    exact (ae_restrict_iff' measurableSet_uIoc).mpr
      (hae.mono fun _ hx hxI => (hx hxI).symm)
  · rw [intervalIntegral.integral_congr_ae hae]
    exact hp.2

/-- Both right traces exist at every admissible point, and are continuous
from the right on their respective null sections. -/
theorem right_expansions_continuous
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      ContinuousWithinAt (d.rightLam p.1) (Ici p.2) p.2 ∧
      ContinuousWithinAt (fun u => d.rightNu u p.2) (Ici p.1) p.1 := by
  have hV : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  obtain ⟨hlam, hnu, _⟩ := expansions_limit h d
  intro p hp
  have hlamBV : BoundedVariationOn (d.lam p.1) (Ioi p.1) :=
    ne_of_lt ((hlam p.1 hp.1).trans_lt hV)
  have hν : BoundedVariationOn (fun u => d.nu u p.2) (Ico 0 p.2) :=
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

/-- Right representatives retain the universal expansion variation bound,
including the initial endpoint of each incoming section. -/
theorem right_expansions_variation
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → eVariationOn (d.rightLam u) (Ioi u) ≤ s4UniversalC * D ^ 2) ∧
    ∀ v, 0 < v → eVariationOn (fun u => d.rightNu u v) (Ico 0 v) ≤ s4UniversalC * D ^ 2 := by
  obtain ⟨hlam, hnu, _⟩ := expansions_limit h d
  constructor
  · intro u hu
    exact (eVariationOn.eVariationOn_rightLim_le isOpen_Ioi).trans (hlam u hu)
  · intro v hv
    rw [eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hv
      (right_expansions_continuous h hD d (0, v) ⟨le_rfl, hv⟩).2]
    exact (eVariationOn.eVariationOn_rightLim_le isOpen_Ioo).trans
      ((eVariationOn.mono _ Ioo_subset_Ico_self).trans (hnu v hv))

/-- All four quantitative expansion inequalities hold for the canonical right
representatives at every point, including `u = 0`. -/
theorem right_expansions_geometry
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ d.rightLam p.1 p.2 ∧ d.rightLam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -d.rightNu p.1 p.2 ∧ -d.rightNu p.1 p.2 ≤ 2 / 3 := by
  have hV : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  obtain ⟨hlam, hnu, hgeom⟩ := expansions_limit h d
  intro p hp
  have hlamBV : BoundedVariationOn (d.lam p.1) (Ioi p.1) :=
    ne_of_lt ((hlam p.1 hp.1).trans_lt hV)
  have hν : BoundedVariationOn (fun u => d.nu u p.2) (Ico 0 p.2) :=
    ne_of_lt ((hnu p.2 (hp.1.trans_lt hp.2)).trans_lt hV)
  have htlam : Tendsto (d.lam p.1) (𝓝[>] p.2) (𝓝 (d.rightLam p.1 p.2)) := by
    apply tendsto_rightLim_of_tendsto
    have ht := hlamBV.exists_tendsto_right p.2
    have he : Ioi p.1 ∩ Ioi p.2 = Ioi p.2 :=
      inter_eq_right.mpr (Ioi_subset_Ioi hp.2.le)
    simpa only [he] using ht
  have htν := tendsto_rightLim_of_tendsto (hν.exists_tendsto_right_Ico hp)
  have hout : ∀ᶠ t in 𝓝[>] p.2,
      (1 / 3 : ℝ) ≤ d.lam p.1 t ∧ d.lam p.1 t ≤ 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨(hgeom (p.1, t) ⟨hp.1, hp.2.trans ht⟩).1,
      (hgeom (p.1, t) ⟨hp.1, hp.2.trans ht⟩).2.1⟩
  have hin : ∀ᶠ t in 𝓝[>] p.1,
      (1 / 3 : ℝ) ≤ -d.nu t p.2 ∧ -d.nu t p.2 ≤ 2 / 3 := by
    filter_upwards [Ioo_mem_nhdsGT hp.2] with t ht
    exact ⟨(hgeom (t, p.2) ⟨hp.1.trans ht.1.le, ht.2⟩).2.2.1,
      (hgeom (t, p.2) ⟨hp.1.trans ht.1.le, ht.2⟩).2.2.2⟩
  exact ⟨ge_of_tendsto htlam (hout.mono fun _ ht => ht.1),
    le_of_tendsto htlam (hout.mono fun _ ht => ht.2),
    ge_of_tendsto htν.neg (hin.mono fun _ ht => ht.1),
    le_of_tendsto htν.neg (hin.mono fun _ ht => ht.2)⟩

/-- On every closed outgoing and incoming segment, the same smooth
subsequence converges almost everywhere to the canonical right expansions.
The separate raw limits still converge at every point. -/
theorem right_expansions_segment_ae_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      ∀ᵐ t : ℝ, t ∈ Icc a b →
        Tendsto (fun n => (T (d.subsequence n)).lam u t) atTop (𝓝 (d.rightLam u t))) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      ∀ᵐ t : ℝ, t ∈ Icc a b →
        Tendsto (fun n => (T (d.subsequence n)).nu t v) atTop (𝓝 (d.rightNu t v)) := by
  have hV : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  obtain ⟨hlam, hnu, _⟩ := expansions_limit h d
  constructor
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    have hBV := BoundedVariationOn.mono
      (ne_of_lt ((hlam u hp.1).trans_lt hV) : BoundedVariationOn (d.lam u) (Ioi u))
      (fun t ht => (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)).2)
    filter_upwards [rightLim_ae_eq_on_interval hab hBV] with t ht htI
    change Tendsto _ _ (𝓝 ((d.lam u).rightLim t))
    rw [ht htI]
    exact d.lam_limit (u, t) (hs ⟨rfl, htI⟩)
  · intro v a b hab hs
    have hp : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
    have hBV := BoundedVariationOn.mono
      (ne_of_lt ((hnu v (hp.1.trans_lt hp.2)).trans_lt hV) :
        BoundedVariationOn (fun u => d.nu u v) (Ico 0 v))
      (fun t ht => (show (t, v) ∈ globalDomain from hs ⟨ht, rfl⟩))
    filter_upwards [rightLim_ae_eq_on_interval hab hBV] with t ht htI
    change Tendsto _ _ (𝓝 ((fun u => d.nu u v).rightLim t))
    rw [ht htI]
    exact d.nu_limit (t, v) (hs ⟨htI, rfl⟩)

/-- Both frozen radius primitives also hold for the canonical right representatives. -/
theorem right_radius_primitive_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (fun v => d.radius (u, v)) (d.rightLam u) a b) ∧
    ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => d.radius (u, v)) (fun u => d.rightNu u v) a b := by
  have hV : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  obtain ⟨hlam, hnu, _⟩ := expansions_limit h d
  obtain ⟨hout, hin⟩ := radius_primitive_limit h hD d
  constructor
  · intro u a b hab hs
    have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
    apply interval_primitive_rightLim hab (hout u a b hab hs)
    exact BoundedVariationOn.mono
      (ne_of_lt ((hlam u hp.1).trans_lt hV) : BoundedVariationOn (d.lam u) (Ioi u))
      (fun t ht => (hs (show (u, t) ∈ outSeg u a b from ⟨rfl, ht⟩)).2)
  · intro v a b hab hs
    have hp : (a, v) ∈ globalDomain := hs ⟨⟨le_rfl, hab⟩, rfl⟩
    apply interval_primitive_rightLim hab (hin v a b hab hs)
    exact BoundedVariationOn.mono
      (ne_of_lt ((hnu v (hp.1.trans_lt hp.2)).trans_lt hV) :
        BoundedVariationOn (fun u => d.nu u v) (Ico 0 v))
      (fun t ht => (show (t, v) ∈ globalDomain from hs ⟨ht, rfl⟩))

end ChristodoulouBV

end
