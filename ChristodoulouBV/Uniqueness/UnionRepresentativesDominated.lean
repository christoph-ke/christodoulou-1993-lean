module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesTransportLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing incoming integrals to a mixed terminal level

An eventual uniform bound and pointwise convergence on a compact incoming
segment give both integrability of the limiting density and convergence of
the interval integrals.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Dominated convergence for a family of interval-integrable real densities
as an outgoing parameter approaches a terminal level from below. -/
theorem intervalIntegrable_and_tendsto_integral_of_eventually_bounded
    {F : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {v a b : ℝ} (hab : a ≤ b)
    (hInt : ∀ᶠ t in 𝓝[<] v, IntervalIntegrable (F t) volume a b)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b, |F t s| ≤ C)
    (hLim : ∀ s ∈ Icc a b,
      Tendsto (fun t => F t s) (𝓝[<] v) (𝓝 (f s))) :
    IntervalIntegrable f volume a b ∧
      Tendsto (fun t => ∫ s in a..b, F t s) (𝓝[<] v)
        (𝓝 (∫ s in a..b, f s)) := by
  classical
  obtain ⟨C, hC, hBoundEv⟩ := hBound
  have hMeasEv : ∀ᶠ t in 𝓝[<] v,
      AEStronglyMeasurable (F t) (volume.restrict (Ι a b)) := by
    filter_upwards [hInt] with t ht
    exact ht.aestronglyMeasurable_restrict_uIoc
  have hBoundAE : ∀ᶠ t in 𝓝[<] v,
      ∀ᵐ s ∂volume, s ∈ Ι a b → ‖F t s‖ ≤ C := by
    filter_upwards [hBoundEv] with t ht
    exact Filter.Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hab] at hs
      simpa only [Real.norm_eq_abs] using ht s ⟨hs.1.le, hs.2⟩
  have hLimAE : ∀ᵐ s ∂volume, s ∈ Ι a b →
      Tendsto (fun t => F t s) (𝓝[<] v) (𝓝 (f s)) :=
    Filter.Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hab] at hs
      exact hLim s ⟨hs.1.le, hs.2⟩
  have hIntegralLimit :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := fun _ => C)
      hMeasEv hBoundAE intervalIntegrable_const hLimAE
  let F' : ℝ → ℝ → ℝ := fun t s =>
    if h : IntervalIntegrable (F t) volume a b then F t s else 0
  have hMeasAll (t : ℝ) :
      AEStronglyMeasurable (F' t) (volume.restrict (Ι a b)) := by
    by_cases ht : IntervalIntegrable (F t) volume a b
    · simpa only [F', ht, dite_true] using
        ht.aestronglyMeasurable_restrict_uIoc
    · simp only [F', ht, dite_false]
      exact aestronglyMeasurable_const
  have hLimAll : ∀ᵐ s ∂volume.restrict (Ι a b),
      Tendsto (fun t => F' t s) (𝓝[<] v) (𝓝 (f s)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hLimAE] with s hs hmem
    have heq : ∀ᶠ t in 𝓝[<] v, F' t s = F t s :=
      hInt.mono (fun t ht => by simp [F', ht])
    exact (hs hmem).congr' (heq.mono fun _ h => h.symm)
  have hMeasF : AEStronglyMeasurable f (volume.restrict (Ι a b)) :=
    aestronglyMeasurable_of_tendsto_ae (𝓝[<] v) hMeasAll hLimAll
  have hBoundF : ∀ᵐ s ∂volume.restrict (Ι a b), ‖f s‖ ≤ C := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hLimAE] with s hs hmem
    have hboundS : ∀ᶠ t in 𝓝[<] v, ‖F t s‖ ≤ C := by
      filter_upwards [hBoundEv] with t ht
      rw [uIoc_of_le hab] at hmem
      simpa only [Real.norm_eq_abs] using ht s ⟨hmem.1.le, hmem.2⟩
    exact le_of_tendsto (hs hmem).norm hboundS
  have hCInt : Integrable (fun _ : ℝ => C) (volume.restrict (Ι a b)) := by
    rw [uIoc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      intervalIntegrable_const
  have hfInt : Integrable f (volume.restrict (Ι a b)) :=
    hCInt.mono' hMeasF hBoundF
  refine ⟨?_, hIntegralLimit⟩
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (by simpa only [uIoc_of_le hab, IntegrableOn] using hfInt)

/-- The same terminal dominated convergence result with an integrable
spatial bound, used for the incoming scalar-radius density. -/
theorem intervalIntegrable_and_tendsto_integral_of_eventually_dominated
    {F : ℝ → ℝ → ℝ} {f g : ℝ → ℝ} {v a b : ℝ} (hab : a ≤ b)
    (hInt : ∀ᶠ t in 𝓝[<] v, IntervalIntegrable (F t) volume a b)
    (hgInt : IntervalIntegrable g volume a b)
    (hBound : ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b, |F t s| ≤ g s)
    (hLim : ∀ s ∈ Icc a b,
      Tendsto (fun t => F t s) (𝓝[<] v) (𝓝 (f s))) :
    IntervalIntegrable f volume a b ∧
      Tendsto (fun t => ∫ s in a..b, F t s) (𝓝[<] v)
        (𝓝 (∫ s in a..b, f s)) := by
  classical
  have hMeasEv : ∀ᶠ t in 𝓝[<] v,
      AEStronglyMeasurable (F t) (volume.restrict (Ι a b)) := by
    filter_upwards [hInt] with t ht
    exact ht.aestronglyMeasurable_restrict_uIoc
  have hBoundAE : ∀ᶠ t in 𝓝[<] v,
      ∀ᵐ s ∂volume, s ∈ Ι a b → ‖F t s‖ ≤ g s := by
    filter_upwards [hBound] with t ht
    exact Filter.Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hab] at hs
      simpa only [Real.norm_eq_abs] using ht s ⟨hs.1.le, hs.2⟩
  have hLimAE : ∀ᵐ s ∂volume, s ∈ Ι a b →
      Tendsto (fun t => F t s) (𝓝[<] v) (𝓝 (f s)) :=
    Filter.Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hab] at hs
      exact hLim s ⟨hs.1.le, hs.2⟩
  have hIntegralLimit :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := g)
      hMeasEv hBoundAE hgInt hLimAE
  let F' : ℝ → ℝ → ℝ := fun t s =>
    if h : IntervalIntegrable (F t) volume a b then F t s else 0
  have hMeasAll (t : ℝ) :
      AEStronglyMeasurable (F' t) (volume.restrict (Ι a b)) := by
    by_cases ht : IntervalIntegrable (F t) volume a b
    · simpa only [F', ht, dite_true] using
        ht.aestronglyMeasurable_restrict_uIoc
    · simp only [F', ht, dite_false]
      exact aestronglyMeasurable_const
  have hLimAll : ∀ᵐ s ∂volume.restrict (Ι a b),
      Tendsto (fun t => F' t s) (𝓝[<] v) (𝓝 (f s)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hLimAE] with s hs hmem
    have heq : ∀ᶠ t in 𝓝[<] v, F' t s = F t s :=
      hInt.mono (fun t ht => by simp [F', ht])
    exact (hs hmem).congr' (heq.mono fun _ h => h.symm)
  have hMeasF : AEStronglyMeasurable f (volume.restrict (Ι a b)) :=
    aestronglyMeasurable_of_tendsto_ae (𝓝[<] v) hMeasAll hLimAll
  have hBoundF : ∀ᵐ s ∂volume.restrict (Ι a b), ‖f s‖ ≤ g s := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hLimAE] with s hs hmem
    have hboundS : ∀ᶠ t in 𝓝[<] v, ‖F t s‖ ≤ g s := by
      filter_upwards [hBound] with t ht
      rw [uIoc_of_le hab] at hmem
      simpa only [Real.norm_eq_abs] using ht s ⟨hmem.1.le, hmem.2⟩
    exact le_of_tendsto (hs hmem).norm hboundS
  have hgInt' : Integrable g (volume.restrict (Ι a b)) := by
    rw [uIoc_of_le hab]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hgInt
  have hfInt : Integrable f (volume.restrict (Ι a b)) :=
    hgInt'.mono' hMeasF hBoundF
  refine ⟨?_, hIntegralLimit⟩
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (by simpa only [uIoc_of_le hab, IntegrableOn] using hfInt)

end ChristodoulouBV.Uniqueness

end
