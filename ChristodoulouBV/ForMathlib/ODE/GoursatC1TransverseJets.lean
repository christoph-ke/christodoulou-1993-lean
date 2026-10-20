module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Transverse
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Transverse jets of characteristic integrals

A jointly continuous vertical derivative of an integrand gives a continuous
vertical jet of its horizontal primitive on a closed rectangle. The derivative
at the top and bottom edges is relative to the closed vertical interval.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A horizontal characteristic integral has a continuous vertical jet when
the parameter derivative of its integrand is continuous on the rectangle.
The vertical derivative of the datum may be prescribed only on its interval. -/
theorem exists_continuous_vertical_jet_of_horizontal_integral
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ < v₁)
    (x₀ x₀' : ℝ → E) (F Fv : ℝ × ℝ → E)
    (hF : ContinuousOn F (rectangle u₀ u₁ v₀ v₁))
    (hFv : ContinuousOn Fv (rectangle u₀ u₁ v₀ v₁))
    (hx₀' : ContinuousOn x₀' (Icc v₀ v₁))
    (hdx₀ : ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt x₀ (x₀' v) (Icc v₀ v₁) v)
    (hderiv : ∀ s ∈ Icc u₀ u₁, ∀ v ∈ Ioo v₀ v₁,
      HasDerivAt (fun t => F (s, t)) (Fv (s, v)) v) :
    ∃ P : C(rectangle u₀ u₁ v₀ v₁, E),
      (∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        P ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
          x₀' v + ∫ s in u₀..u, Fv (s, v)) ∧
      ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt
          (fun t => x₀ t + ∫ s in u₀..u, F (s, t))
          (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩)
          (Icc v₀ v₁) v := by
  let Fc : ℝ × ℝ → E := fun p => Fv (clippedPoint hu hv.le p).1
  have hFc : Continuous Fc := hFv.comp_continuous
    ((continuous_clippedPoint hu hv.le).subtype_val)
    (fun p => (clippedPoint hu hv.le p).2)
  have hI : Continuous (fun p : ℝ × ℝ =>
      ∫ s in u₀..p.1, Fc (s, p.2)) := by
    have hfield : Continuous (fun q : (ℝ × ℝ) × ℝ => Fc (q.2, q.1.2)) := by
      have hp : Continuous (fun q : (ℝ × ℝ) × ℝ => (q.2, q.1.2)) :=
        continuous_snd.prodMk (continuous_snd.comp continuous_fst)
      exact hFc.comp hp
    exact continuous_parametric_intervalIntegral_of_continuous hfield continuous_fst
  have hfirst : ContinuousOn (fun p : ℝ × ℝ => x₀' p.2)
      (rectangle u₀ u₁ v₀ v₁) :=
    hx₀'.comp continuous_snd.continuousOn (by
      intro p hp
      simpa only [rectangle, mem_prod] using hp.2)
  have hPcont : ContinuousOn (fun p : ℝ × ℝ =>
      x₀' p.2 + ∫ s in u₀..p.1, Fc (s, p.2))
      (rectangle u₀ u₁ v₀ v₁) := hfirst.add hI.continuousOn
  let P : C(rectangle u₀ u₁ v₀ v₁, E) :=
    ⟨fun p => x₀' p.1.2 + ∫ s in u₀..p.1.1, Fc (s, p.1.2),
      hPcont.domRestrict⟩
  refine ⟨P, ?_, ?_⟩
  · intro u hu' v hv'
    change x₀' v + ∫ s in u₀..u, Fc (s, v) = _
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu⟩ hu' hs
    have hq : (s, v) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI hv'
    have hclip := clippedPoint_eq_self hu hv.le ⟨(s, v), hq⟩
    simpa only [Fc] using congrArg (fun q : rectangle u₀ u₁ v₀ v₁ => Fv q.1) hclip
  · intro u hu' v hv'
    have hFswap : ContinuousOn (fun p : ℝ × ℝ => F (p.2, p.1))
        (Icc v₀ v₁ ×ˢ Icc u₀ u₁) :=
      hF.comp continuous_swap.continuousOn
        (mapsTo_swap_prod (Icc v₀ v₁) (Icc u₀ u₁))
    have hFvswap : ContinuousOn (fun p : ℝ × ℝ => Fv (p.2, p.1))
        (Icc v₀ v₁ ×ˢ Icc u₀ u₁) :=
      hFv.comp continuous_swap.continuousOn
        (mapsTo_swap_prod (Icc v₀ v₁) (Icc u₀ u₁))
    have hInt := intervalIntegral.hasDerivWithinAt_integral_of_continuousOn_rectangle_banach
      hv hv' hu' hFswap hFvswap
      (by
        intro t ht s hs
        exact hderiv s hs t ht)
    have hsum := (hdx₀ v hv').add hInt
    have hP : P ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
        x₀' v + ∫ s in u₀..u, Fv (s, v) := by
      change x₀' v + ∫ s in u₀..u, Fc (s, v) = _
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Icc u₀ u₁ :=
        Set.uIcc_subset_Icc ⟨le_rfl, hu⟩ hu' hs
      have hq : (s, v) ∈ rectangle u₀ u₁ v₀ v₁ :=
        pair_mem_rectangle hsI hv'
      have hclip := clippedPoint_eq_self hu hv.le ⟨(s, v), hq⟩
      simpa only [Fc] using congrArg (fun q : rectangle u₀ u₁ v₀ v₁ => Fv q.1) hclip
    rw [hP]
    convert hsum using 1

/-- A vertical characteristic integral has a continuous horizontal jet
throughout the closed rectangle, including both horizontal edges. -/
theorem exists_continuous_horizontal_jet_of_vertical_integral
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ ≤ v₁)
    (y₀ y₀' : ℝ → E) (F Fu : ℝ × ℝ → E)
    (hF : ContinuousOn F (rectangle u₀ u₁ v₀ v₁))
    (hFu : ContinuousOn Fu (rectangle u₀ u₁ v₀ v₁))
    (hy₀' : ContinuousOn y₀' (Icc u₀ u₁))
    (hdy₀ : ∀ u ∈ Icc u₀ u₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc u₀ u₁) u)
    (hderiv : ∀ t ∈ Icc v₀ v₁, ∀ u ∈ Ioo u₀ u₁,
      HasDerivAt (fun s => F (s, t)) (Fu (u, t)) u) :
    ∃ Q : C(rectangle u₀ u₁ v₀ v₁, E),
      (∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        Q ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
          y₀' u + ∫ t in v₀..v, Fu (u, t)) ∧
      ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt
          (fun s => y₀ s + ∫ t in v₀..v, F (s, t))
          (Q ⟨(u, v), pair_mem_rectangle hu' hv'⟩)
          (Icc u₀ u₁) u := by
  have hFswap : ContinuousOn (fun p : ℝ × ℝ => F (p.2, p.1))
      (rectangle v₀ v₁ u₀ u₁) :=
    hF.comp continuous_swap.continuousOn (by
      intro p hp
      simpa only [rectangle, mem_prod] using And.symm hp)
  have hFuswap : ContinuousOn (fun p : ℝ × ℝ => Fu (p.2, p.1))
      (rectangle v₀ v₁ u₀ u₁) :=
    hFu.comp continuous_swap.continuousOn (by
      intro p hp
      simpa only [rectangle, mem_prod] using And.symm hp)
  obtain ⟨P, hP, hPderiv⟩ :=
    exists_continuous_vertical_jet_of_horizontal_integral
      hv hu y₀ y₀' (fun p => F (p.2, p.1))
      (fun p => Fu (p.2, p.1)) hFswap hFuswap hy₀' hdy₀
      (by
        intro t ht u hu'
        exact hderiv t ht u hu')
  let σ : C(rectangle u₀ u₁ v₀ v₁, rectangle v₀ v₁ u₀ u₁) :=
    ⟨fun p => ⟨(p.1.2, p.1.1), by
        have hp := p.2
        simpa only [rectangle, mem_prod] using And.symm hp⟩,
      Continuous.subtype_mk
        (continuous_swap.comp continuous_subtype_val)
        (fun p => by
          have hp := p.2
          simpa only [rectangle, mem_prod, Function.comp_def, Prod.swap]
            using And.symm hp)⟩
  let Q : C(rectangle u₀ u₁ v₀ v₁, E) := P.comp σ
  refine ⟨Q, ?_, ?_⟩
  · intro u hu' v hv'
    change P ⟨(v, u), pair_mem_rectangle hv' hu'⟩ = _
    exact hP v hv' u hu'
  · intro u hu' v hv'
    change HasDerivWithinAt
      (fun s => y₀ s + ∫ t in v₀..v, F (s, t))
      (P ⟨(v, u), pair_mem_rectangle hv' hu'⟩) (Icc u₀ u₁) u
    exact hPderiv v hv' u hu'

end Goursat

end
