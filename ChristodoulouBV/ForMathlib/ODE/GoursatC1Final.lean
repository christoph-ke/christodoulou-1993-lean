module

public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Iterates
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Continuous coordinate jets on a closed rectangle

Continuous horizontal and vertical derivatives determine a full first jet on a
nondegenerate rectangle, including its boundary.
-/

public section

open Set Filter
open scoped Topology

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem continuousOn_coprod_coordinate_jets
    {s : Set (ℝ × ℝ)} (L : E → ℝ →L[ℝ] E)
    (hL : Continuous L) (fu fv : ℝ × ℝ → E)
    (hfu : ContinuousOn fu s) (hfv : ContinuousOn fv s) :
    ContinuousOn (fun p => (L (fu p)).coprod (L (fv p))) s := by
  have h₁ : ContinuousOn (fun p => L (fu p)) s := hL.comp_continuousOn hfu
  have h₂ : ContinuousOn (fun p => L (fv p)) s := hL.comp_continuousOn hfv
  exact (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := ℝ)
    (G := E) ℝ).continuous.comp_continuousOn (h₁.prodMk h₂)

/-- Continuous coordinate derivatives on a closed rectangle give `C¹` regularity.
The derivatives in the hypotheses are relative to the closed coordinate intervals. -/
theorem contDiffOn_one_of_continuous_coordinate_jets
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    (f : ℝ × ℝ → E) (fu fv : ℝ × ℝ → E)
    (hf : ContinuousOn f (rectangle u₀ u₁ v₀ v₁))
    (hfu : ContinuousOn fu (rectangle u₀ u₁ v₀ v₁))
    (hfv : ContinuousOn fv (rectangle u₀ u₁ v₀ v₁))
    (hdu : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun s => f (s, v)) (fu (u, v)) (Icc u₀ u₁) u)
    (hdv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun t => f (u, t)) (fv (u, v)) (Icc v₀ v₁) v) :
    ContDiffOn ℝ 1 f (rectangle u₀ u₁ v₀ v₁) := by
  let L : E → ℝ →L[ℝ] E :=
    fun x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) x
  let J : ℝ × ℝ → ℝ × ℝ →L[ℝ] E :=
    fun p => (L (fu p)).coprod (L (fv p))
  have hL : Continuous L :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous
  have hJ : ContinuousOn J (rectangle u₀ u₁ v₀ v₁) :=
    continuousOn_coprod_coordinate_jets L hL fu fv hfu hfv
  have hconv : Convex ℝ (rectangle u₀ u₁ v₀ v₁) := by
    simpa only [rectangle] using
      (convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁)
  have hclosed : IsClosed (rectangle u₀ u₁ v₀ v₁) := by
    simpa only [rectangle] using (isClosed_Icc.prod isClosed_Icc)
  have hinterior : (interior (rectangle u₀ u₁ v₀ v₁)).Nonempty := by
    rw [rectangle, interior_prod_eq, interior_Icc, interior_Icc]
    refine ⟨((u₀ + u₁) / 2, (v₀ + v₁) / 2), ?_⟩
    exact ⟨by constructor <;> linarith, by constructor <;> linarith⟩
  have hstrict (p : ℝ × ℝ) (hp : p ∈ interior (rectangle u₀ u₁ v₀ v₁)) :
      HasStrictFDerivAt f (J p) p := by
    have hp' : p.1 ∈ Ioo u₀ u₁ ∧ p.2 ∈ Ioo v₀ v₁ := by
      simpa only [rectangle, interior_prod_eq, interior_Icc, mem_prod] using hp
    have hnear : Ioo u₀ u₁ ×ˢ Ioo v₀ v₁ ∈ 𝓝 p :=
      (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp'
    have hd₁ : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun s => f (s, q.2)) (L (fu q)) q.1 := by
      filter_upwards [hnear] with q hq
      have hqI : q.1 ∈ Icc u₀ u₁ := Ioo_subset_Icc_self hq.1
      have hqJ : q.2 ∈ Icc v₀ v₁ := Ioo_subset_Icc_self hq.2
      have hmem : Icc u₀ u₁ ∈ 𝓝 q.1 :=
        Filter.mem_of_superset (Ioo_mem_nhds hq.1.1 hq.1.2) Ioo_subset_Icc_self
      exact ((hdu q.1 hqI q.2 hqJ).hasDerivAt hmem).hasFDerivAt
    have hd₂ : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun t => f (q.1, t)) (L (fv q)) q.2 := by
      filter_upwards [hnear] with q hq
      have hqI : q.1 ∈ Icc u₀ u₁ := Ioo_subset_Icc_self hq.1
      have hqJ : q.2 ∈ Icc v₀ v₁ := Ioo_subset_Icc_self hq.2
      have hmem : Icc v₀ v₁ ∈ 𝓝 q.2 :=
        Filter.mem_of_superset (Ioo_mem_nhds hq.2.1 hq.2.2) Ioo_subset_Icc_self
      exact ((hdv q.1 hqI q.2 hqJ).hasDerivAt hmem).hasFDerivAt
    have hmem : rectangle u₀ u₁ v₀ v₁ ∈ 𝓝 p :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset
    have hfuAt : ContinuousAt fu p := (hfu p (interior_subset hp)).continuousAt hmem
    have hfvAt : ContinuousAt fv p := (hfv p (interior_subset hp)).continuousAt hmem
    have h := hasStrictFDerivAt_uncurry_coprod
      (f := fun u v => f (u, v))
      (f₁ := fun u v => L (fu (u, v)))
      (f₂ := fun u v => L (fv (u, v)))
      hd₁ hd₂ (hL.continuousAt.comp hfuAt) (hL.continuousAt.comp hfvAt)
    exact h
  have hdiff : DifferentiableOn ℝ f (interior (rectangle u₀ u₁ v₀ v₁)) :=
    fun p hp => (hstrict p hp).hasFDerivAt.differentiableAt.differentiableWithinAt
  have hderiv : ∀ p ∈ interior (rectangle u₀ u₁ v₀ v₁),
      fderiv ℝ f p = J p :=
    fun p hp => (hstrict p hp).hasFDerivAt.fderiv
  exact hconv.contDiffOn_one_of_continuousOn_fderiv hclosed hinterior hf hJ
    hdiff hderiv

end Goursat

end
