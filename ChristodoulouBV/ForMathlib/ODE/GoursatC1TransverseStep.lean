module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseJets
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# One step of transverse jet propagation in a Goursat iteration

The chain rule supplies a continuous derivative field for a nonlinearity
evaluated along a state with continuous coordinate jets. Differentiating its
characteristic integral gives the next transverse jet, including all edges.
-/

public section

open Set Filter
open scoped Topology

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Propagate the vertical jet of the first Goursat component through one
horizontal characteristic integral. Its source is the full Fréchet derivative
of the nonlinearity applied to the vertical coordinate and state jets. -/
theorem exists_continuous_vertical_jet_of_first_step
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ < v₁)
    (c : E × F) (ρ : ℝ)
    (fX : ℝ × ℝ → E × F → E)
    (DF : ((ℝ × ℝ) × (E × F)) → ((ℝ × ℝ) × (E × F)) →L[ℝ] E)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hDF : ContinuousOn DF
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hderivF : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → HasFDerivAt fX.uncurry (DF (p, z)) (p, z))
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (P : ℝ × ℝ → E) (R : ℝ × ℝ → F)
    (hP : ContinuousOn P (rectangle u₀ u₁ v₀ v₁))
    (hR : ContinuousOn R (rectangle u₀ u₁ v₀ v₁))
    (hPX : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun t => X (u, t)) (P (u, v)) (Icc v₀ v₁) v)
    (hRY : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun t => Y (u, t)) (R (u, v)) (Icc v₀ v₁) v)
    (x₀ x₀' : ℝ → E)
    (hx₀' : ContinuousOn x₀' (Icc v₀ v₁))
    (hdx₀ : ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt x₀ (x₀' v) (Icc v₀ v₁) v) :
    ∃ Pnext : C(rectangle u₀ u₁ v₀ v₁, E),
      (∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        Pnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩ = x₀' v +
          ∫ s in u₀..u,
            DF ((s, v), (X (s, v), Y (s, v)))
              ((0, 1), (P (s, v), R (s, v)))) ∧
      ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt
          (fun t => x₀ t + ∫ s in u₀..u,
            fX (s, t) (X (s, t), Y (s, t)))
          (Pnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩)
          (Icc v₀ v₁) v := by
  let Z : ℝ × ℝ → E × F := fun p => (X p, Y p)
  have hZ : Continuous Z := hX.prodMk hY
  let H : ℝ × ℝ → E := fun p => fX p (Z p)
  let Hv : ℝ × ℝ → E := fun p =>
    DF (p, Z p) ((0, 1), (P p, R p))
  have hvisit : ContinuousOn (fun p : ℝ × ℝ => (p, Z p))
      (rectangle u₀ u₁ v₀ v₁) :=
    (continuous_id.prodMk hZ).continuousOn
  have hmaps : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      (p, Z p) ∈ rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ} := by
    intro p hp
    exact ⟨hp, hball p hp⟩
  have hH : ContinuousOn H (rectangle u₀ u₁ v₀ v₁) :=
    hfX.comp hvisit hmaps
  have hdir : ContinuousOn (fun p : ℝ × ℝ =>
      (((0 : ℝ), (1 : ℝ)), (P p, R p))) (rectangle u₀ u₁ v₀ v₁) :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ)))
      (rectangle u₀ u₁ v₀ v₁)).prodMk (hP.prodMk hR)
  have hHv : ContinuousOn Hv (rectangle u₀ u₁ v₀ v₁) :=
    (hDF.comp hvisit hmaps).clm_apply hdir
  have hstep : ∀ s ∈ Icc u₀ u₁, ∀ v ∈ Ioo v₀ v₁,
      HasDerivAt (fun t => H (s, t)) (Hv (s, v)) v := by
    intro s hs v hv'
    have hvI : v ∈ Icc v₀ v₁ := Ioo_subset_Icc_self hv'
    have hnear : Icc v₀ v₁ ∈ 𝓝 v :=
      Filter.mem_of_superset (Ioo_mem_nhds hv'.1 hv'.2) Ioo_subset_Icc_self
    have hPXat : HasDerivAt (fun t => X (s, t)) (P (s, v)) v :=
      (hPX s hs v hvI).hasDerivAt hnear
    have hRYat : HasDerivAt (fun t => Y (s, t)) (R (s, v)) v :=
      (hRY s hs v hvI).hasDerivAt hnear
    have hZat : HasDerivAt (fun t => Z (s, t)) (P (s, v), R (s, v)) v :=
      hPXat.prodMk hRYat
    have hq : (s, v) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hs hvI
    exact (hderivF (s, v) hq (Z (s, v)) (hball _ hq)).hasDerivAt_vertical_state hZat
  exact exists_continuous_vertical_jet_of_horizontal_integral
    hu hv x₀ x₀' H Hv hH hHv hx₀' hdx₀ hstep

/-- Propagate the horizontal jet of the second Goursat component through
one vertical characteristic integral. -/
theorem exists_continuous_horizontal_jet_of_second_step
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ ≤ v₁)
    (c : E × F) (ρ : ℝ)
    (fY : ℝ × ℝ → E × F → F)
    (DG : ((ℝ × ℝ) × (E × F)) → ((ℝ × ℝ) × (E × F)) →L[ℝ] F)
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hDG : ContinuousOn DG
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hderivG : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → HasFDerivAt fY.uncurry (DG (p, z)) (p, z))
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (S : ℝ × ℝ → E) (Q : ℝ × ℝ → F)
    (hS : ContinuousOn S (rectangle u₀ u₁ v₀ v₁))
    (hQ : ContinuousOn Q (rectangle u₀ u₁ v₀ v₁))
    (hSX : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun s => X (s, v)) (S (u, v)) (Icc u₀ u₁) u)
    (hQY : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun s => Y (s, v)) (Q (u, v)) (Icc u₀ u₁) u)
    (y₀ y₀' : ℝ → F)
    (hy₀' : ContinuousOn y₀' (Icc u₀ u₁))
    (hdy₀ : ∀ u ∈ Icc u₀ u₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc u₀ u₁) u) :
    ∃ Qnext : C(rectangle u₀ u₁ v₀ v₁, F),
      (∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        Qnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩ = y₀' u +
          ∫ t in v₀..v,
            DG ((u, t), (X (u, t), Y (u, t)))
              ((1, 0), (S (u, t), Q (u, t)))) ∧
      ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt
          (fun s => y₀ s + ∫ t in v₀..v,
            fY (s, t) (X (s, t), Y (s, t)))
          (Qnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩)
          (Icc u₀ u₁) u := by
  let Z : ℝ × ℝ → E × F := fun p => (X p, Y p)
  have hZ : Continuous Z := hX.prodMk hY
  let H : ℝ × ℝ → F := fun p => fY p (Z p)
  let Hu : ℝ × ℝ → F := fun p =>
    DG (p, Z p) ((1, 0), (S p, Q p))
  have hvisit : ContinuousOn (fun p : ℝ × ℝ => (p, Z p))
      (rectangle u₀ u₁ v₀ v₁) :=
    (continuous_id.prodMk hZ).continuousOn
  have hmaps : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      (p, Z p) ∈ rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ} := by
    intro p hp
    exact ⟨hp, hball p hp⟩
  have hH : ContinuousOn H (rectangle u₀ u₁ v₀ v₁) :=
    hfY.comp hvisit hmaps
  have hdir : ContinuousOn (fun p : ℝ × ℝ =>
      (((1 : ℝ), (0 : ℝ)), (S p, Q p))) (rectangle u₀ u₁ v₀ v₁) :=
    (continuousOn_const : ContinuousOn
      (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))
      (rectangle u₀ u₁ v₀ v₁)).prodMk (hS.prodMk hQ)
  have hHu : ContinuousOn Hu (rectangle u₀ u₁ v₀ v₁) :=
    (hDG.comp hvisit hmaps).clm_apply hdir
  have hstep : ∀ t ∈ Icc v₀ v₁, ∀ u ∈ Ioo u₀ u₁,
      HasDerivAt (fun s => H (s, t)) (Hu (u, t)) u := by
    intro t ht u hu'
    have huI : u ∈ Icc u₀ u₁ := Ioo_subset_Icc_self hu'
    have hnear : Icc u₀ u₁ ∈ 𝓝 u :=
      Filter.mem_of_superset (Ioo_mem_nhds hu'.1 hu'.2) Ioo_subset_Icc_self
    have hSXat : HasDerivAt (fun s => X (s, t)) (S (u, t)) u :=
      (hSX u huI t ht).hasDerivAt hnear
    have hQYat : HasDerivAt (fun s => Y (s, t)) (Q (u, t)) u :=
      (hQY u huI t ht).hasDerivAt hnear
    have hZat : HasDerivAt (fun s => Z (s, t)) (S (u, t), Q (u, t)) u :=
      hSXat.prodMk hQYat
    have hp : (u, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle huI ht
    exact (hderivG (u, t) hp (Z (u, t)) (hball _ hp)).hasDerivAt_horizontal_state hZat
  exact exists_continuous_horizontal_jet_of_vertical_integral
    hu hv y₀ y₀' H Hu hH hHu hy₀' hdy₀ hstep

end Goursat

end
