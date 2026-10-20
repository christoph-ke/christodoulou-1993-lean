module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseFields
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Linearized equations for Picard coordinate jets

The continuous coordinate jets of a Goursat Picard sequence are unique on a
nondegenerate closed rectangle. Their characteristic components are the
nonlinear fields at the preceding iterate, and their transverse components
obey the linearized integral recursions.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Choose the four continuous coordinate jets of a Goursat Picard sequence
and identify their exact linearized characteristic recursions. -/
theorem exists_coordinate_jet_sequences_of_picard_recursion
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ < u₁) (hv : v₀ < v₁)
    (c : E × F) (ρ : ℝ)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (DF : ((ℝ × ℝ) × (E × F)) → ((ℝ × ℝ) × (E × F)) →L[ℝ] E)
    (DG : ((ℝ × ℝ) × (E × F)) → ((ℝ × ℝ) × (E × F)) →L[ℝ] F)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hDF : ContinuousOn DF
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hDG : ContinuousOn DG
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hderivF : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → HasFDerivAt fX.uncurry (DF (p, z)) (p, z))
    (hderivG : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → HasFDerivAt fY.uncurry (DG (p, z)) (p, z))
    (x₀ x₀' : ℝ → E) (y₀ y₀' : ℝ → F)
    (hx₀' : ContinuousOn x₀' (Icc v₀ v₁))
    (hy₀' : ContinuousOn y₀' (Icc u₀ u₁))
    (hdx₀ : ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt x₀ (x₀' v) (Icc v₀ v₁) v)
    (hdy₀ : ∀ u ∈ Icc u₀ u₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc u₀ u₁) u)
    (X : ℕ → ℝ × ℝ → E) (Y : ℕ → ℝ × ℝ → F)
    (hX : ∀ n, Continuous (X n)) (hY : ∀ n, Continuous (Y n))
    (hball : ∀ n, ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (X n p, Y n p) c ≤ ρ)
    (hzero : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X 0 p = x₀ p.2 ∧ Y 0 p = y₀ p.1)
    (hsucc : ∀ n, ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X (n + 1) p = x₀ p.2 +
        ∫ s in u₀..p.1, fX (s, p.2) (X n (s, p.2), Y n (s, p.2)) ∧
      Y (n + 1) p = y₀ p.1 +
        ∫ t in v₀..p.2, fY (p.1, t) (X n (p.1, t), Y n (p.1, t))) :
    ∃ P : ℕ → C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ Q : ℕ → C(rectangle u₀ u₁ v₀ v₁, F),
      ∃ S : ℕ → C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ R : ℕ → C(rectangle u₀ u₁ v₀ v₁, F),
      (∀ n (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt (fun t => X n (u, t))
          (P n ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v ∧
        HasDerivWithinAt (fun s => Y n (s, v))
          (Q n ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun s => X n (s, v))
          (S n ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun t => Y n (u, t))
          (R n ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v) ∧
      (∀ n (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        P (n + 1) ⟨(u, v), pair_mem_rectangle hu' hv'⟩ = x₀' v +
          ∫ s in u₀..u,
            DF ((s, v), (X n (s, v), Y n (s, v)))
              ((0, 1),
                (P n (clippedPoint hu.le hv.le (s, v)),
                 R n (clippedPoint hu.le hv.le (s, v)))) ∧
        Q (n + 1) ⟨(u, v), pair_mem_rectangle hu' hv'⟩ = y₀' u +
          ∫ t in v₀..v,
            DG ((u, t), (X n (u, t), Y n (u, t)))
              ((1, 0),
                (S n (clippedPoint hu.le hv.le (u, t)),
                 Q n (clippedPoint hu.le hv.le (u, t)))) ∧
        S (n + 1) ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
          fX (u, v) (X n (u, v), Y n (u, v)) ∧
        R (n + 1) ⟨(u, v), pair_mem_rectangle hu' hv'⟩ =
          fY (u, v) (X n (u, v), Y n (u, v))) := by
  have hbase := exists_continuous_coordinate_jets_of_picard_recursion
    u₀ u₁ v₀ v₁ hu hv c ρ fX fY DF DG hfX hfY hDF hDG
    hderivF hderivG x₀ x₀' y₀ y₀' hx₀' hy₀' hdx₀ hdy₀
    X Y hX hY hball hzero hsucc
  choose P Q S R hjets using hbase
  refine ⟨P, Q, S, R, hjets, ?_⟩
  intro n u hu' v hv'
  let q : rectangle u₀ u₁ v₀ v₁ := ⟨(u, v), pair_mem_rectangle hu' hv'⟩
  let Pfull : ℝ × ℝ → E := fun p => P n (clippedPoint hu.le hv.le p)
  let Qfull : ℝ × ℝ → F := fun p => Q n (clippedPoint hu.le hv.le p)
  let Sfull : ℝ × ℝ → E := fun p => S n (clippedPoint hu.le hv.le p)
  let Rfull : ℝ × ℝ → F := fun p => R n (clippedPoint hu.le hv.le p)
  have hPfull : Continuous Pfull := (P n).continuous.comp (continuous_clippedPoint hu.le hv.le)
  have hQfull : Continuous Qfull := (Q n).continuous.comp (continuous_clippedPoint hu.le hv.le)
  have hSfull : Continuous Sfull := (S n).continuous.comp (continuous_clippedPoint hu.le hv.le)
  have hRfull : Continuous Rfull := (R n).continuous.comp (continuous_clippedPoint hu.le hv.le)
  have hXv : ∀ s ∈ Icc u₀ u₁, ∀ t ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun w => X n (s, w)) (Pfull (s, t)) (Icc v₀ v₁) t := by
    intro s hs t ht
    simpa only [Pfull, clippedPoint_eq_self hu.le hv.le
      ⟨(s, t), pair_mem_rectangle hs ht⟩] using (hjets n s hs t ht).1
  have hYu : ∀ s ∈ Icc u₀ u₁, ∀ t ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun w => Y n (w, t)) (Qfull (s, t)) (Icc u₀ u₁) s := by
    intro s hs t ht
    simpa only [Qfull, clippedPoint_eq_self hu.le hv.le
      ⟨(s, t), pair_mem_rectangle hs ht⟩] using (hjets n s hs t ht).2.1
  have hXu : ∀ s ∈ Icc u₀ u₁, ∀ t ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun w => X n (w, t)) (Sfull (s, t)) (Icc u₀ u₁) s := by
    intro s hs t ht
    simpa only [Sfull, clippedPoint_eq_self hu.le hv.le
      ⟨(s, t), pair_mem_rectangle hs ht⟩] using (hjets n s hs t ht).2.2.1
  have hYv : ∀ s ∈ Icc u₀ u₁, ∀ t ∈ Icc v₀ v₁,
      HasDerivWithinAt (fun w => Y n (s, w)) (Rfull (s, t)) (Icc v₀ v₁) t := by
    intro s hs t ht
    simpa only [Rfull, clippedPoint_eq_self hu.le hv.le
      ⟨(s, t), pair_mem_rectangle hs ht⟩] using (hjets n s hs t ht).2.2.2
  obtain ⟨Pstep, hPeq, hPderiv⟩ :=
    exists_continuous_vertical_jet_of_first_step hu.le hv c ρ
      fX DF hfX hDF hderivF (X n) (Y n) (hX n) (hY n)
      (hball n) Pfull Rfull hPfull.continuousOn hRfull.continuousOn
      hXv hYv x₀ x₀' hx₀' hdx₀
  obtain ⟨Qstep, hQeq, hQderiv⟩ :=
    exists_continuous_horizontal_jet_of_second_step hu hv.le c ρ
      fY DG hfY hDG hderivG (X n) (Y n) (hX n) (hY n)
      (hball n) Sfull Qfull hSfull.continuousOn hQfull.continuousOn
      hXu hYu y₀ y₀' hy₀' hdy₀
  have hlineX : ∀ t ∈ Icc v₀ v₁,
      X (n + 1) (u, t) = x₀ t +
        ∫ s in u₀..u, fX (s, t) (X n (s, t), Y n (s, t)) := by
    intro t ht
    exact (hsucc n (u, t) (pair_mem_rectangle hu' ht)).1
  have hlineY : ∀ s ∈ Icc u₀ u₁,
      Y (n + 1) (s, v) = y₀ s +
        ∫ t in v₀..v, fY (s, t) (X n (s, t), Y n (s, t)) := by
    intro s hs
    exact (hsucc n (s, v) (pair_mem_rectangle hs hv')).2
  have hPderiv' : HasDerivWithinAt (fun t => X (n + 1) (u, t))
      (Pstep q) (Icc v₀ v₁) v :=
    (hPderiv u hu' v hv').congr (fun t ht => hlineX t ht) (hlineX v hv')
  have hQderiv' : HasDerivWithinAt (fun s => Y (n + 1) (s, v))
      (Qstep q) (Icc u₀ u₁) u :=
    (hQderiv u hu' v hv').congr (fun s hs => hlineY s hs) (hlineY u hu')
  have hPuniq : P (n + 1) q = Pstep q := by
    have h₁ := ((hjets (n + 1) u hu' v hv').1).derivWithin
      ((uniqueDiffOn_Icc hv) v hv')
    have h₂ := hPderiv'.derivWithin ((uniqueDiffOn_Icc hv) v hv')
    exact h₁.symm.trans h₂
  have hQuniq : Q (n + 1) q = Qstep q := by
    have h₁ := ((hjets (n + 1) u hu' v hv').2.1).derivWithin
      ((uniqueDiffOn_Icc hu) u hu')
    have h₂ := hQderiv'.derivWithin ((uniqueDiffOn_Icc hu) u hu')
    exact h₁.symm.trans h₂
  have hFX : ContinuousOn (fun p : ℝ × ℝ => fX p (X n p, Y n p))
      (rectangle u₀ u₁ v₀ v₁) :=
    continuousOn_first_characteristic_field u₀ u₁ v₀ v₁
      (X n) (Y n) fX (hX n) (hY n) c ρ hfX (hball n)
  have hGY : ContinuousOn (fun p : ℝ × ℝ => fY p (X n p, Y n p))
      (rectangle u₀ u₁ v₀ v₁) :=
    continuousOn_second_characteristic_field u₀ u₁ v₀ v₁
      (X n) (Y n) fY (hX n) (hY n) c ρ hfY (hball n)
  have hFXslice : ContinuousOn
      (fun s => fX (s, v) (X n (s, v), Y n (s, v))) (Icc u₀ u₁) :=
    hFX.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => pair_mem_rectangle hs hv')
  have hGYslice : ContinuousOn
      (fun t => fY (u, t) (X n (u, t), Y n (u, t))) (Icc v₀ v₁) :=
    hGY.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => pair_mem_rectangle hu' ht)
  have hSderiv : HasDerivWithinAt (fun s => X (n + 1) (s, v))
      (fX (u, v) (X n (u, v), Y n (u, v))) (Icc u₀ u₁) u :=
    intervalIntegral.hasDerivWithinAt_of_eq_integral_on_Icc
      (fun s => X (n + 1) (s, v))
      (fun s => fX (s, v) (X n (s, v), Y n (s, v)))
      (x₀ v) hFXslice
      (fun s hs => (hsucc n (s, v) (pair_mem_rectangle hs hv')).1) hu'
  have hRderiv : HasDerivWithinAt (fun t => Y (n + 1) (u, t))
      (fY (u, v) (X n (u, v), Y n (u, v))) (Icc v₀ v₁) v :=
    intervalIntegral.hasDerivWithinAt_of_eq_integral_on_Icc
      (fun t => Y (n + 1) (u, t))
      (fun t => fY (u, t) (X n (u, t), Y n (u, t)))
      (y₀ u) hGYslice
      (fun t ht => (hsucc n (u, t) (pair_mem_rectangle hu' ht)).2) hv'
  have hSuniq : S (n + 1) q = fX (u, v) (X n (u, v), Y n (u, v)) := by
    have h₁ := ((hjets (n + 1) u hu' v hv').2.2.1).derivWithin
      ((uniqueDiffOn_Icc hu) u hu')
    have h₂ := hSderiv.derivWithin ((uniqueDiffOn_Icc hu) u hu')
    exact h₁.symm.trans h₂
  have hRuniq : R (n + 1) q = fY (u, v) (X n (u, v), Y n (u, v)) := by
    have h₁ := ((hjets (n + 1) u hu' v hv').2.2.2).derivWithin
      ((uniqueDiffOn_Icc hv) v hv')
    have h₂ := hRderiv.derivWithin ((uniqueDiffOn_Icc hv) v hv')
    exact h₁.symm.trans h₂
  exact ⟨hPuniq.trans (hPeq u hu' v hv'),
    hQuniq.trans (hQeq u hu' v hv'), hSuniq, hRuniq⟩

end Goursat

end
