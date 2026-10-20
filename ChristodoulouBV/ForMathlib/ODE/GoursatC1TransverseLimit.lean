module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseLinearConvergence
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Limiting linear transverse Goursat jets

The limiting transverse equations are independent linear Volterra equations.
This module constructs their continuous solutions on a short rectangle from
the full derivative fields and the already known characteristic jets.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The two limiting linearized transverse Goursat equations have continuous
solutions on a short rectangle. The edge derivatives need only be continuous
on their respective closed intervals. -/
theorem exists_continuous_linearized_transverse_jets
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (p₀ : ℝ → E) (q₀ : ℝ → F)
    (hp₀ : ContinuousOn p₀ (Icc v₀ v₁))
    (hq₀ : ContinuousOn q₀ (Icc u₀ u₁))
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (G : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (R : C(rectangle u₀ u₁ v₀ v₁, F))
    (S : C(rectangle u₀ u₁ v₀ v₁, E))
    (κ : NNReal)
    (hD : ∀ p (x : E), ‖D p ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖)
    (hG : ∀ p (y : F), ‖G p ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ P : C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ Q : C(rectangle u₀ u₁ v₀ v₁, F),
        (∀ p : rectangle u₀ u₁ v₀ v₁,
          P p = p₀ p.1.2 + ∫ s in u₀..p.1.1,
            D (clippedPoint hu hv (s, p.1.2))
              ((0, 1),
                (P (clippedPoint hu hv (s, p.1.2)),
                 R (clippedPoint hu hv (s, p.1.2))))) ∧
        (∀ p : rectangle u₀ u₁ v₀ v₁,
          Q p = q₀ p.1.1 + ∫ t in v₀..p.1.2,
            G (clippedPoint hu hv (p.1.1, t))
              ((1, 0),
                (S (clippedPoint hu hv (p.1.1, t)),
                 Q (clippedPoint hu hv (p.1.1, t))))) := by
  let p₀c : ℝ → E := fun v => p₀ (clip v₀ v₁ v)
  let q₀c : ℝ → F := fun u => q₀ (clip u₀ u₁ u)
  have hp₀c : Continuous p₀c :=
    hp₀.comp_continuous (continuous_clip v₀ v₁) (clip_mem_Icc hv)
  have hq₀c : Continuous q₀c :=
    hq₀.comp_continuous (continuous_clip u₀ u₁) (clip_mem_Icc hu)
  let A : ℝ × ℝ → E →L[ℝ] E :=
    fun p => firstLinearCoefficient D (clippedPoint hu hv p)
  let B : ℝ × ℝ → F →L[ℝ] F :=
    fun p => secondLinearCoefficient G (clippedPoint hu hv p)
  let H : ℝ × ℝ → E :=
    fun p => firstLinearSource D R (clippedPoint hu hv p)
  let K : ℝ × ℝ → F :=
    fun p => secondLinearSource G S (clippedPoint hu hv p)
  have hA : Continuous A :=
    (firstLinearCoefficient D).continuous.comp (continuous_clippedPoint hu hv)
  have hB : Continuous B :=
    (secondLinearCoefficient G).continuous.comp (continuous_clippedPoint hu hv)
  have hH : Continuous H :=
    (firstLinearSource D R).continuous.comp (continuous_clippedPoint hu hv)
  have hK : Continuous K :=
    (secondLinearSource G S).continuous.comp (continuous_clippedPoint hu hv)
  have hκA : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ‖A p‖ ≤ (κ : ℝ) := by
    intro p hp
    exact norm_firstLinearCoefficient_le D κ κ.coe_nonneg hD (clippedPoint hu hv p)
  have hκB : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ‖B p‖ ≤ (κ : ℝ) := by
    intro p hp
    exact norm_secondLinearCoefficient_le G κ κ.coe_nonneg hG (clippedPoint hu hv p)
  obtain ⟨Pg, Qg, hPg, hQg, hlin⟩ :=
    exists_continuous_linear_solution_on_rectangle u₀ u₁ v₀ v₁ hu hv
      p₀c q₀c hp₀c hq₀c A B H K
      hA.continuousOn hB.continuousOn hH.continuousOn hK.continuousOn
      κ hκA hκB hsmall
  let P : C(rectangle u₀ u₁ v₀ v₁, E) :=
    ⟨fun p => Pg p.1, hPg.comp continuous_subtype_val⟩
  let Q : C(rectangle u₀ u₁ v₀ v₁, F) :=
    ⟨fun p => Qg p.1, hQg.comp continuous_subtype_val⟩
  refine ⟨P, Q, ?_, ?_⟩
  · intro p
    have hpeq := (hlin p.1 p.2).1
    have hvp : p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2.2
    rw [show p₀c p.1.2 = p₀ p.1.2 from congrArg p₀ (clip_eq_self hvp)] at hpeq
    change Pg p.1 = _
    rw [hpeq]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu⟩
        (by simpa only [rectangle, mem_prod] using p.2.1) hs
    have hpt : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI hvp
    have hclip := clippedPoint_eq_self hu hv ⟨(s, p.1.2), hpt⟩
    simp only [A, H, P, firstLinearCoefficient, firstLinearSource]
    have hpoint : Pg (s, p.1.2) = Pg (clippedPoint hu hv (s, p.1.2)).1 := by
      rw [hclip]
    rw [hpoint]
    exact (first_linearized_split
      (D (clippedPoint hu hv (s, p.1.2)))
      (P (clippedPoint hu hv (s, p.1.2)))
      (R (clippedPoint hu hv (s, p.1.2)))).symm
  · intro p
    have hqeq := (hlin p.1 p.2).2
    have hup : p.1.1 ∈ Icc u₀ u₁ := by
      simpa only [rectangle, mem_prod] using p.2.1
    rw [show q₀c p.1.1 = q₀ p.1.1 from congrArg q₀ (clip_eq_self hup)] at hqeq
    change Qg p.1 = _
    rw [hqeq]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hv⟩
        (by simpa only [rectangle, mem_prod] using p.2.2) ht
    have hpt : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hup htI
    have hclip := clippedPoint_eq_self hu hv ⟨(p.1.1, t), hpt⟩
    simp only [B, K, Q, secondLinearCoefficient, secondLinearSource]
    have hpoint : Qg (p.1.1, t) = Qg (clippedPoint hu hv (p.1.1, t)).1 := by
      rw [hclip]
    rw [hpoint]
    exact (second_linearized_split
      (G (clippedPoint hu hv (p.1.1, t)))
      (S (clippedPoint hu hv (p.1.1, t)))
      (Q (clippedPoint hu hv (p.1.1, t)))).symm

end Goursat

end
