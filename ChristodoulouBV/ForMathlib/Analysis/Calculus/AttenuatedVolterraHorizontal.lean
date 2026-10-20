module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Horizontal derivative of an attenuated Volterra integral

The lower endpoint contributes a boundary term. It vanishes when the source
vanishes on the diagonal, as in quadratic diagonal kernels.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

private theorem weightedSource_horizontal_jet
    {a b : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (attenuatedVolterraWeightedSource j k)
      (closedCoordTriangle a b) p) (1, 0) =
      (fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0) *
        Real.exp (attenuatedVolterraPotential k p) +
      j p * Real.exp (attenuatedVolterraPotential k p) *
        (fderivWithin ℝ (attenuatedVolterraPotential k)
          (closedCoordTriangle a b) p) (1, 0) := by
  let K := closedCoordTriangle a b
  let Q := attenuatedVolterraPotential k
  have hQ := contDiffOn_attenuatedVolterraPotential hab hk
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hjdiff : DifferentiableWithinAt ℝ j K p :=
    hj.differentiableOn (by norm_num) p hp
  have hQdiff : DifferentiableWithinAt ℝ Q K p :=
    hQ.differentiableOn (by norm_num) p hp
  change (fderivWithin ℝ (j * fun z => Real.exp (Q z)) K p) (1, 0) = _
  rw [fderivWithin_mul hunique hjdiff hQdiff.exp]
  have hExp : fderivWithin ℝ (fun z => Real.exp (Q z)) K p =
      Real.exp (Q p) • fderivWithin ℝ Q K p :=
    fderivWithin_exp hQdiff hunique
  rw [hExp]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The two potential horizontal jets differ by the negative integral of
the horizontal attenuation-kernel jet over the intervening interval. -/
theorem attenuatedVolterraPotential_horizontal_sub
    {a b u s v : ℝ} (hab : a < b) {k : ℝ × ℝ → ℝ}
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b) :
    (fderivWithin ℝ (attenuatedVolterraPotential k)
      (closedCoordTriangle a b) (u, s)) (1, 0) -
      (fderivWithin ℝ (attenuatedVolterraPotential k)
        (closedCoordTriangle a b) (u, v)) (1, 0) =
      -(∫ t in s..v,
        (fderivWithin ℝ k (closedCoordTriangle a b) (u, t)) (1, 0)) := by
  let K := closedCoordTriangle a b
  let ku : ℝ × ℝ → ℝ := fun z => (fderivWithin ℝ k K z) (1, 0)
  have hks : (fderivWithin ℝ (attenuatedVolterraPotential k) K (u, s)) (1, 0) =
      -k (u, u) + ∫ t in u..s, ku (u, t) := by
    exact radius_horizontal_jet_of_contDiffOn hab hk ⟨hu, hus, hsv.trans hv⟩
  have hkv : (fderivWithin ℝ (attenuatedVolterraPotential k) K (u, v)) (1, 0) =
      -k (u, u) + ∫ t in u..v, ku (u, t) := by
    exact radius_horizontal_jet_of_contDiffOn hab hk ⟨hu, hus.trans hsv, hv⟩
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hku : ContinuousOn ku K :=
    (hk.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hi₁ : IntervalIntegrable (fun t => ku (u, t)) volume u s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hus
    exact hku.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro t ht
      exact ⟨hu, ht.1, ht.2.trans (hsv.trans hv)⟩)
  have hi₂ : IntervalIntegrable (fun t => ku (u, t)) volume s v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hsv
    exact hku.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro t ht
      exact ⟨hu, hus.trans ht.1, ht.2.trans hv⟩)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  rw [hks, hkv]
  dsimp [ku]
  linarith only [hadd]

/-- If the source vanishes on the diagonal, the horizontal derivative is
the attenuated integral of the source jet minus the attenuation-jet term.
This identity holds on the entire closed coordinate triangle. -/
theorem fderivWithin_attenuatedVolterraIntegral_horizontal
    {a b : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hjdiag : ∀ u ∈ Icc a b, j (u, u) = 0)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (fun z : ℝ × ℝ =>
      attenuatedVolterraIntegral j k z.1 z.2)
      (closedCoordTriangle a b) p) (1, 0) =
      ∫ s in p.1..p.2,
        Real.exp (-(∫ t in s..p.2, k (p.1, t))) *
          ((fderivWithin ℝ j (closedCoordTriangle a b) (p.1, s)) (1, 0) -
            j (p.1, s) *
              (∫ t in s..p.2,
                (fderivWithin ℝ k (closedCoordTriangle a b) (p.1, t)) (1, 0))) := by
  let K := closedCoordTriangle a b
  let u := p.1
  let v := p.2
  let Q := attenuatedVolterraPotential k
  let F := attenuatedVolterraWeightedSource j k
  let P := weightedDiagonalRadius F
  let E := Real.exp (-Q p)
  let qu := (fderivWithin ℝ Q K p) (1, 0)
  let Fu : ℝ → ℝ := fun s => (fderivWithin ℝ F K (u, s)) (1, 0)
  let Fs : ℝ → ℝ := fun s => F (u, s)
  have hcoord : a ≤ u ∧ u ≤ v ∧ v ≤ b := hp
  have hseg : ∀ s ∈ Icc u v, (u, s) ∈ K := by
    intro s hs
    exact ⟨hcoord.1, hs.1, hs.2.trans hcoord.2.2⟩
  have hF := contDiffOn_attenuatedVolterraWeightedSource hab hj hk
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hFjet : ContinuousOn (fun z => (fderivWithin ℝ F K z) (1, 0)) K :=
    (hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hiFu : IntervalIntegrable Fu volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcoord.2.1
    exact hFjet.comp (continuous_const.prodMk continuous_id).continuousOn hseg
  have hiFs : IntervalIntegrable Fs volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcoord.2.1
    exact hF.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hseg
  have hdiagF : F (u, u) = 0 := by
    simp only [F, attenuatedVolterraWeightedSource, hjdiag u ⟨hcoord.1,
      hcoord.2.1.trans hcoord.2.2⟩, zero_mul]
  have hbase := fderivWithin_attenuatedVolterraIntegral_horizontal_factor hab hj hk hp
  have hP : P p = ∫ s in u..v, Fs s := rfl
  have hqu : qu = -k (u, u) +
      ∫ s in u..v, (fderivWithin ℝ k K (u, s)) (1, 0) := by
    exact radius_horizontal_jet_of_contDiffOn hab hk hp
  have hbase' :
      (fderivWithin ℝ (fun z : ℝ × ℝ =>
        attenuatedVolterraIntegral j k z.1 z.2) K p) (1, 0) =
        E * (∫ s in u..v, Fu s) - E * qu * P p := by
    have h := hbase
    rw [← hqu] at h
    simpa only [hdiagF, neg_zero, zero_add, E, qu, P, F, Fu, u, v, Q]
      using h
  have hInt :
      (∫ s in u..v, E * (Fu s - qu * Fs s)) =
        E * (∫ s in u..v, Fu s) - E * qu * P p := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hiFu (hiFs.const_mul qu),
      intervalIntegral.integral_const_mul, hP]
    ring
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      E * (Fu s - qu * Fs s) =
        Real.exp (-(∫ t in s..v, k (u, t))) *
          ((fderivWithin ℝ j K (u, s)) (1, 0) -
            j (u, s) *
              (∫ t in s..v, (fderivWithin ℝ k K (u, t)) (1, 0))) := by
    have hFu := weightedSource_horizontal_jet hab hj hk (hseg s hs)
    have hqdiff := attenuatedVolterraPotential_horizontal_sub hab hk
      hcoord.1 hs.1 hs.2 hcoord.2.2
    have he := integral_attenuation_eq_potential_sub hk.continuousOn
      hcoord.1 hs.1 hs.2 hcoord.2.2
    have hfactor : Real.exp (-(∫ t in s..v, k (u, t))) =
        E * Real.exp (Q (u, s)) := by
      rw [he, ← Real.exp_add]
      congr 1
      ring
    have hFu' : Fu s =
        (fderivWithin ℝ j K (u, s)) (1, 0) * Real.exp (Q (u, s)) +
          j (u, s) * Real.exp (Q (u, s)) *
            (fderivWithin ℝ Q K (u, s)) (1, 0) := hFu
    have hFs' : Fs s = j (u, s) * Real.exp (Q (u, s)) := rfl
    have hqdiff' : (fderivWithin ℝ Q K (u, s)) (1, 0) - qu =
        -(∫ t in s..v, (fderivWithin ℝ k K (u, t)) (1, 0)) := hqdiff
    rw [hFu', hFs']
    calc
      _ = E * Real.exp (Q (u, s)) *
            ((fderivWithin ℝ j K (u, s)) (1, 0) +
              j (u, s) *
                ((fderivWithin ℝ Q K (u, s)) (1, 0) - qu)) := by ring
      _ = E * Real.exp (Q (u, s)) *
            ((fderivWithin ℝ j K (u, s)) (1, 0) -
              j (u, s) *
                (∫ t in s..v, (fderivWithin ℝ k K (u, t)) (1, 0))) := by
        rw [hqdiff']
        ring
      _ = _ := by rw [hfactor]
  rw [hbase', ← hInt]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc u v := by
    simpa only [uIcc_of_le hcoord.2.1] using hs
  exact hpoint s hs'

end intervalIntegral

end
