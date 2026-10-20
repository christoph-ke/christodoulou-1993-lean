module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransversePicard
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Coordinate jets of Goursat Picard iterates

Every iterate of a characteristic integral recursion has four continuous
coordinate jets on a closed rectangle when the nonlinearities have continuous
Fréchet derivatives on the visited state ball. This statement is about an
arbitrary continuous sequence satisfying the recursion.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- All four coordinate derivatives of a continuous Goursat Picard sequence
have continuous representatives, including one-sided derivatives at every
edge and corner of the rectangle. -/
theorem exists_continuous_coordinate_jets_of_picard_recursion
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
    ∀ n, ∃ P : C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ Q : C(rectangle u₀ u₁ v₀ v₁, F),
      ∃ S : C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ R : C(rectangle u₀ u₁ v₀ v₁, F),
      ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt (fun t => X n (u, t))
          (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v ∧
        HasDerivWithinAt (fun s => Y n (s, v))
          (Q ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun s => X n (s, v))
          (S ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun t => Y n (u, t))
          (R ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v := by
  intro n
  induction n with
  | zero =>
      have hPcont : ContinuousOn (fun p : ℝ × ℝ => x₀' p.2)
          (rectangle u₀ u₁ v₀ v₁) :=
        hx₀'.comp continuous_snd.continuousOn (fun p hp => hp.2)
      have hQcont : ContinuousOn (fun p : ℝ × ℝ => y₀' p.1)
          (rectangle u₀ u₁ v₀ v₁) :=
        hy₀'.comp continuous_fst.continuousOn (fun p hp => hp.1)
      let P : C(rectangle u₀ u₁ v₀ v₁, E) :=
        ⟨fun p => x₀' p.1.2, hPcont.domRestrict⟩
      let Q : C(rectangle u₀ u₁ v₀ v₁, F) :=
        ⟨fun p => y₀' p.1.1, hQcont.domRestrict⟩
      let S : C(rectangle u₀ u₁ v₀ v₁, E) := 0
      let R : C(rectangle u₀ u₁ v₀ v₁, F) := 0
      refine ⟨P, Q, S, R, ?_⟩
      intro u hu' v hv'
      have hlineX : ∀ t ∈ Icc v₀ v₁, X 0 (u, t) = x₀ t := by
        intro t ht
        exact (hzero (u, t) (pair_mem_rectangle hu' ht)).1
      have hlineY : ∀ s ∈ Icc u₀ u₁, Y 0 (s, v) = y₀ s := by
        intro s hs
        exact (hzero (s, v) (pair_mem_rectangle hs hv')).2
      have hconstX : ∀ s ∈ Icc u₀ u₁, X 0 (s, v) = x₀ v := by
        intro s hs
        exact (hzero (s, v) (pair_mem_rectangle hs hv')).1
      have hconstY : ∀ t ∈ Icc v₀ v₁, Y 0 (u, t) = y₀ u := by
        intro t ht
        exact (hzero (u, t) (pair_mem_rectangle hu' ht)).2
      constructor
      · exact (hdx₀ v hv').congr (fun t ht => hlineX t ht)
          (hlineX v hv')
      constructor
      · exact (hdy₀ u hu').congr (fun s hs => hlineY s hs)
          (hlineY u hu')
      constructor
      · simpa only [S, ContinuousMap.zero_apply] using
          ((hasDerivWithinAt_const (s := Icc u₀ u₁) (x := u)
            (c := x₀ v)).congr (fun s hs => hconstX s hs)
              (hconstX u hu'))
      · simpa only [R, ContinuousMap.zero_apply] using
          ((hasDerivWithinAt_const (s := Icc v₀ v₁) (x := v)
            (c := y₀ u)).congr (fun t ht => hconstY t ht)
              (hconstY v hv'))
  | succ n ih =>
      obtain ⟨P, Q, S, R, hjets⟩ := ih
      let Pfull : ℝ × ℝ → E := fun p => P (clippedPoint hu.le hv.le p)
      let Qfull : ℝ × ℝ → F := fun p => Q (clippedPoint hu.le hv.le p)
      let Sfull : ℝ × ℝ → E := fun p => S (clippedPoint hu.le hv.le p)
      let Rfull : ℝ × ℝ → F := fun p => R (clippedPoint hu.le hv.le p)
      have hPfull : Continuous Pfull := P.continuous.comp (continuous_clippedPoint hu.le hv.le)
      have hQfull : Continuous Qfull := Q.continuous.comp (continuous_clippedPoint hu.le hv.le)
      have hSfull : Continuous Sfull := S.continuous.comp (continuous_clippedPoint hu.le hv.le)
      have hRfull : Continuous Rfull := R.continuous.comp (continuous_clippedPoint hu.le hv.le)
      have hXv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
          HasDerivWithinAt (fun t => X n (u, t)) (Pfull (u, v)) (Icc v₀ v₁) v := by
        intro u hu' v hv'
        simpa only [Pfull, clippedPoint_eq_self hu.le hv.le
          ⟨(u, v), pair_mem_rectangle hu' hv'⟩] using
          (hjets u hu' v hv').1
      have hYu : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
          HasDerivWithinAt (fun s => Y n (s, v)) (Qfull (u, v)) (Icc u₀ u₁) u := by
        intro u hu' v hv'
        simpa only [Qfull, clippedPoint_eq_self hu.le hv.le
          ⟨(u, v), pair_mem_rectangle hu' hv'⟩] using
          (hjets u hu' v hv').2.1
      have hXu : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
          HasDerivWithinAt (fun s => X n (s, v)) (Sfull (u, v)) (Icc u₀ u₁) u := by
        intro u hu' v hv'
        simpa only [Sfull, clippedPoint_eq_self hu.le hv.le
          ⟨(u, v), pair_mem_rectangle hu' hv'⟩] using
          (hjets u hu' v hv').2.2.1
      have hYv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
          HasDerivWithinAt (fun t => Y n (u, t)) (Rfull (u, v)) (Icc v₀ v₁) v := by
        intro u hu' v hv'
        simpa only [Rfull, clippedPoint_eq_self hu.le hv.le
          ⟨(u, v), pair_mem_rectangle hu' hv'⟩] using
          (hjets u hu' v hv').2.2.2
      obtain ⟨Pnext, hPeq, hPderiv⟩ :=
        exists_continuous_vertical_jet_of_first_step hu.le hv c ρ
          fX DF hfX hDF hderivF (X n) (Y n) (hX n) (hY n)
          (hball n) Pfull Rfull hPfull.continuousOn hRfull.continuousOn
          hXv hYv x₀ x₀' hx₀' hdx₀
      obtain ⟨Qnext, hQeq, hQderiv⟩ :=
        exists_continuous_horizontal_jet_of_second_step hu hv.le c ρ
          fY DG hfY hDG hderivG (X n) (Y n) (hX n) (hY n)
          (hball n) Sfull Qfull hSfull.continuousOn hQfull.continuousOn
          hXu hYu y₀ y₀' hy₀' hdy₀
      have hFX : ContinuousOn
          (fun p : ℝ × ℝ => fX p (X n p, Y n p))
          (rectangle u₀ u₁ v₀ v₁) :=
        continuousOn_first_characteristic_field u₀ u₁ v₀ v₁
          (X n) (Y n) fX (hX n) (hY n) c ρ hfX (hball n)
      have hGY : ContinuousOn
          (fun p : ℝ × ℝ => fY p (X n p, Y n p))
          (rectangle u₀ u₁ v₀ v₁) :=
        continuousOn_second_characteristic_field u₀ u₁ v₀ v₁
          (X n) (Y n) fY (hX n) (hY n) c ρ hfY (hball n)
      let Snext : C(rectangle u₀ u₁ v₀ v₁, E) :=
        ⟨fun p => fX p.1 (X n p.1, Y n p.1), hFX.domRestrict⟩
      let Rnext : C(rectangle u₀ u₁ v₀ v₁, F) :=
        ⟨fun p => fY p.1 (X n p.1, Y n p.1), hGY.domRestrict⟩
      refine ⟨Pnext, Qnext, Snext, Rnext, ?_⟩
      intro u hu' v hv'
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
      have hstepX : HasDerivWithinAt (fun t => X (n + 1) (u, t))
          (Pnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v :=
        (hPderiv u hu' v hv').congr (fun t ht => hlineX t ht)
          (hlineX v hv')
      have hstepY : HasDerivWithinAt (fun s => Y (n + 1) (s, v))
          (Qnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u :=
        (hQderiv u hu' v hv').congr (fun s hs => hlineY s hs)
          (hlineY u hu')
      have hFXslice : ContinuousOn
          (fun s => fX (s, v) (X n (s, v), Y n (s, v))) (Icc u₀ u₁) :=
        hFX.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun s hs => pair_mem_rectangle hs hv')
      have hGYslice : ContinuousOn
          (fun t => fY (u, t) (X n (u, t), Y n (u, t))) (Icc v₀ v₁) :=
        hGY.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => pair_mem_rectangle hu' ht)
      have hstepS : HasDerivWithinAt (fun s => X (n + 1) (s, v))
          (Snext ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u := by
        exact intervalIntegral.hasDerivWithinAt_of_eq_integral_on_Icc
          (fun s => X (n + 1) (s, v))
          (fun s => fX (s, v) (X n (s, v), Y n (s, v)))
          (x₀ v) hFXslice (fun s hs =>
            (hsucc n (s, v) (pair_mem_rectangle hs hv')).1) hu'
      have hstepR : HasDerivWithinAt (fun t => Y (n + 1) (u, t))
          (Rnext ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v := by
        exact intervalIntegral.hasDerivWithinAt_of_eq_integral_on_Icc
          (fun t => Y (n + 1) (u, t))
          (fun t => fY (u, t) (X n (u, t), Y n (u, t)))
          (y₀ u) hGYslice (fun t ht =>
            (hsucc n (u, t) (pair_mem_rectangle hu' ht)).2) hv'
      exact ⟨hstepX, hstepY, hstepS, hstepR⟩


/-- The ball-preserving local Picard iterates have continuous coordinate jets
at every closed-rectangle point. The nonlinearities need a continuous full
Fréchet derivative on the visited ball. -/
theorem exists_continuous_coordinate_jets_of_picardIterateOnBall
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ < u₁) (hv : v₀ < v₁)
    (x₀ x₀' : ℝ → E) (y₀ y₀' : ℝ → F)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hx₀' : ContinuousOn x₀' (Icc v₀ v₁))
    (hy₀' : ContinuousOn y₀' (Icc u₀ u₁))
    (hdx₀ : ∀ v ∈ Icc v₀ v₁,
      HasDerivWithinAt x₀ (x₀' v) (Icc v₀ v₁) v)
    (hdy₀ : ∀ u ∈ Icc u₀ u₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc u₀ u₁) u)
    (c : E × F) (ρ : ℝ) (hρ : 0 < ρ)
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
    (r M : ℝ) (hM : 0 ≤ M)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ) :
    let Z := picardIterateOnBall u₀ u₁ v₀ v₁ hu.le hv.le x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY
    let X := fun n => clippedFirst hu.le hv.le (Z n)
    let Y := fun n => clippedSecond hu.le hv.le (Z n)
    ∀ n, ∃ P : C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ Q : C(rectangle u₀ u₁ v₀ v₁, F),
      ∃ S : C(rectangle u₀ u₁ v₀ v₁, E),
      ∃ R : C(rectangle u₀ u₁ v₀ v₁, F),
      ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
        (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
        HasDerivWithinAt (fun t => X n (u, t))
          (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v ∧
        HasDerivWithinAt (fun s => Y n (s, v))
          (Q ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun s => X n (s, v))
          (S ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun t => Y n (u, t))
          (R ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v := by
  dsimp only
  let Z := picardIterateOnBall u₀ u₁ v₀ v₁ hu.le hv.le x₀ y₀ hx₀ hy₀
    c ρ hρ fX fY hfX hfY
  let X : ℕ → ℝ × ℝ → E := fun n => clippedFirst hu.le hv.le (Z n)
  let Y : ℕ → ℝ × ℝ → F := fun n => clippedSecond hu.le hv.le (Z n)
  have hX : ∀ n, Continuous (X n) := fun n => continuous_clippedFirst hu.le hv.le (Z n)
  have hY : ∀ n, Continuous (Y n) := fun n => continuous_clippedSecond hu.le hv.le (Z n)
  have hstate (n : ℕ) (p : ℝ × ℝ)
      (hp : p ∈ rectangle u₀ u₁ v₀ v₁) :
      (X n p, Y n p) = Z n ⟨p, hp⟩ := by
    apply Prod.ext
    · exact clippedFirst_eq hu.le hv.le (Z n) ⟨p, hp⟩
    · exact clippedSecond_eq hu.le hv.le (Z n) ⟨p, hp⟩
  have hball : ∀ n, ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (X n p, Y n p) c ≤ ρ := by
    intro n p hp
    rw [hstate n p hp]
    exact picardIterateOnBall_mem_ball u₀ u₁ v₀ v₁ hu.le hv.le
      x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY r M hM hdata hMX hMY hsize
      n ⟨p, hp⟩
  have hzero : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X 0 p = x₀ p.2 ∧ Y 0 p = y₀ p.1 := by
    intro p hp
    have h := picardIterateOnBall_zero_apply u₀ u₁ v₀ v₁ hu.le hv.le
      x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY ⟨p, hp⟩
    rw [← hstate 0 p hp] at h
    exact Prod.mk.inj h
  have hsucc : ∀ n, ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X (n + 1) p = x₀ p.2 +
        ∫ s in u₀..p.1, fX (s, p.2) (X n (s, p.2), Y n (s, p.2)) ∧
      Y (n + 1) p = y₀ p.1 +
        ∫ t in v₀..p.2, fY (p.1, t) (X n (p.1, t), Y n (p.1, t)) := by
    intro n p hp
    have h := picardIterateOnBall_succ_apply_clipped u₀ u₁ v₀ v₁
      hu.le hv.le x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY
      r M hM hdata hMX hMY hsize n ⟨p, hp⟩
    dsimp only at h
    rw [← hstate (n + 1) p hp] at h
    exact Prod.mk.inj h
  exact exists_continuous_coordinate_jets_of_picard_recursion u₀ u₁ v₀ v₁
    hu hv c ρ fX fY DF DG hfX hfY hDF hDG hderivF hderivG
    x₀ x₀' y₀ y₀' hx₀' hy₀' hdx₀ hdy₀ X Y hX hY hball hzero hsucc

end Goursat

end
