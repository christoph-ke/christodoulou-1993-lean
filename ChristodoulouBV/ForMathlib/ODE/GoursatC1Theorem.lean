module

public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseLimit
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseLinearConvergence
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseJetSequence
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransversePrimitive
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Final
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Jets
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Closed-rectangle regularity for a bounded Goursat solution

The transverse derivatives are obtained as uniform limits of the coordinate
derivatives of ball-preserving Picard iterates. The limiting derivatives solve
linear Volterra equations and extend continuously to every edge and corner.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- A continuous ball-valued Goursat solution has continuous transverse jets.
The derivative fields are the full Fréchet derivatives of the nonlinearities
on the visited rectangle and state ball. The state Lipschitz bounds are stated
explicitly so this lemma also applies in Banach spaces. -/
theorem exists_continuous_transverse_jets_of_integral_equations_on_ball
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
    (r M : ℝ) (hM : 0 ≤ M) (κ : NNReal)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z')
    (hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z')
    (hDFX : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ x : E,
      ‖DF (p, z) ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖)
    (hDGY : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ y : F,
      ‖DG (p, z) ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) ≤ ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t))) :
    ∃ P : C(rectangle u₀ u₁ v₀ v₁, E),
    ∃ Q : C(rectangle u₀ u₁ v₀ v₁, F),
      (∀ p : rectangle u₀ u₁ v₀ v₁,
        P p = x₀' p.1.2 + ∫ s in u₀..p.1.1,
          DF ((s, p.1.2), (X (s, p.1.2), Y (s, p.1.2)))
            ((0, 1), (P (clippedPoint hu.le hv.le (s, p.1.2)),
              fY (s, p.1.2) (X (s, p.1.2), Y (s, p.1.2))))) ∧
      (∀ p : rectangle u₀ u₁ v₀ v₁,
        Q p = y₀' p.1.1 + ∫ t in v₀..p.1.2,
          DG ((p.1.1, t), (X (p.1.1, t), Y (p.1.1, t)))
            ((1, 0), (fX (p.1.1, t) (X (p.1.1, t), Y (p.1.1, t)),
              Q (clippedPoint hu.le hv.le (p.1.1, t))))) ∧
      (∀ (u : ℝ) (huI : u ∈ Icc u₀ u₁),
        ∀ (v : ℝ) (hvI : v ∈ Icc v₀ v₁),
        HasDerivWithinAt (fun t => X (u, t))
          (P ⟨(u, v), pair_mem_rectangle huI hvI⟩)
          (Icc v₀ v₁) v ∧
        HasDerivWithinAt (fun s => Y (s, v))
          (Q ⟨(u, v), pair_mem_rectangle huI hvI⟩)
          (Icc u₀ u₁) u) := by
  let Z : ℕ → C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    picardIterateOnBall u₀ u₁ v₀ v₁ hu.le hv.le x₀ y₀ hx₀ hy₀
      c ρ hρ fX fY hfX hfY
  let Zlim : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1), (hX.prodMk hY).comp continuous_subtype_val⟩
  have hZ : Tendsto Z atTop (𝓝 Zlim) :=
    tendsto_picardIterateOnBall_of_integral_equations u₀ u₁ v₀ v₁
      hu.le hv.le x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY
      r M hM κ hdata hMX hMY hLX hLY hsize hsmall
      X Y hX hY hball heq
  have hZball : ∀ n p, dist (Z n p) c ≤ ρ := by
    intro n p
    exact picardIterateOnBall_mem_ball u₀ u₁ v₀ v₁ hu.le hv.le
      x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY r M hM
      hdata hMX hMY hsize n p
  have hZlimball : ∀ p, dist (Zlim p) c ≤ ρ :=
    fun p => hball p.1 p.2
  let Xn : ℕ → ℝ × ℝ → E := fun n => clippedFirst hu.le hv.le (Z n)
  let Yn : ℕ → ℝ × ℝ → F := fun n => clippedSecond hu.le hv.le (Z n)
  have hXn : ∀ n, Continuous (Xn n) :=
    fun n => continuous_clippedFirst hu.le hv.le (Z n)
  have hYn : ∀ n, Continuous (Yn n) :=
    fun n => continuous_clippedSecond hu.le hv.le (Z n)
  have hstate : ∀ (n : ℕ) (p : ℝ × ℝ)
      (hp : p ∈ rectangle u₀ u₁ v₀ v₁),
      (Xn n p, Yn n p) = Z n ⟨p, hp⟩ := by
    intro n p hp
    exact Prod.ext (clippedFirst_eq hu.le hv.le (Z n) ⟨p, hp⟩)
      (clippedSecond_eq hu.le hv.le (Z n) ⟨p, hp⟩)
  have hzero : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Xn 0 p = x₀ p.2 ∧ Yn 0 p = y₀ p.1 := by
    intro p hp
    have h := picardIterateOnBall_zero_apply u₀ u₁ v₀ v₁ hu.le hv.le
      x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY ⟨p, hp⟩
    rw [← hstate 0 p hp] at h
    exact Prod.mk.inj h
  have hsucc : ∀ n, ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      Xn (n + 1) p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (Xn n (s, p.2), Yn n (s, p.2)) ∧
      Yn (n + 1) p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (Xn n (p.1, t), Yn n (p.1, t)) := by
    intro n p hp
    have h := picardIterateOnBall_succ_apply_clipped u₀ u₁ v₀ v₁
      hu.le hv.le x₀ y₀ hx₀ hy₀ c ρ hρ fX fY hfX hfY
      r M hM hdata hMX hMY hsize n ⟨p, hp⟩
    dsimp only at h
    rw [← hstate (n + 1) p hp] at h
    exact Prod.mk.inj h
  have hballn : ∀ n, ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (Xn n p, Yn n p) c ≤ ρ := by
    intro n p hp
    rw [hstate n p hp]
    exact hZball n ⟨p, hp⟩
  obtain ⟨Pn, Qn, Sn, Rn, hjets, hrec⟩ :=
    exists_coordinate_jet_sequences_of_picard_recursion
      u₀ u₁ v₀ v₁ hu hv c ρ fX fY DF DG hfX hfY hDF hDG
      hderivF hderivG x₀ x₀' y₀ y₀' hx₀' hy₀' hdx₀ hdy₀
      Xn Yn hXn hYn hballn hzero hsucc
  let Dn : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E) := fun n =>
    ⟨fun p => DF (p.1, Z n p),
      hDF.comp_continuous (continuous_subtype_val.prodMk (Z n).continuous)
        (fun p => ⟨p.2, hZball n p⟩)⟩
  let Gn : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F) := fun n =>
    ⟨fun p => DG (p.1, Z n p),
      hDG.comp_continuous (continuous_subtype_val.prodMk (Z n).continuous)
        (fun p => ⟨p.2, hZball n p⟩)⟩
  let Dlim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E) :=
    ⟨fun p => DF (p.1, Zlim p),
      hDF.comp_continuous (continuous_subtype_val.prodMk Zlim.continuous)
        (fun p => ⟨p.2, hZlimball p⟩)⟩
  let Glim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F) :=
    ⟨fun p => DG (p.1, Zlim p),
      hDG.comp_continuous (continuous_subtype_val.prodMk Zlim.continuous)
        (fun p => ⟨p.2, hZlimball p⟩)⟩
  have hDn : Tendsto Dn atTop (𝓝 Dlim) :=
    tendsto_field_comp_state_on_rectangle_ball hu.le hv.le
      c ρ hρ (fun p z => DF (p, z)) hDF Z Zlim hZ hZball hZlimball
  have hGn : Tendsto Gn atTop (𝓝 Glim) :=
    tendsto_field_comp_state_on_rectangle_ball hu.le hv.le
      c ρ hρ (fun p z => DG (p, z)) hDG Z Zlim hZ hZball hZlimball
  let Rlim : C(rectangle u₀ u₁ v₀ v₁, F) :=
    ⟨fun p => fY p.1 (Zlim p),
      hfY.comp_continuous (continuous_subtype_val.prodMk Zlim.continuous)
        (fun p => ⟨p.2, hZlimball p⟩)⟩
  let Slim : C(rectangle u₀ u₁ v₀ v₁, E) :=
    ⟨fun p => fX p.1 (Zlim p),
      hfX.comp_continuous (continuous_subtype_val.prodMk Zlim.continuous)
        (fun p => ⟨p.2, hZlimball p⟩)⟩
  have hmem (p : rectangle u₀ u₁ v₀ v₁) :
      p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
    simpa only [rectangle, mem_prod] using p.2
  have hRn : Tendsto Rn atTop (𝓝 Rlim) := by
    apply tendsto_characteristic_jet_of_picard_states hu.le hv.le
      c ρ hρ fY hfY Z Zlim hZ hZball hZlimball Rn
    intro n p
    have hp := (hrec n p.1.1 (hmem p).1 p.1.2 (hmem p).2).2.2.2
    simpa only [hstate n p.1 p.2] using hp
  have hSn : Tendsto Sn atTop (𝓝 Slim) := by
    apply tendsto_characteristic_jet_of_picard_states hu.le hv.le
      c ρ hρ fX hfX Z Zlim hZ hZball hZlimball Sn
    intro n p
    have hp := (hrec n p.1.1 (hmem p).1 p.1.2 (hmem p).2).2.2.1
    simpa only [hstate n p.1 p.2] using hp
  have hDFbound : ∀ p (x : E),
      ‖Dlim p ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖ := by
    intro p x
    exact hDFX p.1 p.2 (Zlim p) (hZlimball p) x
  have hDGbound : ∀ p (y : F),
      ‖Glim p ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖ := by
    intro p y
    exact hDGY p.1 p.2 (Zlim p) (hZlimball p) y
  obtain ⟨P, Q, hPeq, hQeq⟩ :=
    exists_continuous_linearized_transverse_jets hu.le hv.le
      x₀' y₀' hx₀' hy₀' Dlim Glim Rlim Slim κ
      hDFbound hDGbound hsmall
  have hDnbound : ∀ n p (x : E),
      ‖Dn n p ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖ := by
    intro n p x
    exact hDFX p.1 p.2 (Z n p) (hZball n p) x
  have hGnbound : ∀ n p (y : F),
      ‖Gn n p ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖ := by
    intro n p y
    exact hDGY p.1 p.2 (Z n p) (hZball n p) y
  have hPrec : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      Pn (n + 1) p = x₀' p.1.2 + ∫ s in u₀..p.1.1,
        Dn n (clippedPoint hu.le hv.le (s, p.1.2))
          ((0, 1), (Pn n (clippedPoint hu.le hv.le (s, p.1.2)),
            Rn n (clippedPoint hu.le hv.le (s, p.1.2)))) := by
    intro n p
    rw [(hrec n p.1.1 (hmem p).1 p.1.2 (hmem p).2).1]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu.le⟩ (hmem p).1 hs
    have hpt : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI (hmem p).2
    dsimp only [Dn, ContinuousMap.coe_mk]
    rw [show (Xn n (s, p.1.2), Yn n (s, p.1.2)) =
      Z n (clippedPoint hu.le hv.le (s, p.1.2)) from by
        rw [hstate n (s, p.1.2) hpt]
        congr 1
        exact (clippedPoint_eq_self hu.le hv.le ⟨_, hpt⟩).symm]
    rw [clippedPoint_eq_self hu.le hv.le ⟨_, hpt⟩]
  have hQrec : ∀ n (p : rectangle u₀ u₁ v₀ v₁),
      Qn (n + 1) p = y₀' p.1.1 + ∫ t in v₀..p.1.2,
        Gn n (clippedPoint hu.le hv.le (p.1.1, t))
          ((1, 0), (Sn n (clippedPoint hu.le hv.le (p.1.1, t)),
            Qn n (clippedPoint hu.le hv.le (p.1.1, t)))) := by
    intro n p
    rw [(hrec n p.1.1 (hmem p).1 p.1.2 (hmem p).2).2.1]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hv.le⟩ (hmem p).2 ht
    have hpt : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle (hmem p).1 htI
    dsimp only [Gn, ContinuousMap.coe_mk]
    rw [show (Xn n (p.1.1, t), Yn n (p.1.1, t)) =
      Z n (clippedPoint hu.le hv.le (p.1.1, t)) from by
        rw [hstate n (p.1.1, t) hpt]
        congr 1
        exact (clippedPoint_eq_self hu.le hv.le ⟨_, hpt⟩).symm]
    rw [clippedPoint_eq_self hu.le hv.le ⟨_, hpt⟩]
  have hPn : Tendsto Pn atTop (𝓝 P) :=
    tendsto_first_transverse_of_linearized_recursion hu.le hv.le x₀' κ
      Dn Rn Pn Dlim Rlim P hDn hRn hDnbound
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (le_max_left _ _) κ.coe_nonneg) hsmall)
      hPrec hPeq
  have hQn : Tendsto Qn atTop (𝓝 Q) :=
    tendsto_second_transverse_of_linearized_recursion hu.le hv.le y₀' κ
      Gn Sn Qn Glim Slim Q hGn hSn hGnbound
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (le_max_right _ _) κ.coe_nonneg) hsmall)
      hQrec hQeq
  let Xnc : ℕ → C(rectangle u₀ u₁ v₀ v₁, E) :=
    fun n => ⟨fun p => (Z n p).1, continuous_fst.comp (Z n).continuous⟩
  let Ync : ℕ → C(rectangle u₀ u₁ v₀ v₁, F) :=
    fun n => ⟨fun p => (Z n p).2, continuous_snd.comp (Z n).continuous⟩
  let Xc : C(rectangle u₀ u₁ v₀ v₁, E) :=
    ⟨fun p => X p.1, hX.comp continuous_subtype_val⟩
  let Yc : C(rectangle u₀ u₁ v₀ v₁, F) :=
    ⟨fun p => Y p.1, hY.comp continuous_subtype_val⟩
  let fstMap : C(E × F, E) := ⟨fun z => z.1, continuous_fst⟩
  let sndMap : C(E × F, F) := ⟨fun z => z.2, continuous_snd⟩
  have hXnc : Tendsto Xnc atTop (𝓝 Xc) := by
    exact (fstMap.continuous_postcomp.tendsto Zlim).comp hZ
  have hYnc : Tendsto Ync atTop (𝓝 Yc) := by
    exact (sndMap.continuous_postcomp.tendsto Zlim).comp hZ
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · intro p
    rw [hPeq p]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu.le⟩ (hmem p).1 hs
    have hpt : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI (hmem p).2
    have hclip := clippedPoint_eq_self hu.le hv.le ⟨_, hpt⟩
    dsimp only [Dlim, Rlim, Zlim, ContinuousMap.coe_mk]
    rw [hclip]
    rfl
  · intro p
    rw [hQeq p]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hv.le⟩ (hmem p).2 ht
    have hpt : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle (hmem p).1 htI
    have hclip := clippedPoint_eq_self hu.le hv.le ⟨_, hpt⟩
    dsimp only [Glim, Slim, Zlim, ContinuousMap.coe_mk]
    rw [hclip]
    rfl
  · intro u huI v hvI
    let p : rectangle u₀ u₁ v₀ v₁ :=
      ⟨(u, v), pair_mem_rectangle huI hvI⟩
    constructor
    · have hjet : ∀ n (s : ℝ) (hs : s ∈ Icc u₀ u₁)
          (t : ℝ) (ht : t ∈ Icc v₀ v₁),
          HasDerivWithinAt
            (fun w => Xnc n (clippedPoint hu.le hv.le (s, w)))
            (Pn n ⟨(s, t), pair_mem_rectangle hs ht⟩) (Icc v₀ v₁) t := by
        intro n s hs t ht
        exact (hjets n s hs t ht).1
      have h := hasDerivWithinAt_vertical_of_tendsto_jets hu.le hv.le
        Xnc Pn Xc P hXnc hPn hjet huI hvI
      have hcongr : ∀ t ∈ Icc v₀ v₁,
          Xc ⟨(u, clip v₀ v₁ t),
            pair_mem_rectangle huI (clip_mem_Icc hv.le t)⟩ = X (u, t) := by
        intro t ht
        simp only [Xc, ContinuousMap.coe_mk]
        rw [clip_eq_self ht]
      exact h.congr (fun t ht => (hcongr t ht).symm) (hcongr v hvI).symm
    · have hjet : ∀ n (s : ℝ) (hs : s ∈ Icc u₀ u₁)
          (t : ℝ) (ht : t ∈ Icc v₀ v₁),
          HasDerivWithinAt
            (fun w => Ync n (clippedPoint hu.le hv.le (w, t)))
            (Qn n ⟨(s, t), pair_mem_rectangle hs ht⟩) (Icc u₀ u₁) s := by
        intro n s hs t ht
        exact (hjets n s hs t ht).2.1
      have h := hasDerivWithinAt_horizontal_of_tendsto_jets hu.le hv.le
        Ync Qn Yc Q hYnc hQn hjet huI hvI
      have hcongr : ∀ s ∈ Icc u₀ u₁,
          Yc ⟨(clip u₀ u₁ s, v),
            pair_mem_rectangle (clip_mem_Icc hu.le s) hvI⟩ = Y (s, v) := by
        intro s hs
        simp only [Yc, ContinuousMap.coe_mk]
        rw [clip_eq_self hs]
      exact h.congr (fun s hs => (hcongr s hs).symm) (hcongr u huI).symm

/-- Continuous transverse jets and the characteristic integral equations give
full relative `C¹` regularity on a nondegenerate closed rectangle. -/
theorem contDiffOn_one_of_goursat_transverse_jets
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ < u₁) (hv : v₀ < v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (x₀ : ℝ → E) (y₀ : ℝ → F)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (c : E × F) (ρ : ℝ)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (X p, Y p) c ≤ ρ)
    (heq : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      X p = x₀ p.2 + ∫ s in u₀..p.1,
        fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
      Y p = y₀ p.1 + ∫ t in v₀..p.2,
        fY (p.1, t) (X (p.1, t), Y (p.1, t)))
    (P : C(rectangle u₀ u₁ v₀ v₁, E))
    (Q : C(rectangle u₀ u₁ v₀ v₁, F))
    (hjet : ∀ (u : ℝ) (huI : u ∈ Icc u₀ u₁)
      (v : ℝ) (hvI : v ∈ Icc v₀ v₁),
      HasDerivWithinAt (fun t => X (u, t))
        (P ⟨(u, v), pair_mem_rectangle huI hvI⟩) (Icc v₀ v₁) v ∧
      HasDerivWithinAt (fun s => Y (s, v))
        (Q ⟨(u, v), pair_mem_rectangle huI hvI⟩) (Icc u₀ u₁) u) :
    ContDiffOn ℝ 1 X (rectangle u₀ u₁ v₀ v₁) ∧
    ContDiffOn ℝ 1 Y (rectangle u₀ u₁ v₀ v₁) := by
  let PX : ℝ × ℝ → E := fun p => P (clippedPoint hu.le hv.le p)
  let QY : ℝ × ℝ → F := fun p => Q (clippedPoint hu.le hv.le p)
  have hPX : Continuous PX := P.continuous.comp (continuous_clippedPoint hu.le hv.le)
  have hQY : Continuous QY := Q.continuous.comp (continuous_clippedPoint hu.le hv.le)
  have hFX := continuousOn_first_characteristic_field
    u₀ u₁ v₀ v₁ X Y fX hX hY c ρ hfX hball
  have hGY := continuousOn_second_characteristic_field
    u₀ u₁ v₀ v₁ X Y fY hX hY c ρ hfY hball
  constructor
  · apply contDiffOn_one_of_continuous_coordinate_jets hu hv X
      (fun p => fX p (X p, Y p)) PX
      hX.continuousOn hFX hPX.continuousOn
    · intro u huI v hvI
      exact hasDerivWithinAt_first_of_integral_equation_on_ball
        u₀ u₁ v₀ v₁ X Y x₀ fX hX hY c ρ hfX hball
        (fun p hp => (heq p hp).1) huI hvI
    · intro u huI v hvI
      simpa only [PX, clippedPoint_eq_self hu.le hv.le
        ⟨(u, v), pair_mem_rectangle huI hvI⟩] using
        (hjet u huI v hvI).1
  · apply contDiffOn_one_of_continuous_coordinate_jets hu hv Y
      QY (fun p => fY p (X p, Y p))
      hY.continuousOn hQY.continuousOn hGY
    · intro u huI v hvI
      simpa only [QY, clippedPoint_eq_self hu.le hv.le
        ⟨(u, v), pair_mem_rectangle huI hvI⟩] using
        (hjet u huI v hvI).2
    · intro u huI v hvI
      exact hasDerivWithinAt_second_of_integral_equation_on_ball
        u₀ u₁ v₀ v₁ X Y y₀ fY hX hY c ρ hfY hball
        (fun p hp => (heq p hp).2) huI hvI

end Goursat

end
