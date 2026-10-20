module

public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TheoremBounds
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TheoremDeriv
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Existence and uniqueness of a closed-rectangle C¹ Goursat solution

The theorem assembles the ball fixed point, transverse Picard jets, their
Volterra limits, and the continuous-jet criterion for relative `C¹`.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- Existence and uniqueness of a ball-valued `C¹` Goursat solution with
continuous transverse jets on the entire closed rectangle. The full mixed
edge trace controls the ball margin. Uniform state and coordinate derivative
bounds are explicit hypotheses, allowing Banach state spaces. -/
theorem exists_unique_contDiffOn_goursat_solution_on_ball
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
    (r M H PX₀ QY₀ : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) (κ : NNReal)
    (hdata : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (x₀ p.2, y₀ p.1) c ≤ r)
    (hMX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX q z‖ ≤ M)
    (hMY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY q z‖ ≤ M)
    (hDFstate : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ w : E × F,
      ‖DF (p, z) ((0, 0), w)‖ ≤ (κ : ℝ) * ‖w‖)
    (hDGstate : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ w : E × F,
      ‖DG (p, z) ((0, 0), w)‖ ≤ (κ : ℝ) * ‖w‖)
    (hDFv : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖DF (p, z) ((0, 1), (0, 0))‖ ≤ H)
    (hDGu : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖DG (p, z) ((1, 0), (0, 0))‖ ≤ H)
    (hPX₀ : ∀ v ∈ Icc v₀ v₁, ‖x₀' v‖ ≤ PX₀)
    (hQY₀ : ∀ u ∈ Icc u₀ u₁, ‖y₀' u‖ ≤ QY₀)
    (hsize : r + M * max (u₁ - u₀) (v₁ - v₀) < ρ)
    (hsmall : (κ : ℝ) * max (u₁ - u₀) (v₁ - v₀) < 1) :
    ∃ X : ℝ × ℝ → E, ∃ Y : ℝ × ℝ → F,
    ∃ P : C(rectangle u₀ u₁ v₀ v₁, E),
    ∃ Q : C(rectangle u₀ u₁ v₀ v₁, F),
      Continuous X ∧ Continuous Y ∧
      (∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X p, Y p) c ≤ ρ) ∧
      (∀ p ∈ rectangle u₀ u₁ v₀ v₁,
        X p = x₀ p.2 + ∫ s in u₀..p.1,
          fX (s, p.2) (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in v₀..p.2,
          fY (p.1, t) (X (p.1, t), Y (p.1, t))) ∧
      ContDiffOn ℝ 1 X (rectangle u₀ u₁ v₀ v₁) ∧
      ContDiffOn ℝ 1 Y (rectangle u₀ u₁ v₀ v₁) ∧
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
          (P ⟨(u, v), pair_mem_rectangle huI hvI⟩) (Icc v₀ v₁) v ∧
        HasDerivWithinAt (fun s => Y (s, v))
          (Q ⟨(u, v), pair_mem_rectangle huI hvI⟩) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun s => X (s, v))
          (fX (u, v) (X (u, v), Y (u, v))) (Icc u₀ u₁) u ∧
        HasDerivWithinAt (fun t => Y (u, t))
          (fY (u, v) (X (u, v), Y (u, v))) (Icc v₀ v₁) v) ∧
      (∀ (v : ℝ) (hvI : v ∈ Icc v₀ v₁),
        P ⟨(u₀, v), pair_mem_rectangle ⟨le_rfl, hu.le⟩ hvI⟩ = x₀' v) ∧
      (∀ (u : ℝ) (huI : u ∈ Icc u₀ u₁),
        Q ⟨(u, v₀), pair_mem_rectangle huI ⟨le_rfl, hv.le⟩⟩ = y₀' u) ∧
      (∀ p : rectangle u₀ u₁ v₀ v₁,
        ‖P p‖ ≤ (PX₀ + (H + (κ : ℝ) * M) * (p.1.1 - u₀)) *
          Real.exp ((κ : ℝ) * (p.1.1 - u₀))) ∧
      (∀ p : rectangle u₀ u₁ v₀ v₁,
        ‖Q p‖ ≤ (QY₀ + (H + (κ : ℝ) * M) * (p.1.2 - v₀)) *
          Real.exp ((κ : ℝ) * (p.1.2 - v₀))) ∧
      (∀ p : rectangle u₀ u₁ v₀ v₁,
        ‖P p‖ ≤ (PX₀ + (H + (κ : ℝ) * M) * (u₁ - u₀)) *
          Real.exp ((κ : ℝ) * (u₁ - u₀))) ∧
      (∀ p : rectangle u₀ u₁ v₀ v₁,
        ‖Q p‖ ≤ (QY₀ + (H + (κ : ℝ) * M) * (v₁ - v₀)) *
          Real.exp ((κ : ℝ) * (v₁ - v₀))) ∧
      (HasDerivWithinAt (fun s => X (s, v₀))
          (fX (u₀, v₀) (X (u₀, v₀), Y (u₀, v₀))) (Icc u₀ u₁) u₀ ∧
        HasDerivWithinAt (fun t => X (u₀, t)) (x₀' v₀) (Icc v₀ v₁) v₀ ∧
        HasDerivWithinAt (fun s => Y (s, v₀)) (y₀' u₀) (Icc u₀ u₁) u₀ ∧
        HasDerivWithinAt (fun t => Y (u₀, t))
          (fY (u₀, v₀) (X (u₀, v₀), Y (u₀, v₀))) (Icc v₀ v₁) v₀) ∧
      (∀ (X' : ℝ × ℝ → E) (Y' : ℝ × ℝ → F),
        Continuous X' → Continuous Y' →
        (∀ p ∈ rectangle u₀ u₁ v₀ v₁, dist (X' p, Y' p) c ≤ ρ) →
        (∀ p ∈ rectangle u₀ u₁ v₀ v₁,
          X' p = x₀ p.2 + ∫ s in u₀..p.1,
            fX (s, p.2) (X' (s, p.2), Y' (s, p.2)) ∧
          Y' p = y₀ p.1 + ∫ t in v₀..p.2,
            fY (p.1, t) (X' (p.1, t), Y' (p.1, t))) →
        ∀ p ∈ rectangle u₀ u₁ v₀ v₁, X p = X' p ∧ Y p = Y' p) := by
  have hLX : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fX q z) (fX q z') ≤ (κ : ℝ) * dist z z' := by
    intro q hq z z' hz hz'
    exact dist_nonlinearity_le_of_full_deriv_state_le fX DF q c ρ κ
      (hderivF q hq) (hDFstate q hq) hz hz'
  have hLY : ∀ q ∈ rectangle u₀ u₁ v₀ v₁, ∀ z z',
      dist z c ≤ ρ → dist z' c ≤ ρ →
      dist (fY q z) (fY q z') ≤ (κ : ℝ) * dist z z' := by
    intro q hq z z' hz hz'
    exact dist_nonlinearity_le_of_full_deriv_state_le fY DG q c ρ κ
      (hderivG q hq) (hDGstate q hq) hz hz'
  have hDFX : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ x : E,
      ‖DF (p, z) ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖ := by
    intro p hp z hz x
    simpa [Prod.norm_def] using hDFstate p hp z hz (x, 0)
  have hDGY : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ y : F,
      ‖DG (p, z) ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖ := by
    intro p hp z hz y
    simpa [Prod.norm_def] using hDGstate p hp z hz (0, y)
  have hDFsource : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ y : F,
      ‖DF (p, z) ((0, 1), (0, y))‖ ≤ H + (κ : ℝ) * ‖y‖ := by
    intro p hp z hz y
    have hsplit : (((0, 1), (0, y)) : (ℝ × ℝ) × (E × F)) =
        ((0, 1), (0, 0)) + ((0, 0), (0, y)) := by ext <;> simp
    rw [hsplit, map_add]
    calc
      _ ≤ ‖DF (p, z) ((0, 1), (0, 0))‖ +
          ‖DF (p, z) ((0, 0), (0, y))‖ := norm_add_le _ _
      _ ≤ H + (κ : ℝ) * ‖y‖ :=
        add_le_add (hDFv p hp z hz) (by
          simpa [Prod.norm_def] using hDFstate p hp z hz (0, y))
  have hDGsource : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ x : E,
      ‖DG (p, z) ((1, 0), (x, 0))‖ ≤ H + (κ : ℝ) * ‖x‖ := by
    intro p hp z hz x
    have hsplit : (((1, 0), (x, 0)) : (ℝ × ℝ) × (E × F)) =
        ((1, 0), (0, 0)) + ((0, 0), (x, 0)) := by ext <;> simp
    rw [hsplit, map_add]
    calc
      _ ≤ ‖DG (p, z) ((1, 0), (0, 0))‖ +
          ‖DG (p, z) ((0, 0), (x, 0))‖ := norm_add_le _ _
      _ ≤ H + (κ : ℝ) * ‖x‖ :=
        add_le_add (hDGu p hp z hz) (by
          simpa [Prod.norm_def] using hDGstate p hp z hz (x, 0))
  obtain ⟨X, Y, hX, hY, hball, heq⟩ :=
    exists_continuous_solution_on_rectangle_of_lipschitzOn_ball
      u₀ u₁ v₀ v₁ hu.le hv.le x₀ y₀ fX fY hx₀ hy₀
      c ρ r M hρ hM κ hfX hfY hdata hMX hMY hLX hLY hsize.le hsmall
  obtain ⟨P, Q, hPeq, hQeq, hjet⟩ :=
    exists_continuous_transverse_jets_of_integral_equations_on_ball
      u₀ u₁ v₀ v₁ hu hv x₀ x₀' y₀ y₀' hx₀ hy₀ hx₀' hy₀'
      hdx₀ hdy₀ c ρ hρ fX fY DF DG hfX hfY hDF hDG hderivF hderivG
      r M hM κ hdata hMX hMY hLX hLY hDFX hDGY hsize.le hsmall
      X Y hX hY hball heq
  have hC1 := contDiffOn_one_of_goursat_transverse_jets
    u₀ u₁ v₀ v₁ hu hv X Y hX hY x₀ y₀ fX fY c ρ
    hfX hfY hball heq P Q hjet
  have hbound := norm_transverse_le_exp_of_goursat_jets
    u₀ u₁ v₀ v₁ hu.le hv.le X Y hX hY c ρ
    fX fY DF DG hfX hfY hDF hDG hball
    M H PX₀ QY₀ hM hH κ hMX hMY hDFX hDGY
    hDFsource hDGsource x₀' y₀' hPX₀ hQY₀ P Q hPeq hQeq
  have hBnonneg : 0 ≤ H + (κ : ℝ) * M :=
    add_nonneg hH (mul_nonneg κ.coe_nonneg hM)
  have hPX₀nonneg : 0 ≤ PX₀ :=
    (norm_nonneg (x₀' v₀)).trans (hPX₀ v₀ ⟨le_rfl, hv.le⟩)
  have hQY₀nonneg : 0 ≤ QY₀ :=
    (norm_nonneg (y₀' u₀)).trans (hQY₀ u₀ ⟨le_rfl, hu.le⟩)
  refine ⟨X, Y, P, Q, hX, hY, hball, heq, hC1.1, hC1.2,
    hPeq, hQeq, ?_, ?_, ?_, hbound.1, hbound.2, ?_, ?_, ?_, ?_⟩
  · intro u huI v hvI
    exact ⟨(hjet u huI v hvI).1, (hjet u huI v hvI).2,
      hasDerivWithinAt_first_of_integral_equation_on_ball
        u₀ u₁ v₀ v₁ X Y x₀ fX hX hY c ρ hfX hball
        (fun p hp => (heq p hp).1) huI hvI,
      hasDerivWithinAt_second_of_integral_equation_on_ball
        u₀ u₁ v₀ v₁ X Y y₀ fY hX hY c ρ hfY hball
        (fun p hp => (heq p hp).2) huI hvI⟩
  · intro v hvI
    simpa only [intervalIntegral.integral_same, add_zero] using
      (hPeq ⟨(u₀, v), pair_mem_rectangle ⟨le_rfl, hu.le⟩ hvI⟩)
  · intro u huI
    simpa only [intervalIntegral.integral_same, add_zero] using
      (hQeq ⟨(u, v₀), pair_mem_rectangle huI ⟨le_rfl, hv.le⟩⟩)
  · intro p
    have hpI : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2
    have hlen : p.1.1 - u₀ ≤ u₁ - u₀ := sub_le_sub_right hpI.1.2 _
    have hfactor : PX₀ + (H + (κ : ℝ) * M) * (p.1.1 - u₀) ≤
        PX₀ + (H + (κ : ℝ) * M) * (u₁ - u₀) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlen hBnonneg)
    have hfactor0 : 0 ≤ PX₀ + (H + (κ : ℝ) * M) * (u₁ - u₀) :=
      add_nonneg hPX₀nonneg (mul_nonneg hBnonneg (sub_nonneg.mpr hu.le))
    have hexp : Real.exp ((κ : ℝ) * (p.1.1 - u₀)) ≤
        Real.exp ((κ : ℝ) * (u₁ - u₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlen κ.coe_nonneg)
    calc
      ‖P p‖ ≤ (PX₀ + (H + (κ : ℝ) * M) * (p.1.1 - u₀)) *
          Real.exp ((κ : ℝ) * (p.1.1 - u₀)) := hbound.1 p
      _ ≤ (PX₀ + (H + (κ : ℝ) * M) * (u₁ - u₀)) *
          Real.exp ((κ : ℝ) * (p.1.1 - u₀)) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ ≤ (PX₀ + (H + (κ : ℝ) * M) * (u₁ - u₀)) *
          Real.exp ((κ : ℝ) * (u₁ - u₀)) :=
        mul_le_mul_of_nonneg_left hexp hfactor0
  · intro p
    have hpI : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2
    have hlen : p.1.2 - v₀ ≤ v₁ - v₀ := sub_le_sub_right hpI.2.2 _
    have hfactor : QY₀ + (H + (κ : ℝ) * M) * (p.1.2 - v₀) ≤
        QY₀ + (H + (κ : ℝ) * M) * (v₁ - v₀) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlen hBnonneg)
    have hfactor0 : 0 ≤ QY₀ + (H + (κ : ℝ) * M) * (v₁ - v₀) :=
      add_nonneg hQY₀nonneg (mul_nonneg hBnonneg (sub_nonneg.mpr hv.le))
    have hexp : Real.exp ((κ : ℝ) * (p.1.2 - v₀)) ≤
        Real.exp ((κ : ℝ) * (v₁ - v₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlen κ.coe_nonneg)
    calc
      ‖Q p‖ ≤ (QY₀ + (H + (κ : ℝ) * M) * (p.1.2 - v₀)) *
          Real.exp ((κ : ℝ) * (p.1.2 - v₀)) := hbound.2 p
      _ ≤ (QY₀ + (H + (κ : ℝ) * M) * (v₁ - v₀)) *
          Real.exp ((κ : ℝ) * (p.1.2 - v₀)) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
      _ ≤ (QY₀ + (H + (κ : ℝ) * M) * (v₁ - v₀)) *
          Real.exp ((κ : ℝ) * (v₁ - v₀)) :=
        mul_le_mul_of_nonneg_left hexp hfactor0
  · have hcorner := hjet u₀ ⟨le_rfl, hu.le⟩ v₀ ⟨le_rfl, hv.le⟩
    have hPcorner : P ⟨(u₀, v₀),
        pair_mem_rectangle ⟨le_rfl, hu.le⟩ ⟨le_rfl, hv.le⟩⟩ = x₀' v₀ := by
      simpa only [intervalIntegral.integral_same, add_zero] using
        (hPeq ⟨(u₀, v₀),
          pair_mem_rectangle ⟨le_rfl, hu.le⟩ ⟨le_rfl, hv.le⟩⟩)
    have hQcorner : Q ⟨(u₀, v₀),
        pair_mem_rectangle ⟨le_rfl, hu.le⟩ ⟨le_rfl, hv.le⟩⟩ = y₀' u₀ := by
      simpa only [intervalIntegral.integral_same, add_zero] using
        (hQeq ⟨(u₀, v₀),
          pair_mem_rectangle ⟨le_rfl, hu.le⟩ ⟨le_rfl, hv.le⟩⟩)
    exact ⟨hasDerivWithinAt_first_of_integral_equation_on_ball
        u₀ u₁ v₀ v₁ X Y x₀ fX hX hY c ρ hfX hball
        (fun p hp => (heq p hp).1) ⟨le_rfl, hu.le⟩ ⟨le_rfl, hv.le⟩,
      hPcorner ▸ hcorner.1, hQcorner ▸ hcorner.2,
      hasDerivWithinAt_second_of_integral_equation_on_ball
        u₀ u₁ v₀ v₁ X Y y₀ fY hX hY c ρ hfY hball
        (fun p hp => (heq p hp).2) ⟨le_rfl, hu.le⟩ ⟨le_rfl, hv.le⟩⟩
  · intro X' Y' hX' hY' hball' heq'
    exact eq_on_rectangle_of_integral_equations_of_lipschitzOn_ball
      u₀ u₁ v₀ v₁ hu.le hv.le X X' Y Y' x₀ y₀ fX fY
      hX hX' hY hY' c ρ κ hfX hfY hball hball'
      hLX hLY hsmall heq heq'

end Goursat

end
