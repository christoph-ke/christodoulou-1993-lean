module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseJetSequence
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Continuous linearization fields for transverse Goursat jets

The full derivative of a Goursat nonlinearity yields a state coefficient and
an inhomogeneous transverse source. Both depend continuously on the state
and the known characteristic jet in the uniform norm on a rectangle.
-/

public section

open Set Filter
open scoped Topology

namespace Goursat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The linear coefficient multiplying the first component's transverse jet. -/
@[expose] noncomputable def firstLinearCoefficient
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E)) :
    C(rectangle u₀ u₁ v₀ v₁, E →L[ℝ] E) :=
  ⟨fun p => (D p).comp firstStateInclusion,
    D.continuous.clm_comp continuous_const⟩

/-- The transverse source of the first component, with the known vertical
jet of the second component included. -/
@[expose] noncomputable def firstLinearSource
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (R : C(rectangle u₀ u₁ v₀ v₁, F)) :
    C(rectangle u₀ u₁ v₀ v₁, E) :=
  ⟨fun p => D p ((0, 1), (0, R p)),
    D.continuous.clm_apply
      (continuous_const.prodMk (continuous_const.prodMk R.continuous))⟩

/-- The first transverse linear coefficient converges uniformly whenever
the full derivative field does. -/
theorem tendsto_firstLinearCoefficient
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (D_lim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (hD : Tendsto D atTop (𝓝 D_lim)) :
    Tendsto (fun n => firstLinearCoefficient (D n)) atTop
      (𝓝 (firstLinearCoefficient D_lim)) := by
  let H : C((((ℝ × ℝ) × (E × F)) →L[ℝ] E), E →L[ℝ] E) :=
    ⟨fun L => L.comp firstStateInclusion,
      continuous_id.clm_comp continuous_const⟩
  have h := (H.continuous_postcomp.tendsto D_lim).comp hD
  convert h using 1
  · funext n
    ext p
    rfl
  · congr 1

/-- The first transverse inhomogeneity converges uniformly whenever the
full derivative field and the known vertical jet converge uniformly. -/
theorem tendsto_firstLinearSource
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (R : ℕ → C(rectangle u₀ u₁ v₀ v₁, F))
    (D_lim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (R_lim : C(rectangle u₀ u₁ v₀ v₁, F))
    (hD : Tendsto D atTop (𝓝 D_lim))
    (hR : Tendsto R atTop (𝓝 R_lim)) :
    Tendsto (fun n => firstLinearSource (D n) (R n)) atTop
      (𝓝 (firstLinearSource D_lim R_lim)) := by
  let J : C(F, (ℝ × ℝ) × (E × F)) :=
    ⟨fun r => ((0, 1), (0, r)),
      continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩
  have hdir : Tendsto (fun n => J.comp (R n)) atTop
      (𝓝 (J.comp R_lim)) :=
    (J.continuous_postcomp.tendsto R_lim).comp hR
  have h := tendsto_continuousMap_clm_apply D
    (fun n => J.comp (R n)) D_lim (J.comp R_lim) hD hdir
  convert h using 1
  · funext n
    ext p
    rfl
  · congr 1

/-- The coefficient in the first transverse equation inherits a directional
derivative bound from the full derivative. -/
theorem norm_firstLinearCoefficient_le
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E))
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hD : ∀ p (x : E), ‖D p ((0, 0), (x, 0))‖ ≤ κ * ‖x‖)
    (p : rectangle u₀ u₁ v₀ v₁) :
    ‖firstLinearCoefficient D p‖ ≤ κ :=
  norm_firstState_comp_le (D p) κ hκ (hD p)


/-- The linear coefficient multiplying the second component's transverse jet. -/
@[expose] noncomputable def secondLinearCoefficient
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F)) :
    C(rectangle u₀ u₁ v₀ v₁, F →L[ℝ] F) :=
  ⟨fun p => (D p).comp secondStateInclusion,
    D.continuous.clm_comp continuous_const⟩

/-- The transverse source of the second component, including the known
horizontal jet of the first component. -/
@[expose] noncomputable def secondLinearSource
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (S : C(rectangle u₀ u₁ v₀ v₁, E)) :
    C(rectangle u₀ u₁ v₀ v₁, F) :=
  ⟨fun p => D p ((1, 0), (S p, 0)),
    D.continuous.clm_apply
      (continuous_const.prodMk (S.continuous.prodMk continuous_const))⟩

/-- Uniform convergence of full derivative fields implies uniform
convergence of their second-state coefficients. -/
theorem tendsto_secondLinearCoefficient
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (D_lim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (hD : Tendsto D atTop (𝓝 D_lim)) :
    Tendsto (fun n => secondLinearCoefficient (D n)) atTop
      (𝓝 (secondLinearCoefficient D_lim)) := by
  let H : C((((ℝ × ℝ) × (E × F)) →L[ℝ] F), F →L[ℝ] F) :=
    ⟨fun L => L.comp secondStateInclusion,
      continuous_id.clm_comp continuous_const⟩
  have h := (H.continuous_postcomp.tendsto D_lim).comp hD
  convert h using 1
  · funext n
    ext p
    rfl
  · congr 1

/-- Uniform convergence of the full derivative and known horizontal jet
implies uniform convergence of the second transverse source. -/
theorem tendsto_secondLinearSource
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : ℕ → C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (S : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (D_lim : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (S_lim : C(rectangle u₀ u₁ v₀ v₁, E))
    (hD : Tendsto D atTop (𝓝 D_lim))
    (hS : Tendsto S atTop (𝓝 S_lim)) :
    Tendsto (fun n => secondLinearSource (D n) (S n)) atTop
      (𝓝 (secondLinearSource D_lim S_lim)) := by
  let J : C(E, (ℝ × ℝ) × (E × F)) :=
    ⟨fun s => ((1, 0), (s, 0)),
      continuous_const.prodMk (continuous_id.prodMk continuous_const)⟩
  have hdir : Tendsto (fun n => J.comp (S n)) atTop
      (𝓝 (J.comp S_lim)) :=
    (J.continuous_postcomp.tendsto S_lim).comp hS
  have h := tendsto_continuousMap_clm_apply D
    (fun n => J.comp (S n)) D_lim (J.comp S_lim) hD hdir
  convert h using 1
  · funext n
    ext p
    rfl
  · congr 1

/-- The second-state directional derivative bound controls the operator
coefficient in the second transverse equation. -/
theorem norm_secondLinearCoefficient_le
    {u₀ u₁ v₀ v₁ : ℝ}
    (D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F))
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hD : ∀ p (y : F), ‖D p ((0, 0), (0, y))‖ ≤ κ * ‖y‖)
    (p : rectangle u₀ u₁ v₀ v₁) :
    ‖secondLinearCoefficient D p‖ ≤ κ :=
  norm_secondState_comp_le (D p) κ hκ (hD p)


/-- Split a full vertical jet into its first-state unknown and its known
coordinate and second-state part. -/
theorem first_linearized_split
    (L : ((ℝ × ℝ) × (E × F)) →L[ℝ] E) (x : E) (r : F) :
    L ((0, 1), (x, r)) =
      (L.comp (firstStateInclusion (E := E) (F := F))) x +
        L ((0, 1), (0, r)) := by
  have h : ((0, 1), (x, r)) =
      firstStateInclusion x + ((0, 1), (0, r)) := by
    simp [firstStateInclusion, Prod.add_def]
  rw [h, map_add]
  rfl

/-- Split a full horizontal jet into its second-state unknown and its known
coordinate and first-state part. -/
theorem second_linearized_split
    (L : ((ℝ × ℝ) × (E × F)) →L[ℝ] F) (s : E) (y : F) :
    L ((1, 0), (s, y)) =
      (L.comp (secondStateInclusion (E := E) (F := F))) y +
        L ((1, 0), (s, 0)) := by
  have h : ((1, 0), (s, y)) =
      secondStateInclusion y + ((1, 0), (s, 0)) := by
    simp [secondStateInclusion, Prod.add_def]
  rw [h, map_add]
  rfl

end Goursat

end
