module

public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TheoremExistence
import Mathlib.Tactic

/-!
# Off-axis seven-state rectangle equations

The incoming state `(λ, α)` evolves in `u`; the outgoing state
`(ν, β, m, r, ψ)` evolves in `v`. All rational coefficients are used only
on a state region with positive radius, outgoing expansion, and mass gap.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The two incoming variables `(λ, α)`. -/
abbrev IncomingState := ℝ × ℝ

/-- The five outgoing variables `(ν, β, m, r, ψ)`. -/
abbrev OutgoingState := ℝ × (ℝ × (ℝ × (ℝ × ℝ)))

/-- The seven-state phase space. -/
abbrev RectangleState := IncomingState × OutgoingState

/-- The expansion `λ`. -/
@[expose] def stateLam (z : RectangleState) : ℝ := z.1.1

/-- The scalar transport variable `α`. -/
@[expose] def stateAlpha (z : RectangleState) : ℝ := z.1.2

/-- The incoming expansion `ν`. -/
@[expose] def stateNu (z : RectangleState) : ℝ := z.2.1

/-- The scalar transport variable `β`. -/
@[expose] def stateBeta (z : RectangleState) : ℝ := z.2.2.1

/-- The Hawking mass `m`. -/
@[expose] def stateMass (z : RectangleState) : ℝ := z.2.2.2.1

/-- The area radius `r`. -/
@[expose] def stateRadius (z : RectangleState) : ℝ := z.2.2.2.2.1

/-- The rescaled scalar `ψ = r φ`. -/
@[expose] def statePsi (z : RectangleState) : ℝ := z.2.2.2.2.2

/-- The positive mass gap `r - 2m`. -/
@[expose] def stateMassGap (z : RectangleState) : ℝ :=
  stateRadius z - 2 * stateMass z

/-- The scalar field `φ = ψ/r` on states with `r > 0`. -/
@[expose] noncomputable def statePhi (z : RectangleState) : ℝ :=
  statePsi z / stateRadius z

/-- The outgoing scalar derivative numerator `θ`. -/
@[expose] noncomputable def stateTheta (z : RectangleState) : ℝ :=
  stateAlpha z - stateLam z * statePhi z

/-- The incoming scalar derivative numerator `ζ`. -/
@[expose] noncomputable def stateZeta (z : RectangleState) : ℝ :=
  stateBeta z - stateNu z * statePhi z

/-- The gravitational coefficient `K = 2m λ ν / (r (r-2m))`. -/
@[expose] noncomputable def stateGrav (z : RectangleState) : ℝ :=
  2 * stateMass z * stateLam z * stateNu z /
    (stateRadius z * stateMassGap z)

/-- The incoming pair of semilinear equations. -/
@[expose] noncomputable def rectangleF (z : RectangleState) : IncomingState :=
  (stateGrav z, stateGrav z * statePhi z)

/-- The outgoing quintuple of semilinear equations. -/
@[expose] noncomputable def rectangleG (z : RectangleState) : OutgoingState :=
  (stateGrav z,
    (stateGrav z * statePhi z,
      (stateMassGap z / stateRadius z * stateTheta z ^ 2 /
        (2 * stateLam z), (stateLam z, stateAlpha z))))

/-- Open off-axis safe states. -/
@[expose] def IsSafeRectangleState (z : RectangleState) : Prop :=
  0 < stateRadius z ∧ 0 < stateLam z ∧ stateNu z < 0 ∧
    0 < stateMassGap z

/-- A max-norm cube around a safe seven-state center. The last margin
accounts for one radius and twice the mass excursion in `r-2m`. -/
structure SafeRectangleBox where
  center : RectangleState
  radius : ℝ
  radius_pos : 0 < radius
  radius_margin : radius < stateRadius center
  lam_margin : radius < stateLam center
  nu_margin : radius < -stateNu center
  gap_margin : 3 * radius < stateMassGap center

/-- The closed state cube underlying a safe box. Product norms on the seven
real coordinates are maximum norms. -/
@[expose] def SafeRectangleBox.carrier (B : SafeRectangleBox) : Set RectangleState :=
  Metric.closedBall B.center B.radius

private theorem prod_dist_fst_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x y : E × F) : dist x.1 y.1 ≤ dist x y := by
  simpa [dist_eq_norm] using (norm_fst_le (x - y))

private theorem prod_dist_snd_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (x y : E × F) : dist x.2 y.2 ≤ dist x y := by
  simpa [dist_eq_norm] using (norm_snd_le (x - y))

private theorem abs_lam_sub_le_dist (z c : RectangleState) :
    |stateLam z - stateLam c| ≤ dist z c := by
  exact (by simpa only [stateLam, Real.dist_eq] using
    (prod_dist_fst_le z.1 c.1).trans (prod_dist_fst_le z c))

private theorem abs_alpha_sub_le_dist (z c : RectangleState) :
    |stateAlpha z - stateAlpha c| ≤ dist z c := by
  exact (by simpa only [stateAlpha, Real.dist_eq] using
    (prod_dist_snd_le z.1 c.1).trans (prod_dist_fst_le z c))

private theorem abs_nu_sub_le_dist (z c : RectangleState) :
    |stateNu z - stateNu c| ≤ dist z c := by
  exact (by simpa only [stateNu, Real.dist_eq] using
    (prod_dist_fst_le z.2 c.2).trans (prod_dist_snd_le z c))

private theorem abs_mass_sub_le_dist (z c : RectangleState) :
    |stateMass z - stateMass c| ≤ dist z c := by
  have h₁ := prod_dist_fst_le z.2.2.2 c.2.2.2
  have h₂ := prod_dist_snd_le z.2.2 c.2.2
  have h₃ := prod_dist_snd_le z.2 c.2
  have h₄ := prod_dist_snd_le z c
  simpa only [stateMass, Real.dist_eq] using h₁.trans (h₂.trans (h₃.trans h₄))

private theorem abs_radius_sub_le_dist (z c : RectangleState) :
    |stateRadius z - stateRadius c| ≤ dist z c := by
  have h₁ := prod_dist_fst_le z.2.2.2.2 c.2.2.2.2
  have h₂ := prod_dist_snd_le z.2.2.2 c.2.2.2
  have h₃ := prod_dist_snd_le z.2.2 c.2.2
  have h₄ := prod_dist_snd_le z.2 c.2
  have h₅ := prod_dist_snd_le z c
  simpa only [stateRadius, Real.dist_eq] using
    h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Every point of a safe box has a quantitatively positive area radius,
outgoing expansion, inward expansion, and mass gap. -/
theorem SafeRectangleBox.safe_bounds (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    stateRadius B.center - B.radius ≤ stateRadius z ∧
    stateLam B.center - B.radius ≤ stateLam z ∧
    stateNu z ≤ stateNu B.center + B.radius ∧
    stateMassGap B.center - 3 * B.radius ≤ stateMassGap z := by
  have hdist : dist z B.center ≤ B.radius := hz
  have hr := abs_radius_sub_le_dist z B.center |>.trans hdist
  have hl := abs_lam_sub_le_dist z B.center |>.trans hdist
  have hn := abs_nu_sub_le_dist z B.center |>.trans hdist
  have hm := abs_mass_sub_le_dist z B.center |>.trans hdist
  constructor
  · have h := (abs_le.mp hr).1
    linarith
  constructor
  · have h := (abs_le.mp hl).1
    linarith
  constructor
  · have h := (abs_le.mp hn).2
    linarith
  · dsimp only [stateMassGap]
    rcases abs_le.mp hr with ⟨hrlo, _⟩
    rcases abs_le.mp hm with ⟨_, hmhi⟩
    linarith

/-- The rational coefficients are well-defined throughout the safe cube. -/
theorem SafeRectangleBox.safe (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    IsSafeRectangleState z := by
  obtain ⟨hr, hl, hn, hg⟩ := B.safe_bounds hz
  exact ⟨by linarith [B.radius_margin], by linarith [B.lam_margin],
    by linarith [B.nu_margin], by linarith [B.gap_margin]⟩

/-- Every component is bounded above in absolute value by the center norm
plus the cube radius. -/
theorem SafeRectangleBox.component_bounds (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    |stateLam z| ≤ ‖B.center‖ + B.radius ∧
    |stateAlpha z| ≤ ‖B.center‖ + B.radius ∧
    |stateNu z| ≤ ‖B.center‖ + B.radius ∧
    |stateBeta z| ≤ ‖B.center‖ + B.radius ∧
    |stateMass z| ≤ ‖B.center‖ + B.radius ∧
    |stateRadius z| ≤ ‖B.center‖ + B.radius ∧
    |statePsi z| ≤ ‖B.center‖ + B.radius := by
  have hdist : ‖z - B.center‖ ≤ B.radius := by
    simpa only [SafeRectangleBox.carrier, Metric.mem_closedBall, dist_eq_norm] using hz
  have hnorm : ‖z‖ ≤ ‖B.center‖ + B.radius := by
    calc
      ‖z‖ = ‖(z - B.center) + B.center‖ := by congr 1; abel
      _ ≤ ‖z - B.center‖ + ‖B.center‖ := norm_add_le _ _
      _ ≤ ‖B.center‖ + B.radius := by linarith
  simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] at hnorm
  rcases hnorm with ⟨⟨hl, hα⟩, ⟨hν, hβ, hm, hr, hψ⟩⟩
  exact ⟨hl, hα, hν, hβ, hm, hr, hψ⟩

/-- An explicit positive lower bound for `1-2m/r` throughout the cube. -/
theorem SafeRectangleBox.mass_ratio_lower (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    0 < (stateMassGap B.center - 3 * B.radius) /
      (stateRadius B.center + B.radius) ∧
    (stateMassGap B.center - 3 * B.radius) /
      (stateRadius B.center + B.radius) ≤
        1 - 2 * stateMass z / stateRadius z := by
  obtain ⟨hrlo, _, _, hglo⟩ := B.safe_bounds hz
  have hrabs := abs_radius_sub_le_dist z B.center |>.trans
    (show dist z B.center ≤ B.radius from hz)
  have hrhi : stateRadius z ≤ stateRadius B.center + B.radius := by
    linarith [(abs_le.mp hrabs).2]
  have hrad : 0 < stateRadius z := (B.safe hz).1
  have hupper : 0 < stateRadius B.center + B.radius := by
    linarith [B.radius_margin, B.radius_pos]
  have hgap : 0 ≤ stateMassGap B.center - 3 * B.radius := by
    linarith [B.gap_margin]
  have hratio : 1 - 2 * stateMass z / stateRadius z =
      stateMassGap z / stateRadius z := by
    unfold stateMassGap
    field_simp
  constructor
  · exact div_pos (by linarith [B.gap_margin]) hupper
  · rw [hratio]
    apply (div_le_div_iff₀ hupper hrad).2
    calc
      (stateMassGap B.center - 3 * B.radius) * stateRadius z ≤
          (stateMassGap B.center - 3 * B.radius) *
            (stateRadius B.center + B.radius) :=
        mul_le_mul_of_nonneg_left hrhi hgap
      _ ≤ stateMassGap z * (stateRadius B.center + B.radius) :=
        mul_le_mul_of_nonneg_right hglo hupper.le

private theorem contDiffAt_stateLam (z : RectangleState) :
    ContDiffAt ℝ 1 stateLam z := by
  unfold stateLam
  fun_prop

private theorem contDiffAt_stateAlpha (z : RectangleState) :
    ContDiffAt ℝ 1 stateAlpha z := by
  unfold stateAlpha
  fun_prop

private theorem contDiffAt_stateNu (z : RectangleState) :
    ContDiffAt ℝ 1 stateNu z := by
  unfold stateNu
  fun_prop

private theorem contDiffAt_stateMass (z : RectangleState) :
    ContDiffAt ℝ 1 stateMass z := by
  unfold stateMass
  fun_prop

private theorem contDiffAt_stateRadius (z : RectangleState) :
    ContDiffAt ℝ 1 stateRadius z := by
  unfold stateRadius
  fun_prop

private theorem contDiffAt_statePsi (z : RectangleState) :
    ContDiffAt ℝ 1 statePsi z := by
  unfold statePsi
  fun_prop

private theorem contDiffAt_stateMassGap (z : RectangleState) :
    ContDiffAt ℝ 1 stateMassGap z := by
  unfold stateMassGap
  exact (contDiffAt_stateRadius z).sub
    (contDiffAt_const.mul (contDiffAt_stateMass z))

private theorem contDiffAt_statePhi {z : RectangleState}
    (hz : IsSafeRectangleState z) : ContDiffAt ℝ 1 statePhi z := by
  unfold statePhi
  exact (contDiffAt_statePsi z).div (contDiffAt_stateRadius z) (ne_of_gt hz.1)

private theorem contDiffAt_stateGrav {z : RectangleState}
    (hz : IsSafeRectangleState z) : ContDiffAt ℝ 1 stateGrav z := by
  unfold stateGrav
  apply ContDiffAt.div
  · exact (((contDiffAt_const.mul (contDiffAt_stateMass z)).mul
      (contDiffAt_stateLam z)).mul (contDiffAt_stateNu z))
  · exact (contDiffAt_stateRadius z).mul (contDiffAt_stateMassGap z)
  · exact mul_ne_zero (ne_of_gt hz.1) (ne_of_gt hz.2.2.2)

/-- The incoming rational nonlinearity is continuously differentiable at
every safe off-axis state. -/
theorem contDiffAt_rectangleF {z : RectangleState}
    (hz : IsSafeRectangleState z) : ContDiffAt ℝ 1 rectangleF z := by
  unfold rectangleF
  exact (contDiffAt_stateGrav hz).prodMk
    ((contDiffAt_stateGrav hz).mul (contDiffAt_statePhi hz))

/-- The outgoing rational nonlinearity is continuously differentiable at
every safe off-axis state. -/
theorem contDiffAt_rectangleG {z : RectangleState}
    (hz : IsSafeRectangleState z) : ContDiffAt ℝ 1 rectangleG z := by
  have hphi := contDiffAt_statePhi hz
  have htheta : ContDiffAt ℝ 1 stateTheta z := by
    unfold stateTheta
    exact (contDiffAt_stateAlpha z).sub ((contDiffAt_stateLam z).mul hphi)
  have hmass : ContDiffAt ℝ 1 (fun w : RectangleState =>
      stateMassGap w / stateRadius w * stateTheta w ^ 2 /
        (2 * stateLam w)) z := by
    apply ContDiffAt.div
    · exact ((contDiffAt_stateMassGap z).div
        (contDiffAt_stateRadius z) (ne_of_gt hz.1)).mul (htheta.pow 2)
    · exact contDiffAt_const.mul (contDiffAt_stateLam z)
    · exact mul_ne_zero (by norm_num) (ne_of_gt hz.2.1)
  unfold rectangleG
  exact (contDiffAt_stateGrav hz).prodMk
    (((contDiffAt_stateGrav hz).mul hphi).prodMk
      (hmass.prodMk ((contDiffAt_stateLam z).prodMk (contDiffAt_stateAlpha z))))

/-- An exact uniform value bound: it is the maximum of the two rational
field norms over the compact safe cube. -/
@[expose] noncomputable def SafeRectangleBox.valueBound (B : SafeRectangleBox) : ℝ :=
  max 0 (max
    (sSup ((fun z => ‖rectangleF z‖) '' B.carrier))
    (sSup ((fun z => ‖rectangleG z‖) '' B.carrier)))

/-- An exact uniform state-derivative bound. This is finite because the
seven-state cube is compact and both rational fields are `C¹` there. -/
@[expose] noncomputable def SafeRectangleBox.derivBound (B : SafeRectangleBox) : NNReal :=
  ⟨max 0 (max
    (sSup ((fun z => ‖fderiv ℝ rectangleF z‖) '' B.carrier))
    (sSup ((fun z => ‖fderiv ℝ rectangleG z‖) '' B.carrier))),
    le_max_left _ _⟩

private theorem norm_le_sSup_image_of_compact
    {E : Type*} [NormedAddCommGroup E]
    {K : Set RectangleState} (hK : IsCompact K)
    {f : RectangleState → E} (hf : ContinuousOn f K)
    {z : RectangleState} (hz : z ∈ K) :
    ‖f z‖ ≤ sSup ((fun w => ‖f w‖) '' K) := by
  have hcompact : IsCompact (((fun w => ‖f w‖) '' K)) :=
    hK.image_of_continuousOn hf.norm
  exact le_csSup hcompact.bddAbove ⟨z, hz, rfl⟩

private theorem continuousOn_fderiv_rectangleF (B : SafeRectangleBox) :
    ContinuousOn (fderiv ℝ rectangleF) B.carrier := by
  intro z hz
  exact ((contDiffAt_rectangleF (B.safe hz)).continuousAt_fderiv (by decide)).continuousWithinAt

private theorem continuousOn_fderiv_rectangleG (B : SafeRectangleBox) :
    ContinuousOn (fderiv ℝ rectangleG) B.carrier := by
  intro z hz
  exact ((contDiffAt_rectangleG (B.safe hz)).continuousAt_fderiv (by decide)).continuousWithinAt

/-- The safe cube has the explicit value bound `valueBound`. -/
theorem SafeRectangleBox.norm_rectangleF_le (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    ‖rectangleF z‖ ≤ B.valueBound := by
  have h := norm_le_sSup_image_of_compact
    (isCompact_closedBall B.center B.radius)
    (fun z hz => (contDiffAt_rectangleF (B.safe hz)).continuousAt.continuousWithinAt) hz
  exact h.trans ((le_max_left _ _).trans (le_max_right _ _))

/-- The safe cube has the explicit outgoing value bound `valueBound`. -/
theorem SafeRectangleBox.norm_rectangleG_le (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    ‖rectangleG z‖ ≤ B.valueBound := by
  have h := norm_le_sSup_image_of_compact
    (isCompact_closedBall B.center B.radius)
    (fun z hz => (contDiffAt_rectangleG (B.safe hz)).continuousAt.continuousWithinAt) hz
  exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The incoming state derivative is bounded by `derivBound` on the cube. -/
theorem SafeRectangleBox.norm_fderiv_rectangleF_le (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    ‖fderiv ℝ rectangleF z‖ ≤ (B.derivBound : ℝ) := by
  have h := norm_le_sSup_image_of_compact
    (isCompact_closedBall B.center B.radius)
    (continuousOn_fderiv_rectangleF B) hz
  exact h.trans ((le_max_left _ _).trans (le_max_right _ _))

/-- The outgoing state derivative is bounded by `derivBound` on the cube. -/
theorem SafeRectangleBox.norm_fderiv_rectangleG_le (B : SafeRectangleBox)
    {z : RectangleState} (hz : z ∈ B.carrier) :
    ‖fderiv ℝ rectangleG z‖ ≤ (B.derivBound : ℝ) := by
  have h := norm_le_sSup_image_of_compact
    (isCompact_closedBall B.center B.radius)
    (continuousOn_fderiv_rectangleG B) hz
  exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem contDiffAt_rectangleF_uncurry
    {q : (ℝ × ℝ) × RectangleState} (hz : IsSafeRectangleState q.2) :
    ContDiffAt ℝ 1 (fun t : (ℝ × ℝ) × RectangleState => rectangleF t.2) q := by
  exact (contDiffAt_rectangleF hz).comp q contDiffAt_snd

private theorem contDiffAt_rectangleG_uncurry
    {q : (ℝ × ℝ) × RectangleState} (hz : IsSafeRectangleState q.2) :
    ContDiffAt ℝ 1 (fun t : (ℝ × ℝ) × RectangleState => rectangleG t.2) q := by
  exact (contDiffAt_rectangleG hz).comp q contDiffAt_snd

private theorem fderiv_rectangleF_uncurry_eq
    {q : (ℝ × ℝ) × RectangleState} (hz : IsSafeRectangleState q.2) :
    fderiv ℝ (fun t : (ℝ × ℝ) × RectangleState => rectangleF t.2) q =
      (fderiv ℝ rectangleF q.2).comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) RectangleState) := by
  simpa only [Function.comp_def, fderiv_snd] using
    (((contDiffAt_rectangleF hz).differentiableAt_one.hasFDerivAt.comp q
      hasFDerivAt_snd).fderiv)

private theorem fderiv_rectangleG_uncurry_eq
    {q : (ℝ × ℝ) × RectangleState} (hz : IsSafeRectangleState q.2) :
    fderiv ℝ (fun t : (ℝ × ℝ) × RectangleState => rectangleG t.2) q =
      (fderiv ℝ rectangleG q.2).comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) RectangleState) := by
  simpa only [Function.comp_def, fderiv_snd] using
    (((contDiffAt_rectangleG hz).differentiableAt_one.hasFDerivAt.comp q
      hasFDerivAt_snd).fderiv)

/-- The incoming nonlinearity has no explicit `v` dependence, so its
coordinate derivative bound in the Goursat theorem is `H = 0`. -/
theorem rectangleF_coordinate_deriv_zero
    (p : ℝ × ℝ) {z : RectangleState} (hz : IsSafeRectangleState z) :
    (fderiv ℝ (fun q : (ℝ × ℝ) × RectangleState => rectangleF q.2)
      (p, z)) ((0, 1), (0, 0)) = 0 := by
  rw [fderiv_rectangleF_uncurry_eq (q := (p, z)) hz]
  change (fderiv ℝ rectangleF z) (0 : RectangleState) = 0
  simp

/-- The outgoing nonlinearity has no explicit `u` dependence, so its
coordinate derivative bound in the Goursat theorem is `H = 0`. -/
theorem rectangleG_coordinate_deriv_zero
    (p : ℝ × ℝ) {z : RectangleState} (hz : IsSafeRectangleState z) :
    (fderiv ℝ (fun q : (ℝ × ℝ) × RectangleState => rectangleG q.2)
      (p, z)) ((1, 0), (0, 0)) = 0 := by
  rw [fderiv_rectangleG_uncurry_eq (q := (p, z)) hz]
  change (fderiv ℝ rectangleG z) (0 : RectangleState) = 0
  simp

/-- C¹ minimal-data rectangle solution for the seven-state off-axis system.
The margin is measured over the full mixed characteristic trace
`(x₀(v),y₀(u))`; the only prescribed variables are `x₀` on `u=a₀` and
`y₀` on `v=b₀`. The lifetime inequalities are explicit in the safe cube's
value and derivative bounds. -/
theorem exists_unique_rectangle_solution
    (a₀ a₁ b₀ b₁ : ℝ) (ha : a₀ < a₁) (hb : b₀ < b₁)
    (_hoff : a₁ < b₀)
    (x₀ x₀' : ℝ → IncomingState) (y₀ y₀' : ℝ → OutgoingState)
    (hx₀ : Continuous x₀) (hy₀ : Continuous y₀)
    (hx₀' : ContinuousOn x₀' (Icc b₀ b₁))
    (hy₀' : ContinuousOn y₀' (Icc a₀ a₁))
    (hdx₀ : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt x₀ (x₀' v) (Icc b₀ b₁) v)
    (hdy₀ : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc a₀ a₁) u)
    (B : SafeRectangleBox) (rData PX₀ QY₀ : ℝ)
    (hdata : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      dist (x₀ p.2, y₀ p.1) B.center ≤ rData)
    (hPX₀ : ∀ v ∈ Icc b₀ b₁, ‖x₀' v‖ ≤ PX₀)
    (hQY₀ : ∀ u ∈ Icc a₀ a₁, ‖y₀' u‖ ≤ QY₀)
    (hsize : rData + B.valueBound * max (a₁ - a₀) (b₁ - b₀) < B.radius)
    (hsmall : (B.derivBound : ℝ) * max (a₁ - a₀) (b₁ - b₀) < 1) :
    ∃ X : ℝ × ℝ → IncomingState, ∃ Y : ℝ × ℝ → OutgoingState,
      Continuous X ∧ Continuous Y ∧
      (∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
        dist (X p, Y p) B.center ≤ B.radius) ∧
      (∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
        X p = x₀ p.2 + ∫ s in a₀..p.1,
          rectangleF (X (s, p.2), Y (s, p.2)) ∧
        Y p = y₀ p.1 + ∫ t in b₀..p.2,
          rectangleG (X (p.1, t), Y (p.1, t))) ∧
      ContDiffOn ℝ 1 X (Goursat.rectangle a₀ a₁ b₀ b₁) ∧
      ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁) ∧
      (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
        HasDerivWithinAt (fun s => X (s, v))
          (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
        HasDerivWithinAt (fun t => Y (u, t))
          (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v) ∧
      (∀ X' : ℝ × ℝ → IncomingState, ∀ Y' : ℝ × ℝ → OutgoingState,
        Continuous X' → Continuous Y' →
        (∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
          dist (X' p, Y' p) B.center ≤ B.radius) →
        (∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
          X' p = x₀ p.2 + ∫ s in a₀..p.1,
            rectangleF (X' (s, p.2), Y' (s, p.2)) ∧
          Y' p = y₀ p.1 + ∫ t in b₀..p.2,
            rectangleG (X' (p.1, t), Y' (p.1, t))) →
        ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
          X p = X' p ∧ Y p = Y' p) := by
  let fX : ℝ × ℝ → RectangleState → IncomingState := fun _ z => rectangleF z
  let fY : ℝ × ℝ → RectangleState → OutgoingState := fun _ z => rectangleG z
  let DF := fderiv ℝ (fun q : (ℝ × ℝ) × RectangleState => rectangleF q.2)
  let DG := fderiv ℝ (fun q : (ℝ × ℝ) × RectangleState => rectangleG q.2)
  have hF : ContinuousOn fX.uncurry
      (Goursat.rectangle a₀ a₁ b₀ b₁ ×ˢ {z | dist z B.center ≤ B.radius}) := by
    intro q hq
    exact (contDiffAt_rectangleF_uncurry (B.safe hq.2)).continuousAt.continuousWithinAt
  have hG : ContinuousOn fY.uncurry
      (Goursat.rectangle a₀ a₁ b₀ b₁ ×ˢ {z | dist z B.center ≤ B.radius}) := by
    intro q hq
    exact (contDiffAt_rectangleG_uncurry (B.safe hq.2)).continuousAt.continuousWithinAt
  have hDF : ContinuousOn DF
      (Goursat.rectangle a₀ a₁ b₀ b₁ ×ˢ {z | dist z B.center ≤ B.radius}) := by
    intro q hq
    exact ((contDiffAt_rectangleF_uncurry (B.safe hq.2)).continuousAt_fderiv
      (by decide)).continuousWithinAt
  have hDG : ContinuousOn DG
      (Goursat.rectangle a₀ a₁ b₀ b₁ ×ˢ {z | dist z B.center ≤ B.radius}) := by
    intro q hq
    exact ((contDiffAt_rectangleG_uncurry (B.safe hq.2)).continuousAt_fderiv
      (by decide)).continuousWithinAt
  have hderivF : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁, ∀ z,
      dist z B.center ≤ B.radius → HasFDerivAt fX.uncurry (DF (p, z)) (p, z) := by
    intro p hp z hz
    have hzB : z ∈ B.carrier := by
      simpa only [SafeRectangleBox.carrier, Metric.mem_closedBall] using hz
    exact (contDiffAt_rectangleF_uncurry (B.safe hzB)).differentiableAt_one.hasFDerivAt
  have hderivG : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁, ∀ z,
      dist z B.center ≤ B.radius → HasFDerivAt fY.uncurry (DG (p, z)) (p, z) := by
    intro p hp z hz
    have hzB : z ∈ B.carrier := by
      simpa only [SafeRectangleBox.carrier, Metric.mem_closedBall] using hz
    exact (contDiffAt_rectangleG_uncurry (B.safe hzB)).differentiableAt_one.hasFDerivAt
  have hDFstate : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁, ∀ z,
      dist z B.center ≤ B.radius → ∀ w : RectangleState,
      ‖DF (p, z) ((0, 0), w)‖ ≤ (B.derivBound : ℝ) * ‖w‖ := by
    intro p hp z hz w
    have hformula := fderiv_rectangleF_uncurry_eq (B.safe hz)
      (q := (p, z))
    change ‖(fderiv ℝ (fun q : (ℝ × ℝ) × RectangleState => rectangleF q.2)
      (p, z)) ((0, 0), w)‖ ≤ _
    rw [hformula]
    exact ((fderiv ℝ rectangleF z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (B.norm_fderiv_rectangleF_le hz) (norm_nonneg _))
  have hDGstate : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁, ∀ z,
      dist z B.center ≤ B.radius → ∀ w : RectangleState,
      ‖DG (p, z) ((0, 0), w)‖ ≤ (B.derivBound : ℝ) * ‖w‖ := by
    intro p hp z hz w
    have hformula := fderiv_rectangleG_uncurry_eq (B.safe hz)
      (q := (p, z))
    change ‖(fderiv ℝ (fun q : (ℝ × ℝ) × RectangleState => rectangleG q.2)
      (p, z)) ((0, 0), w)‖ ≤ _
    rw [hformula]
    exact ((fderiv ℝ rectangleG z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (B.norm_fderiv_rectangleG_le hz) (norm_nonneg _))
  have hDFv : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁, ∀ z,
      dist z B.center ≤ B.radius → ‖DF (p, z) ((0, 1), (0, 0))‖ ≤ (0 : ℝ) := by
    intro p hp z hz
    simpa only [DF, rectangleF_coordinate_deriv_zero p (B.safe hz), norm_zero] using
      (le_refl (0 : ℝ))
  have hDGu : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁, ∀ z,
      dist z B.center ≤ B.radius → ‖DG (p, z) ((1, 0), (0, 0))‖ ≤ (0 : ℝ) := by
    intro p hp z hz
    simpa only [DG, rectangleG_coordinate_deriv_zero p (B.safe hz), norm_zero] using
      (le_refl (0 : ℝ))
  obtain ⟨X, Y, P, Q, hX, hY, hball, heq, hCX, hCY,
    hPeq, hQeq, hjet, hPedge, hQedge, hPpoint, hQpoint,
    hPglobal, hQglobal, hcorner, huniq⟩ :=
    Goursat.exists_unique_contDiffOn_goursat_solution_on_ball
      a₀ a₁ b₀ b₁ ha hb x₀ x₀' y₀ y₀' hx₀ hy₀ hx₀' hy₀'
      hdx₀ hdy₀ B.center B.radius B.radius_pos fX fY DF DG
      hF hG hDF hDG hderivF hderivG rData B.valueBound 0 PX₀ QY₀
      (le_max_left _ _) le_rfl B.derivBound hdata
      (fun p hp z hz => B.norm_rectangleF_le hz)
      (fun p hp z hz => B.norm_rectangleG_le hz)
      hDFstate hDGstate hDFv hDGu hPX₀ hQY₀ hsize hsmall
  refine ⟨X, Y, hX, hY, hball, ?_, hCX, hCY, ?_, ?_⟩
  · simpa only [fX, fY] using heq
  · intro u hu v hv
    exact ⟨(hjet u hu v hv).2.2.1, (hjet u hu v hv).2.2.2⟩
  · simpa only [fX, fY] using huniq

end ChristodoulouBV.C1Solution

end
