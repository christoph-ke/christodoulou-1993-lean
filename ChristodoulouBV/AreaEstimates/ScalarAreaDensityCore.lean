module

public import ChristodoulouBV.AreaEstimates.ScalarAreaWeights
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude
import Mathlib.Tactic

/-!
# Coordinate derivatives on the strict unit development

These lemmas identify the one-variable derivatives in the transport bounds
with the Fréchet coordinate jets in the area Jacobians.
-/

public section

open Set MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- A field that is C¹ on the closed unit triangle is differentiable at every
strict point of that triangle. -/
theorem s4_differentiableAt_of_contDiffOn
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 1))
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    DifferentiableAt ℝ f (u, v) := by
  have hp : (u, v) ∈ closedCoordTriangle 0 1 :=
    ⟨hu.le, huv.le, hv.le⟩
  have hpInt : (u, v) ∈ interior (closedCoordTriangle 0 1) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hv⟩
  have hnhds : closedCoordTriangle 0 1 ∈ 𝓝 (u, v) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  exact (hf.differentiableOn (by norm_num) (u, v) hp).differentiableAt hnhds

/-- A vertical section derivative is the vertical Fréchet coordinate jet. -/
theorem s4_vertical_deriv {f : ℝ × ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ f (u, v)) :
    deriv (fun t => f (u, t)) v = (fderiv ℝ f (u, v)) (0, 1) := by
  have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  simpa only [Function.comp_def] using
    (hf.hasFDerivAt.comp_hasDerivAt v hpair).deriv

/-- A horizontal section derivative is the horizontal Fréchet coordinate jet. -/
theorem s4_horizontal_deriv {f : ℝ × ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ f (u, v)) :
    deriv (fun t => f (t, v)) u = (fderiv ℝ f (u, v)) (1, 0) := by
  have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  simpa only [Function.comp_def] using
    (hf.hasFDerivAt.comp_hasDerivAt u hpair).deriv

/-- The `(λ, φ)` absolute Jacobian is globally measurable. -/
theorem sourceLamPhiDensity_measurable (S : Fields) :
    Measurable (fun p => ENNReal.ofReal
      |(fderiv ℝ (sourceLamPhiMap S) p).det|) :=
  ((ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_fderiv ℝ (sourceLamPhiMap S))).abs).ennreal_ofReal

/-- The `(ν, φ)` absolute Jacobian is globally measurable. -/
theorem sourceNuPhiDensity_measurable (S : Fields) :
    Measurable (fun p => ENNReal.ofReal
      |(fderiv ℝ (sourceNuPhiMap S) p).det|) :=
  ((ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_fderiv ℝ (sourceNuPhiMap S))).abs).ennreal_ofReal

/-- The numerical amplitude bounds (4.3) hold at each strict point. -/
theorem sourceThetaZeta_pointwise {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 1) :
    |S.theta p.1 p.2| ≤ 5 * (sourceD S).toReal ∧
      |S.zeta p.1 p.2| ≤ 8 * (sourceD S).toReal := by
  have htheta : ContinuousOn (fun q : ℝ × ℝ => |S.theta q.1 q.2|)
      (closedCoordTriangle 0 1) :=
    (C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1) ▸ H.theta_c1).continuousOn.abs
  have hzeta : ContinuousOn (fun q : ℝ × ℝ => |S.zeta q.1 q.2|)
      (closedCoordTriangle 0 1) :=
    (C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1) ▸ H.zeta_c1).continuousOn.abs
  obtain ⟨Mtheta, hMtheta⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn htheta).bddAbove
  obtain ⟨Mzeta, hMzeta⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hzeta).bddAbove
  have hbTheta : BddAbove
      {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1, x = |S.theta q.1 q.2|} := by
    refine ⟨Mtheta, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    exact hMtheta ⟨q, ⟨hq.1, hq.2.1.le, hq.2.2.le⟩, rfl⟩
  have hbZeta : BddAbove
      {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1, x = |S.zeta q.1 q.2|} := by
    refine ⟨Mzeta, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    exact hMzeta ⟨q, ⟨hq.1, hq.2.1.le, hq.2.2.le⟩, rfl⟩
  have hpU : p ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2⟩
  have hbounds := eq4_3 H hr hcenter hboot
  have hThetaBound :
      sSup {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1,
        x = |S.theta q.1 q.2|} ≤ 5 * (sourceD S).toReal := by
    simpa only [sourceThetaAmp] using hbounds.1
  have hZetaBound :
      sSup {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1,
        x = |S.zeta q.1 q.2|} ≤ 8 * (sourceD S).toReal := by
    simpa only [sourceZetaAmp] using hbounds.2
  exact ⟨
    (le_csSup hbTheta ⟨p, hpU, rfl⟩).trans hThetaBound,
    (le_csSup hbZeta ⟨p, hpU, rfl⟩).trans hZetaBound⟩

/-- The bootstrap lower bound on `λ` gives the matching lower bound on
`-ν` through the BV sign theorem. -/
theorem sourceNu_le_neg_third {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 1) :
    S.nu p.1 p.2 ≤ -(1 / 3 : ℝ) := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  exact hBV.nu_le_neg_lower (by norm_num) hboot.1
    ⟨hp.1.le, hp.2.1, hp.2.2⟩

/-- Lift an absolute two-term Jacobian identity and coefficient bounds to
extended nonnegative densities. -/
theorem scalar_jacobian_density_bound
    {q a b R J : ℝ} {w f m c d : ℝ≥0∞}
    (hq : q = a * R + b * J)
    (ha : ENNReal.ofReal |a| ≤ c * w)
    (hR : ENNReal.ofReal |R| ≤ f)
    (hb : ENNReal.ofReal |b| ≤ d * m) :
    ENNReal.ofReal |q| ≤
      c * (w * f) + d * (m * ENNReal.ofReal |J|) := by
  have htri : ENNReal.ofReal |q| ≤
      ENNReal.ofReal |a * R| + ENNReal.ofReal |b * J| := by
    rw [hq]
    have hcast := ENNReal.ofReal_le_ofReal (abs_add_le (a * R) (b * J))
    rwa [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hcast
  have hfirst : ENNReal.ofReal |a * R| ≤ (c * w) * f := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    exact (mul_le_mul_of_nonneg_right ha bot_le).trans
      (mul_le_mul_of_nonneg_left hR bot_le)
  have hsecond : ENNReal.ofReal |b * J| ≤
      (d * m) * ENNReal.ofReal |J| := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_right hb bot_le
  calc
    ENNReal.ofReal |q| ≤
        ENNReal.ofReal |a * R| + ENNReal.ofReal |b * J| := htri
    _ ≤ (c * w) * f + (d * m) * ENNReal.ofReal |J| :=
      add_le_add hfirst hsecond
    _ = c * (w * f) + d * (m * ENNReal.ofReal |J|) := by ring

/-- The bootstrap lower bound on `λ` controls the two coefficients in
the outgoing scalar quotient Jacobian. -/
theorem alpha_area_coefficients
    {r lam zeta theta D : ℝ}
    (hr : 0 < r) (hlam : (1 / 3 : ℝ) ≤ lam)
    (hD : 0 ≤ D) (htheta : |theta| ≤ 5 * D) :
    ENNReal.ofReal |zeta / r / lam| ≤
        3 * ENNReal.ofReal (|zeta| / r) ∧
      ENNReal.ofReal |theta / lam ^ 2| ≤
        45 * ENNReal.ofReal D := by
  have hlpos : 0 < lam := by linarith only [hlam]
  have hw : 0 ≤ |zeta| / r := div_nonneg (abs_nonneg _) hr.le
  have hreal1 : |zeta / r / lam| ≤ 3 * (|zeta| / r) := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hlpos]
    apply (div_le_iff₀ hlpos).2
    have hm := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 3 * lam by linarith only [hlam]) hw
    nlinarith only [hm]
  have hcast1 := ENNReal.ofReal_le_ofReal hreal1
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hcast1
  have hsq : (1 / 9 : ℝ) ≤ lam ^ 2 := by
    have hmul : 0 ≤ (lam - 1 / 3) * (lam + 1 / 3) :=
      mul_nonneg (by linarith only [hlam]) (by linarith only [hlam])
    nlinarith only [hmul]
  have hreal2 : |theta / lam ^ 2| ≤ 45 * D := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hlpos)]
    apply (div_le_iff₀ (sq_pos_of_pos hlpos)).2
    have hm := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 45 * D by positivity)
    nlinarith only [htheta, hm]
  have hcast2 := ENNReal.ofReal_le_ofReal hreal2
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 45)] at hcast2
  exact ⟨by simpa using hcast1, by simpa using hcast2⟩

/-- The matching bounds for the incoming quotient Jacobian. -/
theorem beta_area_coefficients
    {r nu theta zeta D : ℝ}
    (hr : 0 < r) (hnu : nu ≤ -(1 / 3 : ℝ))
    (hD : 0 ≤ D) (hzeta : |zeta| ≤ 8 * D) :
    ENNReal.ofReal |theta / r / nu| ≤
        3 * ENNReal.ofReal (|theta| / r) ∧
      ENNReal.ofReal |zeta / nu ^ 2| ≤
        72 * ENNReal.ofReal D := by
  have hnneg : nu < 0 := by linarith only [hnu]
  have hna : (1 / 3 : ℝ) ≤ |nu| := by rw [abs_of_neg hnneg]; linarith only [hnu]
  have hnaPos : 0 < |nu| := abs_pos.mpr (ne_of_lt hnneg)
  have hw : 0 ≤ |theta| / r := div_nonneg (abs_nonneg _) hr.le
  have hreal1 : |theta / r / nu| ≤ 3 * (|theta| / r) := by
    rw [abs_div, abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hnaPos).2
    have hm := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ 3 * |nu| by linarith only [hna]) hw
    nlinarith only [hm]
  have hcast1 := ENNReal.ofReal_le_ofReal hreal1
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hcast1
  have hsq : (1 / 9 : ℝ) ≤ nu ^ 2 := by
    have hmul : 0 ≤ (|nu| - 1 / 3) * (|nu| + 1 / 3) :=
      mul_nonneg (by linarith only [hna]) (by linarith only [hna])
    rw [abs_of_neg hnneg] at hmul
    nlinarith only [hmul]
  have hreal2 : |zeta / nu ^ 2| ≤ 72 * D := by
    rw [abs_div, abs_of_pos (sq_pos_of_neg hnneg)]
    apply (div_le_iff₀ (sq_pos_of_neg hnneg)).2
    have hm := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 72 * D by positivity)
    nlinarith only [hzeta, hm]
  have hcast2 := ENNReal.ofReal_le_ofReal hreal2
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 72)] at hcast2
  exact ⟨by simpa using hcast1, by simpa using hcast2⟩

end ChristodoulouBV

end
