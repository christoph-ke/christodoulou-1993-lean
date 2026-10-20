module

public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
public import ChristodoulouBV.Uniqueness.RescalingBasic
public import ChristodoulouBV.C1Solution.Extraction
public import ChristodoulouBV.C1Solution.ExtractionMass
import Mathlib.Tactic

/-!
# Affine rescaling of frozen C¹ solutions

The positive affine chart preserves the frozen equations and the five C¹
fields, including regularity at the closed boundary of a development.
-/

public section

open Set
open scoped Interval

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.Uniqueness

/-- The two-coordinate affine chart maps the closure of a rescaled domain
into the closure of the original domain. -/
theorem affine_chart_mapsTo_closure {U : Set (ℝ × ℝ)} {a h : ℝ} :
    MapsTo (fun p : ℝ × ℝ =>
      (affineCoordinate a h p.1, affineCoordinate a h p.2))
      (closure (rescaledDomain U a h)) (closure U) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      (affineCoordinate a h p.1, affineCoordinate a h p.2)) := by
    unfold affineCoordinate
    fun_prop
  apply (Set.MapsTo.closure (t := U) ?_ hc)
  intro p hp
  exact hp.2

/-- A scalar C¹ field remains C¹ after the positive affine chart. -/
theorem contDiffOn_rescaled_field {U : Set (ℝ × ℝ)} {a h : ℝ}
    {f : ℝ × ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (closure U)) :
    ContDiffOn ℝ 1
      (fun p : ℝ × ℝ =>
        f (affineCoordinate a h p.1, affineCoordinate a h p.2))
      (closure (rescaledDomain U a h)) := by
  have hc : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      (affineCoordinate a h p.1, affineCoordinate a h p.2)) := by
    unfold affineCoordinate
    fun_prop
  exact hf.comp hc.contDiffOn affine_chart_mapsTo_closure

/-- The frozen C¹ solution predicate is invariant under a positive affine
change of both null coordinates. -/
theorem rescaled_isC1Solution {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsC1Solution U S) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    IsC1Solution (rescaledDomain U a h) (rescaledFields S a h) := by
  refine {
    solution := rescaled_isSolution H.solution ha hh
    nu_bounded_below := ?_
    lam_bounded_below := ?_
    lam_c1 := ?_
    nu_c1 := ?_
    phi_c1 := ?_
    theta_c1 := ?_
    zeta_c1 := ?_ }
  · obtain ⟨N, hN⟩ := H.nu_bounded_below
    exact ⟨N, fun p hp => hN _ hp.2⟩
  · obtain ⟨c, hc, hC⟩ := H.lam_bounded_below
    exact ⟨c, hc, fun p hp => hC _ hp.2⟩
  · exact contDiffOn_rescaled_field H.lam_c1
  · exact contDiffOn_rescaled_field H.nu_c1
  · exact contDiffOn_rescaled_field H.phi_c1
  · exact contDiffOn_rescaled_field H.theta_c1
  · exact contDiffOn_rescaled_field H.zeta_c1

/-- Rescaling by `h` divides the endpoint of an initial-edge development
by `h`. -/
theorem rescaledDomain_developmentWithInitialEdge (b : ℝ) {h : ℝ}
    (hh : 0 < h) :
    rescaledDomain (developmentWithInitialEdge b) 0 h =
      developmentWithInitialEdge (b / h) := by
  ext p
  rcases p with ⟨u, v⟩
  simp only [rescaledDomain, developmentWithInitialEdge, affineCoordinate,
    zero_add, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, _, huv, hv⟩
    exact ⟨hu, lt_of_mul_lt_mul_left huv hh.le,
      (lt_div_iff₀ hh).mpr (by simpa only [mul_comm] using hv)⟩
  · rintro ⟨hu, huv, hv⟩
    exact ⟨hu, mul_nonneg hh.le hu,
      mul_lt_mul_of_pos_left huv hh,
      by simpa only [mul_comm] using (lt_div_iff₀ hh).mp hv⟩

/-- A C¹ solution on an initial-edge development rescales to the
corresponding shorter chart. -/
theorem rescaled_development_isC1Solution {b h : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S) (hh : 0 < h) :
    IsC1Solution (developmentWithInitialEdge (b / h))
      (rescaledFields S 0 h) := by
  rw [← rescaledDomain_developmentWithInitialEdge b hh]
  exact rescaled_isC1Solution H le_rfl hh

/-- Equal initial radius and scalar data remain equal after rescaling
two possibly different development lifetimes. -/
theorem rescaled_initial_data_eq {b₁ b₂ h : ℝ} {S₁ S₂ : Fields}
    (hh : 0 < h)
    (hdata : ∀ v, (0, v) ∈
      developmentWithInitialEdge b₁ ∩ developmentWithInitialEdge b₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v) :
    ∀ v, (0, v) ∈
      developmentWithInitialEdge (b₁ / h) ∩
        developmentWithInitialEdge (b₂ / h) →
      (rescaledFields S₁ 0 h).r 0 v =
        (rescaledFields S₂ 0 h).r 0 v ∧
      (rescaledFields S₁ 0 h).phi 0 v =
        (rescaledFields S₂ 0 h).phi 0 v := by
  intro v hv
  have h₁ : (0, h * v) ∈ developmentWithInitialEdge b₁ := by
    have hv₁ := hv.1
    rw [← rescaledDomain_developmentWithInitialEdge b₁ hh] at hv₁
    simpa only [rescaledDomain, affineCoordinate, mul_zero, zero_add,
      Set.mem_ofPred_eq] using hv₁.2
  have h₂ : (0, h * v) ∈ developmentWithInitialEdge b₂ := by
    have hv₂ := hv.2
    rw [← rescaledDomain_developmentWithInitialEdge b₂ hh] at hv₂
    simpa only [rescaledDomain, affineCoordinate, mul_zero, zero_add,
      Set.mem_ofPred_eq] using hv₂.2
  obtain ⟨hr, hphi⟩ := hdata (h * v) ⟨h₁, h₂⟩
  exact ⟨by simpa only [rescaledFields, affineCoordinate, mul_zero,
    zero_add] using congrArg (fun x : ℝ => x / h) hr,
    by simpa only [rescaledFields, affineCoordinate, mul_zero,
      zero_add] using hphi⟩

/-- The canonical radius commutes with rescaling, with radial weight one. -/
theorem canonicalRadius_rescaled (S : Fields) {h : ℝ} (hh : 0 < h)
    (u v : ℝ) :
    canonicalRadius (rescaledFields S 0 h) (u, v) =
      canonicalRadius S (h * u, h * v) / h := by
  simp only [canonicalRadius, intervalIntegral.weightedDiagonalRadius,
    rescaledFields, affineCoordinate, zero_add]
  apply (eq_div_iff hh.ne').2
  simpa only [smul_eq_mul, mul_comm] using
    (intervalIntegral.smul_integral_comp_mul_left
      (f := fun t : ℝ => S.lam (h * u) t) (a := u) (b := v) h)

/-- The canonical scalar radius has the same rescaling weight. -/
theorem canonicalScalarRadius_rescaled (S : Fields) {h : ℝ} (hh : 0 < h)
    (u v : ℝ) :
    canonicalScalarRadius (rescaledFields S 0 h) (u, v) =
      canonicalScalarRadius S (h * u, h * v) / h := by
  simp only [canonicalScalarRadius, intervalIntegral.weightedDiagonalRadius,
    rescaledFields, affineCoordinate, zero_add]
  apply (eq_div_iff hh.ne').2
  simpa only [smul_eq_mul, mul_comm] using
    (intervalIntegral.smul_integral_comp_mul_left
      (f := fun t : ℝ => S.alpha (h * u) t) (a := u) (b := v) h)

/-- The canonical mass totalization commutes with rescaling, including
the excluded axis and terminal boundary. -/
theorem canonicalMass_rescaled (b : ℝ) (S : Fields) {h : ℝ} (hh : 0 < h)
    (u v : ℝ) :
    canonicalMass (b / h) (rescaledFields S 0 h) (u, v) =
      canonicalMass b S (h * u, h * v) / h := by
  have heq' : (u, v) ∈ developmentWithInitialEdge (b / h) ↔
      0 ≤ u ∧ (h * u, h * v) ∈ developmentWithInitialEdge b := by
    rw [← rescaledDomain_developmentWithInitialEdge b hh]
    simp only [rescaledDomain, affineCoordinate, zero_add, Set.mem_ofPred_eq]
  by_cases hp : (u, v) ∈ developmentWithInitialEdge (b / h)
  · have hq : (h * u, h * v) ∈ developmentWithInitialEdge b := by
      exact (heq'.mp hp).2
    simp [canonicalMass, hp, hq, rescaledFields, affineCoordinate]
  · have hq : (h * u, h * v) ∉ developmentWithInitialEdge b := by
      intro hq
      apply hp
      apply heq'.mpr
      exact ⟨(show 0 ≤ u from by
        have hhu : 0 ≤ h * u := hq.1
        exact nonneg_of_mul_nonneg_left
          (by simpa only [mul_comm] using hhu) hh), by
        simpa only [affineCoordinate, zero_add] using hq⟩
    simp [canonicalMass, hp, hq]

/-- The canonical mass ratio is invariant under rescaling, including
its zero extension on the axis. -/
theorem canonicalMassRatio_rescaled (b : ℝ) (S : Fields)
    {h : ℝ} (hh : 0 < h) (u v : ℝ) :
    canonicalMassRatio (b / h) (rescaledFields S 0 h) (u, v) =
      canonicalMassRatio b S (h * u, h * v) := by
  rw [canonicalMassRatio, canonicalMassRatio,
    canonicalMass_rescaled b S hh, canonicalRadius_rescaled S hh]
  by_cases hr : canonicalRadius S (h * u, h * v) = 0
  · simp [hr]
  · field_simp [hh.ne', hr]

end ChristodoulouBV.C1Solution

end
