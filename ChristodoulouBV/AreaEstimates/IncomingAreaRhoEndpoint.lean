module

public import ChristodoulouBV.AreaEstimates.IncomingAreaEndpoint
public import ChristodoulouBV.AreaEstimates.OutgoingAreaRhoMeasurable
import all ChristodoulouBV.AreaEstimates.OutgoingAreaDensity
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The outgoing-axis limit in the conjugate rho estimate

The lower boundary term vanishes by `rho_axis_out` and positivity of `λ`.
The extended integral argument allows an infinite Jacobian area.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

private theorem sourceRho_forward_fiber_integrable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u a c : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Ioo u 1) (hc : c ∈ Ioo a 1) :
    IntervalIntegrable
      (fun v => |2 * (|sourceRho S u v| / S.r u v ^ 3)|)
      volume a c := by
  let B : ℝ := (c + 1) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun v => C1Solution.canonicalRadius S (u, v)
  let I : ℝ → ℝ := fun v => sourceRho S u v / S.lam u v
  let L : ℝ → ℝ := fun v => S.lam u v
  let G : ℝ → ℝ := fun v => |2 * (|I v * L v| / R v ^ 3)|
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, ha.1, hc.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hc.2]
  have hcB : c < B := by dsimp [B]; linarith only [hc.2]
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc a c) K := by
    intro v hv
    exact ⟨hu.1.le, ha.1.le.trans hv.1, hv.2.trans hcB.le⟩
  have hpath : ContinuousOn (fun v : ℝ => (u, v)) (Icc a c) := by
    fun_prop
  have hI : ContinuousOn I (Icc a c) :=
    (sourceRhoOverLam_contDiffOn_fiber H hu ha hc).continuousOn
  have hL : ContinuousOn L (Icc a c) :=
    (C1Solution.five_fields_contDiffOn hB hB1 H).1.continuousOn.comp
      hpath hmap
  have hR : ContinuousOn R (Icc a c) :=
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H).continuousOn.comp
      hpath hmap
  have hRne (v : ℝ) (hv : v ∈ Icc a c) : R v ^ 3 ≠ 0 := by
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, ha.1.trans_le hv.1, hv.2.trans_lt hc.2⟩
    change C1Solution.canonicalRadius S (u, v) ^ 3 ≠ 0
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1.le (ha.1.trans_le hv.1) (hv.2.trans hcB.le)]
    exact pow_ne_zero 3 (ne_of_gt (H.solution.radius_pos (u, v) hpU))
  have hG : ContinuousOn G (Icc a c) :=
    (continuousOn_const.mul
      ((hI.mul hL).abs.div (hR.pow 3) hRne)).abs
  have hGInt : IntervalIntegrable G volume a c :=
    hG.intervalIntegrable_of_Icc hc.1.le
  apply hGInt.congr_uIoo
  intro v hv
  have hv' : v ∈ Ioo a c := by
    simpa only [uIoo_of_le hc.1.le] using hv
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.1.le, ha.1.trans hv'.1, hv'.2.trans hc.2⟩
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    hu.1.le (ha.1.trans hv'.1) (hv'.2.le.trans hcB.le)
  have hlamne := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  dsimp [G, I, L, R]
  rw [hr]
  field_simp [hlamne]

private theorem sourceRho_forward_axis_boundary {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun v =>
      sourceRho S u v / S.lam u v / S.r u v ^ 2)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  let B : ℝ := (u + 1) / 2
  let K := closedCoordTriangle 0 B
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hu.2]
  have huB : u < B := by dsimp [B]; linarith only [hu.2]
  have hpath : ContinuousOn (fun v : ℝ => (u, v)) (Icc u B) := by
    fun_prop
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc u B) K := by
    intro v hv
    exact ⟨hu.1.le, hv.1, hv.2⟩
  have hLamCont : ContinuousOn (fun v => S.lam u v) (Icc u B) :=
    (C1Solution.five_fields_contDiffOn hB hB1 H).1.continuousOn.comp
      hpath hmap
  have hLamEnd : Tendsto (fun v => S.lam u v) (𝓝[>] u)
      (𝓝 (S.lam u u)) := by
    have hright : ContinuousWithinAt (fun v => S.lam u v) (Ici u) u :=
      (continuousWithinAt_Icc_iff_Ici huB).mp
        (hLamCont.continuousWithinAt ⟨le_rfl, huB.le⟩)
    exact (hright.mono Ioi_subset_Ici_self).tendsto
  obtain ⟨δ, hδ, hlamLower⟩ :=
    C1Solution.exists_lam_lower_bound hB hB1 H
  have hlamne : S.lam u u ≠ 0 :=
    ne_of_gt (hδ.trans_le (hlamLower (u, u)
      (show (u, u) ∈ K from ⟨hu.1.le, le_rfl, huB.le⟩)))
  have hratio := (rho_axis_out H hr hcenter hboot hu).div hLamEnd hlamne
  have heq : (fun v => sourceRho S u v / S.lam u v / S.r u v ^ 2) =ᶠ[𝓝[>] u]
      (fun v => (sourceRho S u v / S.r u v ^ 2) / S.lam u v) := by
    filter_upwards [Ioo_mem_nhdsGT huB] with v hv
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hv.1, hv.2.trans hB1⟩
    have hrne := ne_of_gt (H.solution.radius_pos (u, v) hpU)
    have hlamne' := ne_of_gt (H.solution.lam_pos (u, v) hpU)
    field_simp [hrne, hlamne']
  simpa only [zero_div] using hratio.congr' heq.symm

/-- The fixed-outgoing-fiber half-area inequality used in (4.28). -/
theorem sourceRho_forward_fiber_lintegral_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    2 * (∫⁻ v in Ioo u 1, sourceRhoDensity S (u, v)) ≤
      ∫⁻ v in Ioo u 1,
        ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det| := by
  let g : ℝ → ℝ := fun v =>
    |2 * (|sourceRho S u v| / S.r u v ^ 3)|
  let f : ℝ → ℝ := fun v =>
    |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det|
  let q : ℝ → ℝ := fun v =>
    sourceRho S u v / S.lam u v / S.r u v ^ 2
  have hgi (a c : ℝ) (ha : u < a) (hac : a < c) (hc : c < 1) :
      IntervalIntegrable g volume a c :=
    sourceRho_forward_fiber_integrable H hu ⟨ha, hac.trans hc⟩ ⟨hac, hc⟩
  have hfi (a c : ℝ) (ha : u < a) (hac : a < c) (hc : c < 1) :
      IntervalIntegrable f volume a c :=
    sourcePhiAlphaLam_jacobian_integrable_fiber H hu
      ⟨ha, hac.trans hc⟩ ⟨hac, hc⟩
  have hbound (a c : ℝ) (ha : u < a) (hac : a < c) (hc : c < 1) :
      (∫ v in a..c, g v) ≤
        |q a| + ∫ v in a..c, f v := by
    have h := sourceRho_forward_finite_integral_bound H hr hcenter hboot hu
      ⟨ha, hac.trans hc⟩ ⟨hac, hc⟩
    have heq : (∫ v in a..c, g v) =
        ∫ v in a..c, 2 * (|sourceRho S u v| / S.r u v ^ 3) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hac.le
      intro v hv
      change |2 * (|sourceRho S u v| / S.r u v ^ 3)| = _
      have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
        ⟨hu.1.le, ha.trans hv.1, hv.2.trans hc⟩
      have hrpos := H.solution.radius_pos (u, v) hpU
      exact abs_of_nonneg (mul_nonneg (by norm_num)
        (div_nonneg (abs_nonneg _) (pow_nonneg hrpos.le _)))
    rw [heq]
    have hrpos : 0 < S.r u a := H.solution.radius_pos (u, a)
      ⟨hu.1.le, ha, hac.trans hc⟩
    have hqa : |q a| = |sourceRho S u a / S.lam u a| / S.r u a ^ 2 := by
      change |sourceRho S u a / S.lam u a / S.r u a ^ 2| = _
      rw [abs_div, abs_of_pos (pow_pos hrpos 2)]
    rw [hqa]
    exact h
  have hFull := incoming_area_endpoint_lintegral_bound hu.2
    (fun v => abs_nonneg _) (fun v => abs_nonneg _)
    hgi hfi (sourceRho_forward_axis_boundary H hr hcenter hboot hu) hbound
  have hleft : (∫⁻ v in Ioo u 1, ENNReal.ofReal (g v)) =
      2 * (∫⁻ v in Ioo u 1, sourceRhoDensity S (u, v)) := by
    calc
      (∫⁻ v in Ioo u 1, ENNReal.ofReal (g v)) =
          ∫⁻ v in Ioo u 1, 2 * sourceRhoDensity S (u, v) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro v hv
        have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
          ⟨hu.1.le, hv.1, hv.2⟩
        have hrpos := H.solution.radius_pos (u, v) hpU
        have hnonneg : 0 ≤ 2 * (|sourceRho S u v| / S.r u v ^ 3) :=
          mul_nonneg (by norm_num)
            (div_nonneg (abs_nonneg _) (pow_nonneg hrpos.le _))
        dsimp [g]
        rw [abs_of_nonneg hnonneg]
        change ENNReal.ofReal (2 * (|sourceRho S u v| / S.r u v ^ 3)) =
          2 * ENNReal.ofReal (|sourceRho S u v| / S.r u v ^ 3)
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = _ := lintegral_const_mul' _ _ (by norm_num)
  rw [hleft] at hFull
  exact hFull

end ChristodoulouBV

end
