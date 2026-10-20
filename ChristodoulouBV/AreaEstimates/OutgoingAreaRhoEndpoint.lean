module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaRhoMeasurable
import all ChristodoulouBV.AreaEstimates.OutgoingAreaDensity
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The terminal-axis limit in the rho area estimate

The finite-interval boundary term vanishes by `rho_axis` and the negative
axis trace of `ν`; the extended integral argument does not assume that the
Jacobian area is finite.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

private theorem sourceRho_fiber_integrable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v c : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo 0 v) :
    IntervalIntegrable
      (fun u => |2 * (|sourceRho S u v| / S.r u v ^ 3)|)
      volume 0 c := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun u => C1Solution.canonicalRadius S (u, v)
  let I : ℝ → ℝ := fun u => sourceRho S u v / S.nu u v
  let N : ℝ → ℝ := fun u => S.nu u v
  let G : ℝ → ℝ := fun u =>
    |2 * (|I u * N u| / R u ^ 3)|
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 c) K := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hc.2.le, hvB.le⟩
  have hpath : ContinuousOn (fun u : ℝ => (u, v)) (Icc 0 c) := by
    fun_prop
  have hI : ContinuousOn I (Icc 0 c) :=
    (sourceRhoOverNu_contDiffOn_fiber H hv hc).continuousOn
  have hN : ContinuousOn N (Icc 0 c) :=
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1.continuousOn.comp
      hpath hmap
  have hR : ContinuousOn R (Icc 0 c) :=
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H).continuousOn.comp
      hpath hmap
  have hRne (u : ℝ) (hu : u ∈ Icc 0 c) : R u ^ 3 ≠ 0 := by
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1, hu.2.trans_lt hc.2, hv.2⟩
    have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1 (hu.2.trans_lt hc.2) hvB.le
    change C1Solution.canonicalRadius S (u, v) ^ 3 ≠ 0
    rw [hr]
    exact pow_ne_zero 3 (ne_of_gt (H.solution.radius_pos (u, v) hpU))
  have hG : ContinuousOn G (Icc 0 c) :=
    (continuousOn_const.mul
      ((hI.mul hN).abs.div (hR.pow 3) hRne)).abs
  have hGInt : IntervalIntegrable G volume 0 c :=
    hG.intervalIntegrable_of_Icc hc.1.le
  apply hGInt.congr_uIoo
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) c := by
    simpa only [uIoo_of_le hc.1.le] using hu
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu'.1.le, hu'.2.trans hc.2, hv.2⟩
  have hr := C1Solution.canonicalRadius_eq_radius hB hB1 H
    hu'.1.le (hu'.2.trans hc.2) hvB.le
  have hnune := ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H
    (show (u, v) ∈ K from
      ⟨hu'.1.le, (hu'.2.trans hc.2).le, hvB.le⟩))
  dsimp [G, I, N, R]
  rw [hr]
  field_simp [hnune]

private theorem sourceRho_axis_boundary {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun u =>
      sourceRho S u v / S.nu u v / S.r u v ^ 2)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hpath : ContinuousOn (fun u : ℝ => (u, v)) (Icc 0 v) := by
    fun_prop
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 v) K := by
    intro u hu
    exact ⟨hu.1, hu.2, hvB.le⟩
  have hNuCont : ContinuousOn (fun u => S.nu u v) (Icc 0 v) :=
    (C1Solution.five_fields_contDiffOn hB hB1 H).2.1.continuousOn.comp
      hpath hmap
  have hNuEnd : Tendsto (fun u => S.nu u v) (𝓝[<] v)
      (𝓝 (S.nu v v)) := by
    have hleft : ContinuousWithinAt (fun u => S.nu u v) (Iic v) v :=
      (continuousWithinAt_Icc_iff_Iic hv.1).mp
        (hNuCont.continuousWithinAt ⟨hv.1.le, le_rfl⟩)
    exact (hleft.mono Iio_subset_Iic_self).tendsto
  have hnune : S.nu v v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H
      (show (v, v) ∈ K from ⟨hv.1.le, le_rfl, hvB.le⟩))
  have hratio := (rho_axis H hr hcenter hboot hv).div hNuEnd hnune
  have heq : (fun u => sourceRho S u v / S.nu u v / S.r u v ^ 2) =ᶠ[𝓝[<] v]
      (fun u => (sourceRho S u v / S.r u v ^ 2) / S.nu u v) := by
    filter_upwards [Ioo_mem_nhdsLT hv.1] with u hu
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hu.2, hv.2⟩
    have hrne := ne_of_gt (H.solution.radius_pos (u, v) hpU)
    have hnune' := ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H
      (show (u, v) ∈ K from ⟨hu.1.le, hu.2.le, hvB.le⟩))
    field_simp [hrne, hnune']
  simpa only [zero_div] using hratio.congr' heq.symm

/-- The one-dimensional half-area inequality on a fixed incoming fiber. -/
theorem sourceRho_fiber_lintegral_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    2 * (∫⁻ u in Ioo 0 v, sourceRhoDensity S (u, v)) ≤
      ∫⁻ u in Ioo 0 v,
        ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det| := by
  let g : ℝ → ℝ := fun u =>
    |2 * (|sourceRho S u v| / S.r u v ^ 3)|
  let f : ℝ → ℝ := fun u =>
    |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|
  let q : ℝ → ℝ := fun u =>
    sourceRho S u v / S.nu u v / S.r u v ^ 2
  have hgi (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) v) :
      IntervalIntegrable g volume 0 c :=
    sourceRho_fiber_integrable H hv hc
  have hfi (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) v) :
      IntervalIntegrable f volume 0 c :=
    sourcePhiBetaNu_jacobian_integrable_fiber H hv hc
  have hbound (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) v) :
      (∫ u in (0 : ℝ)..c, g u) ≤
        |q c| + ∫ u in (0 : ℝ)..c, f u := by
    have h := sourceRho_finite_integral_bound H hr hcenter hboot hv hc
    have heq : (∫ u in (0 : ℝ)..c, g u) =
        ∫ u in (0 : ℝ)..c, 2 * (|sourceRho S u v| / S.r u v ^ 3) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hc.1.le
      intro u hu
      change |2 * (|sourceRho S u v| / S.r u v ^ 3)| = _
      have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
        ⟨hu.1.le, hu.2.trans hc.2, hv.2⟩
      have hrpos := H.solution.radius_pos (u, v) hpU
      exact abs_of_nonneg (mul_nonneg (by norm_num)
        (div_nonneg (abs_nonneg _) (pow_nonneg hrpos.le _)))
    rw [heq]
    have hrpos : 0 < S.r c v := H.solution.radius_pos (c, v)
      ⟨hc.1.le, hc.2, hv.2⟩
    have hqc : |q c| = |sourceRho S c v / S.nu c v| / S.r c v ^ 2 := by
      change |sourceRho S c v / S.nu c v / S.r c v ^ 2| = _
      rw [abs_div, abs_of_pos (pow_pos hrpos 2)]
    rw [hqc]
    exact h
  have hTerminal := outgoing_area_terminal_lintegral_bound hv.1
    (fun u => abs_nonneg _) (fun u => abs_nonneg _)
    hgi hfi (sourceRho_axis_boundary H hr hcenter hboot hv) hbound
  have hleft : (∫⁻ u in Ioo 0 v, ENNReal.ofReal (g u)) =
      2 * (∫⁻ u in Ioo 0 v, sourceRhoDensity S (u, v)) := by
    calc
      (∫⁻ u in Ioo 0 v, ENNReal.ofReal (g u)) =
          ∫⁻ u in Ioo 0 v, 2 * sourceRhoDensity S (u, v) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro u hu
        have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
          ⟨hu.1.le, hu.2, hv.2⟩
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
  rw [hleft] at hTerminal
  exact hTerminal

end ChristodoulouBV

end
