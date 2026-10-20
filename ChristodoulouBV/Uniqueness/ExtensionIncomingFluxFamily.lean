module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFluxSegment
import ChristodoulouBV.Uniqueness.ExtensionFamily
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform outgoing flux bound for the compatible family

The initial flux is bounded on one fixed compact incoming segment. Family
compatibility transfers that bound, and the outgoing flux inequality adds a
uniform linear source on every later member.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming flux `ζ²/(r|ν|)` has a cutoff independent upper bound on
the strict incoming part of the off-axis strip. -/
theorem exists_flux_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 < u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u ≤ u₁ → vBar ≤ v → v < b →
          (S b).zeta u v ^ 2 /
            ((S b).r u v * (-(S b).nu u v)) ≤ C := by
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_radius_floor_before_star hu₁.le hu₁v hvBarStar hfamily
  obtain ⟨M, hM, hscalar⟩ :=
    exists_scalar_bound_before_star hu₁ hu₁v hvBarStar hα hfamily
  let b₀ : ℝ := (vBar + vStar) / 2
  have hvBar : 0 < vBar := hu₁.trans hu₁v
  have hBarb₀ : vBar < b₀ := by dsimp [b₀]; linarith
  have hb₀Star : b₀ < vStar := by dsimp [b₀]; linarith
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨hvBar.trans hBarb₀, hb₀Star⟩
  let H₀ := (hfamily b₀ hb₀).1
  let B₀ : ℝ := (vBar + b₀) / 2
  have hB₀ : 0 < B₀ := by dsimp [B₀]; linarith
  have hB₀b : B₀ < b₀ := by dsimp [B₀]; linarith
  have hBarB₀ : vBar < B₀ := by dsimp [B₀]; linarith
  have hmap (u : ℝ) (hu : u ∈ Icc (0 : ℝ) u₁) :
      (u, vBar) ∈ closedCoordTriangle 0 B₀ := by
    change 0 ≤ u ∧ u ≤ vBar ∧ vBar ≤ B₀
    exact ⟨hu.1, hu.2.trans hu₁v.le, hBarB₀.le⟩
  have hpU (u : ℝ) (hu : u ∈ Icc (0 : ℝ) u₁) :
      (u, vBar) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu.1, hu.2.trans_lt hu₁v, hBarb₀⟩
  have hRcont : ContinuousOn (fun u => (S b₀).r u vBar)
      (Icc (0 : ℝ) u₁) := by
    have hcanonical : ContinuousOn
        (fun u => C1Solution.canonicalRadius (S b₀) (u, vBar))
        (Icc (0 : ℝ) u₁) :=
      (C1Solution.canonicalRadius_contDiffOn hB₀ hB₀b H₀).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap
    apply hcanonical.congr
    intro u hu
    exact (C1Solution.canonicalRadius_eq_radius hB₀ hB₀b H₀
      hu.1 (hu.2.trans_lt hu₁v) hBarB₀.le).symm
  have hNucont : ContinuousOn (fun u => (S b₀).nu u vBar)
      (Icc (0 : ℝ) u₁) := by
    apply H₀.nu_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
    intro u hu
    exact subset_closure (hpU u hu)
  have hZcont : ContinuousOn (fun u => (S b₀).zeta u vBar)
      (Icc (0 : ℝ) u₁) := by
    apply H₀.zeta_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
    intro u hu
    exact subset_closure (hpU u hu)
  let G₀ : ℝ → ℝ := fun u =>
    (S b₀).zeta u vBar ^ 2 /
      ((S b₀).r u vBar * (-(S b₀).nu u vBar))
  have hden (u : ℝ) (hu : u ∈ Icc (0 : ℝ) u₁) :
      (S b₀).r u vBar * (-(S b₀).nu u vBar) ≠ 0 := by
    have hrpos := H₀.solution.radius_pos (u, vBar) (hpU u hu)
    have hnuneg := (H₀.reduced_signs_of_c1 (hpU u hu)).1
    exact ne_of_gt (mul_pos hrpos (neg_pos.mpr hnuneg))
  have hGcont : ContinuousOn G₀ (Icc (0 : ℝ) u₁) :=
    (hZcont.pow 2).div (hRcont.mul hNucont.neg) hden
  obtain ⟨F, hF⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcont
  have hF0 : 0 ≤ F := by
    have h := hF 0 ⟨le_rfl, hu₁.le⟩
    exact (abs_nonneg (G₀ 0)).trans (by simpa only [Real.norm_eq_abs] using h)
  let C : ℝ := F + (2 * M ^ 2 / ρ ^ 2) * (vStar - vBar)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  have hBarb : vBar < b := hvBarv.trans_lt hvb
  have hflux₀ :
      (S b).zeta u vBar ^ 2 /
        ((S b).r u vBar * (-(S b).nu u vBar)) = G₀ u := by
    have hp₀ : (u, vBar) ∈ developmentWithInitialEdge b₀ :=
      ⟨hu.le, huu₁.trans_lt hu₁v, hBarb₀⟩
    have hpb : (u, vBar) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, huu₁.trans_lt hu₁v, hBarb⟩
    have heq := family_fields_eq_on_common_development hfamily hb₀ hb
      ⟨hp₀, hpb⟩
    have hzeta : (S b₀).zeta u vBar = (S b).zeta u vBar := by
      simp only [Fields.zeta, heq.2.2.2.2.2.2,
        heq.2.2.2.2.1, heq.2.1]
    dsimp [G₀]
    rw [← heq.1, ← heq.2.2.2.2.1, ← hzeta]
  have hbase : G₀ u ≤ F := by
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hF u ⟨hu.le, huu₁⟩)
  have hlocal := incoming_flux_le_of_c1 (hfamily b hb).1
    hu (huu₁.trans_lt hu₁v) hvBarv hvb hρ hM
    (fun w hw => hr b hb u w hu.le huu₁ hw.1 (hw.2.trans_lt hvb))
    (fun w hw => (hscalar b hb u w hu.le huu₁ hw.1
      (hw.2.trans_lt hvb)).1)
    (fun w hw => (hscalar b hb u w hu.le huu₁ hw.1
      (hw.2.trans_lt hvb)).2)
  rw [hflux₀] at hlocal
  have hcoef : 0 ≤ 2 * M ^ 2 / ρ ^ 2 := by positivity
  have hlength : v - vBar ≤ vStar - vBar := by linarith [hvb.trans hb.2]
  calc
    _ ≤ G₀ u + (2 * M ^ 2 / ρ ^ 2) * (v - vBar) := hlocal
    _ ≤ F + (2 * M ^ 2 / ρ ^ 2) * (vStar - vBar) :=
      add_le_add hbase (mul_le_mul_of_nonneg_left hlength hcoef)
    _ = C := rfl

end ChristodoulouBV.Uniqueness

end
