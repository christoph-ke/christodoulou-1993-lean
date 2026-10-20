module

public import ChristodoulouBV.C1Solution.AxisUniformEndpointNormalization
public import ChristodoulouBV.C1Solution.AxisLocalExistenceEdgeTheorem
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# A prescribed endpoint for the physical axis triangle

The Picard fixed point is reconstructed and unscaled at the endpoint supplied
by the caller. The endpoint is never chosen by an existential compact-edge
theorem.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.AxisPicard

/-- Normalized `EdgeData` at a prescribed endpoint gives a physical classical
axis solution, its exact incoming trace, and the scalar-radius primitive. -/
theorem exists_axis_triangle_solution_prescribed_of_edgeData
    {a b M k : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M (fun v => k * g v) hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hk : 0 < k) (hka : k * g a = 1 / 2) :
    ∃ T : Fields,
      AxisClassicalSolution a b T ∧
      (∀ p ∈ closedCoordTriangle a b,
        g a / 2 ≤ T.lam p.1 p.2 ∧
        -(3 * g a / 2) ≤ T.nu p.1 p.2 ∧
        T.nu p.1 p.2 ≤ -(g a / 2) ∧
        0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1 / 4) ∧
      (∀ v ∈ Icc a b,
        T.r a v = ∫ s in a..v, g s ∧
        T.lam a v = g v ∧ T.alpha a v = g v * hEdge v) ∧
      (∀ v ∈ Icc a b, T.alpha a v / T.lam a v = hEdge v) ∧
      (∀ v ∈ Icc a b,
        T.r a v * T.phi a v = ∫ s in a..v, g s * hEdge s) := by
  obtain ⟨x, hfixed, _⟩ := exists_reconstructed_fields D hab hM hsmall
  let S := x.1.toTriple.toFields
  let T := physicalScaleFields (1 / k) S
  have hkne : k ≠ 0 := ne_of_gt hk
  have hc : 0 < 1 / k := one_div_pos.mpr hk
  have hga : 0 < g a := by nlinarith only [hk, hka]
  have hkinv : 1 / k = 2 * g a := by
    apply (div_eq_iff hkne).2
    nlinarith only [hka]
  have hquarter : (1 / (4 * k) : ℝ) = g a / 2 := by
    calc
      1 / (4 * k) = (1 / k) / 4 := by field_simp [hkne]
      _ = g a / 2 := by rw [hkinv]; ring
  have hthree : (3 / (4 * k) : ℝ) = 3 * g a / 2 := by
    calc
      3 / (4 * k) = 3 * (1 / k) / 4 := by field_simp [hkne]
      _ = 3 * g a / 2 := by rw [hkinv]; ring
  have hSclass : AxisClassicalSolution a b S :=
    x.is_classical_axis_triangle hab hM hsmall D.g_lower hfixed
  have hclass : AxisClassicalSolution a b T := hSclass.physicalScale hc
  have hbasic := x.reconstructed_fields_basic hab hM hsmall D.g_lower
  dsimp only at hbasic
  rcases hbasic with
    ⟨_, _, _, _, _, _, _, hsignS, _⟩
  have hsign : ∀ p ∈ closedCoordTriangle a b,
      g a / 2 ≤ T.lam p.1 p.2 ∧
      -(3 * g a / 2) ≤ T.nu p.1 p.2 ∧
      T.nu p.1 p.2 ≤ -(g a / 2) ∧
      0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
      2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1 / 4 := by
    intro p hp
    obtain ⟨hl, hnlo, hnhi, hmlo, hmhi⟩ := hsignS p hp
    have hrati := physicalScaleFields_massRatio (1 / k) S p.1 p.2
      (one_div_ne_zero hkne)
    change 2 * T.m p.1 p.2 / T.r p.1 p.2 =
      2 * S.m p.1 p.2 / S.r p.1 p.2 at hrati
    change (1 / 4 : ℝ) ≤ S.lam p.1 p.2 at hl
    change -(3 / 4 : ℝ) ≤ S.nu p.1 p.2 at hnlo
    change S.nu p.1 p.2 ≤ -(1 / 4 : ℝ) at hnhi
    have hscaled := mul_le_mul_of_nonneg_left hl hc.le
    have hscaledNuLo := mul_le_mul_of_nonneg_left hnlo hc.le
    have hscaledNuHi := mul_le_mul_of_nonneg_left hnhi hc.le
    simp only [T, physicalScaleFields] at hrati ⊢
    rw [hrati]
    rw [← hquarter, ← hthree]
    refine ⟨?_, ?_, ?_, hmlo, hmhi⟩
    · convert hscaled using 1; field_simp [hkne]
    · convert hscaledNuLo using 1; field_simp [hkne]
    · convert hscaledNuHi using 1; field_simp [hkne]
  have hedge : ∀ v ∈ Icc a b,
      T.r a v = ∫ s in a..v, g s ∧
      T.lam a v = g v ∧ T.alpha a v = g v * hEdge v := by
    intro v hv
    obtain ⟨hrv, hlv, hav⟩ := x.reconstructed_edge_trace hv
    change S.r a v = ∫ s in a..v, (fun z => k * g z) s at hrv
    change S.lam a v = k * g v at hlv
    change S.alpha a v = k * g v * hEdge v at hav
    constructor
    · change (1 / k) * S.r a v = _
      rw [hrv, intervalIntegral.integral_const_mul]
      field_simp
    constructor
    · change (1 / k) * S.lam a v = _
      rw [hlv]
      field_simp
    · change (1 / k) * S.alpha a v = _
      rw [hav]
      field_simp
  refine ⟨T, hclass, hsign, hedge, ?_, ?_⟩
  · intro v hv
    have hp : (a, v) ∈ closedCoordTriangle a b := by
      change a ≤ a ∧ a ≤ v ∧ v ≤ b
      exact ⟨le_rfl, hv.1, hv.2⟩
    have hlam := (hsign (a, v) hp).1
    have hgv : g v ≠ 0 := by
      rw [(hedge v hv).2.1] at hlam
      exact ne_of_gt (lt_of_lt_of_le (half_pos hga) hlam)
    rw [(hedge v hv).2.1, (hedge v hv).2.2]
    field_simp [hgv]
  · intro v hv
    exact hclass.psi_edge_integral (fun s hs => (hedge s hs).2.2) hv

/-- Uniform physical bounds give a classical axis triangle for each supplied
endpoint within the same lifetime, independent of its coordinate location. -/
theorem exists_axis_triangle_solution_prescribed_global
    {a L b c Clam H : ℝ} {g hEdge : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 hEdge)
    (hc : 0 < c) (hL : 0 < L)
    (hglo : ∀ v ∈ Icc a (a + L), c ≤ g v)
    (hgderiv : ∀ v ∈ Icc a (a + L), |deriv g v| ≤ Clam)
    (hhval : ∀ v ∈ Icc a (a + L), |hEdge v| ≤ H)
    (hhderiv : ∀ v ∈ Icc a (a + L), |deriv hEdge v| ≤ H)
    (hab : a < b) (hbL : b ≤ a + L)
    (hsmall : b - a ≤ uniformAxisLifetime c Clam H) :
    ∃ T : Fields,
      AxisClassicalSolution a b T ∧
      (∀ p ∈ closedCoordTriangle a b,
        g a / 2 ≤ T.lam p.1 p.2 ∧
        -(3 * g a / 2) ≤ T.nu p.1 p.2 ∧
        T.nu p.1 p.2 ≤ -(g a / 2) ∧
        0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1 / 4) ∧
      (∀ v ∈ Icc a b,
        T.r a v = ∫ s in a..v, g s ∧
        T.lam a v = g v ∧ T.alpha a v = g v * hEdge v) ∧
      (∀ v ∈ Icc a b, T.alpha a v / T.lam a v = hEdge v) ∧
      (∀ v ∈ Icc a b,
        T.r a v * T.phi a v = ∫ s in a..v, g s * hEdge s) := by
  obtain ⟨hk, hka, D⟩ := edgeData_of_uniform_bounds hg hh hc hL
    hglo hgderiv hhval hhderiv hab hbL hsmall
  have hpicard : b - a ≤
      (numericalLedger (uniformAxisM c Clam H)).lifetime
        (uniformAxisM c Clam H) :=
    hsmall.trans (min_le_right _ _)
  exact exists_axis_triangle_solution_prescribed_of_edgeData D hab
    (one_le_uniformAxisM c Clam H) hpicard hk hka

end ChristodoulouBV.C1Solution

end
