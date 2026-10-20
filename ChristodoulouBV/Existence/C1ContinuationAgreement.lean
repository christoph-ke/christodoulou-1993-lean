module

public import ChristodoulouBV.Existence.C1Family
public import ChristodoulouBV.Frozen.Theorem3_1Unique
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Agreement of the continued C¹ solution with the old family

Frozen Theorem 3.1 identifies radius, scalar, and mass. The established C¹
field-recovery theorem gives all remaining fields on smaller closed
triangles, including the initial characteristic.
-/

public section

open Set

namespace ChristodoulouBV

/-- Two C¹ developments with the same prescribed radius and alpha data
agree in all fields. This proof consumes sealed Theorem 3.1 and C¹ field
recovery, including the initial edge. -/
theorem s6_continue_agreement
    {alpha₀ : ℝ → ℝ} {b₁ b₂ : ℝ} {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hdata₁ : ∀ v ∈ Ioo (0 : ℝ) b₁,
      S₁.r 0 v = v / 2 ∧ S₁.alpha 0 v = alpha₀ v)
    (hdata₂ : ∀ v ∈ Ioo (0 : ℝ) b₂,
      S₂.r 0 v = v / 2 ∧ S₂.alpha 0 v = alpha₀ v)
    {p : ℝ × ℝ}
    (hp₁ : p ∈ developmentWithInitialEdge b₁)
    (hp₂ : p ∈ developmentWithInitialEdge b₂) :
    S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.m p.1 p.2 = S₂.m p.1 p.2 ∧
      S₁.lam p.1 p.2 = S₂.lam p.1 p.2 ∧
      S₁.nu p.1 p.2 = S₂.nu p.1 p.2 ∧
      S₁.alpha p.1 p.2 = S₂.alpha p.1 p.2 ∧
      S₁.beta p.1 p.2 = S₂.beta p.1 p.2 ∧
      S₁.theta p.1 p.2 = S₂.theta p.1 p.2 ∧
      S₁.zeta p.1 p.2 = S₂.zeta p.1 p.2 := by
  have hb₁ : 0 < b₁ := (lt_of_le_of_lt hp₁.1 hp₁.2.1).trans hp₁.2.2
  have hb₂ : 0 < b₂ := (lt_of_le_of_lt hp₂.1 hp₂.2.1).trans hp₂.2.2
  have hr₁ : ∀ v ∈ Ioo (0 : ℝ) b₁, S₁.r 0 v = v / 2 :=
    fun v hv => (hdata₁ v hv).1
  have hr₂ : ∀ v ∈ Ioo (0 : ℝ) b₂, S₂.r 0 v = v / 2 :=
    fun v hv => (hdata₂ v hv).1
  have hα : ∀ v ∈ Ioo (0 : ℝ) (min b₁ b₂), S₁.alpha 0 v = S₂.alpha 0 v := by
    intro v hv
    exact (hdata₁ v ⟨hv.1, hv.2.trans_le (min_le_left _ _)⟩).2.trans
      (hdata₂ v ⟨hv.1, hv.2.trans_le (min_le_right _ _)⟩).2.symm
  have hphi := initial_phi_eq_of_radius_alpha_data H₁ H₂ hr₁ hr₂ hα
  have hdata : ∀ v, (0, v) ∈ developmentWithInitialEdge b₁ ∩
      developmentWithInitialEdge b₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v := by
    intro v hv
    have hv₁ : v ∈ Ioo (0 : ℝ) b₁ := ⟨hv.1.2.1, hv.1.2.2⟩
    have hv₂ : v ∈ Ioo (0 : ℝ) b₂ := ⟨hv.2.2.1, hv.2.2.2⟩
    exact ⟨(hr₁ v hv₁).trans (hr₂ v hv₂).symm,
      hphi v ⟨hv₁.1, lt_min hv₁.2 hv₂.2⟩⟩
  have hbase := theorem3_1_unique _ _ S₁ S₂
    (IsC1Solution.isBVSolution_development hb₁ H₁)
    (IsC1Solution.isBVSolution_development hb₂ H₂) hdata
  have hOpen : ∀ q ∈ openDevelopment 0 (min b₁ b₂),
      S₁.r q.1 q.2 = S₂.r q.1 q.2 ∧
      S₁.phi q.1 q.2 = S₂.phi q.1 q.2 ∧
      S₁.m q.1 q.2 = S₂.m q.1 q.2 := by
    intro q hq
    exact hbase q ⟨⟨hq.1.1.le, hq.2.1, hq.2.2.trans_le (min_le_left _ _)⟩,
      ⟨hq.1.1.le, hq.2.1, hq.2.2.trans_le (min_le_right _ _)⟩⟩
  obtain ⟨B, hpB, hBmin⟩ := exists_between (lt_min hp₁.2.2 hp₂.2.2)
  have hB : 0 < B := (lt_of_le_of_lt hp₁.1 hp₁.2.1).trans hpB
  obtain ⟨_, _, _, _, _, _, _, hlam, hnu, halpha, hbeta, _, htheta, hzeta⟩ :=
    c1_field_jets_eq_on_compact_closure_of_r_phi_m_eq hB
      (hBmin.trans_le (min_le_left _ _)) (hBmin.trans_le (min_le_right _ _))
      H₁ H₂ hOpen (p := p) ⟨hp₁.1, hp₁.2.1.le, hpB.le⟩
  obtain ⟨hr, hφ, hm⟩ := hbase p ⟨hp₁, hp₂⟩
  exact ⟨hr, hφ, hm, hlam, hnu, halpha, hbeta, htheta, hzeta⟩

end ChristodoulouBV

end
