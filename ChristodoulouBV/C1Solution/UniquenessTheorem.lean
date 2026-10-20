module

public import ChristodoulouBV.C1Solution.UniquenessSmallTriangle
public import ChristodoulouBV.C1Solution.Rescaling
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Unconditional uniqueness of frozen C¹ solutions

Positive affine rescaling reduces every compact triangle to width one.
The compact equality then exhausts the common development, where the
frozen primitive fields agree with their canonical extensions.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.Uniqueness

/-- Equal initial radius and scalar data force equality of the canonical
outgoing fields on every smaller compact triangle, regardless of width. -/
theorem canonical_outgoing_eq_on_compact_triangle
    {b₁ b₂ T : ℝ} (hT : 0 < T)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : ∀ v ∈ Ioo 0 T, S₁.r 0 v = S₂.r 0 v)
    (hphi : ∀ v ∈ Ioo 0 T, S₁.phi 0 v = S₂.phi 0 v) :
    EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 T) ∧
    EqOn (outgoingQuotient S₁) (outgoingQuotient S₂)
      (closedCoordTriangle 0 T) := by
  let R₁ := rescaledFields S₁ 0 T
  let R₂ := rescaledFields S₂ 0 T
  have hb₁ : 1 < b₁ / T := by
    apply (lt_div_iff₀ hT).2
    simpa only [one_mul] using hT₁
  have hb₂ : 1 < b₂ / T := by
    apply (lt_div_iff₀ hT).2
    simpa only [one_mul] using hT₂
  have HR₁ : IsC1Solution (developmentWithInitialEdge (b₁ / T)) R₁ :=
    rescaled_development_isC1Solution H₁ hT
  have HR₂ : IsC1Solution (developmentWithInitialEdge (b₂ / T)) R₂ :=
    rescaled_development_isC1Solution H₂ hT
  have hrR : ∀ v ∈ Ioo (0 : ℝ) 1, R₁.r 0 v = R₂.r 0 v := by
    intro v hv
    have hvT : T * v ∈ Ioo 0 T := by
      constructor
      · exact mul_pos hT hv.1
      · nlinarith only [hv.2, hT]
    have heq := hr (T * v) hvT
    simpa only [R₁, R₂, rescaledFields, affineCoordinate,
      mul_zero, zero_add] using congrArg (fun x : ℝ => x / T) heq
  have hphiR : ∀ v ∈ Ioo (0 : ℝ) 1, R₁.phi 0 v = R₂.phi 0 v := by
    intro v hv
    have hvT : T * v ∈ Ioo 0 T := by
      constructor
      · exact mul_pos hT hv.1
      · nlinarith only [hv.2, hT]
    have heq := hphi (T * v) hvT
    simpa only [R₁, R₂, rescaledFields, affineCoordinate,
      mul_zero, zero_add] using heq
  have hsmall := canonical_outgoing_eq_on_width_one
    (show (0 : ℝ) < 1 by norm_num) (by norm_num)
    hb₁ hb₂ HR₁ HR₂ hrR hphiR
  constructor
  · intro p hp
    let q : ℝ × ℝ := (p.1 / T, p.2 / T)
    have hq : q ∈ closedCoordTriangle 0 1 := by
      change 0 ≤ p.1 / T ∧ p.1 / T ≤ p.2 / T ∧ p.2 / T ≤ 1
      constructor
      · exact div_nonneg hp.1 hT.le
      constructor
      · exact (div_le_div_iff_of_pos_right hT).2 hp.2.1
      · exact (div_le_iff₀ hT).2 (by simpa only [one_mul] using hp.2.2)
    have heq := hsmall.1 hq
    change R₁.lam q.1 q.2 = R₂.lam q.1 q.2 at heq
    simpa only [R₁, R₂, q, rescaledFields, affineCoordinate,
      zero_add, mul_div_cancel₀ _ hT.ne'] using heq
  · intro p hp
    let q : ℝ × ℝ := (p.1 / T, p.2 / T)
    have hq : q ∈ closedCoordTriangle 0 1 := by
      change 0 ≤ p.1 / T ∧ p.1 / T ≤ p.2 / T ∧ p.2 / T ≤ 1
      constructor
      · exact div_nonneg hp.1 hT.le
      constructor
      · exact (div_le_div_iff_of_pos_right hT).2 hp.2.1
      · exact (div_le_iff₀ hT).2 (by simpa only [one_mul] using hp.2.2)
    have heq := hsmall.2 hq
    change outgoingQuotient R₁ q = outgoingQuotient R₂ q at heq
    simpa only [R₁, R₂, q, outgoingQuotient, rescaledFields,
      affineCoordinate, zero_add, mul_div_cancel₀ _ hT.ne'] using heq

/-- Two frozen C¹ solutions with the same initial radius and scalar data
agree in every original field at every point of their common development. -/
theorem c1_solution_unique_on_common_development
    {b₁ b₂ : ℝ} {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hdata : ∀ v, (0, v) ∈
      developmentWithInitialEdge b₁ ∩ developmentWithInitialEdge b₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ}
    (hp₁ : (u, v) ∈ developmentWithInitialEdge b₁)
    (hp₂ : (u, v) ∈ developmentWithInitialEdge b₂) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v ∧ S₁.theta u v = S₂.theta u v ∧
    S₁.zeta u v = S₂.zeta u v := by
  apply fields_eq_on_common_development_of_compact_lam_h_eq H₁ H₂
    (fun T hT hT₁ hT₂ => ?_) hp₁ hp₂
  apply canonical_outgoing_eq_on_compact_triangle hT hT₁ hT₂ H₁ H₂
  · intro w hw
    exact (hdata w ⟨⟨le_refl _, hw.1, hw.2.trans hT₁⟩,
      ⟨le_refl _, hw.1, hw.2.trans hT₂⟩⟩).1
  · intro w hw
    exact (hdata w ⟨⟨le_refl _, hw.1, hw.2.trans hT₁⟩,
      ⟨le_refl _, hw.1, hw.2.trans hT₂⟩⟩).2

end ChristodoulouBV.C1Solution

end
