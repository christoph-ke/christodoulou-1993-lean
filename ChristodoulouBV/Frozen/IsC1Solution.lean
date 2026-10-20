module

public import ChristodoulouBV.Frozen.IsSolution

/-! The regular C¹ class used in Sections 4–6. -/

@[expose] public section

namespace ChristodoulouBV

/-- The paper's C¹ solution on a development, with regularity on its closure (D6).
Christodoulou 1993, p. 1157; `source/transcription/s4-area-estimates.tex:55-64`. -/
structure IsC1Solution (U : Set (ℝ × ℝ)) (S : Fields) : Prop where
  solution : IsSolution U S
  nu_bounded_below : ∃ N : ℝ, ∀ p ∈ U, -S.nu p.1 p.2 ≤ N
  lam_bounded_below : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ U, c ≤ S.lam p.1 p.2
  lam_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2) (closure U)
  nu_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2) (closure U)
  phi_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) (closure U)
  theta_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) (closure U)
  zeta_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.zeta p.1 p.2) (closure U)

end ChristodoulouBV

end
