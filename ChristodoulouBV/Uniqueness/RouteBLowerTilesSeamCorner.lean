module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesOldSafe
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesNewCharacteristic
import Mathlib.Tactic

/-!
# Initial corner transverse jet

The old and new incoming edges use the same gauge. Since the prescribed
amplitude is C¹ at the shared endpoint, both vertical incoming derivatives
there equal the same pair.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A vertical incoming edge with the prescribed gauge has the expected
one-sided derivative at every positive endpoint. -/
theorem hasDerivWithinAt_incoming_gauge_at
    {lo hi vStar : ℝ} {alpha₀ : ℝ → ℝ}
    {X : ℝ × ℝ → C1Solution.IncomingState}
    (hStar : 0 < vStar) (hlo : lo ≤ vStar) (hhi : vStar ≤ hi)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hgauge : ∀ v ∈ Icc lo hi, X (0, v) = (1 / 2, alpha₀ v)) :
    HasDerivWithinAt (fun v => X (0, v))
      (0, deriv alpha₀ vStar) (Icc lo hi) vStar := by
  have hαAt : DifferentiableAt ℝ alpha₀ vStar :=
    (hα.contDiffAt (Ici_mem_nhds hStar)).differentiableAt (by norm_num)
  have hpair : HasDerivWithinAt
      (fun v : ℝ => ((1 / 2 : ℝ), alpha₀ v))
      (0, deriv alpha₀ vStar) (Icc lo hi) vStar :=
    (((hasDerivAt_const vStar (1 / 2 : ℝ)).prodMk
      hαAt.hasDerivAt).hasDerivWithinAt)
  have hv : vStar ∈ Icc lo hi := ⟨hlo, hhi⟩
  exact hpair.congr
    (fun v hv' => hgauge v hv') (hgauge vStar hv)

end ChristodoulouBV.Uniqueness

end
