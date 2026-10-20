module

public import ChristodoulouBV.Frozen.FieldsTheta
public import ChristodoulouBV.Frozen.FieldsZeta
import Mathlib.Tactic

/-!
# Physical scaling at fixed null coordinates

The radius, mass, and six null derivative fields have weight one under a
positive physical scale. The scalar field and the mass ratio have weight zero.
-/

@[expose] public section

noncomputable section

namespace ChristodoulouBV.C1Solution

/-- Scale the physical fields while fixing the two null coordinates and the
scalar field. -/
def physicalScaleFields (c : ℝ) (S : Fields) : Fields where
  r u v := c * S.r u v
  phi u v := S.phi u v
  m u v := c * S.m u v
  lam u v := c * S.lam u v
  nu u v := c * S.nu u v
  alpha u v := c * S.alpha u v
  beta u v := c * S.beta u v

/-- The outgoing scalar amplitude has physical weight one. -/
theorem physicalScaleFields_theta (c : ℝ) (S : Fields) (u v : ℝ) :
    (physicalScaleFields c S).theta u v = c * S.theta u v := by
  simp only [Fields.theta, physicalScaleFields]
  ring

/-- The incoming scalar amplitude has physical weight one. -/
theorem physicalScaleFields_zeta (c : ℝ) (S : Fields) (u v : ℝ) :
    (physicalScaleFields c S).zeta u v = c * S.zeta u v := by
  simp only [Fields.zeta, physicalScaleFields]
  ring

/-- The totalized ratio `2m/r` is invariant under nonzero physical scaling,
including at zero radius. -/
theorem physicalScaleFields_massRatio (c : ℝ) (S : Fields) (u v : ℝ)
    (hc : c ≠ 0) :
    2 * (physicalScaleFields c S).m u v /
      (physicalScaleFields c S).r u v =
      2 * S.m u v / S.r u v := by
  by_cases hr : S.r u v = 0
  · simp [physicalScaleFields, hr]
  · simp only [physicalScaleFields]
    field_simp [hc, hr]

end ChristodoulouBV.C1Solution

end
