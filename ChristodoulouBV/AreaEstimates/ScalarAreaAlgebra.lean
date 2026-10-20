module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Algebra behind the two scalar quotient Jacobians

The identities here isolate the quotient rule and the mixed field transport
relations from the differentiability argument.
-/

public section

namespace ChristodoulouBV

/-- Algebraic form of the Jacobian of `(φ, α/λ)` from (1.18a). -/
theorem alpha_quotient_jacobian_algebra
    (lam alpha phi theta lamU lamV alphaU alphaV phiU phiV hU hV : ℝ)
    (hlam : lam ≠ 0)
    (htheta : theta = alpha - lam * phi)
    (hprodU : alphaU = lamU * (alpha / lam) + lam * hU)
    (hprodV : alphaV = lamV * (alpha / lam) + lam * hV)
    (htransport : alphaU = lamU * phi) :
    phiU * hV - phiV * hU =
      (phiU / lam) * (alphaV - lamV * phi) +
        (theta / lam ^ 2) * (lamU * phiV - lamV * phiU) := by
  have hhu : hU = (alphaU - lamU * (alpha / lam)) / lam := by
    apply (eq_div_iff hlam).2
    linarith only [hprodU]
  have hhv : hV = (alphaV - lamV * (alpha / lam)) / lam := by
    apply (eq_div_iff hlam).2
    linarith only [hprodV]
  rw [hhu, hhv, htransport, htheta]
  field_simp [hlam]
  ring

/-- Algebraic form of the Jacobian of `(φ, β/ν)` from (1.18b). -/
theorem beta_quotient_jacobian_algebra
    (nu beta phi zeta nuU nuV betaU betaV phiU phiV hU hV : ℝ)
    (hnu : nu ≠ 0)
    (hzeta : zeta = beta - nu * phi)
    (hprodU : betaU = nuU * (beta / nu) + nu * hU)
    (hprodV : betaV = nuV * (beta / nu) + nu * hV)
    (htransport : betaV = nuV * phi) :
    phiU * hV - phiV * hU =
      -(phiV / nu) * (betaU - nuU * phi) +
        (zeta / nu ^ 2) * (nuU * phiV - nuV * phiU) := by
  have hhu : hU = (betaU - nuU * (beta / nu)) / nu := by
    apply (eq_div_iff hnu).2
    linarith only [hprodU]
  have hhv : hV = (betaV - nuV * (beta / nu)) / nu := by
    apply (eq_div_iff hnu).2
    linarith only [hprodV]
  rw [hhu, hhv, htransport, hzeta]
  field_simp [hnu]
  ring

end ChristodoulouBV

end
