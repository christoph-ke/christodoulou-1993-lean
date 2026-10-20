module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaTransport
import Mathlib.Tactic

/-!
# Jacobian algebra for the outgoing and incoming areas

The incoming logarithmic residual has the corrected `- f*` sign from the
sign correction of (4.11b)–(4.13b) and its extension to the area estimates;
see ERRATA.md, ERR-23.
-/

public section

namespace ChristodoulouBV

/-- The algebraic decomposition preceding (4.21). -/
theorem outgoing_area_jacobian_algebra
    {r lam nu theta zeta mu lamU lamV : ℝ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0)
    (hgap : 1 - mu ≠ 0)
    (hLamU : lamU = mu / (1 - mu) * lam * nu / r) :
    lamU * (theta / r) - lamV * (zeta / r) =
      -(lam * zeta / r) *
        (lamV / lam - mu / (1 - mu) * lam / r +
          theta / r * (theta / lam - zeta / nu)) +
      lam * (r * (mu / (1 - mu) * nu * lam + theta * zeta)) /
        r ^ 3 * (theta / lam - zeta / nu) := by
  rw [hLamU]
  field_simp [hr, hlam, hnu, hgap]
  ring

/-- The algebraic decomposition preceding corrected (4.26). The sign on
`f*` is the one fixed by the sign correction described in ERRATA.md, ERR-23. -/
theorem incoming_area_jacobian_algebra
    {r lam nu theta zeta mu nuU nuV : ℝ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0)
    (hgap : 1 - mu ≠ 0)
    (hNuV : nuV = mu / (1 - mu) * lam * nu / r) :
    nuU * (theta / r) - nuV * (zeta / r) =
      nu * theta / r *
        (nuU / nu - mu / (1 - mu) * nu / r -
          zeta / r * (theta / lam - zeta / nu)) +
      nu * (r * (mu / (1 - mu) * nu * lam + theta * zeta)) /
        r ^ 3 * (theta / lam - zeta / nu) := by
  rw [hNuV]
  field_simp [hr, hlam, hnu, hgap]
  ring

end ChristodoulouBV

end
