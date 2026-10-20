module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFiniteSeam
public import ChristodoulouBV.Uniqueness.RouteBIdentificationClosedFinite
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The old/axis seam from the established identification theorem

Each finite cutoff has a canonical old C¹ representative. The established
identification theorem equates it with the axis solution on the right of
`u = a`; a closed old representative equates it on the left. The two
finite-cutoff equalities identify the full first jets, and continuity
closes the triple corner.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The canonical seven-field version of a frozen old member. Radius and
mass use their C¹ extensions at the axis. -/
@[expose] def routeBCanonicalOldFields (d : ℝ) (S : Fields) : Fields where
  r u v := C1Solution.canonicalRadius S (u, v)
  phi := S.phi
  m u v := C1Solution.canonicalMass d S (u, v)
  lam := S.lam
  nu := S.nu
  alpha := S.alpha
  beta := S.beta

/-- A canonical old member has seven C¹ fields on every strict cutoff. -/
theorem routeBCanonicalOldFields_c1
    {e d : ℝ} (he : 0 < e) (hed : e < d)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge d) S) :
    RouteBFieldsC1On (routeBCanonicalOldFields d S)
      (closedCoordTriangle 0 e) := by
  intro c
  cases c
  · exact C1Solution.canonicalRadius_contDiffOn he hed H
  · exact (C1Solution.five_fields_contDiffOn he hed H).2.2.1
  · exact C1Solution.canonicalMass_contDiffOn he hed H
  · exact (C1Solution.five_fields_contDiffOn he hed H).1
  · exact (C1Solution.five_fields_contDiffOn he hed H).2.1
  · change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
        (closedCoordTriangle 0 e)
    exact C1Solution.alpha_contDiffOn he hed H
  · change ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2)
        (closedCoordTriangle 0 e)
    exact C1Solution.beta_contDiffOn he hed H

/-- Once the closed old piece is known to match every canonical old member
on strict cutoffs, item 4 supplies all value and full-jet equalities on the
old/axis seam, including the triple corner. The finite matching hypothesis
is the identification property to be proved for the closed old piece. -/
theorem OffAxisTerminalC1Packet.clipped_old_axis_seam
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haStar : a < vStar)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    {b : ℝ} {SAx SOld : Fields}
    (HT : C1Solution.AxisClassicalSolution a b SAx) (hStarb : vStar < b)
    (hrT : ∀ v ∈ Icc a vStar, SAx.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      SAx.r a v * SAx.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hOldMatch : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a e)) :
    RouteBFieldsEqOn SOld SAx
        (routeBOldRegion a vStar ∩ closedCoordTriangle a b) ∧
      RouteBFieldsJetEqOn SOld SAx
        (routeBOldRegion a vStar) (closedCoordTriangle a b) := by
  have hOpen (c : RouteBField) (v : ℝ) (hv : v ∈ Ioo a vStar) :
      routeBField SOld c (a, v) = routeBField SAx c (a, v) ∧
      fderivWithin ℝ (routeBField SOld c) (routeBOldRegion a vStar) (a, v) =
        fderivWithin ℝ (routeBField SAx c) (closedCoordTriangle a b) (a, v) := by
    let e := (v + vStar) / 2
    let d := (e + vStar) / 2
    have hve : v < e := by dsimp [e]; linarith only [hv.2]
    have heStar : e < vStar := by dsimp [e]; linarith only [hv.2]
    have hed : e < d := by dsimp [d]; linarith only [heStar]
    have hdStar : d < vStar := by dsimp [d]; linarith only [heStar]
    have he : e ∈ Ioo a vStar := ⟨hv.1.trans hve, heStar⟩
    have hd : d ∈ Ioo e vStar := ⟨hed, hdStar⟩
    have hd₀ : d ∈ Ioo (0 : ℝ) vStar :=
      ⟨ha.trans (he.1.trans hed), hdStar⟩
    let F := routeBCanonicalOldFields d (S d)
    have hFC1 : RouteBFieldsC1On F (closedCoordTriangle 0 e) :=
      routeBCanonicalOldFields_c1 (ha.trans he.1) hed (hfamily d hd₀).1
    have hAxisMatch : RouteBFieldsEqOn SAx F (closedCoordTriangle a e) := by
      intro k p hp
      simp only [closedCoordTriangle, mem_ofPred_eq] at hp
      have h := P.axis_eq_old_union_pointwise ha hfamily HT hStarb
        hrT hpsiT hd₀ hp.1 hp.2.1 (hp.2.2.trans_lt hed)
      cases k
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.1
      · exact h.2.2.2.2.1
      · exact h.2.2.2.2.2.1
      · exact h.2.2.2.2.2.2.1
    exact routeB_clipped_scalar_seam_at_of_common ha he.1 he.2 hStarb
      (routeBField SOld c) (routeBField SAx c) (routeBField F c)
      (hOldC1 c) (hAxC1 c) (hFC1 c)
      (hOldMatch e he d hd c) (hAxisMatch c)
      ⟨hv.1.le, hve.le⟩
  exact routeB_clipped_old_axis_seam_of_open ha haStar hStarb SOld SAx
    hOldC1 hAxC1
    (fun c v hv => (hOpen c v hv).1)
    (fun c v hv => (hOpen c v hv).2)

end ChristodoulouBV.Uniqueness

end
