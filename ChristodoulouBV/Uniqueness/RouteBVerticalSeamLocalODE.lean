module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamCoefficient
import Mathlib.Tactic

/-!
# Local transverse equations for the Route B seam

On a safe off-axis rectangle, the classical outgoing equations and C¹
regularity imply ordinary vertical equations for the incoming relative
jets of `ν` and `β`. The rectangle may touch the boundary of its larger
closed solution region.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming jet of `ν` differentiates vertically to the incoming jet
of its gravitational source on any safe off-axis rectangle. -/
theorem routeB_nu_horizontal_jet_hasDerivAt_of_local_classical
    {b : ℝ} {K : Set (ℝ × ℝ)}
    {u₀ u₁ v₀ v₁ s v : ℝ}
    (hu : u₀ < u₁) (hv : v₀ < v) (hv' : v < v₁)
    (hs : s ∈ Icc u₀ u₁)
    (hR : Icc u₀ u₁ ×ˢ Icc v₀ v₁ ⊆ K)
    (hDev : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      p ∈ developmentWithInitialEdge b)
    (hUniqueK : UniqueDiffOn ℝ K)
    {S : Fields} (hC1 : RouteBFieldsC1On S K)
    (hJet : RouteBClassicalJetOn b K S)
    (hr : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0) :
    HasDerivAt
      (fun t => (fderivWithin ℝ (routeBField S .contraction) K (s, t)) (1, 0))
      ((fderivWithin ℝ
        (fun p : ℝ × ℝ => routeBGravCoefficient S p * S.nu p.1 p.2)
        (Icc u₀ u₁ ×ˢ Icc v₀ v₁) (s, v)) (1, 0)) v := by
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  have hC1R : RouteBFieldsC1On S R :=
    fun c => (hC1 c).mono hR
  have hA : ContDiffOn ℝ 1 (routeBGravCoefficient S) R :=
    routeB_gravCoefficient_contDiffOn hC1R hr hgap
  have hG : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => routeBGravCoefficient S p * S.nu p.1 p.2) R :=
    hA.mul (hC1R .contraction)
  have hsource : ∀ p ∈ R,
      (fderivWithin ℝ (routeBField S .contraction) K p) (0, 1) =
        routeBGravCoefficient S p * S.nu p.1 p.2 := by
    intro p hp
    have h := hJet.contraction_out p (hR hp) (hDev p hp)
    change (fderivWithin ℝ (routeBField S .contraction) K p) (0, 1) =
      routeBMixedExpr (fun c => routeBField S c p) at h
    exact h.trans (routeB_mixedExpr_eq_gravCoefficient_mul_nu S p
      (hr p hp) (hgap p hp))
  exact routeB_horizontal_jet_hasDerivAt_of_local_vertical_source
    hu hv hv' hs hR hUniqueK (hC1 .contraction) hG hsource

/-- The incoming jet of `β` differentiates vertically to the incoming jet
of the scalar multiple of the gravitational source on a safe rectangle. -/
theorem routeB_beta_horizontal_jet_hasDerivAt_of_local_classical
    {b : ℝ} {K : Set (ℝ × ℝ)}
    {u₀ u₁ v₀ v₁ s v : ℝ}
    (hu : u₀ < u₁) (hv : v₀ < v) (hv' : v < v₁)
    (hs : s ∈ Icc u₀ u₁)
    (hR : Icc u₀ u₁ ×ˢ Icc v₀ v₁ ⊆ K)
    (hDev : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      p ∈ developmentWithInitialEdge b)
    (hUniqueK : UniqueDiffOn ℝ K)
    {S : Fields} (hC1 : RouteBFieldsC1On S K)
    (hJet : RouteBClassicalJetOn b K S)
    (hr : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0) :
    HasDerivAt
      (fun t => (fderivWithin ℝ (routeBField S .incoming) K (s, t)) (1, 0))
      ((fderivWithin ℝ
        (fun p : ℝ × ℝ =>
          routeBGravCoefficient S p * S.nu p.1 p.2 * S.phi p.1 p.2)
        (Icc u₀ u₁ ×ˢ Icc v₀ v₁) (s, v)) (1, 0)) v := by
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  have hC1R : RouteBFieldsC1On S R :=
    fun c => (hC1 c).mono hR
  have hA : ContDiffOn ℝ 1 (routeBGravCoefficient S) R :=
    routeB_gravCoefficient_contDiffOn hC1R hr hgap
  have hG : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ =>
        routeBGravCoefficient S p * S.nu p.1 p.2 * S.phi p.1 p.2) R :=
    (hA.mul (hC1R .contraction)).mul (hC1R .scalar)
  have hsource : ∀ p ∈ R,
      (fderivWithin ℝ (routeBField S .incoming) K p) (0, 1) =
        routeBGravCoefficient S p * S.nu p.1 p.2 * S.phi p.1 p.2 := by
    intro p hp
    have h := hJet.incoming_out p (hR hp) (hDev p hp)
    change (fderivWithin ℝ (routeBField S .incoming) K p) (0, 1) =
      routeBMixedExpr (fun c => routeBField S c p) * S.phi p.1 p.2 at h
    rw [routeB_mixedExpr_eq_gravCoefficient_mul_nu S p
      (hr p hp) (hgap p hp)] at h
    exact h
  exact routeB_horizontal_jet_hasDerivAt_of_local_vertical_source
    hu hv hv' hs hR hUniqueK (hC1 .incoming) hG hsource

/-- Product-rule form of the local transverse equation for `ν`.  The
coefficient jet is taken on the safe rectangle, while the `ν` jet keeps the
larger solution region's relative derivative. -/
theorem routeB_nu_horizontal_jet_hasDerivAt_linear_local
    {b : ℝ} {K : Set (ℝ × ℝ)}
    {u₀ u₁ v₀ v₁ s v : ℝ}
    (hu : u₀ < u₁) (hv : v₀ < v) (hv' : v < v₁)
    (hs : s ∈ Icc u₀ u₁)
    (hR : Icc u₀ u₁ ×ˢ Icc v₀ v₁ ⊆ K)
    (hDev : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      p ∈ developmentWithInitialEdge b)
    (hUniqueK : UniqueDiffOn ℝ K)
    {S : Fields} (hC1 : RouteBFieldsC1On S K)
    (hJet : RouteBClassicalJetOn b K S)
    (hr : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0) :
    HasDerivAt
      (fun t => (fderivWithin ℝ (routeBField S .contraction) K (s, t)) (1, 0))
      ((fderivWithin ℝ (routeBGravCoefficient S)
          (Icc u₀ u₁ ×ˢ Icc v₀ v₁) (s, v)) (1, 0) * S.nu s v +
        routeBGravCoefficient S (s, v) *
          (fderivWithin ℝ (routeBField S .contraction) K (s, v)) (1, 0)) v := by
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  have hvR : v₀ < v₁ := hv.trans hv'
  have hUniqueR : UniqueDiffOn ℝ R :=
    uniqueDiffOn_convex ((convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁)) (by
      rw [interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨((u₀ + u₁) / 2, (v₀ + v₁) / 2),
        ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩)
  have hpR : (s, v) ∈ R := ⟨hs, ⟨hv.le, hv'.le⟩⟩
  have hAR : ContDiffOn ℝ 1 (routeBGravCoefficient S) R :=
    routeB_gravCoefficient_contDiffOn
      (fun c => (hC1 c).mono hR) hr hgap
  have hAdiff := hAR.differentiableOn (by norm_num) (s, v) hpR
  have hNdiff := ((hC1 .contraction).mono hR).differentiableOn
    (by norm_num) (s, v) hpR
  have hProduct := fderivWithin_fun_mul (hUniqueR (s, v) hpR)
    hAdiff hNdiff
  have hRestr := fderivWithin_subset hR (hUniqueR (s, v) hpR)
    ((hC1 .contraction).differentiableOn (by norm_num) (s, v) (hR hpR))
  have hODE := routeB_nu_horizontal_jet_hasDerivAt_of_local_classical
    hu hv hv' hs hR hDev hUniqueK hC1 hJet hr hgap
  change HasDerivAt
    (fun t => (fderivWithin ℝ (routeBField S .contraction) K (s, t)) (1, 0))
    ((fderivWithin ℝ
      (fun y => routeBGravCoefficient S y * routeBField S .contraction y)
      R (s, v)) (1, 0)) v at hODE
  rw [hProduct] at hODE
  have hRjet := congrArg (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0)) hRestr
  simp only [add_apply, smul_apply, smul_eq_mul, R] at hODE
  rw [hRjet] at hODE
  convert hODE using 1
  simp only [routeBField]
  ring

/-- Product-rule form of the local transverse equation for `β`.  The
scalar incoming jet remains the jet on the original solution region. -/
theorem routeB_beta_horizontal_jet_hasDerivAt_linear_local
    {b : ℝ} {K : Set (ℝ × ℝ)}
    {u₀ u₁ v₀ v₁ s v : ℝ}
    (hu : u₀ < u₁) (hv : v₀ < v) (hv' : v < v₁)
    (hs : s ∈ Icc u₀ u₁)
    (hR : Icc u₀ u₁ ×ˢ Icc v₀ v₁ ⊆ K)
    (hDev : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      p ∈ developmentWithInitialEdge b)
    (hUniqueK : UniqueDiffOn ℝ K)
    {S : Fields} (hC1 : RouteBFieldsC1On S K)
    (hJet : RouteBClassicalJetOn b K S)
    (hr : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0) :
    HasDerivAt
      (fun t => (fderivWithin ℝ (routeBField S .incoming) K (s, t)) (1, 0))
      (((fderivWithin ℝ (routeBGravCoefficient S)
          (Icc u₀ u₁ ×ˢ Icc v₀ v₁) (s, v)) (1, 0) * S.nu s v +
        routeBGravCoefficient S (s, v) *
          (fderivWithin ℝ (routeBField S .contraction) K (s, v)) (1, 0)) *
          S.phi s v +
        routeBGravCoefficient S (s, v) * S.nu s v *
          (fderivWithin ℝ (routeBField S .scalar) K (s, v)) (1, 0)) v := by
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  have hvR : v₀ < v₁ := hv.trans hv'
  have hUniqueR : UniqueDiffOn ℝ R :=
    uniqueDiffOn_convex ((convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁)) (by
      rw [interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨((u₀ + u₁) / 2, (v₀ + v₁) / 2),
        ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩)
  have hpR : (s, v) ∈ R := ⟨hs, ⟨hv.le, hv'.le⟩⟩
  have hAR : ContDiffOn ℝ 1 (routeBGravCoefficient S) R :=
    routeB_gravCoefficient_contDiffOn
      (fun c => (hC1 c).mono hR) hr hgap
  have hAdiff := hAR.differentiableOn (by norm_num) (s, v) hpR
  have hNdiff := ((hC1 .contraction).mono hR).differentiableOn
    (by norm_num) (s, v) hpR
  have hPdiff := ((hC1 .scalar).mono hR).differentiableOn
    (by norm_num) (s, v) hpR
  have hInner := fderivWithin_fun_mul (hUniqueR (s, v) hpR)
    hAdiff hNdiff
  have hOuter := fderivWithin_fun_mul (hUniqueR (s, v) hpR)
    (hAdiff.mul hNdiff) hPdiff
  have hNRestr := fderivWithin_subset hR (hUniqueR (s, v) hpR)
    ((hC1 .contraction).differentiableOn (by norm_num) (s, v) (hR hpR))
  have hPRestr := fderivWithin_subset hR (hUniqueR (s, v) hpR)
    ((hC1 .scalar).differentiableOn (by norm_num) (s, v) (hR hpR))
  have hODE := routeB_beta_horizontal_jet_hasDerivAt_of_local_classical
    hu hv hv' hs hR hDev hUniqueK hC1 hJet hr hgap
  change HasDerivAt
    (fun t => (fderivWithin ℝ (routeBField S .incoming) K (s, t)) (1, 0))
    ((fderivWithin ℝ
      (fun y => (routeBGravCoefficient S y * routeBField S .contraction y) *
        routeBField S .scalar y) R (s, v)) (1, 0)) v at hODE
  simp only [Pi.mul_apply] at hOuter
  rw [hOuter] at hODE
  have hfun : routeBGravCoefficient S * routeBField S .contraction =
      (fun y => routeBGravCoefficient S y * routeBField S .contraction y) := rfl
  rw [hfun] at hODE
  rw [hInner] at hODE
  simp only [add_apply, smul_apply, smul_eq_mul, R] at hODE
  have hNjet := congrArg (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0)) hNRestr
  have hPjet := congrArg (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0)) hPRestr
  rw [hNjet, hPjet] at hODE
  convert hODE using 1
  simp only [routeBField]
  ring

end ChristodoulouBV.Uniqueness

end
