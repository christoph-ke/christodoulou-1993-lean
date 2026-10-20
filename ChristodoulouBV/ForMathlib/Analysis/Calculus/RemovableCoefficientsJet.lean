module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsSquared
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# A removable first jet for a cubic-over-square quotient

The normalized cubic numerator and its normalized first jet need only be
continuous. The proof differentiates the original quotient off the diagonal
and extends that derivative continuously to the closed triangle.
-/

public section

open Set Filter
open scoped Topology

namespace intervalIntegral

/-- The quotient of a cubically vanishing numerator by a squared linearly
vanishing denominator, set to zero on and below the diagonal. -/
@[expose] noncomputable def cubicSquaredQuotient
    (J r : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then J p / r p ^ 2 else 0

/-- The quotient of a cubically vanishing numerator by a linearly vanishing
denominator, with its removable diagonal value set to zero. -/
@[expose] noncomputable def cubicLinearQuotient
    (J r : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then J p / r p else 0

/-- The continuous candidate jet of a cubic-over-square quotient, expressed
using normalized value and first-jet quotients. -/
@[expose] noncomputable def cubicSquaredQuotientJet
    (U ρ : ℝ × ℝ → ℝ)
    (V Gr : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (1 / ρ p ^ 2) • V p - (2 * U p / ρ p ^ 3) • Gr p

/-- The candidate jet of a cubic-over-square quotient is continuous wherever
the normalized denominator is nonzero. -/
theorem continuousOn_cubicSquaredQuotientJet
    {K : Set (ℝ × ℝ)} {U ρ : ℝ × ℝ → ℝ}
    {V Gr : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hU : ContinuousOn U K) (hρ : ContinuousOn ρ K)
    (hV : ContinuousOn V K) (hGr : ContinuousOn Gr K)
    (hρne : ∀ p ∈ K, ρ p ≠ 0) :
    ContinuousOn (cubicSquaredQuotientJet U ρ V Gr) K := by
  have hfirst : ContinuousOn (fun p => (1 / ρ p ^ 2) • V p) K :=
    ((continuousOn_const.div (hρ.pow 2)
      (fun p hp => pow_ne_zero 2 (hρne p hp))).smul hV)
  have hsecond : ContinuousOn
      (fun p => (2 * U p / ρ p ^ 3) • Gr p) K :=
    (((continuousOn_const.mul hU).div (hρ.pow 3)
      (fun p hp => pow_ne_zero 3 (hρne p hp))).smul hGr)
  exact hfirst.sub hsecond

/-- Continuous normalized cubic value and first-jet quotients give a `C¹`
extension and its exact first jet for the squared-denominator quotient. -/
theorem cubicSquaredQuotient_hasJet
    {a b c : ℝ} (hab : a < b)
    {J r U ρ : ℝ × ℝ → ℝ}
    {GJ Gr V : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hU : ContinuousOn U (closedCoordTriangle a b))
    (hρ : ContinuousOn ρ (closedCoordTriangle a b))
    (hV : ContinuousOn V (closedCoordTriangle a b))
    (hGr : ContinuousOn Gr (closedCoordTriangle a b))
    (hdJ : DifferentiableOn ℝ J (interior (closedCoordTriangle a b)))
    (hdr : DifferentiableOn ℝ r (interior (closedCoordTriangle a b)))
    (hderivJ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ J p = GJ p)
    (hderivr : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ r p = Gr p)
    (hρpos : ∀ p ∈ closedCoordTriangle a b, c ≤ ρ p) (hc : 0 < c)
    (hJfactor : ∀ p ∈ closedCoordTriangle a b,
      J p = (p.2 - p.1) ^ 3 * U p)
    (hGJfactor : ∀ p ∈ interior (closedCoordTriangle a b),
      GJ p = (p.2 - p.1) ^ 2 • V p)
    (hrfactor : ∀ p ∈ closedCoordTriangle a b,
      r p = (p.2 - p.1) * ρ p) :
    ContDiffOn ℝ 1 (cubicSquaredQuotient J r) (closedCoordTriangle a b) ∧
      ∀ p ∈ closedCoordTriangle a b,
        fderivWithin ℝ (cubicSquaredQuotient J r)
          (closedCoordTriangle a b) p =
          cubicSquaredQuotientJet U ρ V Gr p := by
  let K := closedCoordTriangle a b
  let A := cubicSquaredQuotient J r
  let G := cubicSquaredQuotientJet U ρ V Gr
  have hρne : ∀ p ∈ K, ρ p ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hρpos p hp))
  have hAeq : ∀ p ∈ K, A p =
      (p.2 - p.1) * U p / ρ p ^ 2 := by
    intro p hp
    have hcoords : p.1 ≤ p.2 := hp.2.1
    by_cases hstrict : p.1 < p.2
    · have hd : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hstrict.ne'
      rw [show A p = J p / r p ^ 2 by simp [A, cubicSquaredQuotient, hstrict],
        hJfactor p hp, hrfactor p hp]
      field_simp [hd, hρne p hp]
    · have heq : p.1 = p.2 := le_antisymm hcoords (le_of_not_gt hstrict)
      rw [show A p = 0 by simp [A, cubicSquaredQuotient, hstrict]]
      simp [heq]
  have hgap : ContinuousOn (fun p : ℝ × ℝ => p.2 - p.1) K := by fun_prop
  have hAcont : ContinuousOn A K := by
    apply ((hgap.mul hU).div (hρ.pow 2)
      (fun p hp => pow_ne_zero 2 (hρne p hp))).congr
    intro p hp
    exact hAeq p hp
  have hGcont : ContinuousOn G K :=
    continuousOn_cubicSquaredQuotientJet hU hρ hV hGr hρne
  have hquot : DifferentiableOn ℝ (fun p => J p / r p ^ 2) (interior K) := by
    intro p hp
    have hp' : p ∈ openCoordTriangle a b := by
      simpa only [K, interior_closedCoordTriangle] using hp
    have hrne : r p ≠ 0 := by
      rw [hrfactor p (interior_subset hp)]
      exact mul_ne_zero (sub_ne_zero.mpr hp'.2.1.ne')
        (hρne p (interior_subset hp))
    have hJa : DifferentiableAt ℝ J p :=
      (hdJ p hp).differentiableAt (isOpen_interior.mem_nhds hp)
    have hra : DifferentiableAt ℝ r p :=
      (hdr p hp).differentiableAt (isOpen_interior.mem_nhds hp)
    have hq : DifferentiableAt ℝ (fun q => J q / r q ^ 2) p := by
      change DifferentiableAt ℝ (J * (fun q => (r q ^ 2)⁻¹)) p
      exact hJa.mul ((hra.pow 2).inv (pow_ne_zero 2 hrne))
    exact hq.differentiableWithinAt
  have hAeqInt : EqOn A (fun p => J p / r p ^ 2) (interior K) := by
    intro p hp
    have hp' : p ∈ openCoordTriangle a b := by
      simpa only [K, interior_closedCoordTriangle] using hp
    simp [A, cubicSquaredQuotient, hp'.2.1]
  have hAdiff : DifferentiableOn ℝ A (interior K) :=
    hquot.congr hAeqInt
  have hAderiv : ∀ p ∈ interior K, fderiv ℝ A p = G p := by
    intro p hp
    have hpK : p ∈ K := interior_subset hp
    have hp' : p ∈ openCoordTriangle a b := by
      simpa only [K, interior_closedCoordTriangle] using hp
    have hd : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hp'.2.1.ne'
    have hrne : r p ≠ 0 := by
      rw [hrfactor p hpK]
      exact mul_ne_zero hd (hρne p hpK)
    have hJa : DifferentiableAt ℝ J p :=
      (hdJ p hp).differentiableAt (isOpen_interior.mem_nhds hp)
    have hra : DifferentiableAt ℝ r p :=
      (hdr p hp).differentiableAt (isOpen_interior.mem_nhds hp)
    have hevent : A =ᶠ[𝓝 p] (fun q => J q / r q ^ 2) := by
      filter_upwards [isOpen_interior.mem_nhds hp] with q hq
      exact hAeqInt hq
    rw [hevent.fderiv_eq, fderiv_div_sq hJa hra hrne,
      hderivJ p hp, hderivr p hp,
      hJfactor p hpK, hGJfactor p hp, hrfactor p hpK]
    apply ContinuousLinearMap.ext
    intro e
    simp only [G, cubicSquaredQuotientJet, sub_apply, smul_apply, smul_eq_mul]
    field_simp [hd, hρne p hpK]
  have hconvex := convex_closedCoordTriangle a b
  have hclosed := isClosed_closedCoordTriangle a b
  have hinterior : (interior K).Nonempty := by
    change (interior (closedCoordTriangle a b)).Nonempty
    rw [interior_closedCoordTriangle]
    exact openCoordTriangle_nonempty hab
  constructor
  · exact hconvex.contDiffOn_one_of_continuousOn_fderiv hclosed hinterior
      hAcont hGcont hAdiff hAderiv
  · intro p hp
    exact hconvex.fderivWithin_eq_of_continuousOn_fderiv hclosed hinterior
      hAcont hGcont hAdiff hAderiv hp

/-- The diagonal first jet of the squared quotient from the cubic numerator
and linear denominator coefficients. The two coordinate signs are opposite. -/
theorem cubicSquaredQuotientJet_axis
    {u l b : ℝ} {U ρ : ℝ × ℝ → ℝ}
    {V Gr : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hl : l ≠ 0)
    (hρ : ρ (u, u) = l)
    (hU : U (u, u) = l * b ^ 2 / 12)
    (hVu : V (u, u) (1, 0) = -(l * b ^ 2 / 4))
    (hVv : V (u, u) (0, 1) = l * b ^ 2 / 4)
    (hGru : Gr (u, u) (1, 0) = -l)
    (hGrv : Gr (u, u) (0, 1) = l) :
    cubicSquaredQuotientJet U ρ V Gr (u, u) (1, 0) =
        -(b ^ 2 / (12 * l)) ∧
      cubicSquaredQuotientJet U ρ V Gr (u, u) (0, 1) =
        b ^ 2 / (12 * l) := by
  constructor
  · simp only [cubicSquaredQuotientJet, sub_apply, smul_apply, smul_eq_mul,
      hρ, hU, hVu, hGru]
    field_simp [hl]
    ring
  · simp only [cubicSquaredQuotientJet, sub_apply, smul_apply, smul_eq_mul,
      hρ, hU, hVv, hGrv]
    field_simp [hl]
    ring

/-- On the closed triangle, the cubic-over-linear quotient is the product
of its cubic-over-square counterpart and the denominator. -/
theorem cubicLinearQuotient_eq_squared_mul
    {a b c : ℝ} {J r ρ : ℝ × ℝ → ℝ}
    (hc : 0 < c)
    (hρpos : ∀ p ∈ closedCoordTriangle a b, c ≤ ρ p)
    (hrfactor : ∀ p ∈ closedCoordTriangle a b,
      r p = (p.2 - p.1) * ρ p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    cubicLinearQuotient J r p = cubicSquaredQuotient J r p * r p := by
  by_cases hstrict : p.1 < p.2
  · have hrne : r p ≠ 0 := by
      rw [hrfactor p hp]
      exact mul_ne_zero (sub_ne_zero.mpr hstrict.ne')
        (ne_of_gt (hc.trans_le (hρpos p hp)))
    simp only [cubicLinearQuotient, cubicSquaredQuotient, hstrict, ↓reduceIte]
    field_simp [hrne]
  · simp [cubicLinearQuotient, cubicSquaredQuotient, hstrict]

/-- The linearly vanishing quotient inherits `C¹` regularity from the
squared-denominator quotient and the original denominator. -/
theorem contDiffOn_cubicLinearQuotient
    {a b c : ℝ} {J r ρ : ℝ × ℝ → ℝ}
    (hA : ContDiffOn ℝ 1 (cubicSquaredQuotient J r)
      (closedCoordTriangle a b))
    (hr : ContDiffOn ℝ 1 r (closedCoordTriangle a b))
    (hc : 0 < c)
    (hρpos : ∀ p ∈ closedCoordTriangle a b, c ≤ ρ p)
    (hrfactor : ∀ p ∈ closedCoordTriangle a b,
      r p = (p.2 - p.1) * ρ p) :
    ContDiffOn ℝ 1 (cubicLinearQuotient J r)
      (closedCoordTriangle a b) := by
  exact (hA.mul hr).congr (fun p hp =>
    cubicLinearQuotient_eq_squared_mul hc hρpos hrfactor hp)

/-- The relative first jet of the cubic-over-linear quotient vanishes at
every diagonal point, since both product factors vanish there. -/
theorem fderivWithin_cubicLinearQuotient_diag
    {a b c : ℝ} {J r ρ : ℝ × ℝ → ℝ} {u : ℝ}
    (hab : a < b)
    (hu : u ∈ Icc a b)
    (hA : ContDiffOn ℝ 1 (cubicSquaredQuotient J r)
      (closedCoordTriangle a b))
    (hr : ContDiffOn ℝ 1 r (closedCoordTriangle a b))
    (hc : 0 < c)
    (hρpos : ∀ p ∈ closedCoordTriangle a b, c ≤ ρ p)
    (hrfactor : ∀ p ∈ closedCoordTriangle a b,
      r p = (p.2 - p.1) * ρ p) :
    fderivWithin ℝ (cubicLinearQuotient J r)
      (closedCoordTriangle a b) (u, u) = 0 := by
  let K := closedCoordTriangle a b
  have hdiag : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hEq : EqOn (cubicLinearQuotient J r)
      (fun p => cubicSquaredQuotient J r p * r p) K :=
    fun p hp => cubicLinearQuotient_eq_squared_mul hc hρpos hrfactor hp
  rw [fderivWithin_congr' hEq hdiag]
  have huDiff : UniqueDiffWithinAt ℝ K (u, u) :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact
        openCoordTriangle_nonempty hab))
      (u, u) hdiag
  rw [fderivWithin_fun_mul huDiff
    ((hA.differentiableOn (by norm_num)) (u, u) hdiag)
    ((hr.differentiableOn (by norm_num)) (u, u) hdiag)]
  have hAz : cubicSquaredQuotient J r (u, u) = 0 := by
    simp [cubicSquaredQuotient]
  have hrz : r (u, u) = 0 := by
    rw [hrfactor (u, u) hdiag]
    ring
  simp [hAz, hrz]

end intervalIntegral

end
