module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableGapPowerAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Normalized coordinate first jets

Two scalar diagonal expansions give a continuous normalized Fréchet first
jet on a coordinate triangle. This packages the horizontal and vertical
asymptotics without differentiating their normalized quotients.
-/

public section

open Set

namespace intervalIntegral

/-- The continuous linear map with prescribed horizontal and vertical
coordinate values. -/
@[expose] noncomputable def coordinateLinearJet (h v : ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  h • ContinuousLinearMap.fst ℝ ℝ ℝ +
    v • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Evaluation of a coordinate linear jet. -/
theorem coordinateLinearJet_apply (h v : ℝ) (e : ℝ × ℝ) :
    coordinateLinearJet h v e = h * e.1 + v * e.2 := by
  simp [coordinateLinearJet, smul_eq_mul]

/-- Every linear functional on the real coordinate plane is determined by
its two coordinate values. -/
theorem coordinateLinearJet_components
    (G : (ℝ × ℝ) →L[ℝ] ℝ) :
    coordinateLinearJet (G (1, 0)) (G (0, 1)) = G := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, y⟩
  have hdecomp : (x, y) = x • (1, 0) + y • (0, 1) := by
    ext <;> simp
  calc
    coordinateLinearJet (G (1, 0)) (G (0, 1)) (x, y) =
        x * G (1, 0) + y * G (0, 1) := by
          simp [coordinateLinearJet_apply]
          ring
    _ = G (x, y) := by
      rw [hdecomp, map_add, map_smul, map_smul]
      ring

/-- The normalized coordinate jet formed from two scalar gap quotients. -/
@[expose] noncomputable def normalizedCoordinateJet
    (n : ℕ) (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (H V : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  coordinateLinearJet
    (gapPowerQuotient n (fun q => G q (1, 0)) H p)
    (gapPowerQuotient n (fun q => G q (0, 1)) V p)

/-- Uniform axis expansions of both coordinate jets give a continuous
normalized full first jet. -/
theorem continuousOn_normalizedCoordinateJet_of_uniform_axis
    {a b : ℝ} {n : ℕ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    {H V : ℝ × ℝ → ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (hH : ContinuousOn H (closedCoordTriangle a b))
    (hV : ContinuousOn V (closedCoordTriangle a b))
    (hHaxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |G (u, v) (1, 0) - H (u, u) * (v - u) ^ n| ≤
          ε * (v - u) ^ n)
    (hVaxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |G (u, v) (0, 1) - V (u, u) * (v - u) ^ n| ≤
          ε * (v - u) ^ n) :
    ContinuousOn (normalizedCoordinateJet n G H V)
      (closedCoordTriangle a b) := by
  have hGH : ContinuousOn (fun p => G p (1, 0))
      (closedCoordTriangle a b) := hG.clm_apply continuousOn_const
  have hGV : ContinuousOn (fun p => G p (0, 1))
      (closedCoordTriangle a b) := hG.clm_apply continuousOn_const
  have hU := continuousOn_gapPowerQuotient_of_uniform_diagonal_axis
    hGH hH hHaxis
  have hW := continuousOn_gapPowerQuotient_of_uniform_diagonal_axis
    hGV hV hVaxis
  have hfst : ContinuousOn (fun p =>
      gapPowerQuotient n (fun q => G q (1, 0)) H p •
        ContinuousLinearMap.fst ℝ ℝ ℝ) (closedCoordTriangle a b) :=
    hU.smul continuousOn_const
  have hsnd : ContinuousOn (fun p =>
      gapPowerQuotient n (fun q => G q (0, 1)) V p •
        ContinuousLinearMap.snd ℝ ℝ ℝ) (closedCoordTriangle a b) :=
    hW.smul continuousOn_const
  exact hfst.add hsnd

/-- Off the diagonal, the original first jet is the gap power times its
normalized coordinate jet. -/
theorem normalizedCoordinateJet_factor
    {n : ℕ} {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    {H V : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p.1 < p.2) :
    G p = (p.2 - p.1) ^ n • normalizedCoordinateJet n G H V p := by
  have hd : (p.2 - p.1) ^ n ≠ 0 :=
    pow_ne_zero n (sub_ne_zero.mpr hp.ne')
  have hcomp := coordinateLinearJet_components (G p)
  rw [← hcomp]
  apply ContinuousLinearMap.ext
  intro e
  simp only [normalizedCoordinateJet, gapPowerQuotient, hp, ↓reduceIte,
    coordinateLinearJet_apply, smul_apply, smul_eq_mul]
  field_simp [hd]

/-- Uniform cubic value and quadratic coordinate-jet asymptotics suffice
for a `C¹` squared-denominator quotient on the closed triangle. The
normalized quotients are constructed by `gapPowerQuotient`; no derivative of
those merely continuous functions is taken. -/
theorem cubicSquaredQuotient_hasJet_of_uniform_axis
    {a b c : ℝ} (hab : a < b)
    {J r ρ C₀ Cᵤ Cᵥ : ℝ × ℝ → ℝ}
    (hJ : ContDiffOn ℝ 1 J (closedCoordTriangle a b))
    (hr : ContDiffOn ℝ 1 r (closedCoordTriangle a b))
    (hρ : ContinuousOn ρ (closedCoordTriangle a b))
    (hC₀ : ContinuousOn C₀ (closedCoordTriangle a b))
    (hCᵤ : ContinuousOn Cᵤ (closedCoordTriangle a b))
    (hCᵥ : ContinuousOn Cᵥ (closedCoordTriangle a b))
    (hρpos : ∀ p ∈ closedCoordTriangle a b, c ≤ ρ p)
    (hc : 0 < c)
    (hrfactor : ∀ p ∈ closedCoordTriangle a b,
      r p = (p.2 - p.1) * ρ p)
    (hJdiag : ∀ u ∈ Icc a b, J (u, u) = 0)
    (hJaxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |J (u, v) - C₀ (u, u) * (v - u) ^ 3| ≤
          ε * (v - u) ^ 3)
    (hJuaxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |(fderivWithin ℝ J (closedCoordTriangle a b) (u, v)) (1, 0) -
          Cᵤ (u, u) * (v - u) ^ 2| ≤ ε * (v - u) ^ 2)
    (hJvaxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |(fderivWithin ℝ J (closedCoordTriangle a b) (u, v)) (0, 1) -
          Cᵥ (u, u) * (v - u) ^ 2| ≤ ε * (v - u) ^ 2) :
    let K := closedCoordTriangle a b
    let GJ := fderivWithin ℝ J K
    let Gr := fderivWithin ℝ r K
    let U := gapPowerQuotient 3 J C₀
    let V := normalizedCoordinateJet 2 GJ Cᵤ Cᵥ
    ContDiffOn ℝ 1 (cubicSquaredQuotient J r) K ∧
      ∀ p ∈ K,
        fderivWithin ℝ (cubicSquaredQuotient J r) K p =
          cubicSquaredQuotientJet U ρ V Gr p := by
  dsimp only
  let K := closedCoordTriangle a b
  let GJ := fderivWithin ℝ J K
  let Gr := fderivWithin ℝ r K
  let U := gapPowerQuotient 3 J C₀
  let V := normalizedCoordinateJet 2 GJ Cᵤ Cᵥ
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hGJ : ContinuousOn GJ K :=
    hJ.continuousOn_fderivWithin hunique (by norm_num)
  have hGr : ContinuousOn Gr K :=
    hr.continuousOn_fderivWithin hunique (by norm_num)
  have hU : ContinuousOn U K :=
    continuousOn_gapPowerQuotient_of_uniform_diagonal_axis
      hJ.continuousOn hC₀ hJaxis
  have hV : ContinuousOn V K :=
    continuousOn_normalizedCoordinateJet_of_uniform_axis
      hGJ hCᵤ hCᵥ hJuaxis hJvaxis
  have hJfactor : ∀ p ∈ K,
      J p = (p.2 - p.1) ^ 3 * U p := by
    intro p hp
    have hpcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    by_cases hstrict : p.1 < p.2
    · have hd : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr hstrict.ne'
      simp only [U, gapPowerQuotient, hstrict, ↓reduceIte]
      field_simp [hd]
    · have heq : p.1 = p.2 := le_antisymm hpcoord.2.1 (le_of_not_gt hstrict)
      have hJz : J p = 0 := by
        have hmem : p.1 ∈ Icc a b := ⟨hpcoord.1, hpcoord.2.1.trans hpcoord.2.2⟩
        rcases p with ⟨u, v⟩
        dsimp at heq hmem ⊢
        subst v
        exact hJdiag u hmem
      rw [hJz, ← heq]
      simp
  have hGJfactor : ∀ p ∈ interior K,
      GJ p = (p.2 - p.1) ^ 2 • V p := by
    intro p hp
    have hp' : p ∈ openCoordTriangle a b := by
      simpa only [K, interior_closedCoordTriangle] using hp
    exact normalizedCoordinateJet_factor hp'.2.1
  have hdJ : DifferentiableOn ℝ J (interior K) :=
    (hJ.differentiableOn (by norm_num)).mono interior_subset
  have hdr : DifferentiableOn ℝ r (interior K) :=
    (hr.differentiableOn (by norm_num)).mono interior_subset
  have hderivJ : ∀ p ∈ interior K, fderiv ℝ J p = GJ p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  have hderivr : ∀ p ∈ interior K, fderiv ℝ r p = Gr p := by
    intro p hp
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm
  exact cubicSquaredQuotient_hasJet hab hU hρ hV hGr
    hdJ hdr hderivJ hderivr hρpos hc hJfactor hGJfactor hrfactor

end intervalIntegral

end
