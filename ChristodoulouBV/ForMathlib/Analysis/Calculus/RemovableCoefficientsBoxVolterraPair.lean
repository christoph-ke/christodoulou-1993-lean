module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxVolterra
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraDifference
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraHorizontalDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# A common box from two attenuated Volterra inputs

The value, horizontal-jet, and vertical-jet Volterra estimates are assembled
into one pair box. The radius estimates are given separately, so the result
also applies when the radii arise from a construction other than an integral.
-/

public section

open Set

namespace intervalIntegral

/-- Input data for the two-input attenuated Volterra estimates. The two
abstract single-input boxes retain the independent axis expansions. -/
structure AttenuatedVolterraPairData (a b c : ℝ) where
  /-- The first single-input axis box. -/
  first : CubicRationalTriangleBox a b c
  /-- The second single-input axis box. -/
  second : CubicRationalTriangleBox a b c
  /-- The first quadratic source. -/
  j₁ : ℝ × ℝ → ℝ
  /-- The second quadratic source. -/
  j₂ : ℝ × ℝ → ℝ
  /-- The first linear attenuation kernel. -/
  k₁ : ℝ × ℝ → ℝ
  /-- The second linear attenuation kernel. -/
  k₂ : ℝ × ℝ → ℝ
  /-- The first numerator is the corresponding attenuated Volterra integral. -/
  first_eq : first.J = fun p => attenuatedVolterraIntegral j₁ k₁ p.1 p.2
  /-- The second numerator is the corresponding attenuated Volterra integral. -/
  second_eq : second.J = fun p => attenuatedVolterraIntegral j₂ k₂ p.1 p.2
  /-- The coordinate triangle is nondegenerate. -/
  hab : a < b
  /-- The coordinate width is at most one. -/
  width_le_one : b - a ≤ 1
  /-- Both sources have a continuous first jet. -/
  j₁_c1 : ContDiffOn ℝ 1 j₁ (closedCoordTriangle a b)
  /-- The second source has a continuous first jet. -/
  j₂_c1 : ContDiffOn ℝ 1 j₂ (closedCoordTriangle a b)
  /-- The first kernel has a continuous first jet. -/
  k₁_c1 : ContDiffOn ℝ 1 k₁ (closedCoordTriangle a b)
  /-- The second kernel has a continuous first jet. -/
  k₂_c1 : ContDiffOn ℝ 1 k₂ (closedCoordTriangle a b)
  /-- Both sources vanish on the diagonal. -/
  j_diag : (∀ u ∈ Icc a b, j₁ (u, u) = 0) ∧
    (∀ u ∈ Icc a b, j₂ (u, u) = 0)
  /-- Common quadratic source coefficient. -/
  S₀ : ℝ
  /-- Common linear horizontal source-jet coefficient. -/
  S₁ : ℝ
  /-- Common linear attenuation coefficient. -/
  T₀ : ℝ
  /-- Common horizontal attenuation-jet coefficient. -/
  T₁ : ℝ
  /-- Source value-difference coefficient. -/
  SΔ₀ : ℝ
  /-- Source horizontal-jet difference coefficient. -/
  SΔ₁ : ℝ
  /-- Kernel value-difference coefficient. -/
  TΔ₀ : ℝ
  /-- Kernel horizontal-jet difference coefficient. -/
  TΔ₁ : ℝ
  /-- Common radius-jet coefficient. -/
  R₁ : ℝ
  /-- Radius-jet difference coefficient. -/
  RΔ : ℝ
  /-- Input distance. -/
  D : ℝ
  /-- All scalar coefficients are nonnegative. -/
  coeff_nonneg : 0 ≤ S₀ ∧ 0 ≤ S₁ ∧ 0 ≤ T₀ ∧ 0 ≤ T₁ ∧
    0 ≤ SΔ₀ ∧ 0 ≤ SΔ₁ ∧ 0 ≤ TΔ₀ ∧ 0 ≤ TΔ₁ ∧
    0 ≤ R₁ ∧ 0 ≤ RΔ ∧ 0 ≤ D
  /-- Both sources have the same nonnegative quadratic bound. -/
  source_bound : ∀ p ∈ closedCoordTriangle a b,
    (0 ≤ j₁ p ∧ j₁ p ≤ S₀ * (p.2 - p.1) ^ 2) ∧
    (0 ≤ j₂ p ∧ j₂ p ≤ S₀ * (p.2 - p.1) ^ 2)
  /-- Both kernels have the same nonnegative linear bound. -/
  kernel_bound : ∀ p ∈ closedCoordTriangle a b,
    (0 ≤ k₁ p ∧ k₁ p ≤ T₀ * (p.2 - p.1)) ∧
    (0 ≤ k₂ p ∧ k₂ p ≤ T₀ * (p.2 - p.1))
  /-- Horizontal source jets have a common linear bound. -/
  source_jet_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ j₁ (closedCoordTriangle a b) p) (1, 0)| ≤
      S₁ * (p.2 - p.1) ∧
    |(fderivWithin ℝ j₂ (closedCoordTriangle a b) p) (1, 0)| ≤
      S₁ * (p.2 - p.1)
  /-- Horizontal kernel jets have a common bound. -/
  kernel_jet_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ k₁ (closedCoordTriangle a b) p) (1, 0)| ≤ T₁ ∧
    |(fderivWithin ℝ k₂ (closedCoordTriangle a b) p) (1, 0)| ≤ T₁
  /-- The two source values differ quadratically. -/
  source_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |j₁ p - j₂ p| ≤ SΔ₀ * (p.2 - p.1) ^ 2 * D
  /-- The two kernel values differ linearly. -/
  kernel_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |k₁ p - k₂ p| ≤ TΔ₀ * (p.2 - p.1) * D
  /-- The horizontal source-jet difference vanishes linearly. -/
  source_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ j₁ (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ j₂ (closedCoordTriangle a b) p) (1, 0)| ≤
        SΔ₁ * (p.2 - p.1) * D
  /-- The horizontal kernel-jet difference is uniformly bounded. -/
  kernel_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |(fderivWithin ℝ k₁ (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ k₂ (closedCoordTriangle a b) p) (1, 0)| ≤ TΔ₁ * D
  /-- Both radius coordinate jets have a common bound. -/
  radius_jet_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ first.r (closedCoordTriangle a b) p) e| ≤ R₁ ∧
      |(fderivWithin ℝ second.r (closedCoordTriangle a b) p) e| ≤ R₁
  /-- The radius value difference vanishes linearly. -/
  radius_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |first.r p - second.r p| ≤ (p.2 - p.1) * D
  /-- The radius coordinate-jet difference has a common bound. -/
  radius_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ first.r (closedCoordTriangle a b) p) e -
        (fderivWithin ℝ second.r (closedCoordTriangle a b) p) e| ≤ RΔ * D

/-- The cubic value coefficient obtained from a quadratic source. -/
@[expose] noncomputable def AttenuatedVolterraPairData.valueCoefficient
    {a b c : ℝ} (B : AttenuatedVolterraPairData a b c) : ℝ := B.S₀ / 3

/-- One coefficient controls both coordinate jets of the cubic numerator. -/
@[expose] noncomputable def AttenuatedVolterraPairData.jetCoefficient
    {a b c : ℝ} (B : AttenuatedVolterraPairData a b c) : ℝ :=
  B.S₀ + B.T₀ * (B.S₀ / 3) + (B.S₁ + B.S₀ * B.T₁) / 2

/-- Cubic value-difference coefficient from the two-input Volterra bound. -/
@[expose] noncomputable def AttenuatedVolterraPairData.valueSubCoefficient
    {a b c : ℝ} (B : AttenuatedVolterraPairData a b c) : ℝ :=
  B.SΔ₀ / 3 + B.S₀ * B.TΔ₀ / 6

/-- One coefficient controls both coordinate-jet differences. -/
@[expose] noncomputable def AttenuatedVolterraPairData.jetSubCoefficient
    {a b c : ℝ} (B : AttenuatedVolterraPairData a b c) : ℝ :=
  (B.SΔ₀ + B.TΔ₀ * (B.S₀ / 3) +
      B.T₀ * (B.SΔ₀ / 3 + B.S₀ * B.TΔ₀ / 6)) +
    (B.TΔ₀ * (B.S₁ + B.S₀ * B.T₁) / 4 +
      (B.SΔ₁ + B.SΔ₀ * B.T₁ + B.S₀ * B.TΔ₁) / 2)

/-- The separate two-input Volterra estimates give one common numerator and
radius box, with the same coefficient for either coordinate jet. -/
noncomputable def AttenuatedVolterraPairData.toCubicRationalPairBox
    {a b c : ℝ} (B : AttenuatedVolterraPairData a b c) :
    CubicRationalPairBox a b c := by
  rcases B.coeff_nonneg with
    ⟨hS₀, hS₁, hT₀, hT₁, hSΔ₀, hSΔ₁, hTΔ₀, hTΔ₁, hR₁, hRΔ, hD⟩
  have hsource₁ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ B.j₁ p ∧ B.j₁ p ≤ B.S₀ * (p.2 - p.1) ^ 2 :=
    fun p hp => (B.source_bound p hp).1
  have hsource₂ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ B.j₂ p ∧ B.j₂ p ≤ B.S₀ * (p.2 - p.1) ^ 2 :=
    fun p hp => (B.source_bound p hp).2
  have hkernel₁ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ B.k₁ p ∧ B.k₁ p ≤ B.T₀ * (p.2 - p.1) :=
    fun p hp => (B.kernel_bound p hp).1
  have hkernel₂ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ B.k₂ p ∧ B.k₂ p ≤ B.T₀ * (p.2 - p.1) :=
    fun p hp => (B.kernel_bound p hp).2
  have hsourceJet₁ : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ B.j₁ (closedCoordTriangle a b) p) (1, 0)| ≤
        B.S₁ * (p.2 - p.1) := fun p hp => (B.source_jet_bound p hp).1
  have hkernelJet₁ : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ B.k₁ (closedCoordTriangle a b) p) (1, 0)| ≤ B.T₁ :=
    fun p hp => (B.kernel_jet_bound p hp).1
  refine {
    first := B.first
    second := B.second
    J₀ := B.valueCoefficient
    J₁ := B.jetCoefficient
    JΔ₀ := B.valueSubCoefficient
    JΔ₁ := B.jetSubCoefficient
    R₁ := B.R₁
    RΔ := B.RΔ
    D := B.D
    width_le_one := B.width_le_one
    J₀_nonneg := by dsimp [AttenuatedVolterraPairData.valueCoefficient]; positivity
    J₁_nonneg := by dsimp [AttenuatedVolterraPairData.jetCoefficient]; positivity
    JΔ₀_nonneg := by dsimp [AttenuatedVolterraPairData.valueSubCoefficient]; positivity
    JΔ₁_nonneg := by dsimp [AttenuatedVolterraPairData.jetSubCoefficient]; positivity
    R₁_nonneg := hR₁
    RΔ_nonneg := hRΔ
    D_nonneg := hD
    J_bound := ?_
    J_jet_bound := ?_
    J_sub_bound := ?_
    J_jet_sub_bound := ?_
    r_jet_bound := B.radius_jet_bound
    r_sub_bound := B.radius_sub_bound
    r_jet_sub_bound := B.radius_jet_sub_bound
  }
  · intro p hp
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have h₁ := attenuatedVolterraIntegral_nonneg_le
      hcoord.1 hcoord.2.1 hcoord.2.2 B.j₁_c1.continuousOn B.k₁_c1.continuousOn
      (fun q hq => (hkernel₁ q hq).1) hsource₁
    have h₂ := attenuatedVolterraIntegral_nonneg_le
      hcoord.1 hcoord.2.1 hcoord.2.2 B.j₂_c1.continuousOn B.k₂_c1.continuousOn
      (fun q hq => (hkernel₂ q hq).1) hsource₂
    simpa only [B.first_eq, B.second_eq,
      AttenuatedVolterraPairData.valueCoefficient, div_mul_eq_mul_div] using
      And.intro h₁ h₂
  · intro p hp e he
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have h₁ : ∀ i : Bool,
        |(fderivWithin ℝ (fun q : ℝ × ℝ =>
          attenuatedVolterraIntegral B.j₁ B.k₁ q.1 q.2)
          (closedCoordTriangle a b) p)
            (if i then (1, 0) else (0, 1))| ≤
        B.jetCoefficient * (p.2 - p.1) ^ 2 := by
      intro i
      cases i
      · have h := abs_fderivWithin_attenuatedVolterraIntegral_vertical_le
          B.hab hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one B.j₁_c1 B.k₁_c1
          hS₀ hT₀ hsource₁ hkernel₁
        have hcoeff : B.S₀ + B.T₀ * (B.S₀ / 3) ≤ B.jetCoefficient := by
          dsimp [AttenuatedVolterraPairData.jetCoefficient]
          have : 0 ≤ B.S₁ + B.S₀ * B.T₁ := by positivity
          linarith
        exact h.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
      · have h := abs_fderivWithin_attenuatedVolterraIntegral_horizontal_le
          B.hab hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one B.j₁_c1 B.k₁_c1
          B.j_diag.1 hS₀ hS₁ hT₁ hsource₁
          (fun q hq => (hkernel₁ q hq).1) hsourceJet₁ hkernelJet₁
        have hcoeff : (B.S₁ + B.S₀ * B.T₁) / 2 ≤ B.jetCoefficient := by
          dsimp [AttenuatedVolterraPairData.jetCoefficient]
          have : 0 ≤ B.T₀ * (B.S₀ / 3) := by positivity
          linarith
        change |(fderivWithin ℝ (fun q : ℝ × ℝ =>
          attenuatedVolterraIntegral B.j₁ B.k₁ q.1 q.2)
          (closedCoordTriangle a b) p) (1, 0)| ≤
            B.jetCoefficient * (p.2 - p.1) ^ 2
        calc
          _ ≤ ((B.S₁ + B.S₀ * B.T₁) / 2) * (p.2 - p.1) ^ 2 := by
            convert h using 1; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    have h₂ : ∀ i : Bool,
        |(fderivWithin ℝ (fun q : ℝ × ℝ =>
          attenuatedVolterraIntegral B.j₂ B.k₂ q.1 q.2)
          (closedCoordTriangle a b) p)
            (if i then (1, 0) else (0, 1))| ≤
        B.jetCoefficient * (p.2 - p.1) ^ 2 := by
      intro i
      cases i
      · have h := abs_fderivWithin_attenuatedVolterraIntegral_vertical_le
          B.hab hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one B.j₂_c1 B.k₂_c1
          hS₀ hT₀ hsource₂ hkernel₂
        have hcoeff : B.S₀ + B.T₀ * (B.S₀ / 3) ≤ B.jetCoefficient := by
          dsimp [AttenuatedVolterraPairData.jetCoefficient]
          have : 0 ≤ B.S₁ + B.S₀ * B.T₁ := by positivity
          linarith
        exact h.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
      · have h := abs_fderivWithin_attenuatedVolterraIntegral_horizontal_le
          B.hab hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one B.j₂_c1 B.k₂_c1
          B.j_diag.2 hS₀ hS₁ hT₁ hsource₂
          (fun q hq => (hkernel₂ q hq).1)
          (fun q hq => (B.source_jet_bound q hq).2)
          (fun q hq => (B.kernel_jet_bound q hq).2)
        have hcoeff : (B.S₁ + B.S₀ * B.T₁) / 2 ≤ B.jetCoefficient := by
          dsimp [AttenuatedVolterraPairData.jetCoefficient]
          have : 0 ≤ B.T₀ * (B.S₀ / 3) := by positivity
          linarith
        change |(fderivWithin ℝ (fun q : ℝ × ℝ =>
          attenuatedVolterraIntegral B.j₂ B.k₂ q.1 q.2)
          (closedCoordTriangle a b) p) (1, 0)| ≤
            B.jetCoefficient * (p.2 - p.1) ^ 2
        calc
          _ ≤ ((B.S₁ + B.S₀ * B.T₁) / 2) * (p.2 - p.1) ^ 2 := by
            convert h using 1; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    rcases he with rfl | rfl
    · rw [B.first_eq, B.second_eq]
      exact ⟨h₁ true, h₂ true⟩
    · rw [B.first_eq, B.second_eq]
      exact ⟨h₁ false, h₂ false⟩
  · intro p hp
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have h := abs_attenuatedVolterraIntegral_sub_le
      hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one
      B.j₁_c1.continuousOn B.j₂_c1.continuousOn
      B.k₁_c1.continuousOn B.k₂_c1.continuousOn
      (fun q hq => (hkernel₁ q hq).1)
      (fun q hq => (hkernel₂ q hq).1)
      hS₀ hTΔ₀ hD hsource₂ B.source_sub_bound B.kernel_sub_bound
    simpa only [B.first_eq, B.second_eq,
      AttenuatedVolterraPairData.valueSubCoefficient] using h
  · intro p hp e he
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    have hv := abs_fderivWithin_attenuatedVolterraIntegral_vertical_sub_le
      B.hab hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one
      B.j₁_c1 B.j₂_c1 B.k₁_c1 B.k₂_c1
      hS₀ hT₀ hSΔ₀ hTΔ₀ hD
      hsource₁ hsource₂ hkernel₁ hkernel₂
      B.source_sub_bound B.kernel_sub_bound
    have hu := abs_fderivWithin_attenuatedVolterraIntegral_horizontal_sub_le
      B.hab hcoord.1 hcoord.2.1 hcoord.2.2 B.width_le_one
      B.j₁_c1 B.j₂_c1 B.k₁_c1 B.k₂_c1 B.j_diag.1 B.j_diag.2
      hS₀ hS₁ hT₁ hSΔ₀ hSΔ₁ hTΔ₀ hTΔ₁ hD
      hsource₁ hsource₂ (fun q hq => (hkernel₁ q hq).1)
      (fun q hq => (hkernel₂ q hq).1)
      hsourceJet₁ hkernelJet₁ B.source_sub_bound B.kernel_sub_bound
      B.source_jet_sub_bound B.kernel_jet_sub_bound
    rcases he with rfl | rfl
    · simp only [B.first_eq, B.second_eq]
      have hcoeff :
          B.TΔ₀ * (B.S₁ + B.S₀ * B.T₁) / 4 +
            (B.SΔ₁ + B.SΔ₀ * B.T₁ + B.S₀ * B.TΔ₁) / 2 ≤
              B.jetSubCoefficient := by
        dsimp [AttenuatedVolterraPairData.jetSubCoefficient]
        have hnonneg : 0 ≤ B.SΔ₀ + B.TΔ₀ * (B.S₀ / 3) +
            B.T₀ * (B.SΔ₀ / 3 + B.S₀ * B.TΔ₀ / 6) := by positivity
        linarith
      calc
        _ ≤ (B.TΔ₀ * (B.S₁ + B.S₀ * B.T₁) / 4 +
            (B.SΔ₁ + B.SΔ₀ * B.T₁ + B.S₀ * B.TΔ₁) / 2) *
              (p.2 - p.1) ^ 2 * B.D := by
          simpa only [Prod.mk.eta] using hu
        _ ≤ B.jetSubCoefficient * (p.2 - p.1) ^ 2 * B.D := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)) hD
    · simp only [B.first_eq, B.second_eq]
      have hcoeff :
          B.SΔ₀ + B.TΔ₀ * (B.S₀ / 3) +
            B.T₀ * (B.SΔ₀ / 3 + B.S₀ * B.TΔ₀ / 6) ≤
              B.jetSubCoefficient := by
        dsimp [AttenuatedVolterraPairData.jetSubCoefficient]
        have hnonneg : 0 ≤ B.TΔ₀ * (B.S₁ + B.S₀ * B.T₁) / 4 +
            (B.SΔ₁ + B.SΔ₀ * B.T₁ + B.S₀ * B.TΔ₁) / 2 := by positivity
        linarith
      calc
        _ ≤ (B.SΔ₀ + B.TΔ₀ * (B.S₀ / 3) +
            B.T₀ * (B.SΔ₀ / 3 + B.S₀ * B.TΔ₀ / 6)) *
              (p.2 - p.1) ^ 2 * B.D := by
          simpa only [Prod.mk.eta] using hv
        _ ≤ B.jetSubCoefficient * (p.2 - p.1) ^ 2 * B.D := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)) hD

end intervalIntegral

end
