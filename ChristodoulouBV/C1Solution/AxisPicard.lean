module

public import ChristodoulouBV.C1Solution.AxisPicardJetSpace
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxSourceQuotient
import Mathlib.Tactic

/-!
# The axis Picard iteration

The numerical ledger below records the constants for the local Picard
existence argument. The lifetime is chosen from their sum, so that each of the
coefficient, invariance, and contraction estimates has the required margin.
-/

public section

noncomputable section

namespace ChristodoulouBV.AxisPicard

/-- The nine coefficients used by the axis Picard invariance and contraction
estimates. Their nonnegativity is part of the numerical ledger. -/
structure Ledger where
  /-- Quadratic coefficient of the mass ratio. -/
  mu₀ : ℝ
  /-- Linear value coefficient of the gravitational term. -/
  K₀ : ℝ
  /-- First-jet coefficient of the gravitational term. -/
  K₁ : ℝ
  /-- Quadratic value coefficient of the scalar source. -/
  Q₀ : ℝ
  /-- Linear first-jet coefficient of the scalar source. -/
  Q₁ : ℝ
  /-- Linear difference coefficient of the gravitational term. -/
  KΔ₀ : ℝ
  /-- First-jet difference coefficient of the gravitational term. -/
  KΔ₁ : ℝ
  /-- Quadratic difference coefficient of the scalar source. -/
  QΔ₀ : ℝ
  /-- Linear first-jet difference coefficient of the scalar source. -/
  QΔ₁ : ℝ
  /-- All ledger coefficients are nonnegative. -/
  nonneg : 0 ≤ mu₀ ∧ 0 ≤ K₀ ∧ 0 ≤ K₁ ∧ 0 ≤ Q₀ ∧ 0 ≤ Q₁ ∧
    0 ≤ KΔ₀ ∧ 0 ≤ KΔ₁ ∧ 0 ≤ QΔ₀ ∧ 0 ≤ QΔ₁

/-- The exact `C_*` sum from the axis Picard estimate ledger. -/
@[expose] def Ledger.Cstar (B : Ledger) (M : ℝ) : ℝ :=
  1 + M + B.mu₀ + B.K₀ + B.K₁ + B.Q₀ + B.Q₁ +
    B.KΔ₀ + B.KΔ₁ + B.QΔ₀ + B.QΔ₁

/-- The lifetime prescribed by the exact ledger sum. -/
@[expose] def Ledger.lifetime (B : Ledger) (M : ℝ) : ℝ :=
  1 / (100 * B.Cstar M)

/-- The coefficient in the maximum of the three Picard output jet distances. -/
@[expose] def Ledger.contractCoefficient (B : Ledger) : ℝ :=
  3 * B.KΔ₀ + 2 * B.KΔ₁ + 2 * B.QΔ₀ + B.QΔ₁

/-- Every coefficient in the ledger is bounded by `C_*`, and the contraction
coefficient is bounded by `8 C_*`. -/
theorem Ledger.coefficients_le_Cstar (B : Ledger) {M : ℝ} (hM : 1 ≤ M) :
    1 ≤ B.Cstar M ∧ M ≤ B.Cstar M ∧
      B.mu₀ ≤ B.Cstar M ∧ B.K₀ ≤ B.Cstar M ∧
      B.K₁ ≤ B.Cstar M ∧ B.Q₀ ≤ B.Cstar M ∧
      B.Q₁ ≤ B.Cstar M ∧ B.KΔ₀ ≤ B.Cstar M ∧
      B.KΔ₁ ≤ B.Cstar M ∧ B.QΔ₀ ≤ B.Cstar M ∧
      B.QΔ₁ ≤ B.Cstar M ∧
      B.contractCoefficient ≤ 8 * B.Cstar M := by
  rcases B.nonneg with ⟨hmu, hK₀, hK₁, hQ₀, hQ₁, hKΔ₀, hKΔ₁, hQΔ₀, hQΔ₁⟩
  dsimp only [Ledger.Cstar, Ledger.contractCoefficient]
  repeat' constructor
  all_goals nlinarith

/-- The explicit lifetime is positive, at most one, and makes every ledger
coefficient times `T` at most `1/100`. The mass-ratio and contraction margins
are included in the same statement. -/
theorem Ledger.lifetime_bounds (B : Ledger) {M T : ℝ}
    (hM : 1 ≤ M) (hT : 0 < T) (hsmall : T ≤ B.lifetime M) :
    T ≤ 1 ∧
      B.mu₀ * T ^ 2 ≤ 1 / 100 ∧
      2 * M * T ≤ 1 / 50 ∧
      B.K₀ * T ^ 2 ≤ 1 / 100 ∧
      B.K₁ * T ≤ 1 / 100 ∧
      B.Q₀ * T ^ 3 ≤ 1 / 100 ∧
      B.Q₁ * T ^ 2 ≤ 1 / 100 ∧
      B.contractCoefficient * T ≤ 2 / 25 := by
  have hC := B.coefficients_le_Cstar hM
  have hCpos : 0 < B.Cstar M := lt_of_lt_of_le (by norm_num) hC.1
  have hbound : B.Cstar M * T ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_left hsmall hCpos.le
    rw [Ledger.lifetime] at h
    convert h using 1
    field_simp
  have hTle : T ≤ 1 / 100 := by nlinarith [mul_le_mul_of_nonneg_right hC.1 hT.le]
  have hT1 : T ≤ 1 := by linarith
  rcases B.nonneg with ⟨hmu, hK₀, hK₁, hQ₀, hQ₁, hKΔ₀, hKΔ₁, hQΔ₀, hQΔ₁⟩
  have hT2 : T ^ 2 ≤ T := by nlinarith
  have hT3 : T ^ 3 ≤ T := by nlinarith
  have hmuT : B.mu₀ * T ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.1 hT.le).trans hbound
  have hMT : M * T ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.1 hT.le).trans hbound
  have hK₀T : B.K₀ * T ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.2.1 hT.le).trans hbound
  have hK₁T : B.K₁ * T ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.2.2.1 hT.le).trans hbound
  have hQ₀T : B.Q₀ * T ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.2.2.2.1 hT.le).trans hbound
  have hQ₁T : B.Q₁ * T ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.2.2.2.2.1 hT.le).trans hbound
  have hcontract : B.contractCoefficient * T ≤ 8 / 100 := by
    calc
      _ ≤ (8 * B.Cstar M) * T :=
        mul_le_mul_of_nonneg_right hC.2.2.2.2.2.2.2.2.2.2.2 hT.le
      _ ≤ 8 / 100 := by nlinarith only [hbound]
  constructor
  · exact hT1
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hT2 hmu]
  constructor
  · nlinarith only [hMT]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hT2 hK₀]
  constructor
  · exact hK₁T
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hT3 hQ₀]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hT2 hQ₁]
  · nlinarith only [hcontract]

/-- The explicit numerical ledger at `c=1/4`, `C=V=3/4`,
`L=B_h=2M`, `ε=3/4`, and width parameter one. Each stored coefficient is
its positive part, which remains a valid upper bound even outside `M ≥ 1`.
The two combined Volterra first-jet bounds are sums of their coordinate
bounds, as in the established box API. -/
@[expose] def numericalLedger (M : ℝ) : Ledger := by
  let c : ℝ := 1 / 4
  let C : ℝ := 3 / 4
  let V : ℝ := 3 / 4
  let L : ℝ := 2 * M
  let Bh : ℝ := L
  let ε : ℝ := 3 / 4
  let R₁ := C + L
  let RΔ : ℝ := 2
  let HΔ₀ := (Bh + C) / (2 * c) + C * Bh / (2 * c ^ 2)
  let H₁ := max (L + (C * Bh + L * Bh + C * L) / c) (Bh + C * Bh / c)
  let HΔ₁ := max
    (1 + (Bh + C * HΔ₀ + Bh + L * (1 + HΔ₀) + L + C) / c +
      (C * Bh + L * Bh + C * L) / c ^ 2)
    (1 + (Bh + C * HΔ₀) / c + C * Bh / c ^ 2)
  let j₀ := C * Bh ^ 2
  let j₁ := L * Bh ^ 2 + 2 * C * Bh * H₁
  let jΔ₀ := Bh ^ 2 + 2 * C * Bh * HΔ₀
  let jΔ₁ := Bh ^ 2 + 2 * L * Bh * HΔ₀ +
    2 * (Bh * H₁ + C * HΔ₀ * H₁ + C * Bh * HΔ₁)
  let k₀ := j₀ / c
  let k₁ := j₁ / c + j₀ * R₁ / c ^ 2
  let kΔ₀ := jΔ₀ / c + j₀ / c ^ 2
  let kΔ₁ := jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * R₁ / c ^ 2 +
    j₀ * RΔ / c ^ 2 + 2 * j₀ * R₁ / c ^ 3
  let J₀ := j₀ / 3
  let BJ := j₁ + j₀ * k₁
  let J₁ := BJ / 2 + j₀ + k₀ * J₀
  let JΔ₀ := jΔ₀ / 3 + j₀ * kΔ₀ / 6
  let JΔu := kΔ₀ * BJ / 4 +
    (jΔ₁ + jΔ₀ * k₁ + j₀ * kΔ₁) / 2
  let JΔv := jΔ₀ + kΔ₀ * J₀ + k₀ * JΔ₀
  let JΔ₁ := JΔu + JΔv
  let μ₀ := J₀ / c
  let μ₁ := J₁ / c + J₀ * R₁ / c ^ 2
  let μΔ₀ := JΔ₀ / c + J₀ / c ^ 2
  let μΔ₁ := JΔ₁ / c + J₁ / c ^ 2 + JΔ₀ * R₁ / c ^ 2 +
    J₀ * RΔ / c ^ 2 + 2 * J₀ * R₁ / c ^ 3
  let A₀ := J₀ / c ^ 2
  let A₁ := J₁ / c ^ 2 + 2 * J₀ * R₁ / c ^ 3
  let AΔ₀ := JΔ₀ / c ^ 2 + 2 * J₀ / c ^ 3
  let AΔ₁ := JΔ₁ / c ^ 2 + 2 * J₁ / c ^ 3 +
    2 * JΔ₀ * R₁ / c ^ 3 + 2 * J₀ * RΔ / c ^ 3 +
    6 * J₀ * R₁ / c ^ 4
  let W₀ := C * V
  let W₁ := L * (C + V)
  let WΔ₀ := C + V
  let WΔ₁ := C + V + 2 * L
  let Z₀ := ε⁻¹
  let Z₁ := μ₁ / ε ^ 2
  let ZΔ₀ := μΔ₀ / ε ^ 2
  let ZΔ₁ := μΔ₁ / ε ^ 2 + 2 * μ₁ * μΔ₀ / ε ^ 3
  let K₀ := A₀ * W₀ * Z₀
  let K₁ := A₁ * W₀ * Z₀ + A₀ * W₁ * Z₀ + A₀ * W₀ * Z₁
  let KΔ₀ := AΔ₀ * W₀ * Z₀ + A₀ * WΔ₀ * Z₀ + A₀ * W₀ * ZΔ₀
  let KΔ₁ := AΔ₁ * W₀ * Z₀ + A₁ * WΔ₀ * Z₀ + A₁ * W₀ * ZΔ₀ +
    AΔ₀ * W₁ * Z₀ + A₀ * WΔ₁ * Z₀ + A₀ * W₁ * ZΔ₀ +
    AΔ₀ * W₀ * Z₁ + A₀ * WΔ₀ * Z₁ + A₀ * W₀ * ZΔ₁
  let P₀ := K₀ * Bh
  let P₁ := K₁ * Bh + K₀ * H₁
  let PΔ₀ := KΔ₀ * Bh + K₀ * HΔ₀
  let PΔ₁ := KΔ₁ * Bh + K₁ * HΔ₀ + KΔ₀ * H₁ + K₀ * HΔ₁
  let Q₀ := P₀ / c
  let Q₁ := P₁ / c + P₀ * L / c ^ 2
  let QΔ₀ := PΔ₀ / c + P₀ / c ^ 2
  let QΔ₁ := PΔ₁ / c + P₁ / c ^ 2 + PΔ₀ * L / c ^ 2 +
    P₀ / c ^ 2 + 2 * P₀ * L / c ^ 3
  exact {
    mu₀ := max 0 μ₀
    K₀ := max 0 K₀
    K₁ := max 0 K₁
    Q₀ := max 0 Q₀
    Q₁ := max 0 Q₁
    KΔ₀ := max 0 KΔ₀
    KΔ₁ := max 0 KΔ₁
    QΔ₀ := max 0 QΔ₀
    QΔ₁ := max 0 QΔ₁
    nonneg := ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _,
      le_max_left _ _, le_max_left _ _, le_max_left _ _,
      le_max_left _ _, le_max_left _ _, le_max_left _ _⟩ }

/-- The three fields iterated in the axis construction. -/
structure Triple where
  /-- Outgoing radius derivative. -/
  lam : ℝ × ℝ → ℝ
  /-- Incoming radius derivative. -/
  nu : ℝ × ℝ → ℝ
  /-- Normalized scalar field. -/
  h : ℝ × ℝ → ℝ

/-- A total representative of a scalar jet value, using zero outside its
closed triangle. All Picard integrals evaluate it inside the triangle. -/
@[expose] def ScalarJet.extendValue {a b : ℝ} (f : ScalarJet a b)
    (p : ℝ × ℝ) : ℝ := by
  classical
  exact if hp : p ∈ closedCoordTriangle a b then f.1.1 ⟨p, hp⟩ else 0

/-- On the closed triangle, the total representative is the jet value. -/
theorem ScalarJet.extendValue_eq {a b : ℝ} (f : ScalarJet a b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    f.extendValue p = f.1.1 ⟨p, hp⟩ := by
  simp [ScalarJet.extendValue, hp]

/-- The raw three-field representative of a complete triple jet. -/
@[expose] def TripleJet.toTriple {a b : ℝ} (x : TripleJet a b) : Triple :=
  { lam := x.1.extendValue
    nu := x.2.1.extendValue
    h := x.2.2.extendValue }

/-- The radius obtained by integrating the outgoing derivative from the axis. -/
@[expose] def Triple.radius (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalRadius x.lam p

/-- The weighted diagonal scalar error. -/
@[expose] def Triple.meanError (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalError x.lam x.h p

/-- The quadratic source for the attenuated mass integral. -/
@[expose] def Triple.massSource (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalQuadraticKernel x.lam x.h p

/-- The linear attenuation kernel for the mass integral. -/
@[expose] def Triple.attenuation (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalQuotientKernel x.lam x.h p

/-- Twice the axis-normalized mass, given by its attenuated Volterra formula. -/
@[expose] def Triple.massNumerator (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.attenuatedVolterraIntegral x.massSource x.attenuation p.1 p.2

/-- The removable gravitational coefficient in the axis Picard equations. -/
@[expose] def Triple.gravitational (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.rationalCubicCoefficient x.massNumerator x.radius x.lam x.nu p

/-- The scalar source `-K_g H / λ` with its removable axis value. -/
@[expose] def Triple.scalarSource (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.rationalCubicSource x.massNumerator x.radius x.lam x.nu
    x.meanError p

/-- The removable gravitational coefficient vanishes on the axis. -/
@[simp] theorem Triple.gravitational_diag (x : Triple) (u : ℝ) :
    x.gravitational (u, u) = 0 := by
  simp [Triple.gravitational, intervalIntegral.rationalCubicCoefficient,
    intervalIntegral.cubicSquaredQuotient]

/-- The scalar source vanishes on the axis. -/
@[simp] theorem Triple.scalarSource_diag (x : Triple) (u : ℝ) :
    x.scalarSource (u, u) = 0 := by
  simp [Triple.scalarSource, intervalIntegral.rationalCubicSource]

/-- The axis Picard update from prescribed outgoing edge data `g` and `hEdge`.
The incoming diagonal trace is taken from the newly updated `λ`. -/
@[expose] def Triple.picard (x : Triple) (a : ℝ) (g hEdge : ℝ → ℝ) : Triple :=
  let lamNew : ℝ × ℝ → ℝ := fun p =>
    g p.2 + ∫ s in a..p.1, x.gravitational (s, p.2)
  { lam := lamNew
    nu := fun p => -lamNew (p.1, p.1) +
      ∫ s in p.1..p.2, x.gravitational (p.1, s)
    h := fun p => hEdge p.2 + ∫ s in a..p.1, x.scalarSource (s, p.2) }

/-- The Picard update has the prescribed outgoing `λ` trace. -/
theorem Triple.picard_lam_edge (x : Triple) (a v : ℝ) (g hEdge : ℝ → ℝ) :
    (x.picard a g hEdge).lam (a, v) = g v := by
  simp [Triple.picard]

/-- The Picard update has the prescribed outgoing scalar trace. -/
theorem Triple.picard_h_edge (x : Triple) (a v : ℝ) (g hEdge : ℝ → ℝ) :
    (x.picard a g hEdge).h (a, v) = hEdge v := by
  simp [Triple.picard]

/-- The incoming trace of the Picard update is regular on the axis. -/
theorem Triple.picard_nu_diag (x : Triple) (a u : ℝ) (g hEdge : ℝ → ℝ) :
    (x.picard a g hEdge).nu (u, u) =
      -(x.picard a g hEdge).lam (u, u) := by
  simp [Triple.picard]

/-- At the corner, the incoming derivative is fixed by the outgoing edge. -/
theorem Triple.picard_nu_corner (x : Triple) (a : ℝ) (g hEdge : ℝ → ℝ) :
    (x.picard a g hEdge).nu (a, a) = -g a := by
  rw [x.picard_nu_diag, x.picard_lam_edge]

/-- The numerical lifetime is positive for every `M ≥ 1`. -/
theorem numerical_lifetime_pos {M : ℝ} (hM : 1 ≤ M) :
    0 < (numericalLedger M).lifetime M := by
  have hC : 0 < (numericalLedger M).Cstar M :=
    lt_of_lt_of_le (by norm_num) ((numericalLedger M).coefficients_le_Cstar hM).1
  unfold Ledger.lifetime
  positivity

/-- The explicit numerical lifetime gives the mass-ratio margin and a
contraction factor at most `2/25`. -/
theorem numerical_lifetime_bounds {M T : ℝ} (hM : 1 ≤ M)
    (hT : 0 < T) (hsmall : T ≤ (numericalLedger M).lifetime M) :
    T ≤ 1 ∧ (numericalLedger M).mu₀ * T ^ 2 ≤ 1 / 100 ∧
      2 * M * T ≤ 1 / 50 ∧
      (numericalLedger M).contractCoefficient * T ≤ 2 / 25 := by
  have h := (numericalLedger M).lifetime_bounds hM hT hsmall
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.2⟩

/-- The diagonal sign and the input vertical variation bound force the
incoming derivative away from zero. This is the input-box sign calculation. -/
theorem input_nu_le_neg_quarter {M T lamDiag nu : ℝ}
    (hM : 1 ≤ M) (hT : 0 < T)
    (hsmall : T ≤ (numericalLedger M).lifetime M)
    (hlam : 3 / 8 ≤ lamDiag)
    (hvariation : nu + lamDiag ≤ 2 * M * T) :
    nu ≤ -(1 / 4 : ℝ) := by
  have hbound := (numerical_lifetime_bounds hM hT hsmall).2.2.1
  linarith

/-- The Picard value estimate gives the same strict sign margin for the
updated incoming derivative. -/
theorem output_nu_le_neg_quarter {M T gDiag nu : ℝ}
    (hM : 1 ≤ M) (hT : 0 < T)
    (hsmall : T ≤ (numericalLedger M).lifetime M)
    (hg : 3 / 8 ≤ gDiag)
    (hvariation : nu + gDiag ≤
      2 * (numericalLedger M).K₀ * T ^ 2) :
    nu ≤ -(1 / 4 : ℝ) := by
  have hbound := ((numericalLedger M).lifetime_bounds hM hT hsmall).2.2.2.1
  linarith

end ChristodoulouBV.AxisPicard

end
