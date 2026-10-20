module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisCoefficients
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Coefficients for the transverse incoming jets

The differentiated outgoing equation for `νᵤ` is linear. Its source is
written without a terminal division by `ν`, which is useful when closing
the compact base jets.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

variable {a vBar vStar : ℝ} {S : ℝ → Fields}

/-- The positive characteristic ratio `κ = λ/(1-μ)` on the terminal
off-axis rectangle. -/
@[expose] noncomputable def OffAxisTerminalTraces.kappa
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  T.lam p / T.massGap p

/-- The coefficient `A = 2mκ/r²` in `νᵥ = Aν`. -/
@[expose] noncomputable def OffAxisTerminalTraces.nuTransportCoefficient
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  2 * T.m p * T.kappa p / T.r p ^ 2

/-- The inhomogeneous term in the outgoing equation for `νᵤ`:
`Aᵤ ν = κ ζ²/r² - 4mκν²/r³`. -/
@[expose] noncomputable def OffAxisTerminalTraces.nuTransportSource
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  T.kappa p * T.zeta p ^ 2 / T.r p ^ 2 -
    4 * T.m p * T.kappa p * T.nu p ^ 2 / T.r p ^ 3

/-- The linear coefficient is the coefficient in the established mixed equation. -/
theorem OffAxisTerminalTraces.nuTransportCoefficient_eq
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) :
    T.nuTransportCoefficient p = T.lam p * T.mixedCoefficient p := by
  simp only [OffAxisTerminalTraces.nuTransportCoefficient,
    OffAxisTerminalTraces.kappa, OffAxisTerminalTraces.mixedCoefficient,
    OffAxisTerminalTraces.massRatio]
  ring

/-- Substituting the incoming mass and `κ` equations into the product
rule for `A = 2mκ/r²` removes the apparent division by `ν` from
`Aᵤν`. -/
theorem nu_transport_source_algebra
    (m κ r ν ζ : ℝ) (hr : r ≠ 0) (hν : ν ≠ 0) :
    ν * (2 * ((1 - 2 * m / r) * ζ ^ 2 / (2 * ν)) * κ / r ^ 2 +
        2 * m * (κ * ζ ^ 2 / (r * ν)) / r ^ 2 -
        4 * m * κ * ν / r ^ 3) =
      κ * ζ ^ 2 / r ^ 2 - 4 * m * κ * ν ^ 2 / r ^ 3 := by
  field_simp [hr, hν]
  ring

/-- Differentiating `K = 2mκν/r²` along an incoming slice gives the
linear coefficient for `νᵤ` and the source with no terminal `ν`
denominator. The hypotheses are precisely the four first-order equations
used by the calculation. -/
theorem grav_hasDerivAt_of_incoming_equations
    {r m κ ν : ℝ → ℝ} {u ζ P : ℝ}
    (hr : HasDerivAt r (ν u) u)
    (hm : HasDerivAt m
      ((1 - 2 * m u / r u) * ζ ^ 2 / (2 * ν u)) u)
    (hκ : HasDerivAt κ (κ u * ζ ^ 2 / (r u * ν u)) u)
    (hν : HasDerivAt ν P u)
    (hr0 : r u ≠ 0) (hν0 : ν u ≠ 0) :
    HasDerivAt (fun t => 2 * m t * κ t * ν t / r t ^ 2)
      ((2 * m u * κ u / r u ^ 2) * P +
        (κ u * ζ ^ 2 / r u ^ 2 -
          4 * m u * κ u * ν u ^ 2 / r u ^ 3)) u := by
  have h :=
    (((hm.const_mul 2).mul hκ).mul hν).div
      (hr.pow 2) (pow_ne_zero 2 hr0)
  convert h using 1
  dsimp
  field_simp [hr0, hν0]
  ring

/-- The transport coefficient and source have joint continuous terminal
traces, using only the positive radius and mass-gap floors. -/
theorem OffAxisTerminalTraces.nu_transport_coefficients_continuousOn
    (T : OffAxisTerminalTraces a vBar vStar S) :
    ContinuousOn T.nuTransportCoefficient
      (Icc 0 a ×ˢ Icc vBar vStar) ∧
    ContinuousOn T.nuTransportSource
      (Icc 0 a ×ˢ Icc vBar vStar) := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  have hr : ∀ p ∈ K, T.r p ≠ 0 := by
    intro p hp
    exact ne_of_gt (T.radius_pos.trans_le
      (T.floors p.1 hp.1 p.2 hp.2).1)
  have hgap : ContinuousOn T.massGap K :=
    continuousOn_const.sub
      ((continuousOn_const.mul T.m_cont).div T.r_cont hr)
  have hgapne : ∀ p ∈ K, T.massGap p ≠ 0 := by
    intro p hp
    exact ne_of_gt (T.gap_pos.trans_le
      (T.floors p.1 hp.1 p.2 hp.2).2.2)
  have hκ : ContinuousOn T.kappa K :=
    T.lam_cont.div hgap hgapne
  have hr2 : ∀ p ∈ K, T.r p ^ 2 ≠ 0 :=
    fun p hp => pow_ne_zero 2 (hr p hp)
  have hr3 : ∀ p ∈ K, T.r p ^ 3 ≠ 0 :=
    fun p hp => pow_ne_zero 3 (hr p hp)
  constructor
  · change ContinuousOn (fun p =>
      2 * T.m p * T.kappa p / T.r p ^ 2) K
    exact ((continuousOn_const.mul T.m_cont).mul hκ).div
      (T.r_cont.pow 2) hr2
  · change ContinuousOn (fun p =>
      T.kappa p * T.zeta p ^ 2 / T.r p ^ 2 -
        4 * T.m p * T.kappa p * T.nu p ^ 2 / T.r p ^ 3) K
    exact ((hκ.mul (T.zeta_cont.pow 2)).div (T.r_cont.pow 2) hr2).sub
      ((((continuousOn_const.mul T.m_cont).mul hκ).mul
        (T.nu_cont.pow 2)).div (T.r_cont.pow 3) hr3)

/-- The closed transport coefficients agree with the equations of each
finite old member wherever that member meets the terminal rectangle. -/
theorem OffAxisTerminalTraces.nu_transport_coefficients_match_old
    (T : OffAxisTerminalTraces a vBar vStar S)
    {b u v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hu : u ∈ Icc 0 a) (hv : v ∈ Ico vBar b) :
    T.kappa (u, v) =
        (S b).lam u v /
          (1 - 2 * (S b).m u v / (S b).r u v) ∧
    T.nuTransportCoefficient (u, v) =
        2 * (S b).m u v *
          ((S b).lam u v /
            (1 - 2 * (S b).m u v / (S b).r u v)) /
          (S b).r u v ^ 2 ∧
    T.nuTransportSource (u, v) =
        ((S b).lam u v /
          (1 - 2 * (S b).m u v / (S b).r u v)) *
            (S b).zeta u v ^ 2 / (S b).r u v ^ 2 -
          4 * (S b).m u v *
            ((S b).lam u v /
              (1 - 2 * (S b).m u v / (S b).r u v)) *
            (S b).nu u v ^ 2 / (S b).r u v ^ 3 := by
  obtain ⟨hr, hm, hl, hn, _, hz, _, _, _⟩ :=
    T.match_old b hb u hu v hv
  simp only [OffAxisTerminalTraces.kappa,
    OffAxisTerminalTraces.nuTransportCoefficient,
    OffAxisTerminalTraces.nuTransportSource,
    OffAxisTerminalTraces.massGap, OffAxisTerminalTraces.massRatio,
    hr, hm, hl, hn, hz]
  exact ⟨trivial, trivial, trivial⟩

end ChristodoulouBV.Uniqueness

end
