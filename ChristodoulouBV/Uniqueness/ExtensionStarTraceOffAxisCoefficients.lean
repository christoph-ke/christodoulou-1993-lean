module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointState

/-!
# Continuous terminal coefficients in equations (5.2) and (10)

Every denominator in the off-axis transport equations has a positive floor
on the closed rectangle. This permits the coefficient expressions to be
evaluated continuously at the terminal edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

variable {a vBar vStar : ℝ} {S : ℝ → Fields}

/-- Terminal mass ratio. -/
@[expose] noncomputable def OffAxisTerminalTraces.massRatio
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  2 * T.m p / T.r p

/-- Terminal positive mass gap. -/
@[expose] noncomputable def OffAxisTerminalTraces.massGap
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  1 - T.massRatio p

/-- Mixed coefficient `μ/((1-μ)r)`. -/
@[expose] noncomputable def OffAxisTerminalTraces.mixedCoefficient
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  T.massRatio p / (T.massGap p * T.r p)

/-- Algebraic outgoing derivative of the mixed coefficient, equation (8). -/
@[expose] noncomputable def OffAxisTerminalTraces.mixedCoefficientV
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  T.lam p * (T.theta p / T.lam p) ^ 2 /
      (T.massGap p * T.r p ^ 2) -
    T.massRatio p * T.lam p *
      (1 / T.massGap p ^ 2 + 1 / T.massGap p) / T.r p ^ 2

/-- Coefficient multiplying `α′` in equation (5.2). -/
@[expose] noncomputable def OffAxisTerminalTraces.alphaPrimeCoefficient
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  -2 * (T.nu p / T.r p) * (T.massRatio p / T.massGap p)

/-- Source term in equation (5.2). -/
@[expose] noncomputable def OffAxisTerminalTraces.alphaPrimeSource
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  3 * (T.nu p / T.r p ^ 2) *
      (T.massRatio p / T.massGap p) * (T.theta p / T.lam p) -
    (T.nu p / T.r p ^ 2) * (1 / T.massGap p) *
      (T.theta p / T.lam p) ^ 3

/-- Coefficient multiplying `λᵥ` in equation (10). -/
@[expose] noncomputable def OffAxisTerminalTraces.lambdaVCoefficient
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  T.nu p * T.mixedCoefficient p

/-- Source term in equation (10). -/
@[expose] noncomputable def OffAxisTerminalTraces.lambdaVSource
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) : ℝ :=
  T.nu p * T.lam p ^ 2 * T.mixedCoefficient p ^ 2 +
    T.nu p * T.lam p * T.mixedCoefficientV p

/-- All coefficients in the two incoming linear equations are continuous on
the closed terminal rectangle. -/
theorem OffAxisTerminalTraces.coefficients_continuousOn
    (T : OffAxisTerminalTraces a vBar vStar S) :
    ContinuousOn T.alphaPrimeCoefficient (Icc 0 a ×ˢ Icc vBar vStar) ∧
    ContinuousOn T.alphaPrimeSource (Icc 0 a ×ˢ Icc vBar vStar) ∧
    ContinuousOn T.lambdaVCoefficient (Icc 0 a ×ˢ Icc vBar vStar) ∧
    ContinuousOn T.lambdaVSource (Icc 0 a ×ˢ Icc vBar vStar) := by
  let K := Icc 0 a ×ˢ Icc vBar vStar
  have hr : ∀ p ∈ K, T.r p ≠ 0 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ne_of_gt (T.radius_pos.trans_le (T.floors u hu v hv).1)
  have hl : ∀ p ∈ K, T.lam p ≠ 0 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ne_of_gt (T.expansion_pos.trans_le (T.floors u hu v hv).2.1)
  have hμ : ContinuousOn T.massRatio K := by
    change ContinuousOn (fun p => 2 * T.m p / T.r p) K
    exact (continuousOn_const.mul T.m_cont).div T.r_cont hr
  have hq : ContinuousOn T.massGap K :=
    continuousOn_const.sub hμ
  have hqne : ∀ p ∈ K, T.massGap p ≠ 0 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ne_of_gt (T.gap_pos.trans_le (T.floors u hu v hv).2.2)
  have hmix : ContinuousOn T.mixedCoefficient K := by
    change ContinuousOn (fun p =>
      T.massRatio p / (T.massGap p * T.r p)) K
    exact hμ.div (hq.mul T.r_cont)
      (fun p hp => mul_ne_zero (hqne p hp) (hr p hp))
  have hrv2 : ∀ p ∈ K, T.r p ^ 2 ≠ 0 :=
    fun p hp => pow_ne_zero 2 (hr p hp)
  have hq2 : ∀ p ∈ K, T.massGap p ^ 2 ≠ 0 :=
    fun p hp => pow_ne_zero 2 (hqne p hp)
  have hratio : ContinuousOn (fun p => T.theta p / T.lam p) K :=
    T.theta_cont.div T.lam_cont hl
  have hqinv : ContinuousOn (fun p => 1 / T.massGap p) K :=
    continuousOn_const.div hq hqne
  have hqinv2 : ContinuousOn (fun p => 1 / T.massGap p ^ 2) K :=
    continuousOn_const.div (hq.pow 2) hq2
  have hrinv : ContinuousOn (fun p => T.nu p / T.r p) K :=
    T.nu_cont.div T.r_cont hr
  have hr2inv : ContinuousOn (fun p => T.nu p / T.r p ^ 2) K :=
    T.nu_cont.div (T.r_cont.pow 2) hrv2
  have hqratio : ContinuousOn
      (fun p => T.massRatio p / T.massGap p) K :=
    hμ.div hq hqne
  have hmixv : ContinuousOn T.mixedCoefficientV K := by
    change ContinuousOn (fun p =>
      T.lam p * (T.theta p / T.lam p) ^ 2 /
          (T.massGap p * T.r p ^ 2) -
        T.massRatio p * T.lam p *
          (1 / T.massGap p ^ 2 + 1 / T.massGap p) /
          T.r p ^ 2) K
    exact ((T.lam_cont.mul (hratio.pow 2)).div
      (hq.mul (T.r_cont.pow 2))
      (fun p hp => mul_ne_zero (hqne p hp) (hrv2 p hp))).sub
        (((hμ.mul T.lam_cont).mul (hqinv2.add hqinv)).div
          (T.r_cont.pow 2) hrv2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ContinuousOn (fun p =>
      -2 * (T.nu p / T.r p) *
        (T.massRatio p / T.massGap p)) K
    exact (continuousOn_const.mul hrinv).mul hqratio
  · change ContinuousOn (fun p =>
      3 * (T.nu p / T.r p ^ 2) *
          (T.massRatio p / T.massGap p) * (T.theta p / T.lam p) -
        (T.nu p / T.r p ^ 2) * (1 / T.massGap p) *
          (T.theta p / T.lam p) ^ 3) K
    exact (((continuousOn_const.mul hr2inv).mul hqratio).mul hratio).sub
      ((hr2inv.mul hqinv).mul (hratio.pow 3))
  · change ContinuousOn (fun p => T.nu p * T.mixedCoefficient p) K
    exact T.nu_cont.mul hmix
  · change ContinuousOn (fun p =>
      T.nu p * T.lam p ^ 2 * T.mixedCoefficient p ^ 2 +
        T.nu p * T.lam p * T.mixedCoefficientV p) K
    exact ((T.nu_cont.mul (T.lam_cont.pow 2)).mul (hmix.pow 2)).add
      ((T.nu_cont.mul T.lam_cont).mul hmixv)

/-- The closed-rectangle coefficients coincide with the finite-member
expressions wherever the old solution is defined. -/
theorem OffAxisTerminalTraces.coefficients_match_old
    (T : OffAxisTerminalTraces a vBar vStar S)
    {b u v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hu : u ∈ Icc 0 a) (hv : v ∈ Ico vBar b) :
    T.alphaPrimeCoefficient (u, v) =
      -2 * ((S b).nu u v / (S b).r u v) *
        ((2 * (S b).m u v / (S b).r u v) /
          (1 - 2 * (S b).m u v / (S b).r u v)) ∧
    T.alphaPrimeSource (u, v) =
      3 * ((S b).nu u v / (S b).r u v ^ 2) *
          ((2 * (S b).m u v / (S b).r u v) /
            (1 - 2 * (S b).m u v / (S b).r u v)) *
          ((S b).theta u v / (S b).lam u v) -
        ((S b).nu u v / (S b).r u v ^ 2) *
          (1 / (1 - 2 * (S b).m u v / (S b).r u v)) *
          ((S b).theta u v / (S b).lam u v) ^ 3 ∧
    T.lambdaVCoefficient (u, v) =
      (S b).nu u v *
        ((2 * (S b).m u v / (S b).r u v) /
          ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v)) ∧
    T.lambdaVSource (u, v) =
      (S b).nu u v * (S b).lam u v ^ 2 *
        ((2 * (S b).m u v / (S b).r u v) /
          ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v)) ^ 2 +
      (S b).nu u v * (S b).lam u v *
        ((S b).lam u v * ((S b).theta u v / (S b).lam u v) ^ 2 /
            ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v ^ 2) -
          (2 * (S b).m u v / (S b).r u v) * (S b).lam u v *
            (1 / (1 - 2 * (S b).m u v / (S b).r u v) ^ 2 +
              1 / (1 - 2 * (S b).m u v / (S b).r u v)) /
            (S b).r u v ^ 2) := by
  obtain ⟨hr, hm, hl, hn, _, _, _, hθ, _⟩ := T.match_old b hb u hu v hv
  simp only [OffAxisTerminalTraces.alphaPrimeCoefficient,
    OffAxisTerminalTraces.alphaPrimeSource,
    OffAxisTerminalTraces.lambdaVCoefficient,
    OffAxisTerminalTraces.lambdaVSource,
    OffAxisTerminalTraces.mixedCoefficient,
    OffAxisTerminalTraces.mixedCoefficientV,
    OffAxisTerminalTraces.massRatio,
    OffAxisTerminalTraces.massGap,
    hr, hm, hl, hn, hθ]
  exact ⟨trivial, trivial, trivial, trivial⟩

end ChristodoulouBV.Uniqueness

end
