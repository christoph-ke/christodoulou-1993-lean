module

public import ChristodoulouBV.Existence.SmoothBoundsCore
import Mathlib.Tactic

/-!+# Uniform amplitudes and the scalar offset

The centered amplitudes and the mass integrands have universal coefficients.
The original scalar amplitudes retain the supremum of the centering offsets.
Its finiteness follows from pointwise data convergence at `v = 1` and the
centered estimate, without any normalization of the original BV datum.
-/

public section

open Set Filter
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- The common scalar offset of a sequence of smooth solutions. Its
finiteness as a real supremum is justified by `smooth_amplitude_bounds`. -/
@[expose] noncomputable def smoothScalarOffset (T : ℕ → Fields) : ℝ :=
  sSup (range (fun n => |(T n).phi 0 0|))

/-- Pointwise amplitudes for one smooth solution. `D` controls the centered
and invariant fields; `C` is only the offset of the original scalar. -/
structure SmoothAmplitudes (D : ℝ≥0∞) (C : ℝ) (S : Fields) : Prop where
  /-- Universal positive lower and upper bounds for the outgoing expansion. -/
  lam : ∀ p ∈ globalDomain, (1 / 3 : ℝ) ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 / 2
  /-- Universal amplitude and strict negative sign of the incoming expansion. -/
  nu : ∀ p ∈ globalDomain, -(2 / 3 : ℝ) ≤ S.nu p.1 p.2 ∧ S.nu p.1 p.2 ≤ -(1 / 3)
  /-- Centered outgoing scalar-radius derivative. -/
  centered_alpha : ∀ p ∈ globalDomain,
    |(smoothCenteredFields S).alpha p.1 p.2| ≤ 2 * D.toReal
  /-- Centered incoming scalar-radius derivative. -/
  centered_beta : ∀ p ∈ globalDomain,
    |(smoothCenteredFields S).beta p.1 p.2| ≤ 4 * D.toReal
  /-- Centered scalar field. -/
  centered_phi : ∀ p ∈ globalDomain,
    |(smoothCenteredFields S).phi p.1 p.2| ≤ 6 * D.toReal
  /-- Original outgoing derivative, with its scalar offset retained. -/
  alpha : ∀ p ∈ globalDomain, |S.alpha p.1 p.2| ≤ 2 * D.toReal + C / 2
  /-- Original incoming derivative, with its scalar offset retained. -/
  beta : ∀ p ∈ globalDomain, |S.beta p.1 p.2| ≤ 4 * D.toReal + 2 * C / 3
  /-- Original scalar, with its offset retained. -/
  phi : ∀ p ∈ globalDomain, |S.phi p.1 p.2| ≤ 6 * D.toReal + C
  /-- Shift-invariant outgoing scalar amplitude. -/
  theta : ∀ p ∈ globalDomain, |S.theta p.1 p.2| ≤ 5 * D.toReal
  /-- Shift-invariant incoming scalar amplitude. -/
  zeta : ∀ p ∈ globalDomain, |S.zeta p.1 p.2| ≤ 8 * D.toReal
  /-- The outgoing mass primitive has a common integrand majorant. -/
  mass_out : ∀ p ∈ globalDomain,
    |(1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.theta p.1 p.2 ^ 2 /
      (2 * S.lam p.1 p.2)| ≤ 100 * D.toReal ^ 2
  /-- The incoming mass primitive has a common integrand majorant. -/
  mass_in : ∀ p ∈ globalDomain,
    |(1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.zeta p.1 p.2 ^ 2 /
      (2 * S.nu p.1 p.2)| ≤ 100 * D.toReal ^ 2

private theorem mass_integrand_bound {q t l d : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : |t| ≤ 8 * d)
    (hl : (1 / 3 : ℝ) ≤ |l|) (_hd : 0 ≤ d) :
    |q * t ^ 2 / (2 * l)| ≤ 100 * d ^ 2 := by
  rw [abs_div, abs_mul, abs_of_nonneg hq, abs_of_nonneg (sq_nonneg t),
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by linarith only [hl] : 0 < 2 * |l|)).mpr
  have ht2 : t ^ 2 ≤ 64 * d ^ 2 := by
    have ht' := (abs_le.mp ht)
    nlinarith only [ht'.1, ht'.2, sq_nonneg (8 * d - t), sq_nonneg (8 * d + t)]
  calc
    q * t ^ 2 ≤ 1 * t ^ 2 := mul_le_mul_of_nonneg_right hq1 (sq_nonneg t)
    _ ≤ 64 * d ^ 2 := by simpa only [one_mul] using ht2
    _ ≤ 100 * d ^ 2 * (2 * |l|) := by nlinarith only [hl, sq_nonneg d]

/-- Uniform original and centered amplitudes for any sequence of global
smooth solutions with the smooth approximating data. The offset is the actual supremum over
all members; it depends on the fixed datum and approximation sequence.
Every other coefficient is universal. -/
theorem smooth_amplitude_bounds
    {alpha₀ : ℝ → ℝ} {alphaₙ : ℕ → ℝ → ℝ} {T : ℕ → Fields}
    (hfinite : ∀ n b, 0 < b → IsC1Solution (developmentWithInitialEdge b) (T n))
    (hdata : ∀ n v, 0 < v → (T n).r 0 v = v / 2 ∧ (T n).alpha 0 v = alphaₙ n v)
    (hsmall : ∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    (hvar : ∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤ eVariationOn alpha₀ (Ioi 0))
    (hpoint : Tendsto (fun n => alphaₙ n 1) atTop (𝓝 (alpha₀ 1))) :
    0 ≤ smoothScalarOffset T ∧
      (∀ n, |(T n).phi 0 0| ≤ smoothScalarOffset T) ∧
      ∀ n, SmoothAmplitudes (eVariationOn alpha₀ (Ioi (0 : ℝ))) (smoothScalarOffset T) (T n) := by
  let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
  have hreal (n : ℕ) : (eVariationOn (alphaₙ n) (Ioi 0)).toReal ≤ D.toReal :=
    ENNReal.toReal_mono (ne_of_lt (hD.trans_le le_top)) (hvar n)
  have hcenter (n : ℕ) (p : ℝ × ℝ) (hp : p ∈ globalDomain) :=
    smooth_centered_amplitude_bounds (hfinite n) (hdata n) (hsmall n) p hp
  have hgeom (n : ℕ) := global_c1_geometry (hfinite n) (hdata n) (hsmall n)
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto (fun n => alphaₙ n 1) hpoint).exists_norm_le
  have hM' (n : ℕ) : |alphaₙ n 1| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM _ (mem_range_self n)
  have hbound (n : ℕ) : |(T n).phi 0 0| ≤ 2 * (M + 2 * D.toReal) := by
    have hα := (hcenter n (0, 1) ⟨le_rfl, by norm_num⟩).1
    have hαD := hα.trans (mul_le_mul_of_nonneg_left (hreal n) (by norm_num))
    have hinit := initial_lam_eq_of_gauge (hfinite n 2 (by norm_num))
      (fun v hv => (hdata n v hv.1).1) (show (1 : ℝ) ∈ Ioo 0 2 by norm_num)
    have heq : (T n).phi 0 0 / 2 =
        alphaₙ n 1 - (smoothCenteredFields (T n)).alpha 0 1 := by
      simp only [smoothCenteredFields, scalarShift, hinit, (hdata n 1 (by norm_num)).2]
      ring
    have htri := abs_sub (alphaₙ n 1) ((smoothCenteredFields (T n)).alpha 0 1)
    rw [← heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
    linarith only [htri, hαD, hM' n]
  have hbdd : BddAbove (range (fun n => |(T n).phi 0 0|)) :=
    ⟨2 * (M + 2 * D.toReal), by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  have hC (n : ℕ) : |(T n).phi 0 0| ≤ smoothScalarOffset T :=
    le_csSup hbdd (mem_range_self n)
  have hC0 : 0 ≤ smoothScalarOffset T := (abs_nonneg _).trans (hC 0)
  refine ⟨hC0, hC, fun n => ?_⟩
  have hnreal := hreal n
  have hraw (p : ℝ × ℝ) (hp : p ∈ globalDomain) :
      |(T n).alpha p.1 p.2| ≤ 2 * D.toReal + smoothScalarOffset T / 2 ∧
      |(T n).beta p.1 p.2| ≤ 4 * D.toReal + 2 * smoothScalarOffset T / 3 ∧
      |(T n).phi p.1 p.2| ≤ 6 * D.toReal + smoothScalarOffset T := by
    obtain ⟨hα, hβ, hφ, _, _⟩ := hcenter n p hp
    obtain ⟨hl0, hl1, hn0, hn1, _, _⟩ := hgeom n p hp
    have hlabs : |(T n).lam p.1 p.2| ≤ 1 / 2 :=
      (abs_of_nonneg (by linarith only [hl0])).le.trans hl1
    have hnabs : |(T n).nu p.1 p.2| ≤ 2 / 3 := by
      rw [abs_of_nonpos (by linarith only [hn0])]
      exact hn1
    have hαr : |(T n).alpha p.1 p.2| ≤
        |(smoothCenteredFields (T n)).alpha p.1 p.2| +
          |(T n).phi 0 0| * |(T n).lam p.1 p.2| := by
      conv_lhs => rw [← smoothCenteredFields_restore (T n)]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul]; rfl)
    have hβr : |(T n).beta p.1 p.2| ≤
        |(smoothCenteredFields (T n)).beta p.1 p.2| +
          |(T n).phi 0 0| * |(T n).nu p.1 p.2| := by
      conv_lhs => rw [← smoothCenteredFields_restore (T n)]
      exact (abs_add_le _ _).trans_eq (by rw [abs_mul]; rfl)
    have hφr : |(T n).phi p.1 p.2| ≤
        |(smoothCenteredFields (T n)).phi p.1 p.2| + |(T n).phi 0 0| := by
      conv_lhs => rw [← smoothCenteredFields_restore (T n)]
      exact abs_add_le _ _
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ 2 * D.toReal + smoothScalarOffset T * (1 / 2) :=
          hαr.trans (add_le_add (hα.trans (by gcongr))
            (mul_le_mul (hC n) hlabs (abs_nonneg _) hC0))
        _ = _ := by ring
    · calc
        _ ≤ 4 * D.toReal + smoothScalarOffset T * (2 / 3) :=
          hβr.trans (add_le_add (hβ.trans (by gcongr))
            (mul_le_mul (hC n) hnabs (abs_nonneg _) hC0))
        _ = _ := by ring
    · exact hφr.trans (add_le_add (hφ.trans (by gcongr)) (hC n))
  refine ⟨fun p hp => ⟨(hgeom n p hp).1, (hgeom n p hp).2.1⟩,
    fun p hp => ⟨by linarith only [(hgeom n p hp).2.2.2.1],
      by linarith only [(hgeom n p hp).2.2.1]⟩,
    fun p hp => (hcenter n p hp).1.trans (by gcongr),
    fun p hp => (hcenter n p hp).2.1.trans (by gcongr),
    fun p hp => (hcenter n p hp).2.2.1.trans (by gcongr),
    fun p hp => (hraw p hp).1, fun p hp => (hraw p hp).2.1,
    fun p hp => (hraw p hp).2.2,
    fun p hp => (hcenter n p hp).2.2.2.1.trans (by gcongr),
    fun p hp => (hcenter n p hp).2.2.2.2.trans (by gcongr), ?_, ?_⟩
  · intro p hp
    obtain ⟨hl0, _, _, _, hq0, hq1⟩ := hgeom n p hp
    exact mass_integrand_bound (by linarith only [hq0]) hq1
      ((hcenter n p hp).2.2.2.1.trans (by
        have hd : 0 ≤ D.toReal := ENNReal.toReal_nonneg
        linarith only [hnreal, hd]))
      (hl0.trans (le_abs_self _)) ENNReal.toReal_nonneg
  · intro p hp
    obtain ⟨_, _, hn0, _, hq0, hq1⟩ := hgeom n p hp
    exact mass_integrand_bound (by linarith only [hq0]) hq1
      ((hcenter n p hp).2.2.2.2.trans (by gcongr))
      (hn0.trans (neg_le_abs _)) ENNReal.toReal_nonneg

end ChristodoulouBV

end
