module

public import ChristodoulouBV.Existence.RadiusLimitHelly
import Mathlib.Tactic

/-!
# From rational sections to all sections

The mixed radius primitive gives a uniform transverse modulus on each
region separated from the axis. The same modulus, multiplied by the raw
scalar amplitude, controls both scalar-radius derivatives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- A sequence with uniform control to its right and convergent values at
rational points converges at the base point as well. -/
theorem exists_tendsto_of_rational_right_control
    {f : ℕ → ℝ → ℝ} {x δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hc : ∀ n y, y ∈ Icc x (x + δ) → |f n x - f n y| ≤ L * (y - x))
    (hq : ∀ q : ℚ, x < (q : ℝ) → (q : ℝ) < x + δ →
      ∃ l : ℝ, Tendsto (fun n => f n q) atTop (𝓝 l)) :
    ∃ l : ℝ, Tendsto (fun n => f n x) atTop (𝓝 l) := by
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let d := min δ (ε / (3 * (L + 1)))
  have hd : 0 < d := lt_min hδ (div_pos hε (by positivity))
  obtain ⟨q, hxq, hqd⟩ := exists_rat_btwn (lt_add_of_pos_right x hd)
  have hqδ : (q : ℝ) < x + δ := hqd.trans_le (add_le_add_right (min_le_left _ _) x)
  obtain ⟨l, hl⟩ := hq q hxq hqδ
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 3) (by positivity)
  have hsmall : L * ((q : ℝ) - x) < ε / 3 := by
    have he : (q : ℝ) - x < ε / (3 * (L + 1)) := by
      have hd' := min_le_right δ (ε / (3 * (L + 1)))
      dsimp [d] at hqd
      linarith only [hqd, hd']
    have he' := (lt_div_iff₀ (by positivity : 0 < 3 * (L + 1))).mp he
    have hpos : 0 < (q : ℝ) - x := sub_pos.mpr hxq
    nlinarith only [he', hpos]
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmn := hN m hm n hn
  have hm' := (hc m q ⟨hxq.le, hqδ.le⟩).trans_lt hsmall
  have hn' := (hc n q ⟨hxq.le, hqδ.le⟩).trans_lt hsmall
  have htriangle : |f m x - f n x| ≤
      |f m x - f m q| + |f m q - f n q| + |f n q - f n x| := by
    calc
      _ ≤ |f m x - f m q| + |f m q - f n x| := abs_sub_le _ _ _
      _ ≤ |f m x - f m q| + (|f m q - f n q| + |f n q - f n x|) :=
        add_le_add_right (abs_sub_le _ _ _) _
      _ = _ := (add_assoc _ _ _).symm
  rw [Real.dist_eq] at hmn ⊢
  rw [abs_sub_comm (f n q) (f n x)] at htriangle
  linarith only [htriangle, hmn, hm', hn']

/-- A universal bound for the mixed radius density away from the axis. -/
theorem SmoothSolutionBounds.mixed_radius_bound
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {p : ℝ × ℝ} (hp : p ∈ globalDomain)
    {d : ℝ} (hd : 0 < d) (hgap : d ≤ p.2 - p.1) :
    |(2 * S.m p.1 p.2 / S.r p.1 p.2) * S.lam p.1 p.2 * S.nu p.1 p.2 /
      ((1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2)| ≤ 9 / d := by
  let μ := 2 * S.m p.1 p.2 / S.r p.1 p.2
  obtain ⟨hl0, hl1, hn0, hn1, hq0, hq1⟩ := h.geometry p hp
  have hμ0 : 0 ≤ μ := by dsimp [μ]; linarith only [hq1]
  have hμ1 : μ ≤ 1 / 3 := by dsimp [μ]; linarith only [hq0]
  have hr : d / 3 ≤ S.r p.1 p.2 := (div_le_div_of_nonneg_right hgap (by norm_num)).trans
    (h.radius_lower hp)
  have hr0 : 0 < S.r p.1 p.2 := (h.solution.solution.radius_pos p hp)
  have hnum : |μ * S.lam p.1 p.2 * S.nu p.1 p.2| ≤ (1 : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hμ0,
      abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) hl0),
      abs_of_nonpos (by linarith only [hn0])]
    calc
      μ * S.lam p.1 p.2 * -S.nu p.1 p.2 ≤ (1 / 3 : ℝ) * (1 / 2) * (2 / 3) :=
        mul_le_mul (mul_le_mul hμ1 hl1 (by linarith only [hl0]) (by norm_num)) hn1
          (by linarith only [hn0]) (by norm_num)
      _ ≤ 1 := by norm_num
  have hden : d / 9 ≤ |(1 - μ) * S.r p.1 p.2| := by
    rw [abs_of_pos (mul_pos (by dsimp [μ]; linarith only [hq0]) hr0)]
    have hh := mul_le_mul hq0 hr (by positivity : (0 : ℝ) ≤ d / 3)
      (by dsimp [μ]; linarith only [hq0] : 0 ≤ 1 - μ)
    change (2 / 3 : ℝ) * (d / 3) ≤ (1 - μ) * S.r p.1 p.2 at hh
    linarith only [hh, hd]
  change |μ * S.lam p.1 p.2 * S.nu p.1 p.2 / ((1 - μ) * S.r p.1 p.2)| ≤ _
  rw [abs_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by positivity : 0 < d / 9) hden)).mpr
  calc
    _ ≤ 1 := hnum
    _ = (9 / d) * (d / 9) := by field_simp
    _ ≤ (9 / d) * |(1 - μ) * S.r p.1 p.2| :=
      mul_le_mul_of_nonneg_left hden (div_nonneg (by norm_num) hd.le)

/-- Uniform transverse bounds for λ and α on incoming short segments. -/
theorem SmoothSolutionBounds.outgoing_fields_right_control
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {u v : ℝ} (hp : (u, v) ∈ globalDomain)
    {s : ℝ} (hs : s ∈ Icc u (u + (v - u) / 2)) :
    |S.lam u v - S.lam s v| ≤ (18 / (v - u)) * (s - u) ∧
    |S.alpha u v - S.alpha s v| ≤
      ((18 / (v - u)) * (6 * D.toReal + C)) * (s - u) := by
  have hd : 0 < (v - u) / 2 := half_pos (sub_pos.mpr hp.2)
  have hsU : inSeg v u s ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨hx, rfl⟩
    exact ⟨hp.1.trans hx.1, by linarith only [hx.2, hs.2, hp.2]⟩
  have hb (t : ℝ) (ht : t ∈ Icc u s) :
      |(2 * S.m t v / S.r t v) * S.lam t v * S.nu t v /
        ((1 - 2 * S.m t v / S.r t v) * S.r t v)| ≤ 18 / (v - u) := by
    convert h.mixed_radius_bound (p := (t, v)) (hsU ⟨ht, rfl⟩) hd
      (by linarith only [ht.2, hs.2]) using 1
    field_simp [(sub_pos.mpr hp.2).ne']
    ring
  constructor
  · simpa only [abs_sub_comm] using
      (h.solution.solution.lam_in v u s hs.1 hsU).abs_sub_le hs.1 hb
  · have hscalar (t : ℝ) (ht : t ∈ Icc u s) := h.amplitudes.phi (t, v) (hsU ⟨ht, rfl⟩)
    simpa only [abs_sub_comm] using
      (h.solution.solution.alpha_in v u s hs.1 hsU).abs_sub_le hs.1
        (fun t ht => by
          rw [abs_mul]
          exact mul_le_mul (hb t ht) (hscalar t ht) (abs_nonneg _)
            (div_nonneg (by norm_num) (sub_pos.mpr hp.2).le))

/-- Uniform transverse bounds for ν and β on outgoing short segments. -/
theorem SmoothSolutionBounds.incoming_fields_right_control
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {u v : ℝ} (hp : (u, v) ∈ globalDomain)
    {s : ℝ} (hs : s ∈ Icc v (v + (v - u) / 2)) :
    |S.nu u v - S.nu u s| ≤ (18 / (v - u)) * (s - v) ∧
    |S.beta u v - S.beta u s| ≤
      ((18 / (v - u)) * (6 * D.toReal + C)) * (s - v) := by
  have hd : 0 < (v - u) / 2 := half_pos (sub_pos.mpr hp.2)
  have hsU : outSeg u v s ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨hp.1, hp.2.trans_le hy.1⟩
  have hb (t : ℝ) (ht : t ∈ Icc v s) :
      |(2 * S.m u t / S.r u t) * S.lam u t * S.nu u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)| ≤ 18 / (v - u) := by
    convert h.mixed_radius_bound (p := (u, t)) (hsU ⟨rfl, ht⟩) hd
      (by linarith only [ht.1, hp.2]) using 1
    field_simp [(sub_pos.mpr hp.2).ne']
    ring
  constructor
  · simpa only [abs_sub_comm] using
      (h.solution.solution.nu_out u v s hs.1 hsU).abs_sub_le hs.1 hb
  · have hscalar (t : ℝ) (ht : t ∈ Icc v s) := h.amplitudes.phi (u, t) (hsU ⟨rfl, ht⟩)
    simpa only [abs_sub_comm] using
      (h.solution.solution.beta_out u v s hs.1 hsU).abs_sub_le hs.1
        (fun t ht => by
          rw [abs_mul]
          exact mul_le_mul (hb t ht) (hscalar t ht) (abs_nonneg _)
            (div_nonneg (by norm_num) (sub_pos.mpr hp.2).le))

end ChristodoulouBV

end
