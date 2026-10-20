module

public import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The removable mixed coefficient of a frozen C¹ solution

All quotients use canonical radius and mass extensions on the closed triangle.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.C1Solution

/-- Twice the canonical mass divided by the square of the canonical radius.
Its axis value is zero by Lean's division convention. -/
@[expose] noncomputable def canonicalMassOverRadiusSq
    (b : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  2 * canonicalMass b S p / (canonicalRadius S p)^2

/-- The normalized canonical mass vanishes on the regular axis. -/
theorem canonicalMassOverRadiusSq_axis (b : ℝ) (S : Fields) (u : ℝ) :
    canonicalMassOverRadiusSq b S (u, u) = 0 := by
  simp [canonicalMassOverRadiusSq, canonicalMass_axis, canonical_outgoing_axis]

/-- Cubic mass decay and linear radius growth give a linear normalized-mass bound. -/
theorem exists_canonicalMassOverRadiusSq_linear_axis_bound {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ closedCoordTriangle 0 B,
      0 ≤ canonicalMassOverRadiusSq b S p ∧
        canonicalMassOverRadiusSq b S p ≤ C * (p.2 - p.1) := by
  obtain ⟨M, hM, hm⟩ := exists_canonicalMass_cubic_axis_bound hB hBb H
  obtain ⟨c, hc, hr⟩ := canonicalRadius_lower_bound hB hBb H
  refine ⟨2 * M / c^2, by positivity, ?_⟩
  rintro ⟨u, v⟩ hp
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hpK : (u, v) ∈ closedCoordTriangle 0 B := hp
    have hd : 0 < v - u := sub_pos.mpr huv
    have hrad : 0 < canonicalRadius S (u, v) :=
      lt_of_lt_of_le (mul_pos hc hd) (hr (u, v) hpK)
    have hradSq : 0 < (canonicalRadius S (u, v))^2 := sq_pos_of_pos hrad
    have hmass := hm (u, v) hpK
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) hmass.1) hradSq.le
    · apply (div_le_iff₀ hradSq).2
      have hradBound : (c * (v - u))^2 ≤ (canonicalRadius S (u, v))^2 :=
        (sq_le_sq₀ (mul_nonneg hc.le hd.le) hrad.le).2 (hr (u, v) hpK)
      have hkey : (2 * M / c^2) * (v - u) * (c * (v - u))^2 =
          2 * M * (v - u)^3 := by
        field_simp
      calc
        2 * canonicalMass b S (u, v) ≤ 2 * (M * (v - u)^3) :=
          mul_le_mul_of_nonneg_left hmass.2 (by norm_num)
        _ = (2 * M / c^2) * (v - u) * (c * (v - u))^2 := by
          calc
            2 * (M * (v - u)^3) = 2 * M * (v - u)^3 := by ring
            _ = _ := hkey.symm
        _ ≤ (2 * M / c^2) * (v - u) * (canonicalRadius S (u, v))^2 := by
          gcongr
  · subst v
    simp [canonicalMassOverRadiusSq_axis]

/-- The normalized canonical mass is continuous at every axis point. -/
theorem canonicalMassOverRadiusSq_continuousWithinAt_axis {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (_hu : u ∈ Icc 0 B) :
    ContinuousWithinAt (canonicalMassOverRadiusSq b S)
      (closedCoordTriangle 0 B) (u, u) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨C, _, hbound⟩ := exists_canonicalMassOverRadiusSq_linear_axis_bound hB hBb H
  have hgap : Tendsto (fun p : ℝ × ℝ => p.2 - p.1)
      (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous (fun p : ℝ × ℝ => p.2 - p.1) := by fun_prop
    change Tendsto (fun p : ℝ × ℝ => p.2 - p.1)
      (𝓝 (u, u) ⊓ 𝓟 K) (𝓝 (0 : ℝ))
    simpa using (hcont.tendsto (u, u)).mono_left inf_le_left
  have hlinear : Tendsto (fun p : ℝ × ℝ => C * (p.2 - p.1))
      (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) := by
    simpa using hgap.const_mul C
  have hnonneg : ∀ᶠ p in 𝓝[K] (u, u),
      0 ≤ canonicalMassOverRadiusSq b S p := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hbound p hp).1
  have hupper : ∀ᶠ p in 𝓝[K] (u, u),
      canonicalMassOverRadiusSq b S p ≤ C * (p.2 - p.1) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hbound p hp).2
  have hlim : Tendsto (canonicalMassOverRadiusSq b S) (𝓝[K] (u, u))
      (𝓝 (0 : ℝ)) := squeeze_zero' hnonneg hupper hlinear
  change Tendsto (canonicalMassOverRadiusSq b S) (𝓝[K] (u, u))
    (𝓝 (canonicalMassOverRadiusSq b S (u, u)))
  rw [canonicalMassOverRadiusSq_axis]
  exact hlim

/-- The normalized canonical mass is continuous on a smaller closed triangle. -/
theorem canonicalMassOverRadiusSq_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMassOverRadiusSq b S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hm := canonicalMass_continuousOn hB hBb H
  have hr := (canonicalRadius_contDiffOn hB hBb H).continuousOn
  intro p hp
  rcases p with ⟨u, v⟩
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hrad : 0 < canonicalRadius S (u, v) := by
      obtain ⟨c, hc, hcl⟩ := canonicalRadius_lower_bound hB hBb H
      exact lt_of_lt_of_le (mul_pos hc (sub_pos.mpr huv)) (hcl (u, v) hp)
    change ContinuousWithinAt
      (fun q => 2 * canonicalMass b S q / (canonicalRadius S q)^2) K (u, v)
    exact (continuousWithinAt_const.mul (hm (u, v) hp)).div
      ((hr (u, v) hp).pow 2) (pow_ne_zero 2 (ne_of_gt hrad))
  · subst v
    exact canonicalMassOverRadiusSq_continuousWithinAt_axis hB hBb H
      ⟨hp.1, hp.2.2⟩

/-- The removable mixed coefficient, expressed using canonical extensions. -/
@[expose] noncomputable def canonicalMixedCoefficient
    (b : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  canonicalMassOverRadiusSq b S p * S.lam p.1 p.2 * S.nu p.1 p.2 /
    (1 - canonicalMassRatio b S p)

/-- The canonical mixed coefficient vanishes on the regular axis. -/
theorem canonicalMixedCoefficient_axis (b : ℝ) (S : Fields) (u : ℝ) :
    canonicalMixedCoefficient b S (u, u) = 0 := by
  simp [canonicalMixedCoefficient, canonicalMassOverRadiusSq_axis]

/-- The removable mixed coefficient is continuous on a smaller closed triangle. -/
theorem canonicalMixedCoefficient_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMixedCoefficient b S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨ε, hε, hgap⟩ := exists_canonical_mass_gap_lower_bound hB hBb H
  obtain ⟨hlam, hnu, _, _, _⟩ := five_fields_contDiffOn hB hBb H
  have hden : ∀ p ∈ K, 1 - canonicalMassRatio b S p ≠ 0 :=
    fun p hp => ne_of_gt (hε.trans_le (hgap p hp))
  change ContinuousOn (fun p : ℝ × ℝ =>
    canonicalMassOverRadiusSq b S p * S.lam p.1 p.2 * S.nu p.1 p.2 /
      (1 - canonicalMassRatio b S p)) K
  exact (((canonicalMassOverRadiusSq_continuousOn hB hBb H).mul
    hlam.continuousOn).mul hnu.continuousOn).div
    (continuousOn_const.sub (canonicalMassRatio_continuousOn hB hBb H)) hden

/-- In the development, the canonical coefficient is the frozen rational density. -/
theorem canonicalMixedCoefficient_eq_frozen {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    canonicalMixedCoefficient b S (u, v) =
      (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) := by
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hpos := mass_gap_pos hB hBb H hu huv hv
    have hrpos := H.solution.radius_pos (u, v) hp
    have heq : 1 - 2 * S.m u v / S.r u v =
        (S.r u v - 2 * S.m u v) / S.r u v := by field_simp
    rw [heq]
    exact ne_of_gt (div_pos hpos hrpos)
  rw [canonicalMixedCoefficient, canonicalMassOverRadiusSq,
    canonicalMassRatio_eq_mass_ratio H hp, canonicalMass_eq_mass hp,
    canonicalRadius_eq_radius hB hBb H hu huv hv]
  field_simp

end ChristodoulouBV.C1Solution

end
