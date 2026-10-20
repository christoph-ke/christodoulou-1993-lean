module

public import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Canonical mass ratio on a closed triangle

The ratio uses the canonical radius and mass. The frozen total fields are used
only at points of the development.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The mass ratio of the canonical radius and mass extensions. At the axis,
Lean's division by zero gives the intended zero extension. -/
@[expose] noncomputable def canonicalMassRatio (b : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  2 * canonicalMass b S p / canonicalRadius S p

/-- The canonical mass ratio agrees with the frozen ratio in the development. -/
theorem canonicalMassRatio_eq_mass_ratio {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge b) :
    canonicalMassRatio b S p = 2 * S.m p.1 p.2 / S.r p.1 p.2 := by
  rw [canonicalMassRatio, canonicalMass_eq_mass hp]
  obtain ⟨u, v⟩ := p
  have hB : 0 < (v + b) / 2 := by
    rcases hp with ⟨hu, huv, hv⟩
    linarith
  have hBb : (v + b) / 2 < b := by
    rcases hp with ⟨hu, huv, hv⟩
    linarith
  have hvB : v ≤ (v + b) / 2 := by
    rcases hp with ⟨hu, huv, hv⟩
    linarith
  rw [canonicalRadius_eq_radius hB hBb H hp.1 hp.2.1 hvB]

/-- The canonical mass ratio has a uniform quadratic bound at the axis. -/
theorem exists_canonicalMassRatio_quadratic_axis_bound {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ closedCoordTriangle 0 B,
      0 ≤ canonicalMassRatio b S p ∧
        canonicalMassRatio b S p ≤ C * (p.2 - p.1)^2 := by
  obtain ⟨M, hM, hm⟩ := exists_canonicalMass_cubic_axis_bound hB hBb H
  obtain ⟨c, hc, hr⟩ := canonicalRadius_lower_bound hB hBb H
  refine ⟨2 * M / c, by positivity, ?_⟩
  rintro ⟨u, v⟩ hp
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · have hpK : (u, v) ∈ closedCoordTriangle 0 B := hp
    have hd : 0 < v - u := sub_pos.mpr huv
    have hrad : 0 < canonicalRadius S (u, v) :=
      lt_of_lt_of_le (mul_pos hc hd) (hr (u, v) hpK)
    have hmass := hm (u, v) hpK
    constructor
    · exact div_nonneg (mul_nonneg (by norm_num) hmass.1) hrad.le
    · apply (div_le_iff₀ hrad).2
      have hkey : (2 * M / c) * (v - u)^2 * (c * (v - u)) =
          2 * M * (v - u)^3 := by
        field_simp
      calc
        2 * canonicalMass b S (u, v) ≤ 2 * (M * (v - u)^3) := by
          exact mul_le_mul_of_nonneg_left hmass.2 (by norm_num)
        _ = (2 * M / c) * (v - u)^2 * (c * (v - u)) := by
          calc
            2 * (M * (v - u)^3) = 2 * M * (v - u)^3 := by ring
            _ = _ := hkey.symm
        _ ≤ (2 * M / c) * (v - u)^2 * canonicalRadius S (u, v) := by
          gcongr
          exact hr (u, v) hpK
  · subst v
    simp [canonicalMassRatio, canonicalMass_axis, canonical_outgoing_axis]

/-- The canonical mass ratio is zero on the regular axis. -/
theorem canonicalMassRatio_axis (b : ℝ) (S : Fields) (u : ℝ) :
    canonicalMassRatio b S (u, u) = 0 := by
  simp [canonicalMassRatio, canonicalMass_axis, canonical_outgoing_axis]

/-- The quadratic bound makes the mass ratio continuous at every axis point. -/
theorem canonicalMassRatio_continuousWithinAt_axis {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (_hu : u ∈ Icc 0 B) :
    ContinuousWithinAt (canonicalMassRatio b S)
      (closedCoordTriangle 0 B) (u, u) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨C, _, hbound⟩ := exists_canonicalMassRatio_quadratic_axis_bound hB hBb H
  have hgap : Tendsto (fun p : ℝ × ℝ => p.2 - p.1)
      (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous (fun p : ℝ × ℝ => p.2 - p.1) := by fun_prop
    change Tendsto (fun p : ℝ × ℝ => p.2 - p.1)
      (𝓝 (u, u) ⊓ 𝓟 K) (𝓝 (0 : ℝ))
    simpa using (hcont.tendsto (u, u)).mono_left inf_le_left
  have hquad : Tendsto (fun p : ℝ × ℝ => C * (p.2 - p.1)^2)
      (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) := by
    simpa using (hgap.pow 2).const_mul C
  have hnonneg : ∀ᶠ p in 𝓝[K] (u, u), 0 ≤ canonicalMassRatio b S p := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hbound p hp).1
  have hupper : ∀ᶠ p in 𝓝[K] (u, u),
      canonicalMassRatio b S p ≤ C * (p.2 - p.1)^2 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hbound p hp).2
  have hlim : Tendsto (canonicalMassRatio b S) (𝓝[K] (u, u)) (𝓝 (0 : ℝ)) :=
    squeeze_zero' hnonneg hupper hquad
  change Tendsto (canonicalMassRatio b S) (𝓝[K] (u, u))
    (𝓝 (canonicalMassRatio b S (u, u)))
  rw [canonicalMassRatio_axis]
  exact hlim

/-- The outgoing mass-gap argument gives a strict pointwise canonical gap. -/
theorem canonicalMassRatio_lt_one {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    canonicalMassRatio b S (u, v) < 1 := by
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  rw [canonicalMassRatio_eq_mass_ratio H hp]
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v) hp
  have hgap := mass_gap_pos hB hBb H hu huv hv
  apply (div_lt_iff₀ hr).2
  linarith only [hgap]

private theorem intervalPrimitive_abs_sub_le {f g : ℝ → ℝ} {a z M : ℝ}
    (haz : a ≤ z) (h : IntervalPrimitive f g a z)
    (hbound : ∀ t ∈ Icc a z, |g t| ≤ M) :
    |f z - f a| ≤ M * (z - a) := by
  rw [h.2]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := z) (C := M) (f := g) (by
      intro t ht
      rw [uIoc_of_le haz] at ht
      simpa only [Real.norm_eq_abs] using hbound t ⟨ht.1.le, ht.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr haz)] using hnorm

private theorem continuousWithinAt_of_coordinate_lipschitz
    {b B M : ℝ} (hBb : B < b) {F : ℝ × ℝ → ℝ}
    (hV : ∀ u v w, (u, v) ∈ closedCoordTriangle 0 B →
      (u, w) ∈ closedCoordTriangle 0 B →
      (u, v) ∈ developmentWithInitialEdge b →
      (u, w) ∈ developmentWithInitialEdge b →
      |F (u, v) - F (u, w)| ≤ M * |v - w|)
    (hU : ∀ u w v, (u, v) ∈ closedCoordTriangle 0 B →
      (w, v) ∈ closedCoordTriangle 0 B →
      (u, v) ∈ developmentWithInitialEdge b →
      (w, v) ∈ developmentWithInitialEdge b →
      |F (u, v) - F (w, v)| ≤ M * |u - w|)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) (hgap : p.1 < p.2) :
    ContinuousWithinAt F (closedCoordTriangle 0 B) p := by
  let K := closedCoordTriangle 0 B
  have hpU : p ∈ developmentWithInitialEdge b :=
    ⟨hp.1, hgap, hp.2.2.trans_lt hBb⟩
  have hopen : IsOpen {q : ℝ × ℝ | q.1 < q.2 ∧ q.1 < p.2} :=
    (isOpen_lt continuous_fst continuous_snd).inter
      (isOpen_lt continuous_fst continuous_const)
  have hnear0 : ∀ᶠ q in 𝓝 p, q.1 < q.2 ∧ q.1 < p.2 :=
    hopen.mem_nhds ⟨hgap, hgap⟩
  have hnear : ∀ᶠ q in 𝓝[K] p, q.1 < q.2 ∧ q.1 < p.2 :=
    hnear0.filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ q in 𝓝[K] p,
      |F q - F p| ≤ M * (|q.2 - p.2| + |q.1 - p.1|) := by
    filter_upwards [hnear, self_mem_nhdsWithin] with q hqgap hqK
    have hqU : q ∈ developmentWithInitialEdge b :=
      ⟨hqK.1, hqgap.1, hqK.2.2.trans_lt hBb⟩
    have hcross : (q.1, p.2) ∈ developmentWithInitialEdge b :=
      ⟨hqK.1, hqgap.2, hp.2.2.trans_lt hBb⟩
    have hcrossK : (q.1, p.2) ∈ K :=
      ⟨hqK.1, hqgap.2.le, hp.2.2⟩
    calc
      |F q - F p| ≤ |F q - F (q.1, p.2)| +
          |F (q.1, p.2) - F p| := abs_sub_le _ _ _
      _ ≤ M * |q.2 - p.2| + M * |q.1 - p.1| :=
        add_le_add (hV q.1 q.2 p.2 hqK hcrossK hqU hcross)
          (hU q.1 p.1 p.2 hcrossK hp hcross hpU)
      _ = M * (|q.2 - p.2| + |q.1 - p.1|) := by ring
  have hright : Tendsto
      (fun q : ℝ × ℝ => M * (|q.2 - p.2| + |q.1 - p.1|))
      (𝓝[K] p) (𝓝 (0 : ℝ)) := by
    have h : Continuous (fun q : ℝ × ℝ =>
        M * (|q.2 - p.2| + |q.1 - p.1|)) := by fun_prop
    change Tendsto _ (𝓝 p ⊓ 𝓟 K) (𝓝 (0 : ℝ))
    simpa using (h.tendsto p).mono_left inf_le_left
  have hleft : Tendsto (fun q : ℝ × ℝ => |F q - F p|)
      (𝓝[K] p) (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      hbound hright
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by
    simpa only [Real.norm_eq_abs] using hleft)

private theorem mass_factor_mem_unit_interval {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ B) :
    0 ≤ 1 - 2 * S.m u v / S.r u v ∧
      1 - 2 * S.m u v / S.r u v ≤ 1 := by
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu, huv, hv.trans_lt hBb⟩
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v) hp
  have hmass := mass_nonneg hB hBb H hu huv hv
  have hgap := mass_gap_pos hB hBb H hu huv hv
  have hratio : 0 ≤ 2 * S.m u v / S.r u v :=
    div_nonneg (mul_nonneg (by norm_num) hmass) hr.le
  constructor
  · have heq : 1 - 2 * S.m u v / S.r u v =
        (S.r u v - 2 * S.m u v) / S.r u v := by
      field_simp
    rw [heq]
    exact (div_pos hgap hr).le
  · linarith only [hratio]

private theorem exists_mass_density_bound {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, 0 ≤ u → u < v → v ≤ B →
      |(1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
          (2 * S.lam u v)| ≤ M ∧
      |(1 - 2 * S.m u v / S.r u v) * (S.zeta u v)^2 /
          (2 * S.nu u v)| ≤ M := by
  let K := closedCoordTriangle 0 B
  let V : ℝ × ℝ → ℝ := fun p =>
    (S.theta p.1 p.2)^2 / (2 * S.lam p.1 p.2)
  let W : ℝ × ℝ → ℝ := fun p =>
    (S.zeta p.1 p.2)^2 / (-(2 * S.nu p.1 p.2))
  obtain ⟨c, hc, hlam⟩ := exists_lam_lower_bound hB hBb H
  have hnu (p : ℝ × ℝ) (hp : p ∈ K) : S.nu p.1 p.2 < 0 :=
    nu_neg_closed_triangle hB hBb H hp
  obtain ⟨hlamC1, hnuC1, _, hthetaC1, hzetaC1⟩ :=
    five_fields_contDiffOn hB hBb H
  have hVcont : ContinuousOn V K := by
    dsimp [V]
    apply (hthetaC1.continuousOn.pow 2).div
      (continuousOn_const.mul hlamC1.continuousOn)
    intro p hp
    exact ne_of_gt (mul_pos (by norm_num) (hc.trans_le (hlam p hp)))
  have hWcont : ContinuousOn W K := by
    dsimp [W]
    apply (hzetaC1.continuousOn.pow 2).div
      (continuousOn_const.mul hnuC1.continuousOn).neg
    intro p hp
    exact ne_of_gt (neg_pos.mpr
      (mul_neg_of_pos_of_neg (by norm_num) (hnu p hp)))
  obtain ⟨M, hM⟩ := (isCompact_closedCoordTriangle 0 B).exists_bound_of_continuousOn
    (hVcont.add hWcont)
  have hzero : (0, 0) ∈ K := ⟨le_rfl, le_rfl, hB.le⟩
  have hMnonneg : 0 ≤ M :=
    (norm_nonneg (V (0, 0) + W (0, 0))).trans (hM (0, 0) hzero)
  refine ⟨M, hMnonneg, ?_⟩
  intro u v hu huv hv
  have hp : (u, v) ∈ K := ⟨hu, huv.le, hv⟩
  have hfac := mass_factor_mem_unit_interval hB hBb H hu huv hv
  have hl : 0 < S.lam u v := hc.trans_le (hlam (u, v) hp)
  have hn : S.nu u v < 0 := hnu (u, v) hp
  have hVnonneg : 0 ≤ V (u, v) := by dsimp [V]; positivity
  have hWnonneg : 0 ≤ W (u, v) := by
    dsimp [W]
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (neg_pos.mpr (mul_neg_of_pos_of_neg (by norm_num) hn)))
  have hsum : V (u, v) + W (u, v) ≤ M := by
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, Pi.add_apply] using hM (u, v) hp)
  have hVle : V (u, v) ≤ M := by linarith only [hWnonneg, hsum]
  have hWle : W (u, v) ≤ M := by linarith only [hVnonneg, hsum]
  have hfactorNonneg : 0 ≤ 1 - 2 * S.m u v / S.r u v := hfac.1
  have hfactorLe : 1 - 2 * S.m u v / S.r u v ≤ 1 := hfac.2
  constructor
  · have hEq : (1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (2 * S.lam u v) =
        (1 - 2 * S.m u v / S.r u v) * V (u, v) := by
      dsimp [V]
      ring
    rw [hEq, abs_of_nonneg (mul_nonneg hfactorNonneg hVnonneg)]
    calc
      _ ≤ 1 * V (u, v) := mul_le_mul_of_nonneg_right hfactorLe hVnonneg
      _ = V (u, v) := one_mul _
      _ ≤ M := hVle
  · have hEq : (1 - 2 * S.m u v / S.r u v) * (S.zeta u v)^2 /
        (2 * S.nu u v) =
        -((1 - 2 * S.m u v / S.r u v) * W (u, v)) := by
      dsimp [W]
      have hne : S.nu u v ≠ 0 := ne_of_lt hn
      field_simp
    rw [hEq, abs_neg, abs_of_nonneg (mul_nonneg hfactorNonneg hWnonneg)]
    calc
      _ ≤ 1 * W (u, v) := mul_le_mul_of_nonneg_right hfactorLe hWnonneg
      _ = W (u, v) := one_mul _
      _ ≤ M := hWle

private theorem exists_mass_coordinate_lipschitz {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ M : ℝ,
      (∀ u v w, (u, v) ∈ closedCoordTriangle 0 B →
        (u, w) ∈ closedCoordTriangle 0 B →
        (u, v) ∈ developmentWithInitialEdge b →
        (u, w) ∈ developmentWithInitialEdge b →
        |canonicalMass b S (u, v) - canonicalMass b S (u, w)| ≤
          M * |v - w|) ∧
      (∀ u w v, (u, v) ∈ closedCoordTriangle 0 B →
        (w, v) ∈ closedCoordTriangle 0 B →
        (u, v) ∈ developmentWithInitialEdge b →
        (w, v) ∈ developmentWithInitialEdge b →
        |canonicalMass b S (u, v) - canonicalMass b S (w, v)| ≤
          M * |u - w|) := by
  obtain ⟨M, _, hden⟩ := exists_mass_density_bound hB hBb H
  refine ⟨M, ?_, ?_⟩
  · intro u v w hvK hwK hvU hwU
    have hbound (a z : ℝ) (haz : a ≤ z) (haU : (u, a) ∈ developmentWithInitialEdge b)
        (hzK : (u, z) ∈ closedCoordTriangle 0 B) :
        |S.m u z - S.m u a| ≤ M * (z - a) := by
      have hzU : (u, z) ∈ developmentWithInitialEdge b :=
        ⟨hzK.1, haU.2.1.trans_le haz, hzK.2.2.trans_lt hBb⟩
      have hseg : outSeg u a z ⊆ developmentWithInitialEdge b :=
        H.solution.development.out_seg_subset hzU haU.2.1 haz le_rfl
      exact intervalPrimitive_abs_sub_le haz (H.solution.mass_out u a z haz hseg)
        (by
          intro t ht
          exact (hden u t haU.1 (haU.2.1.trans_le ht.1)
            (ht.2.trans hzK.2.2)).1)
    rw [canonicalMass_eq_mass hvU, canonicalMass_eq_mass hwU]
    rcases le_total v w with hvw | hwv
    · have h := hbound v w hvw hvU hwK
      calc
        |S.m u v - S.m u w| = |S.m u w - S.m u v| := abs_sub_comm _ _
        _ ≤ M * (w - v) := h
        _ = M * |v - w| := by rw [abs_of_nonpos (sub_nonpos.mpr hvw)]; ring
    · have h := hbound w v hwv hwU hvK
      calc
        |S.m u v - S.m u w| ≤ M * (v - w) := h
        _ = M * |v - w| := by rw [abs_of_nonneg (sub_nonneg.mpr hwv)]
  · intro u w v huK hwK huU hwU
    have hbound (a z : ℝ) (haz : a ≤ z)
        (haK : (a, v) ∈ closedCoordTriangle 0 B)
        (hzU : (z, v) ∈ developmentWithInitialEdge b) :
        |S.m z v - S.m a v| ≤ M * (z - a) := by
      have hseg : inSeg v a z ⊆ developmentWithInitialEdge b := by
        intro p hp
        rcases p with ⟨s, t⟩
        have hst : s ∈ Icc a z ∧ t = v := by simpa [inSeg] using hp
        rcases hst with ⟨hs, rfl⟩
        exact ⟨haK.1.trans hs.1, hs.2.trans_lt hzU.2.1,
          haK.2.2.trans_lt hBb⟩
      exact intervalPrimitive_abs_sub_le haz (H.solution.mass_in v a z haz hseg)
        (by
          intro t ht
          exact (hden t v (haK.1.trans ht.1)
            (ht.2.trans_lt hzU.2.1) haK.2.2).2)
    rw [canonicalMass_eq_mass huU, canonicalMass_eq_mass hwU]
    rcases le_total u w with huw | hwu
    · have h := hbound u w huw huK hwU
      calc
        |S.m u v - S.m w v| = |S.m w v - S.m u v| := abs_sub_comm _ _
        _ ≤ M * (w - u) := h
        _ = M * |u - w| := by rw [abs_of_nonpos (sub_nonpos.mpr huw)]; ring
    · have h := hbound w u hwu hwK huU
      calc
        |S.m u v - S.m w v| ≤ M * (u - w) := h
        _ = M * |u - w| := by rw [abs_of_nonneg (sub_nonneg.mpr hwu)]

/-- The canonical mass is continuous off the axis, including the initial and
top edges of every smaller closed triangle. -/
theorem canonicalMass_continuousWithinAt_off_axis {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) (hgap : p.1 < p.2) :
    ContinuousWithinAt (canonicalMass b S) (closedCoordTriangle 0 B) p := by
  obtain ⟨M, hV, hU⟩ := exists_mass_coordinate_lipschitz hB hBb H
  exact continuousWithinAt_of_coordinate_lipschitz hBb hV hU hp hgap

/-- The canonical mass is continuous on each smaller closed triangle. -/
theorem canonicalMass_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMass b S) (closedCoordTriangle 0 B) := by
  rintro ⟨u, v⟩ hp
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
  rcases lt_or_eq_of_le hp.2.1 with huv | huv
  · exact canonicalMass_continuousWithinAt_off_axis hB hBb H hp huv
  · subst v
    exact canonicalMass_continuousWithinAt_axis hB hBb H ⟨hp.1, hp.2.2⟩

/-- The canonical mass ratio is continuous on the full closed triangle. -/
theorem canonicalMassRatio_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMassRatio b S) (closedCoordTriangle 0 B) := by
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
      (fun q => 2 * canonicalMass b S q / canonicalRadius S q) K (u, v)
    exact (continuousWithinAt_const.mul (hm (u, v) hp)).div
      (hr (u, v) hp) (ne_of_gt hrad)
  · subst v
    exact canonicalMassRatio_continuousWithinAt_axis hB hBb H ⟨hp.1, hp.2.2⟩

/-- The positive canonical mass gap has a uniform lower bound on every
smaller closed triangle. -/
theorem exists_canonical_mass_gap_lower_bound {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ closedCoordTriangle 0 B,
      ε ≤ 1 - canonicalMassRatio b S p := by
  let K := closedCoordTriangle 0 B
  have hnonempty : K.Nonempty := ⟨(0, 0), by
    change (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ B
    exact ⟨le_rfl, le_rfl, hB.le⟩⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      1 - canonicalMassRatio b S p) K :=
    continuousOn_const.sub (canonicalMassRatio_continuousOn hB hBb H)
  have hpos (p : ℝ × ℝ) (hp : p ∈ K) :
      0 < 1 - canonicalMassRatio b S p := by
    rcases p with ⟨u, v⟩
    change 0 ≤ u ∧ u ≤ v ∧ v ≤ B at hp
    rcases lt_or_eq_of_le hp.2.1 with huv | huv
    · linarith only [canonicalMassRatio_lt_one hB hBb H hp.1 huv hp.2.2]
    · subst v
      rw [canonicalMassRatio_axis]
      norm_num
  obtain ⟨p, hp, hmin⟩ := (isCompact_closedCoordTriangle 0 B).exists_isMinOn
    hnonempty hcont
  exact ⟨1 - canonicalMassRatio b S p, hpos p hp, fun q hq => hmin hq⟩

/-- The outgoing mass density expressed using the continuous canonical ratio. -/
@[expose] noncomputable def canonicalMassOutgoingDensity (b : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  (1 - canonicalMassRatio b S p) * (S.theta p.1 p.2)^2 /
    (2 * S.lam p.1 p.2)

/-- The incoming mass density expressed using the continuous canonical ratio. -/
@[expose] noncomputable def canonicalMassIncomingDensity (b : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  (1 - canonicalMassRatio b S p) * (S.zeta p.1 p.2)^2 /
    (2 * S.nu p.1 p.2)

/-- Both canonical mass densities are continuous on a smaller closed triangle. -/
theorem canonicalMass_densities_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalMassOutgoingDensity b S) (closedCoordTriangle 0 B) ∧
      ContinuousOn (canonicalMassIncomingDensity b S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hA : ContinuousOn (fun p : ℝ × ℝ =>
      1 - canonicalMassRatio b S p) K :=
    continuousOn_const.sub (canonicalMassRatio_continuousOn hB hBb H)
  obtain ⟨hlam, hnu, _, htheta, hzeta⟩ := five_fields_contDiffOn hB hBb H
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  constructor
  · change ContinuousOn (fun p : ℝ × ℝ =>
        (1 - canonicalMassRatio b S p) * (S.theta p.1 p.2)^2 /
          (2 * S.lam p.1 p.2)) K
    apply (hA.mul (htheta.continuousOn.pow 2)).div
      (continuousOn_const.mul hlam.continuousOn)
    intro p hp
    exact ne_of_gt (mul_pos (by norm_num) (hc.trans_le (hcl p hp)))
  · change ContinuousOn (fun p : ℝ × ℝ =>
        (1 - canonicalMassRatio b S p) * (S.zeta p.1 p.2)^2 /
          (2 * S.nu p.1 p.2)) K
    apply (hA.mul (hzeta.continuousOn.pow 2)).div
      (continuousOn_const.mul hnu.continuousOn)
    intro p hp
    exact ne_of_lt (mul_neg_of_pos_of_neg (by norm_num)
      (nu_neg_closed_triangle hB hBb H hp))

/-- A continuous interval density is the pointwise derivative of its frozen
primitive at each interior point. -/
theorem hasDerivAt_of_intervalPrimitive_local
    {f g : ℝ → ℝ} {a x c : ℝ} (hax : a < x) (hxc : x < c)
    (hg : ContinuousOn g (Icc a c))
    (hprim : ∀ t ∈ Ioo a c, IntervalPrimitive f g a t) :
    HasDerivAt f (g x) x := by
  have hInt : IntervalIntegrable g volume a x :=
    (hg.mono (fun _ ht => ⟨ht.1, ht.2.trans hxc.le⟩)).intervalIntegrable_of_Icc hax.le
  have hgOpen : ContinuousOn g (Ioo a c) :=
    hg.mono (fun _ ht => ⟨ht.1.le, ht.2.le⟩)
  have hxOpen : x ∈ Ioo a c := ⟨hax, hxc⟩
  have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    hgOpen.stronglyMeasurableAtFilter isOpen_Ioo x hxOpen
  have hcontAt : ContinuousAt g x :=
    (hgOpen x hxOpen).continuousAt (isOpen_Ioo.mem_nhds hxOpen)
  have hFTC : HasDerivAt (fun t => f a + ∫ s in a..t, g s) (g x) x :=
    (intervalIntegral.integral_hasDerivAt_right hInt hmeas hcontAt).const_add (f a)
  have hEq : f =ᶠ[𝓝 x] (fun t => f a + ∫ s in a..t, g s) := by
    filter_upwards [Ioo_mem_nhds hax hxc] with t ht
    have h := (hprim t ht).2
    linarith only [h]
  exact hFTC.congr_of_eventuallyEq hEq

/-- On the triangle interior, the vertical derivative of canonical mass is
the outgoing canonical density. -/
theorem canonicalMass_vertical_hasDerivAt {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => canonicalMass b S (u, t))
      (canonicalMassOutgoingDensity b S (u, v)) v := by
  have hparts : 0 < u ∧ u < v ∧ v < B := hp
  let a := (u + v) / 2
  let c := (v + B) / 2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hvc : v < c := by dsimp [c]; linarith
  have hcB : c < B := by dsimp [c]; linarith
  have hmap (s : ℝ) (hs : s ∈ Icc a c) :
      (u, s) ∈ closedCoordTriangle 0 B :=
    ⟨hparts.1.le, hua.le.trans hs.1, hs.2.trans hcB.le⟩
  have hmem (s : ℝ) (hs : s ∈ Icc a c) :
      (u, s) ∈ developmentWithInitialEdge b :=
    ⟨hparts.1.le, hua.trans_le hs.1, (hs.2.trans_lt hcB).trans hBb⟩
  let g : ℝ → ℝ := fun s =>
    (1 - 2 * S.m u s / S.r u s) * (S.theta u s)^2 / (2 * S.lam u s)
  have hg : ContinuousOn g (Icc a c) := by
    have hcanon : ContinuousOn (fun s => canonicalMassOutgoingDensity b S (u, s))
        (Icc a c) :=
      (canonicalMass_densities_continuousOn hB hBb H).1.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
    apply hcanon.congr
    intro s hs
    dsimp [g, canonicalMassOutgoingDensity]
    rw [canonicalMassRatio_eq_mass_ratio H (hmem s hs)]
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (S.m u) g a t := by
    have htU : (u, t) ∈ developmentWithInitialEdge b :=
      hmem t ⟨ht.1.le, ht.2.le⟩
    have hseg : outSeg u a t ⊆ developmentWithInitialEdge b :=
      H.solution.development.out_seg_subset htU hua ht.1.le le_rfl
    exact H.solution.mass_out u a t ht.1.le hseg
  have hderiv : HasDerivAt (S.m u) (g v) v :=
    hasDerivAt_of_intervalPrimitive_local hav hvc hg hprim
  have hvalue : g v = canonicalMassOutgoingDensity b S (u, v) := by
    dsimp [g, canonicalMassOutgoingDensity]
    rw [canonicalMassRatio_eq_mass_ratio H
      (hmem v ⟨hav.le, hvc.le⟩)]
  rw [hvalue] at hderiv
  have hEq : (fun t => canonicalMass b S (u, t)) =ᶠ[𝓝 v] S.m u := by
    filter_upwards [Ioo_mem_nhds hav hvc] with t ht
    exact canonicalMass_eq_mass (hmem t ⟨ht.1.le, ht.2.le⟩)
  exact hderiv.congr_of_eventuallyEq hEq

/-- On the triangle interior, the horizontal derivative of canonical mass is
the incoming canonical density. -/
theorem canonicalMass_horizontal_hasDerivAt {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun t => canonicalMass b S (t, v))
      (canonicalMassIncomingDensity b S (u, v)) u := by
  have hparts : 0 < u ∧ u < v ∧ v < B := hp
  let a := u / 2
  let c := (u + v) / 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hau : a < u := by dsimp [a]; linarith
  have huc : u < c := by dsimp [c]; linarith
  have hcv : c < v := by dsimp [c]; linarith
  have hmap (s : ℝ) (hs : s ∈ Icc a c) :
      (s, v) ∈ closedCoordTriangle 0 B :=
    ⟨ha.trans hs.1, hs.2.trans hcv.le, hparts.2.2.le⟩
  have hmem (s : ℝ) (hs : s ∈ Icc a c) :
      (s, v) ∈ developmentWithInitialEdge b :=
    ⟨ha.trans hs.1, hs.2.trans_lt hcv, hparts.2.2.trans hBb⟩
  let g : ℝ → ℝ := fun s =>
    (1 - 2 * S.m s v / S.r s v) * (S.zeta s v)^2 / (2 * S.nu s v)
  have hg : ContinuousOn g (Icc a c) := by
    have hcanon : ContinuousOn (fun s => canonicalMassIncomingDensity b S (s, v))
        (Icc a c) :=
      (canonicalMass_densities_continuousOn hB hBb H).2.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap
    apply hcanon.congr
    intro s hs
    dsimp [g, canonicalMassIncomingDensity]
    rw [canonicalMassRatio_eq_mass_ratio H (hmem s hs)]
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (fun s => S.m s v) g a t := by
    have hseg : inSeg v a t ⊆ developmentWithInitialEdge b := by
      intro p hp
      rcases p with ⟨s, w⟩
      have hsw : s ∈ Icc a t ∧ w = v := by simpa [inSeg] using hp
      rcases hsw with ⟨hs, rfl⟩
      exact ⟨ha.trans hs.1, hs.2.trans_lt (ht.2.trans hcv),
        hparts.2.2.trans hBb⟩
    exact H.solution.mass_in v a t ht.1.le hseg
  have hderiv : HasDerivAt (fun s => S.m s v) (g u) u :=
    hasDerivAt_of_intervalPrimitive_local hau huc hg hprim
  have hvalue : g u = canonicalMassIncomingDensity b S (u, v) := by
    dsimp [g, canonicalMassIncomingDensity]
    rw [canonicalMassRatio_eq_mass_ratio H
      (hmem u ⟨hau.le, huc.le⟩)]
  rw [hvalue] at hderiv
  have hEq : (fun t => canonicalMass b S (t, v)) =ᶠ[𝓝 u]
      (fun t => S.m t v) := by
    filter_upwards [Ioo_mem_nhds hau huc] with t ht
    exact canonicalMass_eq_mass (hmem t ⟨ht.1.le, ht.2.le⟩)
  exact hderiv.congr_of_eventuallyEq hEq

/-- The canonical mass has a continuous full first jet on every smaller
closed triangle. Its boundary values are the canonical extension, not the
frozen total mass. -/
theorem canonicalMass_contDiffOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalMass b S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  let fu := canonicalMassIncomingDensity b S
  let fv := canonicalMassOutgoingDensity b S
  let L : ℝ → ℝ →L[ℝ] ℝ :=
    fun x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) x
  let J : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ :=
    fun p => (L (fu p)).coprod (L (fv p))
  have hL : Continuous L :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous
  obtain ⟨hfv, hfu⟩ := canonicalMass_densities_continuousOn hB hBb H
  have hJ : ContinuousOn J K := by
    have h₁ : ContinuousOn (fun p => L (fu p)) K :=
      hL.comp_continuousOn hfu
    have h₂ : ContinuousOn (fun p => L (fv p)) K :=
      hL.comp_continuousOn hfv
    exact (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := ℝ)
      (G := ℝ) ℝ).continuous.comp_continuousOn (h₁.prodMk h₂)
  have hstrict (p : ℝ × ℝ) (hp : p ∈ interior K) :
      HasStrictFDerivAt (canonicalMass b S) (J p) p := by
    have hnear : openCoordTriangle 0 B ∈ 𝓝 p := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior.mem_nhds hp
    have hdu : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun s => canonicalMass b S (s, q.2)) (L (fu q)) q.1 := by
      filter_upwards [hnear] with q hq
      exact (canonicalMass_horizontal_hasDerivAt hB hBb H hq).hasFDerivAt
    have hdv : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun t => canonicalMass b S (q.1, t)) (L (fv q)) q.2 := by
      filter_upwards [hnear] with q hq
      exact (canonicalMass_vertical_hasDerivAt hB hBb H hq).hasFDerivAt
    have hKmem : K ∈ 𝓝 p :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset
    have hfuAt : ContinuousAt fu p :=
      (hfu p (interior_subset hp)).continuousAt hKmem
    have hfvAt : ContinuousAt fv p :=
      (hfv p (interior_subset hp)).continuousAt hKmem
    exact hasStrictFDerivAt_uncurry_coprod
      (f := fun u v => canonicalMass b S (u, v))
      (f₁ := fun u v => L (fu (u, v)))
      (f₂ := fun u v => L (fv (u, v)))
      hdu hdv (hL.continuousAt.comp hfuAt) (hL.continuousAt.comp hfvAt)
  have hdiff : DifferentiableOn ℝ (canonicalMass b S) (interior K) :=
    fun p hp => (hstrict p hp).hasFDerivAt.differentiableAt.differentiableWithinAt
  have hderiv : ∀ p ∈ interior K, fderiv ℝ (canonicalMass b S) p = J p :=
    fun p hp => (hstrict p hp).hasFDerivAt.fderiv
  exact (convex_closedCoordTriangle 0 B).contDiffOn_one_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle 0 B)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
    (canonicalMass_continuousOn hB hBb H) hJ hdiff hderiv

/-- The two relative coordinate derivatives of canonical mass are the
continuous canonical densities, including on the closed boundary. -/
theorem canonicalMass_coordinate_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (canonicalMass b S) (closedCoordTriangle 0 B) p) (1, 0) =
      canonicalMassIncomingDensity b S p ∧
    (fderivWithin ℝ (canonicalMass b S) (closedCoordTriangle 0 B) p) (0, 1) =
      canonicalMassOutgoingDensity b S p := by
  let K := closedCoordTriangle 0 B
  let f := canonicalMass b S
  have hC1 := canonicalMass_contDiffOn hB hBb H
  have hden := canonicalMass_densities_continuousOn hB hBb H
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hG := hC1.continuousOn_fderivWithin hunique (by norm_num)
  have hopen (q : ℝ × ℝ) (hq : q ∈ openCoordTriangle 0 B) :
      (fderivWithin ℝ f K q) (1, 0) = canonicalMassIncomingDensity b S q ∧
      (fderivWithin ℝ f K q) (0, 1) = canonicalMassOutgoingDensity b S q := by
    have hqi : q ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hq
    have hdiff : DifferentiableAt ℝ f q :=
      ((hC1.differentiableOn (by norm_num)).mono interior_subset q hqi).differentiableAt
        (isOpen_interior.mem_nhds hqi)
    have hwithin : fderivWithin ℝ f K q = fderiv ℝ f q :=
      fderivWithin_eq_fderiv (hunique q (interior_subset hqi)) hdiff
    rcases q with ⟨u, v⟩
    have hpairU : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    have hpairV : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hcompU : HasDerivAt (fun t => f (t, v))
        (fderiv ℝ f (u, v) (1, 0)) u := by
      simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpairU
    have hcompV : HasDerivAt (fun t => f (u, t))
        (fderiv ℝ f (u, v) (0, 1)) v := by
      simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt v hpairV
    constructor
    · rw [hwithin]
      exact hcompU.unique (canonicalMass_horizontal_hasDerivAt hB hBb H hq)
    · rw [hwithin]
      exact hcompV.unique (canonicalMass_vertical_hasDerivAt hB hBb H hq)
  have hEqU : EqOn (fun q => (fderivWithin ℝ f K q) (1, 0))
      (canonicalMassIncomingDensity b S) K :=
    (show EqOn (fun q => (fderivWithin ℝ f K q) (1, 0))
      (canonicalMassIncomingDensity b S) (openCoordTriangle 0 B) from
        fun q hq => (hopen q hq).1).of_subset_closure
      (hG.clm_apply continuousOn_const) hden.2
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hB])
  have hEqV : EqOn (fun q => (fderivWithin ℝ f K q) (0, 1))
      (canonicalMassOutgoingDensity b S) K :=
    (show EqOn (fun q => (fderivWithin ℝ f K q) (0, 1))
      (canonicalMassOutgoingDensity b S) (openCoordTriangle 0 B) from
        fun q hq => (hopen q hq).2).of_subset_closure
      (hG.clm_apply continuousOn_const) hden.1
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hB])
  exact ⟨hEqU hp, hEqV hp⟩

/-- Both coordinate jets of canonical mass vanish on the regular axis. -/
theorem canonicalMass_axis_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (canonicalMass b S) (closedCoordTriangle 0 B) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ (canonicalMass b S) (closedCoordTriangle 0 B) (u, u)) (0, 1) = 0 := by
  have hp : (u, u) ∈ closedCoordTriangle 0 B := ⟨hu.1, le_rfl, hu.2⟩
  obtain ⟨hU, hV⟩ := canonicalMass_coordinate_jets hB hBb H hp
  rw [hU, hV]
  simp [canonicalMassIncomingDensity, canonicalMassOutgoingDensity,
    theta_axis_eq_zero hB hBb H hu, zeta_axis_eq_zero hB hBb H hu]

end ChristodoulouBV.C1Solution

end
