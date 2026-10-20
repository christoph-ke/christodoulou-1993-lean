module

public import Mathlib

/-!
# Two-variable Volterra inequalities on rectangles

Bounds for a nonnegative function controlled by integrals along the two incoming
coordinate segments of a rectangle. Only interval integrability of the slices is
used; joint measurability is not required.
-/

public section

open MeasureTheory Set intervalIntegral

namespace intervalIntegral

private theorem mul_integral_exp_affine_le {x y k d : ℝ} :
    k * (∫ t in x..y, Real.exp (k * t + d)) ≤ Real.exp (k * y + d) := by
  rw [intervalIntegral.mul_integral_comp_mul_add]
  rw [integral_exp]
  have h : 0 ≤ Real.exp (k * x + d) := (Real.exp_pos _).le
  linarith

private theorem integral_exp_shift_le {a u k : ℝ} :
    k * (∫ s in a..u, Real.exp (k * (s - a))) ≤ Real.exp (k * (u - a)) := by
  have h := mul_integral_exp_affine_le (x := a) (y := u) (k := k) (d := -(k * a))
  simpa only [sub_eq_add_neg, mul_add, mul_neg] using h

private theorem integral_weight_first_le {a b u v k : ℝ} :
    k * (∫ s in a..u, Real.exp (k * (s - a)) * Real.exp (k * (v - b))) ≤
      Real.exp (k * (u - a)) * Real.exp (k * (v - b)) := by
  rw [intervalIntegral.integral_mul_const]
  convert mul_le_mul_of_nonneg_right (integral_exp_shift_le (a := a) (u := u) (k := k))
    (Real.exp_pos (k * (v - b))).le using 1; ring

private theorem integral_weight_second_le {a b u v k : ℝ} :
    k * (∫ t in b..v, Real.exp (k * (u - a)) * Real.exp (k * (t - b))) ≤
      Real.exp (k * (u - a)) * Real.exp (k * (v - b)) := by
  rw [intervalIntegral.integral_const_mul]
  calc
    k * (Real.exp (k * (u - a)) * ∫ t in b..v, Real.exp (k * (t - b))) =
        Real.exp (k * (u - a)) * (k * ∫ t in b..v, Real.exp (k * (t - b))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_exp_shift_le (a := b) (u := v) (k := k)) (Real.exp_pos _).le

/-- A two-variable Volterra inequality with a bounded source. The only regularity
required of `F` is interval integrability on each incoming coordinate segment. -/
theorem le_two_variable_volterra_exp {a a' b b' C B G : ℝ}
    {F g : ℝ → ℝ → ℝ}
    (haa' : a ≤ a') (hbb' : b ≤ b') (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hF0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F u v)
    (hFB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v ≤ B)
    (hgB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', g u v ≤ G)
    (hFu : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F s v) volume a u)
    (hFv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F u t) volume b v)
    (hineq : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      F u v ≤ g u v + C * (∫ s in a..u, F s v) +
        C * (∫ t in b..v, F u t)) :
    ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      F u v ≤ 2 * G * (Real.exp ((4 * C + 1) * (u - a)) *
        Real.exp ((4 * C + 1) * (v - b))) := by
  let k : ℝ := 4 * C + 1
  let w : ℝ → ℝ → ℝ := fun u v => Real.exp (k * (u - a)) * Real.exp (k * (v - b))
  have hk : 0 < k := by dsimp [k]; linarith
  have hwpos (u v : ℝ) : 0 < w u v := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hwge (u v : ℝ) (hu : u ∈ Icc a a') (hv : v ∈ Icc b b') :
      1 ≤ w u v := by
    have hu' : 0 ≤ k * (u - a) := mul_nonneg hk.le (sub_nonneg.mpr hu.1)
    have hv' : 0 ≤ k * (v - b) := mul_nonneg hk.le (sub_nonneg.mpr hv.1)
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp hu') (Real.one_le_exp hv')
  let R : Set (ℝ × ℝ) := Icc a a' ×ˢ Icc b b'
  let T : Set ℝ := Set.range (fun p : R => F p.1.1 p.1.2 / w p.1.1 p.1.2)
  have hTne : T.Nonempty := by
    refine ⟨F a b / w a b, ?_⟩
    exact ⟨⟨(a, b), ⟨⟨le_rfl, haa'⟩, ⟨le_rfl, hbb'⟩⟩⟩, rfl⟩
  have hTbd : BddAbove T := by
    refine ⟨B, ?_⟩
    rintro z ⟨p, rfl⟩
    have hwp := hwge p.1.1 p.1.2 p.2.1 p.2.2
    exact (div_le_iff₀ (hwpos _ _)).mpr
      ((hFB _ p.2.1 _ p.2.2).trans (le_mul_of_one_le_right hB hwp))
  let S : ℝ := sSup T
  have hS0 : 0 ≤ S := by
    have hp : (F a b / w a b) ∈ T := by
      exact ⟨⟨(a, b), ⟨⟨le_rfl, haa'⟩, ⟨le_rfl, hbb'⟩⟩⟩, rfl⟩
    exact (div_nonneg (hF0 a ⟨le_rfl, haa'⟩ b ⟨le_rfl, hbb'⟩) (hwpos _ _).le).trans
      (le_csSup hTbd hp)
  have hFS (u : ℝ) (hu : u ∈ Icc a a') (v : ℝ) (hv : v ∈ Icc b b') :
      F u v ≤ S * w u v := by
    have hp : F u v / w u v ∈ T := by
      exact ⟨⟨(u, v), ⟨hu, hv⟩⟩, rfl⟩
    exact (div_le_iff₀ (hwpos _ _)).mp (le_csSup hTbd hp)
  have hIu (u : ℝ) (hu : u ∈ Icc a a') (v : ℝ) (hv : v ∈ Icc b b') :
      C * (∫ s in a..u, F s v) ≤ (C / k) * S * w u v := by
    have hmono : (∫ s in a..u, F s v) ≤
        ∫ s in a..u, S * w s v := by
      apply intervalIntegral.integral_mono_on hu.1 (hFu u hu v hv)
      · have hc : Continuous (fun s : ℝ => S * w s v) := by
          dsimp [w]
          fun_prop
        exact hc.intervalIntegrable a u
      · intro s hs
        exact hFS s ⟨hs.1, hs.2.trans hu.2⟩ v hv
    have hwei : k * (∫ s in a..u, w s v) ≤ w u v :=
      integral_weight_first_le
    have hdiv : (∫ s in a..u, w s v) ≤ w u v / k :=
      (le_div_iff₀ hk).mpr (by nlinarith only [hwei])
    calc
      C * (∫ s in a..u, F s v) ≤ C * (∫ s in a..u, S * w s v) :=
        mul_le_mul_of_nonneg_left hmono hC
      _ = C * (S * ∫ s in a..u, w s v) := by rw [intervalIntegral.integral_const_mul]
      _ ≤ C * (S * (w u v / k)) := by gcongr
      _ = (C / k) * S * w u v := by ring
  have hIv (u : ℝ) (hu : u ∈ Icc a a') (v : ℝ) (hv : v ∈ Icc b b') :
      C * (∫ t in b..v, F u t) ≤ (C / k) * S * w u v := by
    have hmono : (∫ t in b..v, F u t) ≤
        ∫ t in b..v, S * w u t := by
      apply intervalIntegral.integral_mono_on hv.1 (hFv u hu v hv)
      · have hc : Continuous (fun t : ℝ => S * w u t) := by
          dsimp [w]
          fun_prop
        exact hc.intervalIntegrable b v
      · intro t ht
        exact hFS u hu t ⟨ht.1, ht.2.trans hv.2⟩
    have hwei : k * (∫ t in b..v, w u t) ≤ w u v :=
      integral_weight_second_le
    have hdiv : (∫ t in b..v, w u t) ≤ w u v / k :=
      (le_div_iff₀ hk).mpr (by nlinarith only [hwei])
    calc
      C * (∫ t in b..v, F u t) ≤ C * (∫ t in b..v, S * w u t) :=
        mul_le_mul_of_nonneg_left hmono hC
      _ = C * (S * ∫ t in b..v, w u t) := by rw [intervalIntegral.integral_const_mul]
      _ ≤ C * (S * (w u v / k)) := by gcongr
      _ = (C / k) * S * w u v := by ring
  have hcoef : 2 * (C / k) ≤ (1 / 2 : ℝ) := by
    calc
      2 * (C / k) = (2 * C) / k := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hk).mpr (by dsimp [k]; nlinarith only [hC])
  have hpoint (u : ℝ) (hu : u ∈ Icc a a') (v : ℝ) (hv : v ∈ Icc b b') :
      F u v / w u v ≤ G + S / 2 := by
    have hmain := hineq u hu v hv
    have hsource := hgB u hu v hv
    have hterm : (C / k) * S * w u v + (C / k) * S * w u v ≤
        (S / 2) * w u v := by
      calc
        _ = (2 * (C / k)) * S * w u v := by ring
        _ ≤ (1 / 2) * S * w u v :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef hS0) (hwpos _ _).le
        _ = (S / 2) * w u v := by ring
    have hG' : G ≤ G * w u v := le_mul_of_one_le_right hG (hwge u v hu hv)
    apply (div_le_iff₀ (hwpos u v)).mpr
    calc
      F u v ≤ g u v + C * (∫ s in a..u, F s v) +
          C * (∫ t in b..v, F u t) := hmain
      _ ≤ G + (C / k) * S * w u v + (C / k) * S * w u v :=
        add_le_add (add_le_add hsource (hIu u hu v hv)) (hIv u hu v hv)
      _ ≤ (G + S / 2) * w u v := by nlinarith [hterm, hG']
  have hSle : S ≤ G + S / 2 := by
    apply csSup_le hTne
    rintro z ⟨p, rfl⟩
    exact hpoint _ p.2.1 _ p.2.2
  have hSbound : S ≤ 2 * G := by linarith
  intro u hu v hv
  calc
    F u v ≤ S * w u v := hFS u hu v hv
    _ ≤ (2 * G) * w u v := mul_le_mul_of_nonneg_right hSbound (hwpos _ _).le
    _ = 2 * G * (Real.exp ((4 * C + 1) * (u - a)) *
      Real.exp ((4 * C + 1) * (v - b))) := by rfl

/-- The supremum of a bounded Volterra subsolution is controlled explicitly by
the supremum of its source on the rectangle. -/
theorem csSup_two_variable_volterra_le {a a' b b' C B G : ℝ}
    {F g : ℝ → ℝ → ℝ}
    (haa' : a ≤ a') (hbb' : b ≤ b') (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hg0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ g u v)
    (hgB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', g u v ≤ G)
    (hF0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F u v)
    (hFB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v ≤ B)
    (hFu : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F s v) volume a u)
    (hFv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F u t) volume b v)
    (hineq : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      F u v ≤ g u v + C * (∫ s in a..u, F s v) +
        C * (∫ t in b..v, F u t)) :
    sSup (Set.range (fun p : Icc a a' ×ˢ Icc b b' => F p.1.1 p.1.2)) ≤
      2 * sSup (Set.range (fun p : Icc a a' ×ˢ Icc b b' => g p.1.1 p.1.2)) *
        (Real.exp ((4 * C + 1) * (a' - a)) *
          Real.exp ((4 * C + 1) * (b' - b))) := by
  let R : Set (ℝ × ℝ) := Icc a a' ×ˢ Icc b b'
  let Sg : ℝ := sSup (Set.range (fun p : R => g p.1.1 p.1.2))
  have hgBd : BddAbove (Set.range (fun p : R => g p.1.1 p.1.2)) := by
    refine ⟨G, ?_⟩
    rintro z ⟨p, rfl⟩
    exact hgB _ p.2.1 _ p.2.2
  have hgS (u : ℝ) (hu : u ∈ Icc a a') (v : ℝ) (hv : v ∈ Icc b b') :
      g u v ≤ Sg :=
    le_csSup hgBd ⟨⟨(u, v), ⟨hu, hv⟩⟩, rfl⟩
  have hSg0 : 0 ≤ Sg :=
    (hg0 a ⟨le_rfl, haa'⟩ b ⟨le_rfl, hbb'⟩).trans
      (hgS a ⟨le_rfl, haa'⟩ b ⟨le_rfl, hbb'⟩)
  have hpoint := le_two_variable_volterra_exp haa' hbb' hC hB hSg0
    hF0 hFB hgS hFu hFv hineq
  have hk : 0 ≤ 4 * C + 1 := by linarith
  apply csSup_le
  · exact ⟨F a b, ⟨⟨(a, b), ⟨⟨le_rfl, haa'⟩, ⟨le_rfl, hbb'⟩⟩⟩, rfl⟩⟩
  rintro z ⟨p, rfl⟩
  have hu : p.1.1 ∈ Icc a a' := p.2.1
  have hv : p.1.2 ∈ Icc b b' := p.2.2
  have huExp : Real.exp ((4 * C + 1) * (p.1.1 - a)) ≤
      Real.exp ((4 * C + 1) * (a' - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hu.2]) hk)
  have hvExp : Real.exp ((4 * C + 1) * (p.1.2 - b)) ≤
      Real.exp ((4 * C + 1) * (b' - b)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hv.2]) hk)
  calc
    F p.1.1 p.1.2 ≤ 2 * Sg *
        (Real.exp ((4 * C + 1) * (p.1.1 - a)) *
          Real.exp ((4 * C + 1) * (p.1.2 - b))) := hpoint _ hu _ hv
    _ ≤ 2 * Sg * (Real.exp ((4 * C + 1) * (a' - a)) *
        Real.exp ((4 * C + 1) * (b' - b))) := by gcongr

/-- A bounded nonnegative solution of a homogeneous two-variable Volterra
inequality vanishes on its characteristic rectangle. -/
theorem eq_zero_of_le_two_variable_volterra {a a' b b' C B : ℝ}
    {F : ℝ → ℝ → ℝ}
    (haa' : a ≤ a') (hbb' : b ≤ b') (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F u v)
    (hFB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v ≤ B)
    (hFu : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F s v) volume a u)
    (hFv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F u t) volume b v)
    (hineq : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      F u v ≤ C * (∫ s in a..u, F s v) +
        C * (∫ t in b..v, F u t)) :
    ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v = 0 := by
  have h := le_two_variable_volterra_exp (F := F) (g := fun _ _ => 0)
    haa' hbb' hC hB le_rfl hF0 hFB (by simp) hFu hFv (by
      intro u hu v hv
      simpa only [zero_add] using hineq u hu v hv)
  intro u hu v hv
  have hle := h u hu v hv
  simp only [mul_zero, zero_mul] at hle
  exact le_antisymm hle (hF0 u hu v hv)

/-- If the Volterra inequality holds on a conull set of outgoing parameters,
the function vanishes at every point with a good outgoing parameter. No
continuity is needed for this conclusion. -/
theorem eq_zero_of_le_two_variable_volterra_ae {a a' b b' C B : ℝ}
    {F : ℝ → ℝ → ℝ} {P : Set ℝ}
    (haa' : a ≤ a') (hbb' : b ≤ b') (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hP : ∀ᵐ v : ℝ ∂volume, v ∈ P)
    (hF0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F u v)
    (hFB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v ≤ B)
    (hFu : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F s v) volume a u)
    (hFv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F u t) volume b v)
    (hineq : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', v ∈ P →
      F u v ≤ C * (∫ s in a..u, F s v) +
        C * (∫ t in b..v, F u t)) :
    ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', v ∈ P → F u v = 0 := by
  classical
  let F' : ℝ → ℝ → ℝ := fun u v => if v ∈ P then F u v else 0
  have hF'0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F' u v := by
    intro u hu v hv
    dsimp [F']
    split_ifs
    · exact hF0 u hu v hv
    · exact le_rfl
  have hF'B : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F' u v ≤ B := by
    intro u hu v hv
    dsimp [F']
    split_ifs
    · exact hFB u hu v hv
    · exact hB
  have hF'u : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F' s v) volume a u := by
    intro u hu v hv
    by_cases hvP : v ∈ P
    · simpa only [F', ite_eq_left hvP] using hFu u hu v hv
    · simp only [F', ite_eq_right hvP]
      exact intervalIntegrable_const
  have hF'v : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F' u t) volume b v := by
    intro u hu v hv
    apply (hFv u hu v hv).congr_ae
    apply ae_restrict_of_ae
    filter_upwards [hP] with t ht
    simp only [F', ite_eq_left ht]
  have hvertical (u v : ℝ) :
      (∫ t in b..v, F' u t) = ∫ t in b..v, F u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hP] with t ht _
    simp only [F', ite_eq_left ht]
  have hineq' : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      F' u v ≤ C * (∫ s in a..u, F' s v) +
        C * (∫ t in b..v, F' u t) := by
    intro u hu v hv
    by_cases hvP : v ∈ P
    · simpa only [F', ite_eq_left hvP, hvertical] using hineq u hu v hv hvP
    · have hI : 0 ≤ ∫ t in b..v, F' u t := by
        apply intervalIntegral.integral_nonneg hv.1
        intro t ht
        exact hF'0 u hu t ⟨ht.1, ht.2.trans hv.2⟩
      simpa only [F', ite_eq_right hvP, integral_zero, mul_zero, zero_add] using
        mul_nonneg hC hI
  have hzero := eq_zero_of_le_two_variable_volterra (F := F')
    haa' hbb' hC hB hF'0 hF'B hF'u hF'v hineq'
  intro u hu v hv hvP
  simpa only [F', ite_eq_left hvP] using hzero u hu v hv

/-- Continuity in the outgoing variable extends the conull-parameter conclusion
to the whole rectangle, provided the outgoing interval has positive length. -/
theorem eq_zero_of_le_two_variable_volterra_ae_of_continuousOn
    {a a' b b' C B : ℝ} {F : ℝ → ℝ → ℝ} {P : Set ℝ}
    (haa' : a ≤ a') (hbb' : b < b') (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hP : ∀ᵐ v : ℝ ∂volume, v ∈ P)
    (hF0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F u v)
    (hFB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v ≤ B)
    (hFu : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F s v) volume a u)
    (hFv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F u t) volume b v)
    (hcont : ∀ u ∈ Icc a a', ContinuousOn (F u) (Icc b b'))
    (hineq : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', v ∈ P →
      F u v ≤ C * (∫ s in a..u, F s v) +
        C * (∫ t in b..v, F u t)) :
    ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v = 0 := by
  have hgood := eq_zero_of_le_two_variable_volterra_ae haa' hbb'.le hC hB
    hP hF0 hFB hFu hFv hineq
  intro u hu v hv
  have hae : (fun t => F u t) =ᵐ[volume.restrict (Icc b b')] (fun _ => (0 : ℝ)) := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hP] with t htP ht
    exact hgood u hu t ht htP
  exact (MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hbb') hae
    (hcont u hu) continuousOn_const) hv

end intervalIntegral

end
