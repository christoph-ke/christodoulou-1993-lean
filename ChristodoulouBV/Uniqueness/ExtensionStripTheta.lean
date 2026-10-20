module

public import ChristodoulouBV.Uniqueness.ExtensionStripAxis
import ChristodoulouBV.BVSolution.Geometry

/-!
# The outgoing theta ratio estimate on the enlarged domain

The outgoing ray is integrated from its axis endpoint. Its `α′` bound must
hold on the entire ray, including the part below the old/new seam.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem outgoing_radius_power_integral_eq_local
    {R L : ℝ → ℝ} {a b δ : ℝ} (hab : a < b)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hR : ContinuousOn R (Icc a b))
    (hL : ContinuousOn L (Icc a b))
    (hR0 : R a = 0)
    (hRpos : ∀ s ∈ Ioo a b, 0 < R s)
    (hD : ∀ s ∈ Ioo a b, HasDerivAt R (L s) s) :
    (∫ s in a..b, (R s)^(1 - δ) * L s) =
      (R b)^(2 - δ) / (2 - δ) := by
  let F : ℝ → ℝ := fun s => (R s)^(2 - δ) / (2 - δ)
  let G : ℝ → ℝ := fun s => (R s)^(1 - δ) * L s
  have hexp : 0 ≤ 2 - δ := by linarith
  have hexp' : 0 ≤ 1 - δ := by linarith
  have hFC : ContinuousOn F (Icc a b) :=
    (hR.rpow_const (fun _ _ => Or.inr hexp)).div_const _
  have hGC : ContinuousOn G (Icc a b) :=
    (hR.rpow_const (fun _ _ => Or.inr hexp')).mul hL
  have hGI : IntervalIntegrable G volume a b :=
    hGC.intervalIntegrable_of_Icc hab.le
  have hderiv : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s := by
    intro s hs
    have hr := hRpos s hs
    have h := (Real.hasDerivAt_rpow_const
      (p := 2 - δ) (Or.inl (ne_of_gt hr))).comp s (hD s hs)
    have h' := h.div_const (2 - δ)
    have hden : 2 - δ ≠ 0 := by linarith
    have heq : ((2 - δ) * (R s)^(2 - δ - 1) * L s) / (2 - δ) = G s := by
      dsimp [G]
      have hexpEq : 2 - δ - 1 = 1 - δ := by ring
      rw [hexpEq]
      field_simp
    simpa only [F, G, Function.comp_apply, heq] using h'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab.le hFC hderiv hGI
  have hF0 : F a = 0 := by
    dsimp [F]
    rw [hR0, Real.zero_rpow (by linarith : 2 - δ ≠ 0)]
    simp
  change (∫ s in a..b, G s) = F b - F a at hFTC
  simpa only [hF0, sub_zero, F, G] using hFTC

/-- The full-ray form of (5.16), with exponent `1/2` and coefficient `2/3`.
The weighted bound covers both sides of `vStar` through the entire ray. -/
theorem strip_theta_ratio_le
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    {u v A : ℝ} (_hu : 0 < u)
    (hp : (u, v) ∈ extensionWorkingDomain u₁ top)
    (hA : ∀ s ∈ Ioc u v,
      (T.r u s) ^ ((1 : ℝ) / 2) *
        |deriv (fun t => T.alpha u t / T.lam u t) s / T.lam u s| ≤ A) :
    |T.theta u v / T.lam u v| ≤
      ((2 : ℝ) / 3) * A * (T.r u v) ^ ((1 : ℝ) / 2) := by
  let R : ℝ → ℝ := fun s => ∫ t in u..s, T.lam u t
  let Q : ℝ → ℝ := fun s => T.alpha u s / T.lam u s
  let L : ℝ → ℝ := fun s => T.lam u s
  let P : ℝ → ℝ := fun s => deriv Q s / L s
  let δ : ℝ := (1 : ℝ) / 2
  have huv : u < v := hp.2.1
  have hδ : 0 < δ := by dsimp [δ]; norm_num
  have hδ1 : δ < 1 := by dsimp [δ]; norm_num
  have haxis : (u, u) ∈ closure (extensionWorkingDomain u₁ top) :=
    H.solution.development.axis_mem hp
  have hmap (s : ℝ) (hs : s ∈ Icc u v) :
      (u, s) ∈ closure (extensionWorkingDomain u₁ top) := by
    rcases eq_or_lt_of_le hs.1 with heq | hlt
    · subst s
      exact haxis
    · exact subset_closure
        (H.solution.development.outgoing_mem hp hlt hs.2)
  have hpair : ContDiff ℝ 1 (fun s : ℝ => (u, s)) :=
    contDiff_const.prodMk contDiff_id
  have hQc1 : ContDiffOn ℝ 1 Q (Icc u v) :=
    (alpha_div_lam_contDiffOn_closure H).comp hpair.contDiffOn hmap
  have hL : ContinuousOn L (Icc u v) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hLint : IntervalIntegrable L volume u v :=
    hL.intervalIntegrable_of_Icc huv.le
  have hRAC : AbsolutelyContinuousOnInterval R u v := by
    exact hLint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hRcont : ContinuousOn R (Icc u v) := by
    simpa only [uIcc_of_le huv.le] using hRAC.continuousOn
  have hQAC : AbsolutelyContinuousOnInterval Q u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv.le] using hQc1
  have hR0 : R u = 0 := by simp [R]
  have hReq : ∀ s ∈ Ioc u v, R s = T.r u s := by
    intro s hs
    exact (radius_eq_outgoing_lam_integral_of_c1_domain H
      (H.solution.development.outgoing_mem hp hs.1 hs.2)).symm
  have hRpos : ∀ s ∈ Ioc u v, 0 < R s := by
    intro s hs
    rw [hReq s hs]
    exact H.solution.radius_pos (u, s)
      (H.solution.development.outgoing_mem hp hs.1 hs.2)
  have hRderiv : ∀ s ∈ Ioo u v, HasDerivAt R (L s) s := by
    intro s hs
    have hLint' : IntervalIntegrable L volume u s :=
      (hL.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le
    have hLat : ContinuousAt L s := hL.continuousAt (Icc_mem_nhds hs.1 hs.2)
    have hMeas : StronglyMeasurableAtFilter L (𝓝 s) :=
      (hL.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter
        isOpen_Ioo s hs
    exact intervalIntegral.integral_hasDerivAt_right hLint' hMeas hLat
  have hRderivEq : ∀ s ∈ Ioo u v, deriv R s = L s :=
    fun s hs => (hRderiv s hs).deriv
  have hαInt : (∫ s in u..v, deriv R s * Q s) =
      ∫ s in u..v, T.alpha u s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume v] with s hne hs
    have hsIoc : s ∈ Ioc u v := by
      simpa only [uIoc_of_le huv.le] using hs
    have hs' : s ∈ Ioo u v :=
      ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hne⟩
    rw [hRderivEq s hs']
    dsimp [L, Q]
    have hlam : T.lam u s ≠ 0 := ne_of_gt
      (H.solution.lam_pos (u, s)
        (H.solution.development.outgoing_mem hp hs'.1 hs'.2.le))
    field_simp [hlam]
  have hIBP := hRAC.integral_mul_deriv_eq_deriv_mul hQAC
  have hIBP' : (∫ s in u..v, R s * deriv Q s) =
      (T.r u v) * Q v - ∫ s in u..v, T.alpha u s := by
    rw [hReq v (right_mem_Ioc.mpr huv), hR0, zero_mul, sub_zero, hαInt] at hIBP
    exact hIBP
  have hr := H.solution.radius_pos (u, v) hp
  have htheta : T.theta u v / T.lam u v =
      (∫ s in u..v, R s * deriv Q s) / T.r u v := by
    rw [theta_ratio_axis_identity_of_c1_domain H hp, hIBP']
    dsimp [Q]
    field_simp [hr.ne']
  have hA0 : 0 ≤ A := by
    have hsample := hA v (right_mem_Ioc.mpr huv)
    exact (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans hsample
  have hPower := outgoing_radius_power_integral_eq_local huv hδ hδ1
    hRcont hL hR0
    (fun s hs => hRpos s ⟨hs.1, hs.2.le⟩) hRderiv
  have hWint : IntervalIntegrable (fun s => (R s) ^ (1 - δ) * L s)
      volume u v := by
    have hpow : ContinuousOn (fun s => (R s) ^ (1 - δ)) (Icc u v) :=
      hRcont.rpow_const (fun _ _ => Or.inr (by linarith))
    exact (hpow.mul hL).intervalIntegrable_of_Icc huv.le
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u v →
      ‖R s * deriv Q s‖ ≤ A * ((R s) ^ (1 - δ) * L s) := by
    filter_upwards [Measure.ae_ne volume v] with s hne hsIoc
    have hs : s ∈ Ioo u v := ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hne⟩
    have hr_s := hRpos s hsIoc
    have hlam := H.solution.lam_pos (u, s)
      (H.solution.development.outgoing_mem hp hs.1 hs.2.le)
    have hbound := hA s hsIoc
    have hQprime : deriv Q s = L s * P s := by
      dsimp [P, L]
      field_simp [hlam.ne']
    have hpowMul : (R s) ^ (1 - δ) * (R s) ^ δ = R s := by
      rw [← Real.rpow_add hr_s]
      calc
        (R s) ^ (1 - δ + δ) = (R s) ^ (1 : ℝ) := by congr 1; ring
        _ = R s := Real.rpow_one _
    have hbound' : (R s) ^ δ * |P s| ≤ A := by
      simpa only [hReq s hsIoc, P, Q, L, δ] using hbound
    rw [hQprime, Real.norm_eq_abs, abs_mul, abs_of_pos hr_s,
      abs_mul, abs_of_pos hlam]
    calc
      R s * (L s * |P s|) =
          ((R s) ^ (1 - δ) * L s) * ((R s) ^ δ * |P s|) := by
            calc
              R s * (L s * |P s|) =
                  ((R s) ^ (1 - δ) * (R s) ^ δ) * (L s * |P s|) := by
                    rw [hpowMul]
              _ = ((R s) ^ (1 - δ) * L s) * ((R s) ^ δ * |P s|) := by
                    ring
      _ ≤ ((R s) ^ (1 - δ) * L s) * A :=
        mul_le_mul_of_nonneg_left hbound'
          (mul_nonneg (Real.rpow_nonneg hr_s.le _) hlam.le)
      _ = A * ((R s) ^ (1 - δ) * L s) := mul_comm _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le huv.le hmaj
    (hWint.const_mul A)
  have hIntBound : |∫ s in u..v, R s * deriv Q s| ≤
      A * ((T.r u v) ^ (2 - δ) / (2 - δ)) := by
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      hPower, hReq v (right_mem_Ioc.mpr huv)] using hnorm
  rw [htheta, abs_div, abs_of_pos hr]
  have hden : 0 < 2 - δ := by linarith
  have hpowEq : (T.r u v) ^ (2 - δ) =
      (T.r u v) ^ (1 - δ) * T.r u v := by
    calc
      (T.r u v) ^ (2 - δ) = (T.r u v) ^ ((1 - δ) + 1) := by congr 1; ring
      _ = (T.r u v) ^ (1 - δ) * (T.r u v) ^ (1 : ℝ) :=
        Real.rpow_add hr _ _
      _ = (T.r u v) ^ (1 - δ) * T.r u v := by rw [Real.rpow_one]
  calc
    |∫ s in u..v, R s * deriv Q s| / T.r u v
        ≤ (A * ((T.r u v) ^ (2 - δ) / (2 - δ))) / T.r u v :=
          div_le_div_of_nonneg_right hIntBound hr.le
    _ = ((2 : ℝ) / 3) * A * (T.r u v) ^ ((1 : ℝ) / 2) := by
      rw [hpowEq]
      dsimp [δ]
      field_simp
      norm_num
      ring

end ChristodoulouBV.Uniqueness

end
