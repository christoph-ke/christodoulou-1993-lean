module

public import ChristodoulouBV.BVSolution.AxisExponential
public import ChristodoulouBV.BVSolution.IncomingAxis
public import ChristodoulouBV.BVSolution.PrelocalFieldBounds
public import ChristodoulouBV.Uniqueness.Triangle

/-!
# Axis integrals on augmented comparison triangles

An incoming terminal axis is available only when the entire half-open
characteristic is contained in the development. The augmented triangle
provides precisely that access.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The fixed pair has one baseline field bound on every full augmented
comparison triangle. Its witnesses are chosen before preliminary or final
smallness, the compact top, and the localization width. -/
theorem preloc_coefficient_bounds
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w : ℝ} (href : (0, w) ∈ U₁ ∩ U₂)
    (hdata : S₁.phi 0 w = S₂.phi 0 w) :
    ∃ c C₀ : ℝ, 0 < c ∧ 0 ≤ C₀ ∧
      ∀ a b u v, Uniqueness.triangle a b ⊆ U₁ ∩ U₂ →
        (u, v) ∈ Uniqueness.triangle a b →
        ∀ S : Fields, (S = S₁ ∨ S = S₂) →
          c ≤ S.lam u v ∧ S.lam u v ≤ C₀ ∧
          c ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₀ ∧
          |S.phi u v| ≤ C₀ ∧ |S.theta u v| ≤ C₀ ∧
          |S.zeta u v| ≤ C₀ :=
  exists_pair_preloc_field_bounds h₁ h₂ href hdata

/-- The baseline bounds control the one-sided expansion trace. The outgoing
and incoming scalar amplitudes have the zero traces required by the local
comparison on a full triangle. -/
theorem preloc_axis_traces
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w : ℝ} (href : (0, w) ∈ U₁ ∩ U₂)
    (hdata : S₁.phi 0 w = S₂.phi 0 w) :
    ∃ c C₀ : ℝ, 0 < c ∧ 0 ≤ C₀ ∧
      ∀ a b u v, Uniqueness.triangle a b ⊆ U₁ ∩ U₂ →
        (u, v) ∈ Uniqueness.triangle a b →
        ∀ S : Fields, (S = S₁ ∨ S = S₂) →
          ∃ L P : ℝ, c ≤ L ∧ L ≤ C₀ ∧ |P| ≤ C₀ ∧
            Tendsto (S.lam u) (𝓝[>] u) (𝓝 L) ∧
            Tendsto (S.nu u) (𝓝[>] u) (𝓝 (-L)) ∧
            Tendsto (S.phi u) (𝓝[>] u) (𝓝 P) ∧
            Tendsto (S.alpha u) (𝓝[>] u) (𝓝 (L * P)) ∧
            Tendsto (S.beta u) (𝓝[>] u) (𝓝 (-(L * P))) ∧
            Tendsto (S.theta u) (𝓝[>] u) (𝓝 (0 : ℝ)) ∧
            Tendsto (fun s => S.zeta s v) (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  obtain ⟨c, C₀, hc, hC₀, hfield⟩ :=
    h₁.preloc_coefficient_bounds h₂ href hdata
  refine ⟨c, C₀, hc, hC₀, ?_⟩
  intro a b u v hT huv S hS
  have hLamBound : ∀ t ∈ Ioc u v,
      c ≤ S.lam u t ∧ S.lam u t ≤ C₀ := by
    intro t ht
    have hut : (u, t) ∈ Uniqueness.triangle a b :=
      (Uniqueness.mem_triangle).2
        ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    have hb := hfield a b u t hT hut S hS
    exact ⟨hb.1, hb.2.1⟩
  have hPhiBound : ∀ t ∈ Ioc u v, |S.phi u t| ≤ C₀ := by
    intro t ht
    have hut : (u, t) ∈ Uniqueness.triangle a b :=
      (Uniqueness.mem_triangle).2
        ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    exact (hfield a b u t hT hut S hS).2.2.2.2.1
  have hcore {U : Set (ℝ × ℝ)} (h : IsBVSolution U S)
      (hSU : (u, v) ∈ U)
      (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
      ∃ L P : ℝ, c ≤ L ∧ L ≤ C₀ ∧ |P| ≤ C₀ ∧
        Tendsto (S.lam u) (𝓝[>] u) (𝓝 L) ∧
        Tendsto (S.nu u) (𝓝[>] u) (𝓝 (-L)) ∧
        Tendsto (S.phi u) (𝓝[>] u) (𝓝 P) ∧
        Tendsto (S.alpha u) (𝓝[>] u) (𝓝 (L * P)) ∧
        Tendsto (S.beta u) (𝓝[>] u) (𝓝 (-(L * P))) ∧
        Tendsto (S.theta u) (𝓝[>] u) (𝓝 (0 : ℝ)) ∧
        Tendsto (fun s => S.zeta s v) (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    obtain ⟨L, hLam⟩ := h.exists_lam_axis_limit_out hSU
    obtain ⟨P, hPhi⟩ := h.exists_phi_axis_limit_out hSU
    have hlow : ∀ᶠ t in 𝓝[>] u, c ≤ S.lam u t := by
      filter_upwards [Ioo_mem_nhdsGT huv.2.1] with t ht
      exact (hLamBound t ⟨ht.1, ht.2.le⟩).1
    have hupp : ∀ᶠ t in 𝓝[>] u, S.lam u t ≤ C₀ := by
      filter_upwards [Ioo_mem_nhdsGT huv.2.1] with t ht
      exact (hLamBound t ⟨ht.1, ht.2.le⟩).2
    have hLlo : c ≤ L :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hLam hlow
    have hLhi : L ≤ C₀ := le_of_tendsto hLam hupp
    have hphiBound : ∀ᶠ t in 𝓝[>] u, |S.phi u t| ≤ C₀ := by
      filter_upwards [Ioo_mem_nhdsGT huv.2.1] with t ht
      exact hPhiBound t ⟨ht.1, ht.2.le⟩
    have hPbound : |P| ≤ C₀ := le_of_tendsto hPhi.abs hphiBound
    have haxis : Tendsto (fun t => S.nu u t + S.lam u t)
        (𝓝[>] u) (𝓝 (0 : ℝ)) := by
      simpa only [h.solution.development.axis_filter_eq hSU] using
        h.item2 u (h.solution.development.axis_mem hSU)
    have hNu : Tendsto (S.nu u) (𝓝[>] u) (𝓝 (-L)) := by
      simpa only [add_sub_cancel_right, zero_sub] using haxis.sub hLam
    have hTheta := h.theta_tendsto_zero_axis_out hSU
    have hAlpha : Tendsto (S.alpha u) (𝓝[>] u) (𝓝 (L * P)) := by
      have heq : S.alpha u =
          fun t => S.theta u t + S.lam u t * S.phi u t := by
        funext t
        dsimp [Fields.theta]
        ring
      rw [heq]
      simpa only [zero_add] using hTheta.add (hLam.mul hPhi)
    have hbetaAxis : Tendsto (fun t => S.alpha u t + S.beta u t)
        (𝓝[>] u) (𝓝 (0 : ℝ)) := by
      simpa only [h.solution.development.axis_filter_eq hSU] using
        h.item6 u (h.solution.development.axis_mem hSU)
    have hBeta : Tendsto (S.beta u) (𝓝[>] u) (𝓝 (-(L * P))) := by
      simpa only [add_sub_cancel_left, zero_sub] using hbetaAxis.sub hAlpha
    exact ⟨L, P, hLlo, hLhi, hPbound, hLam, hNu, hPhi, hAlpha, hBeta,
      hTheta,
      h.zeta_tendsto_zero_axis_in_of_half_open_access huv.2.1 haccess⟩
  rcases hS with rfl | rfl
  · exact hcore h₁ (hT huv).1
      (fun s hs => (hT ((Uniqueness.mem_triangle).2
        ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)).1)
  · exact hcore h₂ (hT huv).2
      (fun s hs => (hT ((Uniqueness.mem_triangle).2
        ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)).2)

/-- An integrable primitive with a zero missing left trace starts at the
excluded endpoint without a boundary constant. -/
theorem primitive_eq_integral_of_left_trace
    {F g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hInt : IntervalIntegrable g volume a b)
    (hprim : ∀ x ∈ Ioo a b, IntervalPrimitive F g x b)
    (htrace : Tendsto F (𝓝[>] a) (𝓝 (0 : ℝ))) :
    F b = ∫ t in a..b, g t := by
  let G : ℝ → ℝ := fun x => ∫ t in x..b, g t
  have hAC : AbsolutelyContinuousOnInterval
      (fun x => ∫ t in a..x, g t) a b :=
    hInt.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hright : Tendsto (fun x : ℝ => x) (𝓝[>] a) (𝓝[Icc a b] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsGT hab)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)⟩
  have hleftInt : Tendsto (fun x => ∫ t in a..x, g t)
      (𝓝[>] a) (𝓝 (0 : ℝ)) := by
    have hc : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hAC.continuousOn
    have hh := (hc.continuousWithinAt
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)).tendsto.comp hright
    simpa only [Function.comp_def, intervalIntegral.integral_same] using hh
  have hrightInt : Tendsto G (𝓝[>] a) (𝓝 (∫ t in a..b, g t)) := by
    have heq : ∀ᶠ x in 𝓝[>] a,
        G x = (∫ t in a..b, g t) - ∫ t in a..x, g t := by
      filter_upwards [Ioo_mem_nhdsGT hab] with x hx
      have h₁ : IntervalIntegrable g volume a x :=
        hInt.mono_set (by
          rw [uIcc_of_le hab.le, uIcc_of_le hx.1.le]
          exact Icc_subset_Icc_right hx.2.le)
      have h₂ : IntervalIntegrable g volume x b :=
        hInt.mono_set (by
          rw [uIcc_of_le hab.le, uIcc_of_le hx.2.le]
          exact Icc_subset_Icc_left hx.1.le)
      have hh := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
      dsimp [G]
      linarith
    have hlim : Tendsto
        (fun x => (∫ t in a..b, g t) - ∫ t in a..x, g t)
        (𝓝[>] a) (𝓝 (∫ t in a..b, g t)) := by
      simpa using tendsto_const_nhds.sub hleftInt
    exact hlim.congr' (heq.mono fun _ he => he.symm)
  have hprim' : ∀ᶠ x in 𝓝[>] a, F b - F x = G x := by
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact (hprim x hx).2
  have hlimF : Tendsto (fun x => F b - F x)
      (𝓝[>] a) (𝓝 (F b)) := by
    simpa using tendsto_const_nhds.sub htrace
  exact tendsto_nhds_unique
    (hlimF.congr' hprim') hrightInt

/-- An integrable primitive with a zero missing right trace has the negative
integral as its initial value. -/
theorem primitive_eq_integral_of_right_trace
    {F g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hInt : IntervalIntegrable g volume a b)
    (hprim : ∀ x ∈ Ioo a b, IntervalPrimitive F g a x)
    (htrace : Tendsto F (𝓝[<] b) (𝓝 (0 : ℝ))) :
    F a = -(∫ t in a..b, g t) := by
  have hAC : AbsolutelyContinuousOnInterval
      (fun x => ∫ t in a..x, g t) a b :=
    hInt.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hleft : Tendsto (fun x : ℝ => x) (𝓝[<] b) (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT hab)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)⟩
  have hIntLim : Tendsto (fun x => ∫ t in a..x, g t)
      (𝓝[<] b) (𝓝 (∫ t in a..b, g t)) := by
    have hc : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hAC.continuousOn
    exact (hc.continuousWithinAt
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)).tendsto.comp hleft
  have hprim' : ∀ᶠ x in 𝓝[<] b,
      F x - F a = ∫ t in a..x, g t := by
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (hprim x hx).2
  have hlimF : Tendsto (fun x => F x - F a)
      (𝓝[<] b) (𝓝 (-F a)) := by
    simpa using htrace.sub_const (F a)
  have heq : -F a = ∫ t in a..b, g t :=
    tendsto_nhds_unique (hlimF.congr' hprim') hIntLim
  linarith

/-- A uniformly bounded density that is integrable on every compact
subinterval away from the missing left endpoint is integrable on the full
half-open interval. -/
theorem interval_integrable_of_bounded_left
    {g : ℝ → ℝ} {a b M : ℝ} (hab : a < b) (hM : 0 ≤ M)
    (hlocal : ∀ x ∈ Ioc a b, IntervalIntegrable g volume x b)
    (hbound : ∀ x ∈ Ioc a b, |g x| ≤ M) :
    IntervalIntegrable g volume a b := by
  let x : ℕ → ℝ := fun n => a + (b - a) * (1 / ((n : ℝ) + 1))
  have hxa (n : ℕ) : a < x n := by
    dsimp [x]
    have hd : 0 < (b - a) * (1 / ((n : ℝ) + 1)) :=
      mul_pos (sub_pos.mpr hab) (one_div_pos.mpr (by positivity))
    linarith
  have hxb (n : ℕ) : x n ≤ b := by
    dsimp [x]
    have hp : 1 ≤ ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hone)]
  have hx : Tendsto x atTop (𝓝 a) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ha : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
    have hd : Tendsto (fun _ : ℕ => b - a) atTop (𝓝 (b - a)) :=
      tendsto_const_nhds
    simpa only [x, mul_zero, add_zero] using ha.add (hd.mul hzero)
  have hloc (n : ℕ) : IntegrableOn g (Ioc (x n) b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hxb n)).1
      (hlocal (x n) ⟨hxa n, hxb n⟩)
  have hnorm (n : ℕ) :
      ∫ t in Ioc (x n) b, ‖g t‖ ≤ M * (b - a) := by
    have hi : IntervalIntegrable g volume (x n) b :=
      hlocal (x n) ⟨hxa n, hxb n⟩
    have hmono : (∫ t in (x n)..b, ‖g t‖) ≤ ∫ _ in (x n)..b, M := by
      apply intervalIntegral.integral_mono_on (hxb n) hi.norm intervalIntegrable_const
      intro t ht
      simpa only [Real.norm_eq_abs] using
        hbound t ⟨(hxa n).trans_le ht.1, ht.2⟩
    rw [intervalIntegral.integral_of_le (hxb n)] at hmono
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    have hdiff : b - x n ≤ b - a := by linarith [hxa n]
    calc
      (∫ t in Ioc (x n) b, ‖g t‖) ≤ (b - x n) * M := hmono
      _ ≤ (b - a) * M := mul_le_mul_of_nonneg_right hdiff hM
      _ = M * (b - a) := mul_comm _ _
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
    (integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hloc hx
      (Filter.Eventually.of_forall hnorm))

/-- The corresponding endpoint integrability result for a missing right
endpoint. -/
theorem interval_integrable_of_bounded_right
    {g : ℝ → ℝ} {a b M : ℝ} (hab : a < b) (hM : 0 ≤ M)
    (hlocal : ∀ x ∈ Ico a b, IntervalIntegrable g volume a x)
    (hbound : ∀ x ∈ Ico a b, |g x| ≤ M) :
    IntervalIntegrable g volume a b := by
  let x : ℕ → ℝ := fun n => b - (b - a) * (1 / ((n : ℝ) + 1))
  have hxa (n : ℕ) : a ≤ x n := by
    dsimp [x]
    have hp : 1 ≤ ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hone)]
  have hxb (n : ℕ) : x n < b := by
    dsimp [x]
    have hd : 0 < (b - a) * (1 / ((n : ℝ) + 1)) :=
      mul_pos (sub_pos.mpr hab) (one_div_pos.mpr (by positivity))
    linarith
  have hx : Tendsto x atTop (𝓝 b) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hb : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
    have hd : Tendsto (fun _ : ℕ => b - a) atTop (𝓝 (b - a)) :=
      tendsto_const_nhds
    simpa only [x, mul_zero, sub_zero] using hb.sub (hd.mul hzero)
  have hloc (n : ℕ) : IntegrableOn g (Ioc a (x n)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hxa n)).1
      (hlocal (x n) ⟨hxa n, hxb n⟩)
  have hnorm (n : ℕ) :
      ∫ t in Ioc a (x n), ‖g t‖ ≤ M * (b - a) := by
    have hi : IntervalIntegrable g volume a (x n) :=
      hlocal (x n) ⟨hxa n, hxb n⟩
    have hmono : (∫ t in a..(x n), ‖g t‖) ≤ ∫ _ in a..(x n), M := by
      apply intervalIntegral.integral_mono_on (hxa n) hi.norm intervalIntegrable_const
      intro t ht
      simpa only [Real.norm_eq_abs] using
        hbound t ⟨ht.1, ht.2.trans_lt (hxb n)⟩
    rw [intervalIntegral.integral_of_le (hxa n)] at hmono
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    have hdiff : x n - a ≤ b - a := by linarith [hxb n]
    calc
      (∫ t in Ioc a (x n), ‖g t‖) ≤ (x n - a) * M := hmono
      _ ≤ (b - a) * M := mul_le_mul_of_nonneg_right hdiff hM
      _ = M * (b - a) := mul_comm _ _
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
    (integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hloc hx
      (Filter.Eventually.of_forall hnorm))

/-- A point of a full augmented triangle has its entire incoming half-open
characteristic in the development. -/
theorem incoming_axis_access_of_triangle
    {U : Set (ℝ × ℝ)} {a b u v : ℝ}
    (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    ∀ s ∈ Ico u v, (s, v) ∈ U := by
  intro s hs
  apply hT
  exact (Uniqueness.mem_triangle).2
    ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩

/-- The incoming mass tends to zero along a full augmented triangle. -/
theorem incoming_mass_axis_trace_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    Tendsto (fun s => S.m s v) (𝓝[<] v) (𝓝 (0 : ℝ)) :=
  h.mass_tendsto_axis_in_of_half_open_access huv.2.1
    (incoming_axis_access_of_triangle hT huv)

/-- The full-triangle incoming mass integral has its zero terminal constant
fixed by the axis trace. -/
theorem incoming_mass_axis_integral_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    S.m u v = -(∫ s in u..v, massInDensity S s v) :=
  h.mass_eq_incoming_axis_integral_of_half_open_access huv.2.1
    (incoming_axis_access_of_triangle hT huv)

/-- On a full augmented triangle the incoming mass ratio tends to zero. -/
theorem mu_axis_incoming_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    Tendsto (fun s => 2 * S.m s v / S.r s v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) :=
  h.mass_ratio_tendsto_zero_axis_in_of_half_open_access huv.2.1
    (incoming_axis_access_of_triangle hT huv)

/-- The incoming mass-ratio limit is available on every nonempty incoming
slice of the triangle, including its initial edge. -/
theorem mu_axis_incoming_of_triangle_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (hav : a < v) (hvb : v < b) :
    Tendsto (fun s => 2 * S.m s v / S.r s v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) :=
  h.mu_axis_incoming_of_triangle hT
    ((Uniqueness.mem_triangle).2 ⟨le_rfl, hav, hvb⟩)

/-- The radius tends to zero along an accessible incoming characteristic. -/
theorem incoming_radius_axis_trace_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    Tendsto (fun s => S.r s v) (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  obtain ⟨K, _, hK⟩ := h.exists_uniform_radius_upper
  have hlow : ∀ᶠ s in 𝓝[<] v, 0 ≤ S.r s v := by
    filter_upwards [Ioo_mem_nhdsLT huv.2.1] with s hs
    exact (h.solution.radius_pos (s, v)
      (incoming_axis_access_of_triangle hT huv s ⟨hs.1.le, hs.2⟩)).le
  have hupp : ∀ᶠ s in 𝓝[<] v, S.r s v ≤ K * (v - s) := by
    filter_upwards [Ioo_mem_nhdsLT huv.2.1] with s hs
    exact hK s v (incoming_axis_access_of_triangle hT huv s ⟨hs.1.le, hs.2⟩)
  have hzero : Tendsto (fun s : ℝ => K * (v - s))
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[<] v) (𝓝 v) :=
      tendsto_id.mono_left inf_le_left
    have hconst : Tendsto (fun _ : ℝ => v) (𝓝[<] v) (𝓝 v) :=
      tendsto_const_nhds
    simpa only [sub_self, mul_zero] using
      ((hconst.sub hid).const_mul K)
  exact squeeze_zero' hlow hupp hzero

/-- The incoming scalar-radius primitive has zero terminal trace on a full
triangle. The scalar is bounded along the complete incoming slice by its BV
variation. -/
theorem incoming_scalar_radius_axis_trace_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    Tendsto (fun s => S.r s v * S.phi s v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  have hBV : BoundedVariationOn (fun s => S.phi s v)
      {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.2 v)
  obtain ⟨B, hB, hbound⟩ := hBV.exists_bound_on
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hlow : ∀ᶠ s in 𝓝[<] v, 0 ≤ |S.r s v * S.phi s v| :=
    Filter.Eventually.of_forall fun _ => abs_nonneg _
  have hupp : ∀ᶠ s in 𝓝[<] v,
      |S.r s v * S.phi s v| ≤ B * S.r s v := by
    filter_upwards [Ioo_mem_nhdsLT huv.2.1] with s hs
    have hsv := incoming_axis_access_of_triangle hT huv s ⟨hs.1.le, hs.2⟩
    have hr := h.solution.radius_pos (s, v) hsv
    rw [abs_mul, abs_of_pos hr]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left (hbound s hsv) hr.le)
  have hzero : Tendsto (fun s => B * S.r s v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (h.incoming_radius_axis_trace_of_triangle hT huv).const_mul B
  exact squeeze_zero' hlow hupp hzero

/-- Both incoming terminal primitive traces vanish, and the radius has a
uniform linear bound fixed globally before choosing a comparison triangle. -/
theorem incoming_radius_scalar_axis_trace
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ K : ℝ, ∀ a b u v, Uniqueness.triangle a b ⊆ U →
      (u, v) ∈ Uniqueness.triangle a b →
      S.r u v ≤ K * (v - u) ∧
      Tendsto (fun s => S.r s v) (𝓝[<] v) (𝓝 (0 : ℝ)) ∧
      Tendsto (fun s => S.r s v * S.phi s v)
        (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  obtain ⟨K, _, hK⟩ := h.exists_uniform_radius_upper
  refine ⟨K, ?_⟩
  intro a b u v hT huv
  exact ⟨hK u v (hT huv), h.incoming_radius_axis_trace_of_triangle hT huv,
    h.incoming_scalar_radius_axis_trace_of_triangle hT huv⟩

/-- A global radius upper bound remains valid on every comparison triangle,
with a constant chosen before its top or width. -/
theorem incoming_radius_linear_bound_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ K : ℝ, ∀ a b u v, Uniqueness.triangle a b ⊆ U →
      (u, v) ∈ Uniqueness.triangle a b → S.r u v ≤ K * (v - u) := by
  obtain ⟨K, _, hK⟩ := h.exists_uniform_radius_upper
  exact ⟨K, fun _ _ u v hT huv => hK u v (hT huv)⟩

/-- The outgoing radius is the full axis-to-point integral of `λ`. -/
theorem radius_eq_outgoing_axis_integral
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    S.r u v = ∫ t in u..v, S.lam u t := by
  have hlt := (h.solution.development.wedge huv).2
  obtain ⟨K, hK, _⟩ := h.exists_uniform_radius_upper
  have hKnonneg : 0 ≤ K := by
    have hr := h.solution.lam_pos (u, v) huv
    linarith [hK (u, v) huv]
  have hlocal : ∀ t ∈ Ioc u v,
      IntervalIntegrable (S.lam u) volume t v := by
    intro t ht
    exact (h.solution.radius_out u t v ht.2
      (h.solution.development.out_seg_subset huv ht.1 ht.2 le_rfl)).1
  have hbound : ∀ t ∈ Ioc u v, |S.lam u t| ≤ K := by
    intro t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2
    rw [abs_of_pos (h.solution.lam_pos (u, t) htU)]
    exact hK (u, t) htU
  have hInt : IntervalIntegrable (S.lam u) volume u v :=
    interval_integrable_of_bounded_left hlt hKnonneg hlocal hbound
  apply primitive_eq_integral_of_left_trace hlt hInt
  · intro t ht
    exact h.solution.radius_out u t v ht.2.le
      (h.solution.development.out_seg_subset huv ht.1 ht.2.le le_rfl)
  · exact h.radius_tendsto_axis_out huv

/-- On a full augmented triangle the incoming radius is the negative full
terminal integral of `ν`. -/
theorem radius_eq_incoming_axis_integral_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    S.r u v = -(∫ s in u..v, S.nu s v) := by
  obtain ⟨N, hN⟩ := h.nu_bounded_below
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have huU := hT huv
  have hNnonneg : 0 ≤ N := by
    have hn := h.nu_le_neg_lower hc hlam huU
    linarith [hN (u, v) huU]
  have haccess := incoming_axis_access_of_triangle hT huv
  have hlocal : ∀ s ∈ Ico u v,
      IntervalIntegrable (fun t => S.nu t v) volume u s := by
    intro s hs
    exact (h.solution.radius_in v u s hs.1
      (incoming_seg_subset_of_half_open_access hs.2 haccess)).1
  have hbound : ∀ s ∈ Ico u v, |S.nu s v| ≤ N := by
    intro s hs
    have hsU := haccess s hs
    rw [abs_of_neg ((h.nu_le_neg_lower hc hlam hsU).trans_lt
      (neg_lt_zero.mpr hc))]
    exact hN (s, v) hsU
  have hInt : IntervalIntegrable (fun s => S.nu s v) volume u v :=
    interval_integrable_of_bounded_right huv.2.1 hNnonneg hlocal hbound
  apply primitive_eq_integral_of_right_trace
    (F := fun s => S.r s v) huv.2.1 hInt
  · intro s hs
    exact h.solution.radius_in v u s hs.1.le
      (incoming_seg_subset_of_half_open_access hs.2 haccess)
  · exact h.incoming_radius_axis_trace_of_triangle hT huv

/-- The outgoing expansion is integrable on its complete axis-to-point
characteristic. -/
theorem lam_integrable_outgoing_axis
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntervalIntegrable (S.lam u) volume u v := by
  obtain ⟨K, hK, _⟩ := h.exists_uniform_radius_upper
  have hKnonneg : 0 ≤ K := by
    have hl := h.solution.lam_pos (u, v) huv
    linarith [hK (u, v) huv]
  apply interval_integrable_of_bounded_left
    (h.solution.development.wedge huv).2 hKnonneg
  · intro t ht
    exact (h.solution.radius_out u t v ht.2
      (h.solution.development.out_seg_subset huv ht.1 ht.2 le_rfl)).1
  · intro t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2
    rw [abs_of_pos (h.solution.lam_pos (u, t) htU)]
    exact hK (u, t) htU

/-- The incoming expansion is integrable up to the terminal axis on a full
augmented triangle. -/
theorem nu_integrable_incoming_axis_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    IntervalIntegrable (fun s => S.nu s v) volume u v := by
  obtain ⟨N, hN⟩ := h.nu_bounded_below
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have haccess := incoming_axis_access_of_triangle hT huv
  have hNnonneg : 0 ≤ N := by
    have hn := h.nu_le_neg_lower hc hlam (hT huv)
    linarith [hN (u, v) (hT huv)]
  apply interval_integrable_of_bounded_right huv.2.1 hNnonneg
  · intro s hs
    exact (h.solution.radius_in v u s hs.1
      (incoming_seg_subset_of_half_open_access hs.2 haccess)).1
  · intro s hs
    have hsU := haccess s hs
    rw [abs_of_neg ((h.nu_le_neg_lower hc hlam hsU).trans_lt
      (neg_lt_zero.mpr hc))]
    exact hN (s, v) hsU

/-- Subtracting the two outgoing axis primitives gives the exact difference
formula used in the comparison argument. -/
theorem radius_difference_eq_outgoing_axis_integral
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u v : ℝ} (hmem : (u, v) ∈ U₁ ∩ U₂) :
    S₁.r u v - S₂.r u v =
      ∫ t in u..v, (S₁.lam u t - S₂.lam u t) := by
  rw [h₁.radius_eq_outgoing_axis_integral hmem.1,
    h₂.radius_eq_outgoing_axis_integral hmem.2,
    intervalIntegral.integral_sub
      (h₁.lam_integrable_outgoing_axis hmem.1)
      (h₂.lam_integrable_outgoing_axis hmem.2)]

/-- Subtracting the two incoming terminal primitives gives the exact
difference formula on a common full augmented triangle. -/
theorem radius_difference_eq_incoming_axis_integral_of_triangle
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U₁ ∩ U₂)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    S₁.r u v - S₂.r u v =
      -(∫ s in u..v, (S₁.nu s v - S₂.nu s v)) := by
  have hT₁ : Uniqueness.triangle a b ⊆ U₁ := fun p hp => (hT hp).1
  have hT₂ : Uniqueness.triangle a b ⊆ U₂ := fun p hp => (hT hp).2
  rw [h₁.radius_eq_incoming_axis_integral_of_triangle hT₁ huv,
    h₂.radius_eq_incoming_axis_integral_of_triangle hT₂ huv,
    intervalIntegral.integral_sub
      (h₁.nu_integrable_incoming_axis_of_triangle hT₁ huv)
      (h₂.nu_integrable_incoming_axis_of_triangle hT₂ huv)]
  ring

/-- The outgoing scalar is recovered from the axis primitive for `rφ`. -/
theorem phi_eq_outgoing_alpha_integral
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    S.phi u v = (∫ t in u..v, S.alpha u t) / S.r u v := by
  have hlt := (h.solution.development.wedge huv).2
  obtain ⟨K, hK, _⟩ := h.exists_uniform_radius_upper
  have hKnonneg : 0 ≤ K := by
    have hl := h.solution.lam_pos (u, v) huv
    linarith [hK (u, v) huv]
  have hBVφ : BoundedVariationOn (S.phi u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.1 u)
  have hBVθ : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  obtain ⟨Bφ, hBφ, hφ⟩ := hBVφ.exists_bound_on
  obtain ⟨Bθ, hBθ, hθ⟩ := hBVθ.exists_bound_on
  have hbound : ∀ t ∈ Ioc u v, |S.alpha u t| ≤ Bθ + K * Bφ := by
    intro t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2
    have hlpos := h.solution.lam_pos (u, t) htU
    have hprod : |S.lam u t * S.phi u t| ≤ K * Bφ := by
      rw [abs_mul, abs_of_pos hlpos]
      calc
        S.lam u t * |S.phi u t| ≤ K * |S.phi u t| :=
          mul_le_mul_of_nonneg_right (hK (u, t) htU) (abs_nonneg _)
        _ ≤ K * Bφ := mul_le_mul_of_nonneg_left (hφ t htU) hKnonneg
    have heq : S.alpha u t = S.theta u t + S.lam u t * S.phi u t := by
      dsimp [Fields.theta]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans
      (add_le_add (hθ t htU) hprod)
  have hlocal : ∀ t ∈ Ioc u v,
      IntervalIntegrable (S.alpha u) volume t v := by
    intro t ht
    exact (h.solution.scalar_radius_out u t v ht.2
      (h.solution.development.out_seg_subset huv ht.1 ht.2 le_rfl)).1
  have hInt : IntervalIntegrable (S.alpha u) volume u v :=
    interval_integrable_of_bounded_left hlt
      (by positivity : 0 ≤ Bθ + K * Bφ) hlocal hbound
  have htrace : Tendsto (fun t => S.r u t * S.phi u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    obtain ⟨L, hφlim⟩ := h.exists_phi_axis_limit_out huv
    simpa only [zero_mul] using (h.radius_tendsto_axis_out huv).mul hφlim
  have heq : S.r u v * S.phi u v = ∫ t in u..v, S.alpha u t :=
    primitive_eq_integral_of_left_trace (F := fun t => S.r u t * S.phi u t)
      hlt hInt (by
        intro t ht
        exact h.solution.scalar_radius_out u t v ht.2.le
          (h.solution.development.out_seg_subset huv ht.1 ht.2.le le_rfl))
      htrace
  exact (eq_div_iff (ne_of_gt (h.solution.radius_pos (u, v) huv))).2
    (by simpa only [mul_comm] using heq)

/-- On a full augmented triangle the incoming scalar is recovered from the
terminal axis primitive for `rφ`. -/
theorem phi_eq_incoming_beta_integral_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : Uniqueness.triangle a b ⊆ U)
    (huv : (u, v) ∈ Uniqueness.triangle a b) :
    S.phi u v = -(∫ s in u..v, S.beta s v) / S.r u v := by
  obtain ⟨N, hN⟩ := h.nu_bounded_below
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have haccess := incoming_axis_access_of_triangle hT huv
  have hNnonneg : 0 ≤ N := by
    have huU := hT huv
    have hn := h.nu_le_neg_lower hc hlam huU
    linarith [hN (u, v) huU]
  have hBVφ : BoundedVariationOn (fun s => S.phi s v)
      {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.2 v)
  have hBVζ : BoundedVariationOn (fun s => S.zeta s v)
      {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item5.choose_spec.2 v)
  obtain ⟨Bφ, hBφ, hφ⟩ := hBVφ.exists_bound_on
  obtain ⟨Bζ, hBζ, hζ⟩ := hBVζ.exists_bound_on
  have hbound : ∀ s ∈ Ico u v, |S.beta s v| ≤ Bζ + N * Bφ := by
    intro s hs
    have hsU := haccess s hs
    have hnneg : S.nu s v < 0 :=
      (h.nu_le_neg_lower hc hlam hsU).trans_lt (neg_lt_zero.mpr hc)
    have hprod : |S.nu s v * S.phi s v| ≤ N * Bφ := by
      rw [abs_mul, abs_of_neg hnneg]
      calc
        -S.nu s v * |S.phi s v| ≤ N * |S.phi s v| :=
          mul_le_mul_of_nonneg_right (hN (s, v) hsU) (abs_nonneg _)
        _ ≤ N * Bφ := mul_le_mul_of_nonneg_left (hφ s hsU) hNnonneg
    have heq : S.beta s v = S.zeta s v + S.nu s v * S.phi s v := by
      dsimp [Fields.zeta]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (hζ s hsU) hprod)
  have hlocal : ∀ s ∈ Ico u v,
      IntervalIntegrable (fun t => S.beta t v) volume u s := by
    intro s hs
    exact (h.solution.scalar_radius_in v u s hs.1
      (incoming_seg_subset_of_half_open_access hs.2 haccess)).1
  have hInt : IntervalIntegrable (fun s => S.beta s v) volume u v :=
    interval_integrable_of_bounded_right huv.2.1
      (by positivity : 0 ≤ Bζ + N * Bφ) hlocal hbound
  have heq : S.r u v * S.phi u v =
      -(∫ s in u..v, S.beta s v) :=
    primitive_eq_integral_of_right_trace
      (F := fun s => S.r s v * S.phi s v) huv.2.1 hInt
      (by
        intro s hs
        exact h.solution.scalar_radius_in v u s hs.1.le
          (incoming_seg_subset_of_half_open_access hs.2 haccess))
      (h.incoming_scalar_radius_axis_trace_of_triangle hT huv)
  exact (eq_div_iff (ne_of_gt (h.solution.radius_pos (u, v) (hT huv)))).2
    (by simpa only [mul_comm] using heq)

end ChristodoulouBV.IsBVSolution

end
