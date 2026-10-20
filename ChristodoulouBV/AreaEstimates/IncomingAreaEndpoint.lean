module

public import ChristodoulouBV.AreaEstimates.IncomingAreaRhoFinite
import Mathlib.Tactic

/-!
# Axis and terminal limits for forward fiber estimates

A compact-interval estimate with a lower-axis boundary term extends to
the full open interval when that term vanishes at the axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- A forward interval estimate passes to both open endpoints without
assuming finiteness of the full right-hand integral. -/
theorem incoming_area_endpoint_lintegral_bound
    {a b : ℝ} (hab : a < b) {g f q : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hf : ∀ t, 0 ≤ f t)
    (hgi : ∀ x y, a < x → x < y → y < b → IntervalIntegrable g volume x y)
    (hfi : ∀ x y, a < x → x < y → y < b → IntervalIntegrable f volume x y)
    (hq : Tendsto q (𝓝[>] a) (𝓝 (0 : ℝ)))
    (hbound : ∀ x y, a < x → x < y → y < b →
      (∫ t in x..y, g t) ≤ |q x| + ∫ t in x..y, f t) :
    (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) ≤
      ∫⁻ t in Ioo a b, ENNReal.ofReal (f t) := by
  let d : ℕ → ℝ := fun n => (b - a) / ((n : ℝ) + 2)
  let x : ℕ → ℝ := fun n => a + d n
  let y : ℕ → ℝ := fun n => b - d n
  let E : ℕ → Set ℝ := fun n => Ioo (x n) (y n)
  have hdpos (n : ℕ) : 0 < d n := by
    dsimp [d]
    exact div_pos (sub_pos.mpr hab) (by positivity)
  have hdhalf (n : ℕ) : 2 * d n ≤ b - a := by
    dsimp [d]
    have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith only [this]
    have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hab.le)
    calc
      2 * ((b - a) / ((n : ℝ) + 2)) = (2 * (b - a)) / ((n : ℝ) + 2) := by ring
      _ ≤ b - a := (div_le_iff₀ hden).2 (by nlinarith only [hmul])
  have hx (n : ℕ) : a < x n := by dsimp [x]; linarith only [hdpos n]
  have hy (n : ℕ) : y n < b := by dsimp [y]; linarith only [hdpos n]
  have hxy (n : ℕ) : x n ≤ y n := by
    dsimp [x, y]
    linarith only [hdhalf n]
  have hdmono : Antitone d := by
    intro n m hnm
    have hden : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right hnm 2
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hab.le)
      (by positivity) hden
  have hxmono : Antitone x := by
    intro n m hnm
    dsimp [x]
    linarith only [hdmono hnm]
  have hymono : Monotone y := by
    intro n m hnm
    exact sub_le_sub_left (hdmono hnm) b
  have hEmono : Monotone E := by
    intro n m hnm t ht
    exact ⟨lt_of_le_of_lt (hxmono hnm) ht.1,
      ht.2.trans_le (hymono hnm)⟩
  have hdlim : Tendsto d atTop (𝓝 (0 : ℝ)) := by
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hfrac : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
        atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (tendsto_const_nhds (x := (0 : ℝ))) hbase
      · intro n
        positivity
      · intro n
        have hle : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by norm_num
        exact one_div_le_one_div_of_le (by positivity) hle
    have h := hfrac.const_mul (b - a)
    simpa only [d, div_eq_mul_inv, one_mul, mul_zero] using h
  have hxlim : Tendsto x atTop (𝓝 a) := by
    simpa only [x, add_zero] using (tendsto_const_nhds (x := a)).add hdlim
  have hylim : Tendsto y atTop (𝓝 b) := by
    simpa only [y, sub_zero] using (tendsto_const_nhds (x := b)).sub hdlim
  have hxwithin : Tendsto x atTop (𝓝[>] a) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Eventually.of_forall fun n => hx n⟩
  have hqlim : Tendsto (fun n => |q (x n)|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, abs_zero] using (hq.comp hxwithin).abs
  have hcover : (⋃ n, E n) = Ioo a b := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, htn⟩ := Set.mem_iUnion.mp ht
      exact ⟨(hx n).trans htn.1, htn.2.trans (hy n)⟩
    · intro ht
      have hxev : ∀ᶠ n in atTop, x n < t :=
        (tendsto_order.mp hxlim).2 _ ht.1
      have hyev : ∀ᶠ n in atTop, t < y n :=
        (tendsto_order.mp hylim).1 _ ht.2
      obtain ⟨n, hxn, hyn⟩ := (hxev.and hyev).exists
      exact Set.mem_iUnion.mpr ⟨n, hxn, hyn⟩
  have hdir : Directed (· ⊆ ·) E := by
    intro n m
    exact ⟨max n m, hEmono (le_max_left n m), hEmono (le_max_right n m)⟩
  have hfinite (n : ℕ) :
      (∫⁻ t in E n, ENNReal.ofReal (g t)) ≤
        ENNReal.ofReal |q (x n)| +
          ∫⁻ t in E n, ENNReal.ofReal (f t) := by
    by_cases heq : x n = y n
    · have hE : E n = ∅ := by simp [E, heq]
      simp [hE]
    · have hlt : x n < y n := lt_of_le_of_ne (hxy n) heq
      have hgOn : IntegrableOn g (Ioo (x n) (y n)) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le).mp
          (hgi (x n) (y n) (hx n) hlt (hy n))
      have hfOn : IntegrableOn f (Ioo (x n) (y n)) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le).mp
          (hfi (x n) (y n) (hx n) hlt (hy n))
      have hgCast : (∫⁻ t in E n, ENNReal.ofReal (g t)) =
          ENNReal.ofReal (∫ t in x n..y n, g t) := by
        rw [intervalIntegral.integral_of_le hlt.le,
          integral_Ioc_eq_integral_Ioo]
        exact (ofReal_integral_eq_lintegral_ofReal hgOn
          (Eventually.of_forall fun t => hg t)).symm
      have hfCast : (∫⁻ t in E n, ENNReal.ofReal (f t)) =
          ENNReal.ofReal (∫ t in x n..y n, f t) := by
        rw [intervalIntegral.integral_of_le hlt.le,
          integral_Ioc_eq_integral_Ioo]
        exact (ofReal_integral_eq_lintegral_ofReal hfOn
          (Eventually.of_forall fun t => hf t)).symm
      have hfin0 : 0 ≤ ∫ t in x n..y n, f t :=
        intervalIntegral.integral_nonneg hlt.le (fun t _ => hf t)
      rw [hgCast, hfCast, ← ENNReal.ofReal_add (abs_nonneg _) hfin0]
      exact ENNReal.ofReal_le_ofReal
        (hbound (x n) (y n) (hx n) hlt (hy n))
  have htarget : ∀ ε : NNReal, 0 < ε →
      (∫⁻ t in Ioo a b, ENNReal.ofReal (f t)) < ∞ →
      (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) ≤
        (∫⁻ t in Ioo a b, ENNReal.ofReal (f t)) + ε := by
    intro ε hε _
    have hεreal : (0 : ℝ) < (ε : ℝ) := hε
    have hev : ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal |q (x n)| ≤ (ε : ℝ≥0∞) := by
      have hEv := hqlim.eventually (Iio_mem_nhds hεreal)
      filter_upwards [hEv] with n hn
      simpa only [ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hn.le
    have hm (m : ℕ) :
        (∫⁻ t in E m, ENNReal.ofReal (g t)) ≤
          (∫⁻ t in Ioo a b, ENNReal.ofReal (f t)) + ε := by
      obtain ⟨n, hmn, hεn⟩ :=
        ((Filter.eventually_ge_atTop m).and hev).exists
      calc
        (∫⁻ t in E m, ENNReal.ofReal (g t)) ≤
            ∫⁻ t in E n, ENNReal.ofReal (g t) :=
          lintegral_mono_set (hEmono hmn)
        _ ≤ ENNReal.ofReal |q (x n)| +
              ∫⁻ t in E n, ENNReal.ofReal (f t) := hfinite n
        _ ≤ ε + ∫⁻ t in Ioo a b, ENNReal.ofReal (f t) :=
          add_le_add hεn (lintegral_mono_set (by
            intro t ht
            exact ⟨(hx n).trans ht.1, ht.2.trans (hy n)⟩))
        _ = _ := by ac_rfl
    calc
      (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) =
          ∫⁻ t in ⋃ n, E n, ENNReal.ofReal (g t) := by rw [hcover]
      _ = ⨆ n, ∫⁻ t in E n, ENNReal.ofReal (g t) :=
        setLIntegral_iUnion_of_directed _ hdir
      _ ≤ _ := iSup_le hm
  exact ENNReal.le_of_forall_pos_le_add htarget

end ChristodoulouBV

end
