module

public import ChristodoulouBV.BVSolution.Signs
public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Primitive
import ChristodoulouBV.BVSolution.AxisTraces

/-!
# Initial data on an outgoing characteristic

The primitive densities are determined almost everywhere by the pointwise
radius and scalar data.  No representative convention is used.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- Pointwise equality of the radii on an outgoing initial slice determines
the two outgoing expansions almost everywhere on each compact subinterval
away from the axis. -/
theorem initial_lam_ae_on_compact
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b x y : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b → S₁.r a v = S₂.r a v)
    (hax : a < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    ∀ᵐ v ∂volume, v ∈ Icc x y → S₁.lam a v = S₂.lam a v := by
  let F : ℝ → ℝ := S₁.r a
  have hseg₁ (s t : ℝ) (hxs : x ≤ s) (hst : s ≤ t) (hty : t ≤ y) :
      outSeg a s t ⊆ U₁ :=
    h₁.solution.development.out_seg_subset h₁ab (hax.trans_le hxs) hst
      (hty.trans hyb)
  have hseg₂ (s t : ℝ) (hxs : x ≤ s) (hst : s ≤ t) (hty : t ≤ y) :
      outSeg a s t ⊆ U₂ :=
    h₂.solution.development.out_seg_subset h₂ab (hax.trans_le hxs) hst
      (hty.trans hyb)
  apply AbsolutelyContinuousOnInterval.ae_eq_of_same_integral_increments hxy
  · intro s t hxs hst hty
    exact (h₁.solution.radius_out a s t hst (hseg₁ s t hxs hst hty)).1
  · intro s t hxs hst hty
    exact (h₂.solution.radius_out a s t hst (hseg₂ s t hxs hst hty)).1
  · intro s t hxs hst hty
    exact (h₁.solution.radius_out a s t hst (hseg₁ s t hxs hst hty)).2
  · intro s t hxs hst hty
    have hp := (h₂.solution.radius_out a s t hst (hseg₂ s t hxs hst hty)).2
    rw [hdata s (hax.trans_le hxs) (hst.trans (hty.trans hyb)),
      hdata t (hax.trans_le (hxs.trans hst)) (hty.trans hyb)]
    exact hp

/-- Pointwise equality of the radius and scalar field on an outgoing initial
slice determines the scalar-radius densities almost everywhere on every
compact subinterval away from the axis. -/
theorem initial_alpha_ae_on_compact
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b x y : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v)
    (hax : a < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    ∀ᵐ v ∂volume, v ∈ Icc x y → S₁.alpha a v = S₂.alpha a v := by
  let F : ℝ → ℝ := fun v => S₁.r a v * S₁.phi a v
  have hseg₁ (s t : ℝ) (hxs : x ≤ s) (hst : s ≤ t) (hty : t ≤ y) :
      outSeg a s t ⊆ U₁ :=
    h₁.solution.development.out_seg_subset h₁ab (hax.trans_le hxs) hst
      (hty.trans hyb)
  have hseg₂ (s t : ℝ) (hxs : x ≤ s) (hst : s ≤ t) (hty : t ≤ y) :
      outSeg a s t ⊆ U₂ :=
    h₂.solution.development.out_seg_subset h₂ab (hax.trans_le hxs) hst
      (hty.trans hyb)
  apply AbsolutelyContinuousOnInterval.ae_eq_of_same_integral_increments hxy
  · intro s t hxs hst hty
    exact (h₁.solution.scalar_radius_out a s t hst (hseg₁ s t hxs hst hty)).1
  · intro s t hxs hst hty
    exact (h₂.solution.scalar_radius_out a s t hst (hseg₂ s t hxs hst hty)).1
  · intro s t hxs hst hty
    exact (h₁.solution.scalar_radius_out a s t hst (hseg₁ s t hxs hst hty)).2
  · intro s t hxs hst hty
    have hp := (h₂.solution.scalar_radius_out a s t hst (hseg₂ s t hxs hst hty)).2
    rcases hdata s (hax.trans_le hxs) (hst.trans (hty.trans hyb)) with
      ⟨hrs, hφs⟩
    rcases hdata t (hax.trans_le (hxs.trans hst)) (hty.trans hyb) with
      ⟨hrt, hφt⟩
    rw [hrs, hφs, hrt, hφt]
    exact hp

/-- Pointwise initial radius and scalar data determine the outgoing primitive
densities almost everywhere on the entire half-open initial slice. -/
theorem initial_lam_alpha_ae
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∀ᵐ v ∂volume, v ∈ Ioc a b →
      S₁.lam a v = S₂.lam a v ∧ S₁.alpha a v = S₂.alpha a v := by
  have hq : ∀ q : ℚ, ∀ᵐ v ∂volume,
      a < (q : ℝ) → (q : ℝ) ≤ b → v ∈ Icc (q : ℝ) b →
        S₁.lam a v = S₂.lam a v ∧ S₁.alpha a v = S₂.alpha a v := by
    intro q
    by_cases haq : a < (q : ℝ)
    · by_cases hqb : (q : ℝ) ≤ b
      · filter_upwards [h₁.initial_lam_ae_on_compact h₂ h₁ab h₂ab
            (fun v hav hvb => (hdata v hav hvb).1) haq hqb le_rfl,
          h₁.initial_alpha_ae_on_compact h₂ h₁ab h₂ab hdata haq hqb le_rfl]
          with v hlam halpha _ _ hv
        exact ⟨hlam hv, halpha hv⟩
      · exact Filter.Eventually.of_forall (fun _ _ h => (hqb h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (haq h).elim)
  filter_upwards [eventually_countable_forall.mpr hq] with v hv hvab
  obtain ⟨q, haq, hqv⟩ := exists_rat_btwn hvab.1
  exact hv q haq (hqv.le.trans hvab.2) ⟨hqv.le, hvab.2⟩

/-- Equal initial radius and scalar data also determine the outgoing scalar
amplitude almost everywhere on compact off-axis intervals. -/
theorem initial_theta_ae_on_compact
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b x y : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v)
    (hax : a < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    ∀ᵐ v ∂volume, v ∈ Icc x y → S₁.theta a v = S₂.theta a v := by
  filter_upwards [h₁.initial_lam_ae_on_compact h₂ h₁ab h₂ab
      (fun v hav hvb => (hdata v hav hvb).1) hax hxy hyb,
    h₁.initial_alpha_ae_on_compact h₂ h₁ab h₂ab hdata hax hxy hyb]
    with v hlam halpha hv
  have hφ := (hdata v (hax.trans_le hv.1) (hv.2.trans hyb)).2
  dsimp [Fields.theta]
  rw [hlam hv, halpha hv, hφ]

/-- On a common initial slice, subtraction of the mass densities leaves a
homogeneous linear term with nonpositive coefficient. -/
theorem initial_mass_density_difference_ae_on_compact
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b x y : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v)
    (hax : a < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    ∀ᵐ v ∂volume, v ∈ Icc x y →
      massV S₁ a v - massV S₂ a v =
        -(S₁.theta a v * S₁.theta a v * (S₁.r a v)⁻¹ *
          (S₁.lam a v)⁻¹) * (S₁.m a v - S₂.m a v) := by
  filter_upwards [h₁.initial_lam_ae_on_compact h₂ h₁ab h₂ab
      (fun v hav hvb => (hdata v hav hvb).1) hax hxy hyb,
    h₁.initial_theta_ae_on_compact h₂ h₁ab h₂ab hdata hax hxy hyb]
    with v hlam htheta hv
  have hvU : (a, v) ∈ U₁ := h₁.solution.development.outgoing_mem h₁ab
    (hax.trans_le hv.1) (hv.2.trans hyb)
  have hr : S₁.r a v = S₂.r a v :=
    (hdata v (hax.trans_le hv.1) (hv.2.trans hyb)).1
  have hrne : S₁.r a v ≠ 0 :=
    (h₁.solution.radius_pos (a, v) hvU).ne'
  have hlne : S₁.lam a v ≠ 0 :=
    (h₁.solution.lam_pos (a, v) hvU).ne'
  dsimp [massV]
  rw [hlam hv, htheta hv, ← hr]
  field_simp
  ring

/-- On any compact off-axis part of a common initial slice, the mass
difference cannot grow: the shared mass equation has nonnegative damping. -/
theorem initial_mass_difference_abs_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b x y : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v)
    (hax : a < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    |S₁.m a y - S₂.m a y| ≤ |S₁.m a x - S₂.m a x| := by
  let k : ℝ → ℝ := fun s =>
    -(S₁.theta a s * S₁.theta a s * (S₁.r a s)⁻¹ * (S₁.lam a s)⁻¹)
  let z : ℝ → ℝ := fun s => S₁.m a s - S₂.m a s
  have hseg₁ (s t : ℝ) (hxs : x ≤ s) (hst : s ≤ t) (hty : t ≤ y) :
      outSeg a s t ⊆ U₁ :=
    h₁.solution.development.out_seg_subset h₁ab (hax.trans_le hxs) hst
      (hty.trans hyb)
  have hseg₂ (s t : ℝ) (hxs : x ≤ s) (hst : s ≤ t) (hty : t ≤ y) :
      outSeg a s t ⊆ U₂ :=
    h₂.solution.development.out_seg_subset h₂ab (hax.trans_le hxs) hst
      (hty.trans hyb)
  have hprim₁ (t : ℝ) (ht : t ∈ Icc x y) :
      IntervalPrimitive (S₁.m a) (massV S₁ a) x t := by
    change IntervalPrimitive (S₁.m a)
      (fun s => (1 - 2 * S₁.m a s / S₁.r a s) * S₁.theta a s ^ 2 /
        (2 * S₁.lam a s)) x t
    exact h₁.solution.mass_out a x t ht.1 (hseg₁ x t le_rfl ht.1 ht.2)
  have hprim₂ (t : ℝ) (ht : t ∈ Icc x y) :
      IntervalPrimitive (S₂.m a) (massV S₂ a) x t := by
    change IntervalPrimitive (S₂.m a)
      (fun s => (1 - 2 * S₂.m a s / S₂.r a s) * S₂.theta a s ^ 2 /
        (2 * S₂.lam a s)) x t
    exact h₂.solution.mass_out a x t ht.1 (hseg₂ x t le_rfl ht.1 ht.2)
  have h₁int : IntervalIntegrable (massV S₁ a) volume x y :=
    (hprim₁ y ⟨hxy, le_rfl⟩).1
  have h₂int : IntervalIntegrable (massV S₂ a) volume x y :=
    (hprim₂ y ⟨hxy, le_rfl⟩).1
  have hdiff := h₁.initial_mass_density_difference_ae_on_compact h₂
    h₁ab h₂ab hdata hax hxy hyb
  have hkae : (fun s => massV S₁ a s - massV S₂ a s) =ᵐ[
      volume.restrict (Ioc x y)] (fun s => k s * z s) := by
    change ∀ᵐ s ∂volume.restrict (Ioc x y),
      massV S₁ a s - massV S₂ a s = k s * z s
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hdiff] with s hs hxy'
    exact hs ⟨hxy'.1.le, hxy'.2⟩
  have hkz : IntervalIntegrable (fun s => k s * z s) volume x y :=
    (h₁int.sub h₂int).congr_ae (by
      simpa only [uIoc_of_le hxy] using hkae)
  have hk : IntervalIntegrable k volume x y := by
    have hh := barrier_coefficient_integrable h₁.solution.development h₁
      h₁ab hax hxy hyb
    convert hh.neg using 1
  have hy : ∀ t ∈ Icc x y,
      z t - z x = ∫ s in x..t, (k s * z s + (0 : ℝ)) := by
    intro t ht
    have hp₁ := hprim₁ t ht
    have hp₂ := hprim₂ t ht
    have hsub : ∫ s in x..t, massV S₁ a s - massV S₂ a s =
        ∫ s in x..t, k s * z s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hdiff] with s hs hsxt
      have hsxy : s ∈ Icc x y := by
        rw [uIoc_of_le ht.1] at hsxt
        exact ⟨hsxt.1.le, hsxt.2.trans ht.2⟩
      exact hs hsxy
    have hlin := intervalIntegral.integral_sub hp₁.1 hp₂.1
    dsimp [z]
    simp only [add_zero]
    rw [← hsub, hlin]
    linarith [hp₁.2, hp₂.2]
  have hk_nonpos : ∀ s ∈ Icc x y, k s ≤ 0 := by
    intro s hs
    have hsU := h₁.solution.development.outgoing_mem h₁ab
      (hax.trans_le hs.1) (hs.2.trans hyb)
    have hrpos := h₁.solution.radius_pos (a, s) hsU
    have hlpos := h₁.solution.lam_pos (a, s) hsU
    dsimp [k]
    apply neg_nonpos.mpr
    exact mul_nonneg
      (mul_nonneg (mul_self_nonneg _) (inv_nonneg.mpr hrpos.le))
      (inv_nonneg.mpr hlpos.le)
  have hint_nonpos : (∫ s in x..y, k s) ≤ 0 := by
    have hh : 0 ≤ ∫ s in x..y, -k s :=
      intervalIntegral.integral_nonneg hxy (fun s hs => neg_nonneg.mpr (hk_nonpos s hs))
    rw [intervalIntegral.integral_neg] at hh
    linarith
  have hform := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    hxy hk intervalIntegrable_const hkz hy (show y ∈ Icc x y from ⟨hxy, le_rfl⟩)
  have hE : Real.exp (∫ s in x..y, k s) ≤ 1 := Real.exp_le_one_iff.mpr hint_nonpos
  have hEpos : 0 < Real.exp (∫ s in x..y, k s) := Real.exp_pos _
  have hform' : z y = Real.exp (∫ s in x..y, k s) * z x := by
    simpa only [mul_zero, intervalIntegral.integral_zero, add_zero] using hform
  change |z y| ≤ |z x|
  rw [hform', abs_mul, abs_of_pos hEpos]
  exact mul_le_of_le_one_left (abs_nonneg _) hE

/-- Equality of the radius and scalar field on a common outgoing initial
slice forces pointwise equality of the Hawking masses there.  The proof
uses the nonexpanding homogeneous mass difference on compact segments and
the zero mass trace at the excluded axis. -/
theorem initial_mass_eq
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b : ℝ} (h₁ab : (a, b) ∈ U₁) (h₂ab : (a, b) ∈ U₂)
    (hdata : ∀ v, a < v → v ≤ b →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∀ v ∈ Ioc a b, S₁.m a v = S₂.m a v := by
  intro v hv
  have hlim : Tendsto (fun x => |S₁.m a x - S₂.m a x|)
      (𝓝[>] a) (𝓝 (0 : ℝ)) := by
    simpa using ((h₁.mass_tendsto_axis_out h₁ab).sub
      (h₂.mass_tendsto_axis_out h₂ab)).abs
  have hbound : ∀ᶠ x in 𝓝[>] a,
      |S₁.m a v - S₂.m a v| ≤ |S₁.m a x - S₂.m a x| := by
    filter_upwards [Ioo_mem_nhdsGT hv.1] with x hx
    exact h₁.initial_mass_difference_abs_le h₂ h₁ab h₂ab hdata
      hx.1 hx.2.le hv.2
  have hzero : |S₁.m a v - S₂.m a v| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

end ChristodoulouBV.IsBVSolution

end
