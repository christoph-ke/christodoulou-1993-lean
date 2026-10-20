module

public import ChristodoulouBV.Uniqueness.RegularRectangleBounds
public import ChristodoulouBV.Uniqueness.RegularRectangleVolterra

/-!
# Seven-field comparison on a regular rectangle

The BV representatives are only integrated on compact characteristic
segments. No pointwise boundary value is assigned to an exceptional density.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- The nonnegative seven-field difference used in the characteristic
Volterra inequality. -/
def regularDifference (S₁ S₂ : Fields) (u v : ℝ) : ℝ :=
  |S₁.r u v - S₂.r u v| +
  |S₁.phi u v - S₂.phi u v| +
  |S₁.m u v - S₂.m u v| +
  |S₁.lam u v - S₂.lam u v| +
  |S₁.nu u v - S₂.nu u v| +
  |S₁.alpha u v - S₂.alpha u v| +
  |S₁.beta u v - S₂.beta u v|

/-- The seven-field comparison is nonnegative everywhere. -/
theorem regularDifference_nonneg (S₁ S₂ : Fields) (u v : ℝ) :
    0 ≤ regularDifference S₁ S₂ u v := by
  unfold regularDifference
  positivity

/-- Each component difference is controlled by the seven-field sum. -/
theorem regularDifference_components (S₁ S₂ : Fields) (u v : ℝ) :
    |S₁.r u v - S₂.r u v| ≤ regularDifference S₁ S₂ u v ∧
    |S₁.phi u v - S₂.phi u v| ≤ regularDifference S₁ S₂ u v ∧
    |S₁.m u v - S₂.m u v| ≤ regularDifference S₁ S₂ u v ∧
    |S₁.lam u v - S₂.lam u v| ≤ regularDifference S₁ S₂ u v ∧
    |S₁.nu u v - S₂.nu u v| ≤ regularDifference S₁ S₂ u v ∧
    |S₁.alpha u v - S₂.alpha u v| ≤ regularDifference S₁ S₂ u v ∧
    |S₁.beta u v - S₂.beta u v| ≤ regularDifference S₁ S₂ u v := by
  unfold regularDifference
  have h₁ := abs_nonneg (S₁.r u v - S₂.r u v)
  have h₂ := abs_nonneg (S₁.phi u v - S₂.phi u v)
  have h₃ := abs_nonneg (S₁.m u v - S₂.m u v)
  have h₄ := abs_nonneg (S₁.lam u v - S₂.lam u v)
  have h₅ := abs_nonneg (S₁.nu u v - S₂.nu u v)
  have h₆ := abs_nonneg (S₁.alpha u v - S₂.alpha u v)
  have h₇ := abs_nonneg (S₁.beta u v - S₂.beta u v)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Product differences split into one difference in each factor. -/
theorem regular_product_difference_le (a₁ a₂ b₁ b₂ : ℝ) :
    |a₁ * b₁ - a₂ * b₂| ≤
      |a₁| * |b₁ - b₂| + |b₂| * |a₁ - a₂| := by
  have heq : a₁ * b₁ - a₂ * b₂ =
      a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂ := by ring
  rw [heq]
  simpa only [abs_mul, mul_comm] using
    (abs_add_le (a₁ * (b₁ - b₂)) ((a₁ - a₂) * b₂))

/-- On an outgoing rectangle slice, every frozen field is interval
integrable. The two transverse densities use BV variation rather than
pointwise continuity. -/
theorem regular_rectangle_outgoing_field_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ u : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U)
    (hu' : u ∈ Icc u₀ u₁) :
    IntervalIntegrable (S.r u) volume v₀ v₁ ∧
    IntervalIntegrable (S.phi u) volume v₀ v₁ ∧
    IntervalIntegrable (S.m u) volume v₀ v₁ ∧
    IntervalIntegrable (S.lam u) volume v₀ v₁ ∧
    IntervalIntegrable (S.nu u) volume v₀ v₁ ∧
    IntervalIntegrable (S.alpha u) volume v₀ v₁ ∧
    IntervalIntegrable (S.beta u) volume v₀ v₁ := by
  have hs := regularRectangle_outSeg_subset hR hu'
  have hBVsubset : uIcc v₀ v₁ ⊆ {v | (u, v) ∈ U} := by
    intro v hv'
    exact hR ⟨hu', by simpa only [uIcc_of_le hv] using hv'⟩
  have hBVlam : BoundedVariationOn (S.lam u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item1.choose_spec.1 u)
  have hBVphi : BoundedVariationOn (S.phi u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.1 u)
  have hBVtheta : BoundedVariationOn (S.theta u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  have hBValpha : BoundedVariationOn (S.alpha u) {v | (u, v) ∈ U} := by
    have hsum := hBVtheta.add (hBVlam.mul hBVphi)
    convert hsum using 1
    funext v
    dsimp [Fields.theta]
    ring
  have hslice := (regular_rectangle_slice_continuity h hu hv hR).1 u hu'
  have hνcont : ContinuousOn (S.nu u) (Icc v₀ v₁) := by
    simpa only [uIcc_of_le hv] using
      (h.solution.nu_out_ac_ae hv hs).1.continuousOn
  have hβcont : ContinuousOn (S.beta u) (Icc v₀ v₁) := by
    simpa only [uIcc_of_le hv] using
      (h.solution.beta_out_ac_ae hv hs).1.continuousOn
  exact ⟨hslice.1.intervalIntegrable_of_Icc hv,
    hslice.2.1.intervalIntegrable_of_Icc hv,
    hslice.2.2.intervalIntegrable_of_Icc hv,
    hBVlam.intervalIntegrable hBVsubset,
    hνcont.intervalIntegrable_of_Icc hv,
    hBValpha.intervalIntegrable hBVsubset,
    hβcont.intervalIntegrable_of_Icc hv⟩

/-- On an incoming rectangle slice, every frozen field is interval
integrable. Here `ν,β` use their incoming BV variation. -/
theorem regular_rectangle_incoming_field_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ v : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U)
    (hv' : v ∈ Icc v₀ v₁) :
    IntervalIntegrable (fun u => S.r u v) volume u₀ u₁ ∧
    IntervalIntegrable (fun u => S.phi u v) volume u₀ u₁ ∧
    IntervalIntegrable (fun u => S.m u v) volume u₀ u₁ ∧
    IntervalIntegrable (fun u => S.lam u v) volume u₀ u₁ ∧
    IntervalIntegrable (fun u => S.nu u v) volume u₀ u₁ ∧
    IntervalIntegrable (fun u => S.alpha u v) volume u₀ u₁ ∧
    IntervalIntegrable (fun u => S.beta u v) volume u₀ u₁ := by
  have hs := regularRectangle_inSeg_subset hR hv'
  have hBVsubset : uIcc u₀ u₁ ⊆ {u | (u, v) ∈ U} := by
    intro u hu'
    exact hR ⟨by simpa only [uIcc_of_le hu] using hu', hv'⟩
  have hBVnu : BoundedVariationOn (fun u => S.nu u v) {u | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item1.choose_spec.2 v)
  have hBVphi : BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.2 v)
  have hBVzeta : BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.2 v)
  have hBVbeta : BoundedVariationOn (fun u => S.beta u v) {u | (u, v) ∈ U} := by
    have hsum := hBVzeta.add (hBVnu.mul hBVphi)
    convert hsum using 1
    funext u
    dsimp [Fields.zeta]
    ring
  have hslice := (regular_rectangle_slice_continuity h hu hv hR).2 v hv'
  have hLamCont : ContinuousOn (fun u => S.lam u v) (Icc u₀ u₁) := by
    simpa only [uIcc_of_le hu] using
      (h.solution.lam_in_ac_ae hu hs).1.continuousOn
  have hαcont : ContinuousOn (fun u => S.alpha u v) (Icc u₀ u₁) := by
    simpa only [uIcc_of_le hu] using
      (h.solution.alpha_in_ac_ae hu hs).1.continuousOn
  exact ⟨hslice.1.intervalIntegrable_of_Icc hu,
    hslice.2.1.intervalIntegrable_of_Icc hu,
    hslice.2.2.intervalIntegrable_of_Icc hu,
    hLamCont.intervalIntegrable_of_Icc hu,
    hBVnu.intervalIntegrable hBVsubset,
    hαcont.intervalIntegrable_of_Icc hu,
    hBVbeta.intervalIntegrable hBVsubset⟩

/-- The seven-field difference is integrable on every complete incoming and
outgoing segment of the rectangle. -/
theorem regularDifference_intervalIntegrable
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂) :
    (∀ u ∈ Icc u₀ u₁,
      IntervalIntegrable (regularDifference S₁ S₂ u) volume v₀ v₁) ∧
    (∀ v ∈ Icc v₀ v₁,
      IntervalIntegrable (fun u => regularDifference S₁ S₂ u v)
        volume u₀ u₁) := by
  constructor
  · intro u hu'
    obtain ⟨hr₁, hφ₁, hm₁, hlam₁, hnu₁, halpha₁, hbeta₁⟩ :=
      regular_rectangle_outgoing_field_integrable h₁ hu hv hR₁ hu'
    obtain ⟨hr₂, hφ₂, hm₂, hlam₂, hnu₂, halpha₂, hbeta₂⟩ :=
      regular_rectangle_outgoing_field_integrable h₂ hu hv hR₂ hu'
    have hsum :=
      ((((((hr₁.sub hr₂).abs.add (hφ₁.sub hφ₂).abs).add
        (hm₁.sub hm₂).abs).add (hlam₁.sub hlam₂).abs).add
        (hnu₁.sub hnu₂).abs).add (halpha₁.sub halpha₂).abs).add
        (hbeta₁.sub hbeta₂).abs
    exact hsum
  · intro v hv'
    obtain ⟨hr₁, hφ₁, hm₁, hlam₁, hnu₁, halpha₁, hbeta₁⟩ :=
      regular_rectangle_incoming_field_integrable h₁ hu hv hR₁ hv'
    obtain ⟨hr₂, hφ₂, hm₂, hlam₂, hnu₂, halpha₂, hbeta₂⟩ :=
      regular_rectangle_incoming_field_integrable h₂ hu hv hR₂ hv'
    have hsum :=
      ((((((hr₁.sub hr₂).abs.add (hφ₁.sub hφ₂).abs).add
        (hm₁.sub hm₂).abs).add (hlam₁.sub hlam₂).abs).add
        (hnu₁.sub hnu₂).abs).add (halpha₁.sub halpha₂).abs).add
        (hbeta₁.sub hbeta₂).abs
    exact hsum

/-- The seven-field difference has a finite uniform bound on a closed
regular rectangle. -/
theorem regularDifference_bounded
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        regularDifference S₁ S₂ u v ≤ B := by
  obtain ⟨ρ, δ, c, C, hρ, hδ, hc, hC, hfield⟩ :=
    regular_rectangle_basic_bounds h₁ h₂ hu hv hsep hR₁ hR₂
  have hcompact : IsCompact (regularRectangle u₀ u₁ v₀ v₁) := by
    simpa only [regularRectangle] using isCompact_Icc.prod isCompact_Icc
  have hprimary₁ := regular_rectangle_primary_continuousOn h₁ hu hv hR₁
  have hprimary₂ := regular_rectangle_primary_continuousOn h₂ hu hv hR₂
  obtain ⟨Br₁, hBr₁⟩ :=
    hcompact.exists_bound_of_continuousOn hprimary₁.1
  obtain ⟨Br₂, hBr₂⟩ :=
    hcompact.exists_bound_of_continuousOn hprimary₂.1
  obtain ⟨Bm₁, hBm₁⟩ :=
    hcompact.exists_bound_of_continuousOn hprimary₁.2.2
  obtain ⟨Bm₂, hBm₂⟩ :=
    hcompact.exists_bound_of_continuousOn hprimary₂.2.2
  have hcorner : (u₀, v₀) ∈ regularRectangle u₀ u₁ v₀ v₁ :=
    ⟨⟨le_rfl, hu⟩, ⟨le_rfl, hv⟩⟩
  have hBr₁0 : 0 ≤ Br₁ := (norm_nonneg _).trans (hBr₁ _ hcorner)
  have hBr₂0 : 0 ≤ Br₂ := (norm_nonneg _).trans (hBr₂ _ hcorner)
  have hBm₁0 : 0 ≤ Bm₁ := (norm_nonneg _).trans (hBm₁ _ hcorner)
  have hBm₂0 : 0 ≤ Bm₂ := (norm_nonneg _).trans (hBm₂ _ hcorner)
  let B := 1 + Br₁ + Br₂ + Bm₁ + Bm₂ + 10 * C + 4 * C ^ 2
  have hB : 0 ≤ B := by dsimp [B]; nlinarith [sq_nonneg C]
  refine ⟨B, hB, ?_⟩
  intro u hu' v hv'
  have hp : (u, v) ∈ regularRectangle u₀ u₁ v₀ v₁ := ⟨hu', hv'⟩
  have hr₁ : |S₁.r u v| ≤ Br₁ := by
    simpa only [Real.norm_eq_abs] using hBr₁ _ hp
  have hr₂ : |S₂.r u v| ≤ Br₂ := by
    simpa only [Real.norm_eq_abs] using hBr₂ _ hp
  have hm₁ : |S₁.m u v| ≤ Bm₁ := by
    simpa only [Real.norm_eq_abs] using hBm₁ _ hp
  have hm₂ : |S₂.m u v| ≤ Bm₂ := by
    simpa only [Real.norm_eq_abs] using hBm₂ _ hp
  obtain ⟨_, _, _, _, hlam₁, hnu₁, hphi₁, htheta₁, hzeta₁⟩ :=
    hfield u hu' v hv' S₁ (Or.inl rfl)
  obtain ⟨_, _, _, _, hlam₂, hnu₂, hphi₂, htheta₂, hzeta₂⟩ :=
    hfield u hu' v hv' S₂ (Or.inr rfl)
  have halpha₁ : |S₁.alpha u v| ≤ C + C ^ 2 := by
    have heq : S₁.alpha u v =
        S₁.theta u v + S₁.lam u v * S₁.phi u v := by
      dsimp [Fields.theta]; ring
    rw [heq]
    exact regular_scalar_density_abs_le hC htheta₁ hlam₁ hphi₁
  have halpha₂ : |S₂.alpha u v| ≤ C + C ^ 2 := by
    have heq : S₂.alpha u v =
        S₂.theta u v + S₂.lam u v * S₂.phi u v := by
      dsimp [Fields.theta]; ring
    rw [heq]
    exact regular_scalar_density_abs_le hC htheta₂ hlam₂ hphi₂
  have hbeta₁ : |S₁.beta u v| ≤ C + C ^ 2 := by
    have heq : S₁.beta u v =
        S₁.zeta u v + S₁.nu u v * S₁.phi u v := by
      dsimp [Fields.zeta]; ring
    rw [heq]
    exact regular_scalar_density_abs_le hC hzeta₁ hnu₁ hphi₁
  have hbeta₂ : |S₂.beta u v| ≤ C + C ^ 2 := by
    have heq : S₂.beta u v =
        S₂.zeta u v + S₂.nu u v * S₂.phi u v := by
      dsimp [Fields.zeta]; ring
    rw [heq]
    exact regular_scalar_density_abs_le hC hzeta₂ hnu₂ hphi₂
  unfold regularDifference
  have habs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    calc
      |x - y| = |x + -y| := by rw [sub_eq_add_neg]
      _ ≤ |x| + |-y| := abs_add_le _ _
      _ = |x| + |y| := by rw [abs_neg]
  have hb₁ := habs (S₁.r u v) (S₂.r u v)
  have hb₂ := habs (S₁.phi u v) (S₂.phi u v)
  have hb₃ := habs (S₁.m u v) (S₂.m u v)
  have hb₄ := habs (S₁.lam u v) (S₂.lam u v)
  have hb₅ := habs (S₁.nu u v) (S₂.nu u v)
  have hb₆ := habs (S₁.alpha u v) (S₂.alpha u v)
  have hb₇ := habs (S₁.beta u v) (S₂.beta u v)
  dsimp [B]
  linarith

end ChristodoulouBV.Uniqueness

end
