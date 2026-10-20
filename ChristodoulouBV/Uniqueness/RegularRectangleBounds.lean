module

public import ChristodoulouBV.BVSolution.PrimitiveCalculus
public import ChristodoulouBV.BVSolution.CoefficientClosure

/-!
# Bounds and continuity on a regular rectangle

Characteristic primitives and global BV variation provide local bounds.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The closed characteristic rectangle with lower corner `(u₀,v₀)`. -/
def regularRectangle (u₀ u₁ v₀ v₁ : ℝ) : Set (ℝ × ℝ) :=
  Icc u₀ u₁ ×ˢ Icc v₀ v₁

/-- A rectangle contained in a development supplies every outgoing segment
at one of its incoming coordinates. -/
theorem regularRectangle_outSeg_subset
    {U : Set (ℝ × ℝ)} {u₀ u₁ v₀ v₁ u : ℝ}
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U)
    (hu : u ∈ Icc u₀ u₁) :
    outSeg u v₀ v₁ ⊆ U := by
  intro p hp
  rcases p with ⟨x, y⟩
  obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc v₀ v₁ := by
    simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
  exact hR ⟨hu, hy⟩

/-- A rectangle contained in a development supplies every incoming segment
at one of its outgoing coordinates. -/
theorem regularRectangle_inSeg_subset
    {U : Set (ℝ × ℝ)} {u₀ u₁ v₀ v₁ v : ℝ}
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U)
    (hv : v ∈ Icc v₀ v₁) :
    inSeg v u₀ u₁ ⊆ U := by
  intro p hp
  rcases p with ⟨x, y⟩
  obtain ⟨hx, rfl⟩ : x ∈ Icc u₀ u₁ ∧ y = v := by
    simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
  exact hR ⟨hx, hv⟩

/-- On every characteristic crossing a closed regular rectangle, the three
primary fields have continuous traces up to both faces. -/
theorem regular_rectangle_slice_continuity
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    (∀ u ∈ Icc u₀ u₁,
      ContinuousOn (S.r u) (Icc v₀ v₁) ∧
      ContinuousOn (S.phi u) (Icc v₀ v₁) ∧
      ContinuousOn (S.m u) (Icc v₀ v₁)) ∧
    (∀ v ∈ Icc v₀ v₁,
      ContinuousOn (fun u => S.r u v) (Icc u₀ u₁) ∧
      ContinuousOn (fun u => S.phi u v) (Icc u₀ u₁) ∧
      ContinuousOn (fun u => S.m u v) (Icc u₀ u₁)) := by
  constructor
  · intro u hu'
    have hs := regularRectangle_outSeg_subset hR hu'
    have hr := (h.solution.radius_out_ac_ae hv hs).1.continuousOn
    have hp := (h.item3_ac_out u v₀ v₁ hv hs).continuousOn
    have hm := (h.solution.mass_out_ac_ae hv hs).1.continuousOn
    simpa only [uIcc_of_le hv] using (show
      ContinuousOn (S.r u) (uIcc v₀ v₁) ∧
      ContinuousOn (S.phi u) (uIcc v₀ v₁) ∧
      ContinuousOn (S.m u) (uIcc v₀ v₁) from ⟨hr, hp, hm⟩)
  · intro v hv'
    have hs := regularRectangle_inSeg_subset hR hv'
    have hr := (h.solution.radius_in_ac_ae hu hs).1.continuousOn
    have hp := (h.item3_ac_in v u₀ u₁ hu hs).continuousOn
    have hm := (h.solution.mass_in_ac_ae hu hs).1.continuousOn
    simpa only [uIcc_of_le hu] using (show
      ContinuousOn (fun u => S.r u v) (uIcc u₀ u₁) ∧
      ContinuousOn (fun u => S.phi u v) (uIcc u₀ u₁) ∧
      ContinuousOn (fun u => S.m u v) (uIcc u₀ u₁) from ⟨hr, hp, hm⟩)

/-- A fixed positive distance from the axis gives one positive lower radius
bound for each member of the pair on the whole rectangle. -/
theorem regular_rectangle_radius_lower
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (_hu : u₀ ≤ u₁) (_hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        ρ ≤ S₁.r u v ∧ ρ ≤ S₂.r u v := by
  obtain ⟨c₁, hc₁, hlam₁⟩ := h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := h₂.lam_bounded_below
  let ρ := min c₁ c₂ * (v₀ - u₁)
  have hρ : 0 < ρ := mul_pos (lt_min hc₁ hc₂) (sub_pos.mpr hsep)
  refine ⟨ρ, hρ, ?_⟩
  intro u hu' v hv'
  have hdist : v₀ - u₁ ≤ v - u := by
    exact sub_le_sub hv'.1 hu'.2
  have hdist0 : 0 ≤ v - u := by linarith
  have hpt₁ : (u, v) ∈ U₁ := hR₁ ⟨hu', hv'⟩
  have hpt₂ : (u, v) ∈ U₂ := hR₂ ⟨hu', hv'⟩
  have hrad₁ := h₁.radius_lower hlam₁ hpt₁
  have hrad₂ := h₂.radius_lower hlam₂ hpt₂
  constructor
  · calc
      ρ ≤ c₁ * (v₀ - u₁) :=
        mul_le_mul_of_nonneg_right (min_le_left c₁ c₂)
          (sub_pos.mpr hsep).le
      _ ≤ c₁ * (v - u) := mul_le_mul_of_nonneg_left hdist hc₁.le
      _ ≤ S₁.r u v := hrad₁
  · calc
      ρ ≤ c₂ * (v₀ - u₁) :=
        mul_le_mul_of_nonneg_right (min_le_right c₁ c₂)
          (sub_pos.mpr hsep).le
      _ ≤ c₂ * (v - u) := mul_le_mul_of_nonneg_left hdist hc₂.le
      _ ≤ S₂.r u v := hrad₂

/-- Uniform outgoing BV variation and a continuous incoming anchor give a
bound on the whole rectangle. This is the local replacement for an axis
triangle bound when the target's causal past stops before the axis. -/
theorem regular_rectangle_bound_of_outgoing_variation
    {U : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ} {C : ℝ}
    {u₀ u₁ v₀ v₁ : ℝ} (_hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U)
    (hface : ContinuousOn (fun u => f u v₀) (Icc u₀ u₁))
    (hvar : ∀ u, eVariationOn (f u) {v | (u, v) ∈ U} ≤ ENNReal.ofReal C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁, |f u v| ≤ M := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hface
  let M := max B 0 + max C 0
  have hM : 0 ≤ M := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨M, hM, ?_⟩
  intro u hu' v hv'
  have hBV : BoundedVariationOn (f u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar u)
  have hTV :
      (eVariationOn (f u) {v | (u, v) ∈ U}).toReal ≤ max C 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right C 0)
      ((hvar u).trans (ENNReal.ofReal_le_ofReal (le_max_left C 0)))
  have hdiff := hBV.abs_sub_le_variation
    (hR ⟨hu', hv'⟩) (hR ⟨hu', ⟨le_rfl, hv⟩⟩)
  have hbase : |f u v₀| ≤ max B 0 := by
    simpa only [Real.norm_eq_abs] using
      (hB u hu').trans (le_max_left B 0)
  have htri : |f u v| ≤ |f u v - f u v₀| + |f u v₀| := by
    calc
      |f u v| = |(f u v - f u v₀) + f u v₀| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
  exact htri.trans (by dsimp [M]; linarith)

/-- Uniform incoming BV variation and a continuous outgoing anchor give a
bound on the whole rectangle. -/
theorem regular_rectangle_bound_of_incoming_variation
    {U : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ} {C : ℝ}
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (_hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U)
    (hface : ContinuousOn (fun v => f u₀ v) (Icc v₀ v₁))
    (hvar : ∀ v, eVariationOn (fun u => f u v) {u | (u, v) ∈ U} ≤
      ENNReal.ofReal C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁, |f u v| ≤ M := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hface
  let M := max B 0 + max C 0
  have hM : 0 ≤ M := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨M, hM, ?_⟩
  intro u hu' v hv'
  have hBV : BoundedVariationOn (fun u => f u v) {u | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar v)
  have hTV :
      (eVariationOn (fun u => f u v) {u | (u, v) ∈ U}).toReal ≤ max C 0 :=
    ENNReal.toReal_le_of_le_ofReal (le_max_right C 0)
      ((hvar v).trans (ENNReal.ofReal_le_ofReal (le_max_left C 0)))
  have hdiff := hBV.abs_sub_le_variation
    (hR ⟨hu', hv'⟩) (hR ⟨⟨le_rfl, hu⟩, hv'⟩)
  have hbase : |f u₀ v| ≤ max B 0 := by
    simpa only [Real.norm_eq_abs] using
      (hB v hv').trans (le_max_left B 0)
  have htri : |f u v| ≤ |f u v - f u₀ v| + |f u₀ v| := by
    calc
      |f u v| = |(f u v - f u₀ v) + f u₀ v| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
  exact htri.trans (by dsimp [M]; linarith)

/-- The five field amplitudes needed in the regular equations are uniformly
bounded on a closed rectangle. The anchors are the continuous primitive
traces on its past faces, so no complete axis triangle is required. -/
theorem regular_rectangle_field_bounds
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    ∃ c B_lam Bν Bφ Bθ Bζ : ℝ,
      0 < c ∧ 0 ≤ B_lam ∧ 0 ≤ Bν ∧ 0 ≤ Bφ ∧
      0 ≤ Bθ ∧ 0 ≤ Bζ ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        c ≤ S.lam u v ∧ S.nu u v ≤ -c ∧
        |S.lam u v| ≤ B_lam ∧ |S.nu u v| ≤ Bν ∧
        |S.phi u v| ≤ Bφ ∧ |S.theta u v| ≤ Bθ ∧
        |S.zeta u v| ≤ Bζ := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hsIn := regularRectangle_inSeg_subset hR ⟨le_rfl, hv⟩
  have hsOut := regularRectangle_outSeg_subset hR ⟨le_rfl, hu⟩
  have hLamCont : ContinuousOn (fun u => S.lam u v₀) (Icc u₀ u₁) := by
    simpa only [uIcc_of_le hu] using
      (h.solution.lam_in_ac_ae hu hsIn).1.continuousOn
  have hαcont : ContinuousOn (fun u => S.alpha u v₀) (Icc u₀ u₁) := by
    simpa only [uIcc_of_le hu] using
      (h.solution.alpha_in_ac_ae hu hsIn).1.continuousOn
  have hφinCont : ContinuousOn (fun u => S.phi u v₀) (Icc u₀ u₁) := by
    simpa only [uIcc_of_le hu] using
      (h.item3_ac_in v₀ u₀ u₁ hu hsIn).continuousOn
  have hθcont : ContinuousOn (fun u => S.theta u v₀) (Icc u₀ u₁) := by
    convert hαcont.sub (hLamCont.mul hφinCont) using 1
    funext u
    simp only [Fields.theta, Pi.sub_apply, Pi.mul_apply]
  have hνcont : ContinuousOn (S.nu u₀) (Icc v₀ v₁) := by
    simpa only [uIcc_of_le hv] using
      (h.solution.nu_out_ac_ae hv hsOut).1.continuousOn
  have hβcont : ContinuousOn (S.beta u₀) (Icc v₀ v₁) := by
    simpa only [uIcc_of_le hv] using
      (h.solution.beta_out_ac_ae hv hsOut).1.continuousOn
  have hφoutCont : ContinuousOn (S.phi u₀) (Icc v₀ v₁) := by
    simpa only [uIcc_of_le hv] using
      (h.item3_ac_out u₀ v₀ v₁ hv hsOut).continuousOn
  have hζcont : ContinuousOn (fun v => S.zeta u₀ v) (Icc v₀ v₁) := by
    convert hβcont.sub (hνcont.mul hφoutCont) using 1
    funext v
    simp only [Fields.zeta, Pi.sub_apply, Pi.mul_apply]
  obtain ⟨B_lam, hB_lam, hLam⟩ :=
    regular_rectangle_bound_of_outgoing_variation hu hv hR hLamCont
      h.item1.choose_spec.1
  obtain ⟨Bν, hBν, hν⟩ :=
    regular_rectangle_bound_of_incoming_variation hu hv hR hνcont
      h.item1.choose_spec.2
  obtain ⟨Bφ, hBφ, hφ⟩ :=
    regular_rectangle_bound_of_outgoing_variation hu hv hR hφinCont
      h.item3_variation.choose_spec.1
  obtain ⟨Bθ, hBθ, hθ⟩ :=
    regular_rectangle_bound_of_outgoing_variation hu hv hR hθcont
      h.item5.choose_spec.1
  obtain ⟨Bζ, hBζ, hζ⟩ :=
    regular_rectangle_bound_of_incoming_variation hu hv hR hζcont
      h.item5.choose_spec.2
  refine ⟨c, B_lam, Bν, Bφ, Bθ, Bζ, hc, hB_lam, hBν, hBφ, hBθ, hBζ, ?_⟩
  intro u hu' v hv'
  have hpt : (u, v) ∈ U := hR ⟨hu', hv'⟩
  exact ⟨hlam (u, v) hpt, h.nu_le_neg_lower hc hlam hpt,
    hLam u hu' v hv', hν u hu' v hv',
    hφ u hu' v hv', hθ u hu' v hv', hζ u hu' v hv'⟩

/-- A family of bounded interval primitives is uniformly Lipschitz on its
closed characteristic segment. -/
theorem regular_intervalPrimitive_lipschitz
    {F g : ℝ → ℝ} {a b M : ℝ} (_hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      IntervalPrimitive F g x y)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ M) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |F x - F y| ≤ M * |x - y| := by
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have hbound : ∀ t ∈ Set.uIoc x y, ‖g t‖ ≤ M := by
      intro t ht
      have htxy : t ∈ Icc x y := by
        simpa only [uIcc_of_le hxy] using Set.uIoc_subset_uIcc ht
      simpa only [Real.norm_eq_abs] using
        (hg t ⟨hx.1.trans htxy.1, htxy.2.trans hy.2⟩)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have heq := (hF x hx y hy hxy).2
    rw [← heq] at hI
    have hdist : |x - y| = y - x := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    rw [hdist]
    simpa only [Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hxy)] using hI
  · have hbound : ∀ t ∈ Set.uIoc y x, ‖g t‖ ≤ M := by
      intro t ht
      have htyx : t ∈ Icc y x := by
        simpa only [uIcc_of_le hyx] using Set.uIoc_subset_uIcc ht
      simpa only [Real.norm_eq_abs] using
        (hg t ⟨hy.1.trans htyx.1, htyx.2.trans hx.2⟩)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have heq := (hF y hy x hx hyx).2
    rw [← heq] at hI
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hyx)]
      using hI

/-- Uniform Lipschitz bounds in both characteristic variables yield joint
continuity on the closed rectangle. -/
theorem regular_rectangle_continuousOn_of_slice_lipschitz
    {F : ℝ → ℝ → ℝ} {u₀ u₁ v₀ v₁ M : ℝ}
    (hU : ∀ v ∈ Icc v₀ v₁, ∀ u ∈ Icc u₀ u₁,
      ∀ u' ∈ Icc u₀ u₁,
        |F u v - F u' v| ≤ M * |u - u'|)
    (hV : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      ∀ v' ∈ Icc v₀ v₁,
        |F u v - F u v'| ≤ M * |v - v'|) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (regularRectangle u₀ u₁ v₀ v₁) := by
  intro p hp
  have hp' : p.1 ∈ Icc u₀ u₁ ∧ p.2 ∈ Icc v₀ v₁ := hp
  let E : ℝ × ℝ → ℝ :=
    fun q => M * (|q.1 - p.1| + |q.2 - p.2|)
  have hE : Tendsto E (𝓝[regularRectangle u₀ u₁ v₀ v₁] p) (𝓝 0) := by
    have hcont : ContinuousAt E p := by
      dsimp [E]
      fun_prop
    have hle :
        𝓝[regularRectangle u₀ u₁ v₀ v₁] p ≤ 𝓝 p := inf_le_left
    have hlim := hcont.tendsto.mono_left hle
    simpa only [E, sub_self, abs_zero, zero_add, mul_zero] using hlim
  have hBound : ∀ᶠ q in 𝓝[regularRectangle u₀ u₁ v₀ v₁] p,
      |F q.1 q.2 - F p.1 p.2| ≤ E q := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : q.1 ∈ Icc u₀ u₁ ∧ q.2 ∈ Icc v₀ v₁ := hq
    have htri : |F q.1 q.2 - F p.1 p.2| ≤
        |F q.1 q.2 - F p.1 q.2| +
          |F p.1 q.2 - F p.1 p.2| := by
      have heq : F q.1 q.2 - F p.1 p.2 =
          (F q.1 q.2 - F p.1 q.2) +
            (F p.1 q.2 - F p.1 p.2) := by ring
      rw [heq]
      exact abs_add_le _ _
    exact htri.trans (by
      dsimp [E]
      linarith [hU q.2 hq'.2 q.1 hq'.1 p.1 hp'.1,
        hV p.1 hp'.1 q.2 hq'.2 p.2 hp'.2])
  have hzero :
      Tendsto (fun q : ℝ × ℝ => |F q.1 q.2 - F p.1 p.2|)
        (𝓝[regularRectangle u₀ u₁ v₀ v₁] p) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hBound hE
  exact tendsto_iff_dist_tendsto_zero.mpr (by
    simpa only [Real.dist_eq] using hzero)

/-- The frozen radius primitives and the local BV bounds make the radius
jointly continuous on a closed off-axis rectangle. -/
theorem regular_rectangle_radius_continuousOn
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2)
      (regularRectangle u₀ u₁ v₀ v₁) := by
  obtain ⟨c, B_lam, Bν, Bφ, Bθ, Bζ, hc, hB_lam, hBν,
    hBφ, hBθ, hBζ, hfield⟩ :=
    regular_rectangle_field_bounds h hu hv hR
  let M := max B_lam Bν
  apply regular_rectangle_continuousOn_of_slice_lipschitz (M := M)
  · intro v hv' u hu' u' hu''
    have hs := regularRectangle_inSeg_subset hR hv'
    have hlip := regular_intervalPrimitive_lipschitz hu
      (F := fun x => S.r x v) (g := fun x => S.nu x v) (M := Bν)
      (by
        intro x hx y hy hxy
        exact h.solution.radius_in v x y hxy
          ((inSeg_subsegment hx.1 hxy hy.2).trans hs))
      (by intro x hx; exact (hfield x hx v hv').2.2.2.1)
      u hu' u' hu''
    exact hlip.trans (mul_le_mul_of_nonneg_right
      (le_max_right B_lam Bν) (abs_nonneg _))
  · intro u hu' v hv' v' hv''
    have hs := regularRectangle_outSeg_subset hR hu'
    have hlip := regular_intervalPrimitive_lipschitz hv
      (F := S.r u) (g := S.lam u) (M := B_lam)
      (by
        intro x hx y hy hxy
        exact h.solution.radius_out u x y hxy
          ((outSeg_subsegment hx.1 hxy hy.2).trans hs))
      (by intro x hx; exact (hfield u hu' x hx).2.2.1)
      v hv' v' hv''
    exact hlip.trans (mul_le_mul_of_nonneg_right
      (le_max_left B_lam Bν) (abs_nonneg _))

/-- A quadratic mass density is bounded by the scalar amplitude and the
absolute lower expansion. The sign of the expansion is immaterial. -/
theorem regular_mass_density_abs_le
    {g z d c B : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hc : 0 < c) (hd : c ≤ |d|)
    (hB : 0 ≤ B) (hz : |z| ≤ B) :
    |g * z ^ 2 / (2 * d)| ≤ B ^ 2 / (2 * c) := by
  have hnum0 : 0 ≤ g * z ^ 2 := mul_nonneg hg0 (sq_nonneg z)
  have hsq : z ^ 2 ≤ B ^ 2 := by
    exact (sq_le_sq).2 (by simpa only [abs_of_nonneg hB] using hz)
  have hnum : g * z ^ 2 ≤ B ^ 2 := by
    calc
      g * z ^ 2 ≤ 1 * z ^ 2 :=
        mul_le_mul_of_nonneg_right hg1 (sq_nonneg z)
      _ = z ^ 2 := one_mul _
      _ ≤ B ^ 2 := hsq
  have hdpos : 0 < |d| := hc.trans_le hd
  have hden : 0 < 2 * |d| := by positivity
  have hdenC : 0 < 2 * c := by positivity
  have hdiv : g * z ^ 2 / (2 * |d|) ≤ B ^ 2 / (2 * c) := by
    apply (div_le_div_iff₀ hden hdenC).2
    calc
      (g * z ^ 2) * (2 * c) ≤ B ^ 2 * (2 * c) :=
        mul_le_mul_of_nonneg_right hnum hdenC.le
      _ ≤ B ^ 2 * (2 * |d|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg B)
  have habs : |g * z ^ 2 / (2 * d)| =
      g * z ^ 2 / (2 * |d|) := by
    rw [abs_div, abs_of_nonneg hnum0, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs]
  exact hdiv

/-- The signed mass primitives have uniformly bounded densities on a regular
rectangle, so the mass is jointly continuous there. -/
theorem regular_rectangle_mass_continuousOn
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    ContinuousOn (fun p : ℝ × ℝ => S.m p.1 p.2)
      (regularRectangle u₀ u₁ v₀ v₁) := by
  obtain ⟨c, B_lam, Bν, Bφ, Bθ, Bζ, hc, hB_lam, hBν,
    hBφ, hBθ, hBζ, hfield⟩ :=
    regular_rectangle_field_bounds h hu hv hR
  let M := max (Bθ ^ 2 / (2 * c)) (Bζ ^ 2 / (2 * c))
  have hmassOut (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁) :
      |IsBVSolution.massV S u v| ≤ M := by
    have hpt : (u, v) ∈ U := hR ⟨hu', hv'⟩
    obtain ⟨hlam, _, _, _, _, hθ, _⟩ := hfield u hu' v hv'
    obtain ⟨hμ0, hμ1⟩ := h.mass_ratio_bounds hpt
    have hgap0 : 0 ≤ 1 - 2 * S.m u v / S.r u v := by linarith
    have hgap1 : 1 - 2 * S.m u v / S.r u v ≤ 1 := by linarith
    have hlamPos : 0 < S.lam u v := hc.trans_le hlam
    have hden : c ≤ |S.lam u v| := by
      rwa [abs_of_pos hlamPos]
    have hbound := regular_mass_density_abs_le hgap0 hgap1 hc hden hBθ hθ
    have hh : |IsBVSolution.massV S u v| ≤ Bθ ^ 2 / (2 * c) := by
      exact hbound
    exact hh.trans (le_max_left _ _)
  have hmassIn (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁) :
      |IsBVSolution.massInDensity S u v| ≤ M := by
    have hpt : (u, v) ∈ U := hR ⟨hu', hv'⟩
    obtain ⟨_, hnu, _, _, _, _, hζ⟩ := hfield u hu' v hv'
    obtain ⟨hμ0, hμ1⟩ := h.mass_ratio_bounds hpt
    have hgap0 : 0 ≤ 1 - 2 * S.m u v / S.r u v := by linarith
    have hgap1 : 1 - 2 * S.m u v / S.r u v ≤ 1 := by linarith
    have hnuNeg : S.nu u v < 0 := lt_of_le_of_lt hnu (neg_lt_zero.mpr hc)
    have hden : c ≤ |S.nu u v| := by
      rw [abs_of_neg hnuNeg]
      linarith
    have hbound := regular_mass_density_abs_le hgap0 hgap1 hc hden hBζ hζ
    have hh : |IsBVSolution.massInDensity S u v| ≤ Bζ ^ 2 / (2 * c) := by
      exact hbound
    exact hh.trans (le_max_right _ _)
  apply regular_rectangle_continuousOn_of_slice_lipschitz (M := M)
  · intro v hv' u hu' u' hu''
    have hs := regularRectangle_inSeg_subset hR hv'
    exact regular_intervalPrimitive_lipschitz hu
      (F := fun x => S.m x v)
      (g := fun x => IsBVSolution.massInDensity S x v) (M := M)
      (by
        intro x hx y hy hxy
        change IntervalPrimitive (fun t => S.m t v)
          (fun t => (1 - 2 * S.m t v / S.r t v) *
            S.zeta t v ^ 2 / (2 * S.nu t v)) x y
        exact h.solution.mass_in v x y hxy
          ((inSeg_subsegment hx.1 hxy hy.2).trans hs))
      (by intro x hx; exact hmassIn x hx v hv')
      u hu' u' hu''
  · intro u hu' v hv' v' hv''
    have hs := regularRectangle_outSeg_subset hR hu'
    exact regular_intervalPrimitive_lipschitz hv
      (F := S.m u)
      (g := IsBVSolution.massV S u) (M := M)
      (by
        intro x hx y hy hxy
        change IntervalPrimitive (S.m u)
          (fun t => (1 - 2 * S.m u t / S.r u t) *
            S.theta u t ^ 2 / (2 * S.lam u t)) x y
        exact h.solution.mass_out u x y hxy
          ((outSeg_subsegment hx.1 hxy hy.2).trans hs))
      (by intro x hx; exact hmassOut u hu' x hx)
      v hv' v' hv''

/-- Joint continuity upgrades the pointwise BV sign of the mass gap to a
positive minimum on a closed regular rectangle. -/
theorem regular_rectangle_gap_lower
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        δ ≤ 1 - 2 * S.m u v / S.r u v := by
  have hrcont := regular_rectangle_radius_continuousOn h hu hv hR
  have hmcont := regular_rectangle_mass_continuousOn h hu hv hR
  have hrne : ∀ p ∈ regularRectangle u₀ u₁ v₀ v₁,
      S.r p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (h.solution.radius_pos p (hR hp))
  have hgapcont : ContinuousOn
      (fun p : ℝ × ℝ => 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2)
      (regularRectangle u₀ u₁ v₀ v₁) := by
    have hconst : ContinuousOn (fun _ : ℝ × ℝ => (1 : ℝ))
        (regularRectangle u₀ u₁ v₀ v₁) := continuousOn_const
    have hmul : ContinuousOn
        (fun p : ℝ × ℝ => 2 * S.m p.1 p.2)
        (regularRectangle u₀ u₁ v₀ v₁) := by
      convert
        (continuousOn_const.mul hmcont : ContinuousOn
          ((fun _ : ℝ × ℝ => (2 : ℝ)) *
            fun p : ℝ × ℝ => S.m p.1 p.2)
          (regularRectangle u₀ u₁ v₀ v₁)) using 1
    exact hconst.sub (hmul.div hrcont hrne)
  have hcompact : IsCompact (regularRectangle u₀ u₁ v₀ v₁) := by
    simpa only [regularRectangle] using isCompact_Icc.prod isCompact_Icc
  have hnonempty : (regularRectangle u₀ u₁ v₀ v₁).Nonempty :=
    ⟨(u₀, v₀), ⟨⟨le_rfl, hu⟩, ⟨le_rfl, hv⟩⟩⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hcompact.exists_isMinOn hnonempty hgapcont
  have hδ : 0 <
      1 - 2 * S.m p₀.1 p₀.2 / S.r p₀.1 p₀.2 := by
    have hlt := (h.mass_ratio_bounds (hR hp₀)).2
    linarith
  refine ⟨_, hδ, ?_⟩
  intro u hu' v hv'
  exact hmin (a := (u, v)) ⟨hu', hv'⟩

/-- A fixed pair has positive radius, mass-gap, and expansion bounds and
finite field amplitudes on each closed off-axis rectangle. All constants may
depend on that rectangle and on the pair. -/
theorem regular_rectangle_basic_bounds
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hsep : u₁ < v₀)
    (hR₁ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₁)
    (hR₂ : regularRectangle u₀ u₁ v₀ v₁ ⊆ U₂) :
    ∃ ρ δ c C : ℝ, 0 < ρ ∧ 0 < δ ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
        ∀ S : Fields, (S = S₁ ∨ S = S₂) →
          ρ ≤ S.r u v ∧ δ ≤ 1 - 2 * S.m u v / S.r u v ∧
          c ≤ S.lam u v ∧ S.nu u v ≤ -c ∧
          |S.lam u v| ≤ C ∧ |S.nu u v| ≤ C ∧
          |S.phi u v| ≤ C ∧ |S.theta u v| ≤ C ∧
          |S.zeta u v| ≤ C := by
  obtain ⟨ρ, hρ, hr⟩ :=
    regular_rectangle_radius_lower h₁ h₂ hu hv hsep hR₁ hR₂
  obtain ⟨δ₁, hδ₁, hgap₁⟩ :=
    regular_rectangle_gap_lower h₁ hu hv hR₁
  obtain ⟨δ₂, hδ₂, hgap₂⟩ :=
    regular_rectangle_gap_lower h₂ hu hv hR₂
  obtain ⟨c₁, B_lam₁, Bν₁, Bφ₁, Bθ₁, Bζ₁,
    hc₁, hB_lam₁, hBν₁, hBφ₁, hBθ₁, hBζ₁, hfield₁⟩ :=
    regular_rectangle_field_bounds h₁ hu hv hR₁
  obtain ⟨c₂, B_lam₂, Bν₂, Bφ₂, Bθ₂, Bζ₂,
    hc₂, hB_lam₂, hBν₂, hBφ₂, hBθ₂, hBζ₂, hfield₂⟩ :=
    regular_rectangle_field_bounds h₂ hu hv hR₂
  let δ := min δ₁ δ₂
  let c := min c₁ c₂
  let C := 1 + B_lam₁ + Bν₁ + Bφ₁ + Bθ₁ + Bζ₁ +
    B_lam₂ + Bν₂ + Bφ₂ + Bθ₂ + Bζ₂
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  refine ⟨ρ, δ, c, C, hρ, lt_min hδ₁ hδ₂,
    lt_min hc₁ hc₂, hC, ?_⟩
  intro u hu' v hv' S hS
  rcases hS with rfl | rfl
  · obtain ⟨hlam, hnu, hblam, hbnu, hbphi, hbtheta, hbzeta⟩ :=
      hfield₁ u hu' v hv'
    have hr' := (hr u hu' v hv').1
    have hg' := hgap₁ u hu' v hv'
    refine ⟨hr', (min_le_left δ₁ δ₂).trans hg',
      (min_le_left c₁ c₂).trans hlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [min_le_left c₁ c₂]
    all_goals dsimp [C]; linarith
  · obtain ⟨hlam, hnu, hblam, hbnu, hbphi, hbtheta, hbzeta⟩ :=
      hfield₂ u hu' v hv'
    have hr' := (hr u hu' v hv').2
    have hg' := hgap₂ u hu' v hv'
    refine ⟨hr', (min_le_right δ₁ δ₂).trans hg',
      (min_le_right c₁ c₂).trans hlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [min_le_right c₁ c₂]
    all_goals dsimp [C]; linarith

/-- Bounding `θ,λ,φ` also bounds the corresponding scalar-radius primitive
density, and likewise for `ζ,ν,φ`. -/
theorem regular_scalar_density_abs_le
    {a l p C : ℝ} (hC : 0 ≤ C)
    (ha : |a| ≤ C) (hl : |l| ≤ C) (hp : |p| ≤ C) :
    |a + l * p| ≤ C + C ^ 2 := by
  have hprod : |l * p| ≤ C ^ 2 := by
    rw [abs_mul, pow_two]
    exact (mul_le_mul_of_nonneg_right hl (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hp hC)
  exact (abs_add_le _ _).trans (add_le_add ha hprod)

/-- The scalar-radius field is jointly continuous on a regular rectangle. -/
theorem regular_rectangle_scalar_radius_continuousOn
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2 * S.phi p.1 p.2)
      (regularRectangle u₀ u₁ v₀ v₁) := by
  obtain ⟨c, B_lam, Bν, Bφ, Bθ, Bζ, hc, hB_lam, hBν,
    hBφ, hBθ, hBζ, hfield⟩ :=
    regular_rectangle_field_bounds h hu hv hR
  let C := 1 + B_lam + Bν + Bφ + Bθ + Bζ
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hα (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁) :
      |S.alpha u v| ≤ C + C ^ 2 := by
    obtain ⟨_, _, hlam, _, hphi, htheta, _⟩ := hfield u hu' v hv'
    have hθC : |S.theta u v| ≤ C := by dsimp [C]; linarith
    have hLamC : |S.lam u v| ≤ C := by dsimp [C]; linarith
    have hφC : |S.phi u v| ≤ C := by dsimp [C]; linarith
    have heq : S.alpha u v =
        S.theta u v + S.lam u v * S.phi u v := by
      dsimp [Fields.theta]
      ring
    rw [heq]
    exact regular_scalar_density_abs_le hC hθC hLamC hφC
  have hβ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁) :
      |S.beta u v| ≤ C + C ^ 2 := by
    obtain ⟨_, _, _, hnu, hphi, _, hzeta⟩ := hfield u hu' v hv'
    have hζC : |S.zeta u v| ≤ C := by dsimp [C]; linarith
    have hνC : |S.nu u v| ≤ C := by dsimp [C]; linarith
    have hφC : |S.phi u v| ≤ C := by dsimp [C]; linarith
    have heq : S.beta u v =
        S.zeta u v + S.nu u v * S.phi u v := by
      dsimp [Fields.zeta]
      ring
    rw [heq]
    exact regular_scalar_density_abs_le hC hζC hνC hφC
  apply regular_rectangle_continuousOn_of_slice_lipschitz
    (F := fun u v => S.r u v * S.phi u v) (M := C + C ^ 2)
  · intro v hv' u hu' u' hu''
    have hs := regularRectangle_inSeg_subset hR hv'
    exact regular_intervalPrimitive_lipschitz hu
      (F := fun x => S.r x v * S.phi x v)
      (g := fun x => S.beta x v) (M := C + C ^ 2)
      (by
        intro x hx y hy hxy
        exact h.solution.scalar_radius_in v x y hxy
          ((inSeg_subsegment hx.1 hxy hy.2).trans hs))
      (by intro x hx; exact hβ x hx v hv')
      u hu' u' hu''
  · intro u hu' v hv' v' hv''
    have hs := regularRectangle_outSeg_subset hR hu'
    exact regular_intervalPrimitive_lipschitz hv
      (F := fun y => S.r u y * S.phi u y)
      (g := S.alpha u) (M := C + C ^ 2)
      (by
        intro x hx y hy hxy
        exact h.solution.scalar_radius_out u x y hxy
          ((outSeg_subsegment hx.1 hxy hy.2).trans hs))
      (by intro x hx; exact hα u hu' x hx)
      v hv' v' hv''

/-- All three primary fields are jointly continuous on a closed regular
rectangle. -/
theorem regular_rectangle_primary_continuousOn
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (hR : regularRectangle u₀ u₁ v₀ v₁ ⊆ U) :
    ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2)
        (regularRectangle u₀ u₁ v₀ v₁) ∧
      ContinuousOn (fun p : ℝ × ℝ => S.phi p.1 p.2)
        (regularRectangle u₀ u₁ v₀ v₁) ∧
      ContinuousOn (fun p : ℝ × ℝ => S.m p.1 p.2)
        (regularRectangle u₀ u₁ v₀ v₁) := by
  have hr := regular_rectangle_radius_continuousOn h hu hv hR
  have hm := regular_rectangle_mass_continuousOn h hu hv hR
  have hψ := regular_rectangle_scalar_radius_continuousOn h hu hv hR
  have hrne : ∀ p ∈ regularRectangle u₀ u₁ v₀ v₁,
      S.r p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (h.solution.radius_pos p (hR hp))
  have hφ : ContinuousOn (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (regularRectangle u₀ u₁ v₀ v₁) := by
    have hdiv := hψ.div hr hrne
    apply hdiv.congr
    intro p hp
    dsimp
    field_simp [hrne p hp]
  exact ⟨hr, hφ, hm⟩

end ChristodoulouBV.Uniqueness

end
