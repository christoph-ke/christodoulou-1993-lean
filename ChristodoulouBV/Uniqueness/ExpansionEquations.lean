module

public import ChristodoulouBV.Uniqueness.GoodVTraces
public import ChristodoulouBV.Uniqueness.RadiusMassTerm
public import ChristodoulouBV.Uniqueness.RadiusScalar
public import ChristodoulouBV.BVSolution.AxisExponential
public import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation

/-!
# Expansion comparison along characteristics

The outgoing boundary value is a one-sided BV trace. The comparison norms
sample only the fixed conull set of incoming coordinates.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The one-sided difference of outgoing expansions at the axis is bounded by
the good-ray expansion norm. The actual values at the axis play no role. -/
theorem ComparisonData.lam_axis_trace_le_L (D : ComparisonData)
    {V u : ℝ} (_haV : D.a < V) (hVb : V < D.b)
    (hu : u ∈ Ico D.a V) :
    ∃ l : ℝ,
      Tendsto (fun v => D.S₁.lam u v - D.S₂.lam u v) (𝓝[>] u) (𝓝 l) ∧
      |l| ≤ D.L V := by
  have hpoint : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  have hp := D.hT hpoint
  obtain ⟨l₁, hl₁⟩ := D.h₁.exists_lam_axis_limit_out hp.1
  obtain ⟨l₂, hl₂⟩ := D.h₂.exists_lam_axis_limit_out hp.2
  refine ⟨l₁ - l₂, hl₁.sub hl₂, ?_⟩
  obtain ⟨K₁, hK₁, _⟩ := D.h₁.exists_uniform_radius_upper
  obtain ⟨K₂, hK₂, _⟩ := D.h₂.exists_uniform_radius_upper
  let M := max (K₁ + K₂) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x y, (x, y) ∈ triangle D.a V →
      y ∈ D.goodV → |D.S₁.lam x y - D.S₂.lam x y| ≤ M := by
    intro x y hxy _
    have hp' := D.hT ((mem_triangle).2
      ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩)
    have hpos₁ := D.h₁.solution.lam_pos (x, y) hp'.1
    have hpos₂ := D.h₂.solution.lam_pos (x, y) hp'.2
    calc
      |D.S₁.lam x y - D.S₂.lam x y| ≤
          |D.S₁.lam x y| + |D.S₂.lam x y| := abs_sub _ _
      _ = D.S₁.lam x y + D.S₂.lam x y := by
        rw [abs_of_pos hpos₁, abs_of_pos hpos₂]
      _ ≤ K₁ + K₂ := add_le_add (hK₁ (x, y) hp'.1) (hK₂ (x, y) hp'.2)
      _ ≤ M := le_max_left _ _
  have hpointBound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.lam x y - D.S₂.lam x y| ≤ D.L V :=
    D.le_goodVNorm hM hbound hxy hyG
  have hcl : u ∈ closure (D.goodV ∩ Ioo u V) := by
    have hs : Ioo u V ⊆ closure (D.goodV ∩ Ioo u V) := by
      simpa only [inter_comm] using
        (D.goodV_properties).2.1.open_subset_closure_inter isOpen_Ioo
    have hs' := closure_mono hs
    rw [closure_closure, closure_Ioo (ne_of_lt hu.2)] at hs'
    exact hs' ⟨le_rfl, hu.2.le⟩
  have hne : (𝓝[D.goodV ∩ Ioo u V] u).NeBot :=
    mem_closure_iff_clusterPt.mp hcl
  have hfilter : 𝓝[D.goodV ∩ Ioo u V] u ≤ 𝓝[>] u := by
    apply nhdsWithin_mono
    intro x hx
    exact hx.2.1
  have hlim : Tendsto
      (fun v => |D.S₁.lam u v - D.S₂.lam u v|)
      (𝓝[D.goodV ∩ Ioo u V] u) (𝓝 |l₁ - l₂|) :=
    (hl₁.sub hl₂).abs.mono_left hfilter
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact hpointBound u v ((mem_triangle).2 ⟨hu.1, hv.2.1, hv.2.2⟩) hv.1

private theorem intervalPrimitive_sub
    {f₁ f₂ g₁ g₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : IntervalPrimitive f₁ g₁ a b)
    (h₂ : IntervalPrimitive f₂ g₂ a b) :
    IntervalPrimitive (fun x => f₁ x - f₂ x)
      (fun x => g₁ x - g₂ x) a b := by
  refine ⟨h₁.1.sub h₂.1, ?_⟩
  rw [intervalIntegral.integral_sub h₁.1 h₂.1, ← h₁.2, ← h₂.2]
  ring

/-- The difference of the outgoing expansion primitives obeys the exact
integral mixed-radius equation on each closed subsegment away from the axis. -/
theorem ComparisonData.nu_difference_integral (D : ComparisonData)
    {u x y : ℝ} (hau : D.a ≤ u) (hux : u < x)
    (hxy : x ≤ y) (hyb : y < D.b) :
    IntervalPrimitive
      (fun t => D.S₁.nu u t - D.S₂.nu u t)
      (fun t => IsBVSolution.radiusCoeff D.S₁ u t -
        IsBVSolution.radiusCoeff D.S₂ u t) x y := by
  have hseg : outSeg u x y ⊆ D.U₁ ∩ D.U₂ := by
    intro p hp
    rcases p with ⟨s, t⟩
    have hs : s = u := hp.1
    subst s
    exact D.hT ((mem_triangle).2
      ⟨hau, hux.trans_le hp.2.1, hp.2.2.trans_lt hyb⟩)
  have h₁ := D.h₁.solution.nu_out u x y hxy (fun p hp => (hseg hp).1)
  have h₂ := D.h₂.solution.nu_out u x y hxy (fun p hp => (hseg hp).2)
  change IntervalPrimitive (D.S₁.nu u)
    (IsBVSolution.radiusCoeff D.S₁ u) x y at h₁
  change IntervalPrimitive (D.S₂.nu u)
    (IsBVSolution.radiusCoeff D.S₂ u) x y at h₂
  exact intervalPrimitive_sub h₁ h₂

/-- The difference of the incoming expansion primitives obeys the same
mixed-radius equation on the full comparison triangle. -/
theorem ComparisonData.lam_difference_integral (D : ComparisonData)
    {v x y : ℝ} (hax : D.a ≤ x) (hxy : x ≤ y)
    (hyv : y < v) (hvb : v < D.b) :
    IntervalPrimitive
      (fun t => D.S₁.lam t v - D.S₂.lam t v)
      (fun t => IsBVSolution.radiusCoeff D.S₁ t v -
        IsBVSolution.radiusCoeff D.S₂ t v) x y := by
  have hseg : inSeg v x y ⊆ D.U₁ ∩ D.U₂ := by
    intro p hp
    rcases p with ⟨s, t⟩
    have ht : t = v := hp.2
    subst t
    exact D.hT ((mem_triangle).2
      ⟨hax.trans hp.1.1, hp.1.2.trans_lt hyv, hvb⟩)
  have h₁ := D.h₁.solution.lam_in v x y hxy (fun p hp => (hseg hp).1)
  have h₂ := D.h₂.solution.lam_in v x y hxy (fun p hp => (hseg hp).2)
  change IntervalPrimitive (fun t => D.S₁.lam t v)
    (fun t => IsBVSolution.radiusCoeff D.S₁ t v) x y at h₁
  change IntervalPrimitive (fun t => D.S₂.lam t v)
    (fun t => IsBVSolution.radiusCoeff D.S₂ t v) x y at h₂
  exact intervalPrimitive_sub h₁ h₂

private theorem outgoing_radius_coefficient_algebra
    {μ₁ μ₂ l₁ l₂ n₁ n₂ r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hg₁ : 1 - μ₁ ≠ 0) (hg₂ : 1 - μ₂ ≠ 0) :
    μ₁ * l₁ * n₁ / ((1 - μ₁) * r₁) -
      μ₂ * l₂ * n₂ / ((1 - μ₂) * r₂) =
    μ₁ * l₁ / ((1 - μ₁) * r₁) * (n₁ - n₂) +
      μ₂ * n₂ / ((1 - μ₂) * r₂) *
        ((l₁ - l₂) - l₁ * (r₁ - r₂) / r₁) +
      (μ₁ - μ₂) / ((1 - μ₁) * (1 - μ₂)) * l₁ / r₁ * n₂ := by
  field_simp
  ring

private theorem incoming_radius_coefficient_algebra
    {μ₁ μ₂ l₁ l₂ n₁ n₂ r₁ r₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hg₁ : 1 - μ₁ ≠ 0) (hg₂ : 1 - μ₂ ≠ 0) :
    μ₁ * l₁ * n₁ / ((1 - μ₁) * r₁) -
      μ₂ * l₂ * n₂ / ((1 - μ₂) * r₂) =
    μ₁ * n₁ / ((1 - μ₁) * r₁) * (l₁ - l₂) +
      μ₂ * l₂ / ((1 - μ₂) * r₂) *
        ((n₁ - n₂) - n₁ * (r₁ - r₂) / r₁) +
      (μ₁ - μ₂) / ((1 - μ₁) * (1 - μ₂)) * n₁ / r₁ * l₂ := by
  field_simp
  ring

/-- The outgoing mixed-radius difference equation, written with the first
solution's homogeneous coefficient and the two comparison forcing terms. -/
theorem ComparisonData.nu_difference_coefficient (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.radiusCoeff D.S₁ u v -
      IsBVSolution.radiusCoeff D.S₂ u v =
    (IsBVSolution.mu D.S₁ u v * D.S₁.lam u v /
      ((1 - IsBVSolution.mu D.S₁ u v) * D.S₁.r u v)) *
        (D.S₁.nu u v - D.S₂.nu u v) +
    (IsBVSolution.mu D.S₂ u v * D.S₂.nu u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
        ((D.S₁.lam u v - D.S₂.lam u v) -
          D.S₁.lam u v * (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) +
    (IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      D.S₁.lam u v / D.S₁.r u v * D.S₂.nu u v := by
  have hp := D.hT huv
  have hr₁ : D.S₁.r u v ≠ 0 :=
    ne_of_gt (D.h₁.solution.radius_pos (u, v) hp.1)
  have hr₂ : D.S₂.r u v ≠ 0 :=
    ne_of_gt (D.h₂.solution.radius_pos (u, v) hp.2)
  have hg₁ : 1 - IsBVSolution.mu D.S₁ u v ≠ 0 := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    unfold IsBVSolution.mu
    linarith
  have hg₂ : 1 - IsBVSolution.mu D.S₂ u v ≠ 0 := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    unfold IsBVSolution.mu
    linarith
  convert outgoing_radius_coefficient_algebra hr₁ hr₂ hg₁ hg₂ using 1; rfl

/-- The incoming mixed-radius difference equation, with the first solution's
incoming homogeneous coefficient. -/
theorem ComparisonData.lam_difference_coefficient (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.radiusCoeff D.S₁ u v -
      IsBVSolution.radiusCoeff D.S₂ u v =
    (IsBVSolution.mu D.S₁ u v * D.S₁.nu u v /
      ((1 - IsBVSolution.mu D.S₁ u v) * D.S₁.r u v)) *
        (D.S₁.lam u v - D.S₂.lam u v) +
    (IsBVSolution.mu D.S₂ u v * D.S₂.lam u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
        ((D.S₁.nu u v - D.S₂.nu u v) -
          D.S₁.nu u v * (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) +
    (IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      D.S₁.nu u v / D.S₁.r u v * D.S₂.lam u v := by
  have hp := D.hT huv
  have hr₁ : D.S₁.r u v ≠ 0 :=
    ne_of_gt (D.h₁.solution.radius_pos (u, v) hp.1)
  have hr₂ : D.S₂.r u v ≠ 0 :=
    ne_of_gt (D.h₂.solution.radius_pos (u, v) hp.2)
  have hg₁ : 1 - IsBVSolution.mu D.S₁ u v ≠ 0 := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    unfold IsBVSolution.mu
    linarith
  have hg₂ : 1 - IsBVSolution.mu D.S₂ u v ≠ 0 := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    unfold IsBVSolution.mu
    linarith
  convert incoming_radius_coefficient_algebra hr₁ hr₂ hg₁ hg₂ using 1; rfl

/-- On a compact outgoing subsegment, the expansion difference is absolutely
continuous and has the difference of the two mixed-radius densities as its
almost-everywhere derivative. `nu_difference_coefficient` expands that density
into the three terms of the outgoing comparison equation. -/
theorem ComparisonData.nu_difference_ae (D : ComparisonData)
    {u x y : ℝ} (hau : D.a ≤ u) (hux : u < x)
    (hxy : x ≤ y) (hyb : y < D.b) :
    AbsolutelyContinuousOnInterval
      (fun t => D.S₁.nu u t - D.S₂.nu u t) x y ∧
    ∀ᵐ t ∂volume, t ∈ Icc x y →
      deriv (fun s => D.S₁.nu u s - D.S₂.nu u s) t =
        IsBVSolution.radiusCoeff D.S₁ u t -
          IsBVSolution.radiusCoeff D.S₂ u t := by
  apply IntervalPrimitive.ac_ae_of_subsegments hxy
  intro s t hxs hst hty
  exact D.nu_difference_integral hau (hux.trans_le hxs) hst
    (hty.trans_lt hyb)

/-- On a compact incoming subsegment, the expansion difference is absolutely
continuous and has the corresponding mixed-radius difference as its
almost-everywhere derivative. `lam_difference_coefficient` supplies the
incoming comparison decomposition. -/
theorem ComparisonData.lam_difference_ae (D : ComparisonData)
    {v x y : ℝ} (hax : D.a ≤ x) (hxy : x ≤ y)
    (hyv : y < v) (hvb : v < D.b) :
    AbsolutelyContinuousOnInterval
      (fun t => D.S₁.lam t v - D.S₂.lam t v) x y ∧
    ∀ᵐ t ∂volume, t ∈ Icc x y →
      deriv (fun s => D.S₁.lam s v - D.S₂.lam s v) t =
        IsBVSolution.radiusCoeff D.S₁ t v -
          IsBVSolution.radiusCoeff D.S₂ t v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hxy
  intro s t hxs hst hty
  exact D.lam_difference_integral (hax.trans hxs) hst
    (hty.trans_lt hyv) hvb

private theorem absorb_expansion_bounds
    {L N Γ Γstar C ε : ℝ}
    (hC : 1 ≤ C) (hε : 0 ≤ ε)
    (hsmall : C ^ 2 * ε ≤ 1 / 2)
    (_hL : 0 ≤ L) (hN : 0 ≤ N)
    (hΓ : 0 ≤ Γ) (hΓstar : 0 ≤ Γstar)
    (hOut : N ≤ C * (L + Γ))
    (hIn : L ≤ C * (ε * N + Γstar)) :
    L ≤ 2 * C ^ 2 * (Γ + Γstar) ∧
      N ≤ 2 * C ^ 2 * (Γ + Γstar) := by
  have hCnonneg : 0 ≤ C := by linarith
  have hC₂ : C ≤ C ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hCnonneg]
  have hsmallN : C ^ 2 * ε * N ≤ N / 2 := by
    convert mul_le_mul_of_nonneg_right hsmall hN using 1; ring
  have hInC := mul_le_mul_of_nonneg_left hIn hCnonneg
  have hCΓ := mul_le_mul_of_nonneg_right hC₂ hΓ
  have hNbound : N ≤ 2 * C ^ 2 * (Γ + Γstar) := by
    nlinarith
  have hLbound : L ≤ 2 * C ^ 2 * (Γ + Γstar) := by
    have hεnonneg : 0 ≤ C * ε := mul_nonneg hCnonneg hε
    have hprod := mul_le_mul_of_nonneg_left hNbound hεnonneg
    have hsmall' : 2 * C ^ 2 * ε ≤ 1 := by linarith
    have hsmallC := mul_le_mul_of_nonneg_left hsmall' hCnonneg
    have hprod' := mul_le_mul_of_nonneg_right hsmallC
      (add_nonneg hΓ hΓstar)
    have hCΓstar := mul_le_mul_of_nonneg_right hC₂ hΓstar
    nlinarith
  exact ⟨hLbound, hNbound⟩

private theorem exp_abs_sub_le_of_nonpos {x y : ℝ}
    (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have hderiv (t : ℝ) (ht : t ∈ Iic (0 : ℝ)) :
      ‖deriv Real.exp t‖ ≤ (1 : ℝ) := by
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (s := Iic (0 : ℝ)) (C := 1)
    (fun t _ => Real.differentiableAt_exp) hderiv (convex_Iic 0) hy hx
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- The outgoing expansion difference has an exact axis-trace representation.
Its boundary contribution is controlled by the good-ray norm. -/
theorem ComparisonData.nu_difference_axis_formula (D : ComparisonData)
    {V u v : ℝ} (haV : D.a < V) (hVb : V < D.b)
    (huv : (u, v) ∈ triangle D.a V) :
    ∃ l₁ l₂ : ℝ,
      |l₁ - l₂| ≤ D.L V ∧
      Tendsto (D.S₂.lam u) (𝓝[>] u) (𝓝 l₂) ∧
      D.S₁.nu u v - D.S₂.nu u v =
        -(l₁ - l₂) *
          Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        l₂ * (Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
          Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)) := by
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hp := D.hT hfull
  obtain ⟨l₁, hlim₁, hν₁⟩ := D.h₁.nu_axis_exponential hp.1
  obtain ⟨l₂, hlim₂, hν₂⟩ := D.h₂.nu_axis_exponential hp.2
  obtain ⟨l, hlim, hbound⟩ :=
    D.lam_axis_trace_le_L haV hVb
      (show u ∈ Ico D.a V from ⟨huv.1, huv.2.1.trans huv.2.2⟩)
  have hl : l = l₁ - l₂ :=
    tendsto_nhds_unique hlim (hlim₁.sub hlim₂)
  refine ⟨l₁, l₂, hl ▸ hbound, hlim₂, ?_⟩
  rw [hν₁, hν₂]
  ring

/-- On a full comparison triangle, the incoming expansion has the exact
linear coefficient exponential formula from the initial characteristic. -/
theorem lam_in_exponential_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b) :
    S.lam u v =
      Real.exp (∫ s in a..u, IsBVSolution.incomingCoeff S s v) *
        S.lam a v := by
  have hav : a < v := huv.1.trans_lt huv.2.1
  have hseg : inSeg v a u ⊆ U := by
    intro p hp
    rcases p with ⟨s, t⟩
    have ht : t = v := hp.2
    subst t
    exact hT ((mem_triangle).2
      ⟨hp.1.1, hp.1.2.trans_lt huv.2.1, huv.2.2⟩)
  have hk : IntervalIntegrable
      (fun s => IsBVSolution.incomingCoeff S s v) volume a u :=
    h.incomingCoeff_integrable huv.1 huv.2.1 hseg
  have hprim (t : ℝ) (ht : t ∈ Icc a u) :
      IntervalPrimitive (fun s => S.lam s v)
        (fun s => IsBVSolution.radiusCoeff S s v) a t := by
    have hsub : inSeg v a t ⊆ U := by
      intro p hp
      apply hseg
      rcases p with ⟨s, w⟩
      exact ⟨⟨hp.1.1, hp.1.2.trans ht.2⟩, hp.2⟩
    change IntervalPrimitive (fun s => S.lam s v)
      (fun s => (2 * S.m s v / S.r s v) * S.lam s v * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) a t
    exact h.solution.lam_in v a t ht.1 hsub
  have hcoeff (s : ℝ) :
      IsBVSolution.radiusCoeff S s v =
        IsBVSolution.incomingCoeff S s v * S.lam s v := by
    unfold IsBVSolution.radiusCoeff IsBVSolution.incomingCoeff
    ring
  have hky : IntervalIntegrable
      (fun s => IsBVSolution.incomingCoeff S s v * S.lam s v)
      volume a u := by
    apply (hprim u ⟨huv.1, le_rfl⟩).1.congr_uIoo
    intro s _
    exact hcoeff s
  have hy : ∀ t ∈ Icc a u,
      S.lam t v - S.lam a v =
        ∫ s in a..t,
          (IsBVSolution.incomingCoeff S s v * S.lam s v + 0) := by
    intro t ht
    have hh := (hprim t ht).2
    have heq : (∫ s in a..t, IsBVSolution.radiusCoeff S s v) =
        ∫ s in a..t,
          IsBVSolution.incomingCoeff S s v * S.lam s v := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1
      intro s _
      exact hcoeff s
    rw [heq] at hh
    simpa only [add_zero] using hh
  have hformula := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    huv.1 hk intervalIntegrable_const hky hy
    (show u ∈ Icc a u from ⟨huv.1, le_rfl⟩)
  simpa using hformula

/-- On each good incoming ray, the initial expansion difference vanishes.
The remaining difference is exactly the difference of the two incoming
coefficient exponentials. -/
theorem ComparisonData.lam_difference_goodV_formula (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hvG : v ∈ D.goodV) :
    D.S₁.lam u v - D.S₂.lam u v =
      D.S₁.lam D.a v *
        (Real.exp (∫ s in D.a..u,
          IsBVSolution.incomingCoeff D.S₁ s v) -
         Real.exp (∫ s in D.a..u,
          IsBVSolution.incomingCoeff D.S₂ s v)) := by
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hinit : D.S₁.lam D.a v = D.S₂.lam D.a v := by
    have hv : v ∈ Ioo D.a D.b := ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩
    exact (hvG hv).1
  rw [lam_in_exponential_of_triangle D.h₁ hT₁ huv,
    lam_in_exponential_of_triangle D.h₂ hT₂ huv,
    ← hinit]
  ring

/-- Difference of the outgoing logarithmic transport coefficients. The
radius and mass-ratio errors are kept separate for weighted integration. -/
theorem ComparisonData.nuCoeff_difference_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.nuCoeff D.S₁ u v -
      IsBVSolution.nuCoeff D.S₂ u v =
    (IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
        ((D.S₁.lam u v - D.S₂.lam u v) -
          D.S₁.lam u v * (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) +
    (IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      D.S₁.lam u v / D.S₁.r u v := by
  have hp := D.hT huv
  have hr₁ : D.S₁.r u v ≠ 0 :=
    ne_of_gt (D.h₁.solution.radius_pos (u, v) hp.1)
  have hr₂ : D.S₂.r u v ≠ 0 :=
    ne_of_gt (D.h₂.solution.radius_pos (u, v) hp.2)
  have hg₁ : 1 - IsBVSolution.mu D.S₁ u v ≠ 0 := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    unfold IsBVSolution.mu
    linarith
  have hg₂ : 1 - IsBVSolution.mu D.S₂ u v ≠ 0 := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    unfold IsBVSolution.mu
    linarith
  rw [D.h₁.nuCoeff_eq_mass_ratio_coefficient_out hp.1,
    D.h₂.nuCoeff_eq_mass_ratio_coefficient_out hp.2]
  have hh := outgoing_radius_coefficient_algebra
    (μ₁ := IsBVSolution.mu D.S₁ u v)
    (μ₂ := IsBVSolution.mu D.S₂ u v)
    (l₁ := D.S₁.lam u v) (l₂ := D.S₂.lam u v)
    (n₁ := 1) (n₂ := 1) (r₁ := D.S₁.r u v) (r₂ := D.S₂.r u v)
    hr₁ hr₂ hg₁ hg₂
  simpa only [IsBVSolution.mu, mul_one, one_mul, sub_self, mul_zero,
    zero_add] using hh

/-- Difference of the incoming logarithmic transport coefficients. This
identity retains the unsigned coefficient needed for the usable (3.12). -/
theorem ComparisonData.incomingCoeff_difference_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.incomingCoeff D.S₁ u v -
      IsBVSolution.incomingCoeff D.S₂ u v =
    (IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
        ((D.S₁.nu u v - D.S₂.nu u v) -
          D.S₁.nu u v * (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) +
    (IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      D.S₁.nu u v / D.S₁.r u v := by
  have hp := D.hT huv
  have hr₁ : D.S₁.r u v ≠ 0 :=
    ne_of_gt (D.h₁.solution.radius_pos (u, v) hp.1)
  have hr₂ : D.S₂.r u v ≠ 0 :=
    ne_of_gt (D.h₂.solution.radius_pos (u, v) hp.2)
  have hg₁ : 1 - IsBVSolution.mu D.S₁ u v ≠ 0 := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    unfold IsBVSolution.mu
    linarith
  have hg₂ : 1 - IsBVSolution.mu D.S₂ u v ≠ 0 := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    unfold IsBVSolution.mu
    linarith
  have hh := incoming_radius_coefficient_algebra
    (μ₁ := IsBVSolution.mu D.S₁ u v)
    (μ₂ := IsBVSolution.mu D.S₂ u v)
    (l₁ := 1) (l₂ := 1)
    (n₁ := D.S₁.nu u v) (n₂ := D.S₂.nu u v)
    (r₁ := D.S₁.r u v) (r₂ := D.S₂.r u v)
    hr₁ hr₂ hg₁ hg₂
  have hcoeff₁ : IsBVSolution.incomingCoeff D.S₁ u v =
      IsBVSolution.mu D.S₁ u v * D.S₁.nu u v /
        ((1 - IsBVSolution.mu D.S₁ u v) * D.S₁.r u v) := by
    unfold IsBVSolution.incomingCoeff IsBVSolution.mu
    rfl
  have hcoeff₂ : IsBVSolution.incomingCoeff D.S₂ u v =
      IsBVSolution.mu D.S₂ u v * D.S₂.nu u v /
        ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) := by
    unfold IsBVSolution.incomingCoeff IsBVSolution.mu
    rfl
  rw [hcoeff₁, hcoeff₂]
  simpa only [IsBVSolution.mu, mul_one, one_mul, sub_self, mul_zero,
    zero_add] using hh

/-- On a good incoming ray, the expansion difference is bounded by the
integral of the absolute incoming coefficient difference. The exponential
factor costs no constant because both incoming coefficients are nonpositive. -/
theorem ComparisonData.lam_difference_le_integral_coeff (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hvG : v ∈ D.goodV) :
    |D.S₁.lam u v - D.S₂.lam u v| ≤
      |D.S₁.lam D.a v| *
        (∫ s in D.a..u,
          |IsBVSolution.incomingCoeff D.S₁ s v -
            IsBVSolution.incomingCoeff D.S₂ s v|) := by
  have hseg : inSeg v D.a u ⊆ D.U₁ ∩ D.U₂ := by
    intro p hp
    rcases p with ⟨s, t⟩
    have ht : t = v := hp.2
    subst t
    exact D.hT ((mem_triangle).2
      ⟨hp.1.1, hp.1.2.trans_lt huv.2.1, huv.2.2⟩)
  have hk₁ : IntervalIntegrable
      (fun s => IsBVSolution.incomingCoeff D.S₁ s v) volume D.a u :=
    D.h₁.incomingCoeff_integrable huv.1 huv.2.1
      (fun p hp => (hseg hp).1)
  have hk₂ : IntervalIntegrable
      (fun s => IsBVSolution.incomingCoeff D.S₂ s v) volume D.a u :=
    D.h₂.incomingCoeff_integrable huv.1 huv.2.1
      (fun p hp => (hseg hp).2)
  have hnonpos (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      (∫ s in D.a..u, IsBVSolution.incomingCoeff S s v) ≤ 0 := by
    have hnonneg : 0 ≤ ∫ s in D.a..u,
        -IsBVSolution.incomingCoeff S s v := by
      apply intervalIntegral.integral_nonneg huv.1
      intro s hs
      have hpt : (s, v) ∈ triangle D.a D.b :=
        (mem_triangle).2
          ⟨hs.1, hs.2.trans_lt huv.2.1, huv.2.2⟩
      rcases hS with rfl | rfl
      · exact neg_nonneg.mpr (D.h₁.incomingCoeff_nonpos (D.hT hpt).1)
      · exact neg_nonneg.mpr (D.h₂.incomingCoeff_nonpos (D.hT hpt).2)
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  have hExp := exp_abs_sub_le_of_nonpos
    (hnonpos D.S₁ (Or.inl rfl)) (hnonpos D.S₂ (Or.inr rfl))
  have hIntEq :
      (∫ s in D.a..u, IsBVSolution.incomingCoeff D.S₁ s v) -
        (∫ s in D.a..u, IsBVSolution.incomingCoeff D.S₂ s v) =
      ∫ s in D.a..u,
        (IsBVSolution.incomingCoeff D.S₁ s v -
          IsBVSolution.incomingCoeff D.S₂ s v) := by
    exact (intervalIntegral.integral_sub hk₁ hk₂).symm
  rw [D.lam_difference_goodV_formula huv hvG, abs_mul]
  calc
    |D.S₁.lam D.a v| *
        |Real.exp (∫ s in D.a..u, IsBVSolution.incomingCoeff D.S₁ s v) -
          Real.exp (∫ s in D.a..u, IsBVSolution.incomingCoeff D.S₂ s v)| ≤
      |D.S₁.lam D.a v| *
        |(∫ s in D.a..u, IsBVSolution.incomingCoeff D.S₁ s v) -
          (∫ s in D.a..u, IsBVSolution.incomingCoeff D.S₂ s v)| :=
      mul_le_mul_of_nonneg_left hExp (abs_nonneg _)
    _ = |D.S₁.lam D.a v| *
        |∫ s in D.a..u,
          (IsBVSolution.incomingCoeff D.S₁ s v -
            IsBVSolution.incomingCoeff D.S₂ s v)| := by rw [hIntEq]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (intervalIntegral.abs_integral_le_integral_abs huv.1) (abs_nonneg _)

end ChristodoulouBV.Uniqueness

end
