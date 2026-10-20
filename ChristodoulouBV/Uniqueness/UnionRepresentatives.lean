module

public import ChristodoulouBV.Frozen.Theorem3_1Unique
public import ChristodoulouBV.BVSolution.PrimitiveCalculus
import ChristodoulouBV.BVSolution.InitialData
import ChristodoulouBV.BVSolution.AxisExponential

/-!
# Representatives on the union of two BV developments

The three pointwise fields are selected using Theorem 3.1 uniqueness. The
outgoing primitive densities are compared almost everywhere on every compact
part of the overlap; no pointwise convention for BV representatives is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The three fields whose values are fixed by Theorem 3.1 uniqueness. -/
structure PrimaryFields where
  r : ℝ → ℝ → ℝ
  phi : ℝ → ℝ → ℝ
  m : ℝ → ℝ → ℝ

/-- Select the first solution on its domain, and the second elsewhere. Outside
the union the choice is immaterial. -/
noncomputable def commonPrimary (U₁ : Set (ℝ × ℝ)) (S₁ S₂ : Fields) :
    PrimaryFields := by
  classical
  exact {
    r := fun u v => if (u, v) ∈ U₁ then S₁.r u v else S₂.r u v
    phi := fun u v => if (u, v) ∈ U₁ then S₁.phi u v else S₂.phi u v
    m := fun u v => if (u, v) ∈ U₁ then S₁.m u v else S₂.m u v }

/-- The common primary fields restrict to the first source on its domain. -/
theorem commonPrimary_eq_first {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    (commonPrimary U₁ S₁ S₂).r u v = S₁.r u v ∧
      (commonPrimary U₁ S₁ S₂).phi u v = S₁.phi u v ∧
      (commonPrimary U₁ S₁ S₂).m u v = S₁.m u v := by
  classical
  simp [commonPrimary, hp]

/-- The common primary fields restrict to the second source on its domain. -/
theorem commonPrimary_eq_second {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    (commonPrimary U₁ S₁ S₂).r u v = S₂.r u v ∧
      (commonPrimary U₁ S₁ S₂).phi u v = S₂.phi u v ∧
      (commonPrimary U₁ S₁ S₂).m u v = S₂.m u v := by
  by_cases hmem : (u, v) ∈ U₁
  · obtain ⟨hr, hφ, hm⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata
      (u, v) ⟨hmem, hp⟩
    classical
    simp only [commonPrimary, hmem, ↓reduceIte]
    exact ⟨hr, hφ, hm⟩
  · classical
    simp [commonPrimary, hmem]

/-- The outgoing radius densities agree almost everywhere on a compact
subsegment of the overlap. -/
theorem source_lam_ae_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U₁ ∩ U₂) :
    ∀ᵐ v ∂volume, v ∈ Icc a b → S₁.lam u v = S₂.lam u v := by
  apply IntervalPrimitive.same_primitive_ae_of_eqOn hab
    (fun x y hax hxy hyb =>
      h₁.solution.radius_out u x y hxy
        ((outSeg_subsegment hax hxy hyb).trans (fun p hp => (hseg hp).1)))
    (fun x y hax hxy hyb =>
      h₂.solution.radius_out u x y hxy
        ((outSeg_subsegment hax hxy hyb).trans (fun p hp => (hseg hp).2)))
  intro v hv
  exact (theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata (u, v)
    (hseg ⟨rfl, hv⟩)).1

/-- The outgoing scalar-radius densities agree almost everywhere on a compact
subsegment of the overlap. -/
theorem source_alpha_ae_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U₁ ∩ U₂) :
    ∀ᵐ v ∂volume, v ∈ Icc a b → S₁.alpha u v = S₂.alpha u v := by
  apply IntervalPrimitive.same_primitive_ae_of_eqOn hab
    (fun x y hax hxy hyb =>
      h₁.solution.scalar_radius_out u x y hxy
        ((outSeg_subsegment hax hxy hyb).trans (fun p hp => (hseg hp).1)))
    (fun x y hax hxy hyb =>
      h₂.solution.scalar_radius_out u x y hxy
        ((outSeg_subsegment hax hxy hyb).trans (fun p hp => (hseg hp).2)))
  intro v hv
  obtain ⟨hr, hφ, _⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata
    (u, v) (hseg ⟨rfl, hv⟩)
  change S₁.r u v * S₁.phi u v = S₂.r u v * S₂.phi u v
  rw [hr, hφ]

/-- A common almost-everywhere density on a nontrivial interval has a common
left trace whenever both one-sided limits exist. -/
theorem left_trace_eq_of_ae_eq
    {f g : ℝ → ℝ} {a b lf lg : ℝ} (hab : a < b)
    (hfg : ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = g t)
    (hf : Tendsto f (𝓝[<] b) (𝓝 lf))
    (hg : Tendsto g (𝓝[<] b) (𝓝 lg)) : lf = lg := by
  let good : Set ℝ := {t | t ∈ Ioo a b → f t = g t}
  have hdense : Dense good := volume.dense_of_ae hfg
  let s : Set ℝ := good ∩ Ioo a b
  have hbcl : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  have hscl : b ∈ closure s := by
    rw [mem_closure_iff]
    intro V hV hbV
    obtain ⟨t, htV, htI⟩ := (mem_closure_iff.mp hbcl) V hV hbV
    obtain ⟨y, hygood, hyopen⟩ :=
      hdense.exists_mem_open (isOpen_Ioo.inter hV) ⟨t, htI, htV⟩
    exact ⟨y, hyopen.2, ⟨hygood, hyopen.1⟩⟩
  have hne : (𝓝[s] b).NeBot := mem_closure_iff_clusterPt.mp hscl
  have hslt : s ⊆ Iio b := fun _ ht => ht.2.2
  have hEq : EqOn f g s := by
    intro y hy
    exact hy.1 hy.2
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left (nhdsWithin_mono b hslt))
    (hg.mono_left (nhdsWithin_mono b hslt))
    (hEq.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- A BV function on a nondegenerate closed interval has a left trace at its
right endpoint, in the ordinary left-neighborhood filter. -/
theorem exists_left_trace_of_bv_compact
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Icc a b)) :
    ∃ l : ℝ, Tendsto f (𝓝[<] b) (𝓝 l) := by
  obtain ⟨l, hl⟩ := hf.exists_tendsto_left b
  refine ⟨l, hl.mono_left ?_⟩
  have hs : Icc a b ∩ Iio b ∈ 𝓝[<] b :=
    mem_of_superset (Ioo_mem_nhdsLT hab)
      (fun _ ht => ⟨⟨ht.1.le, ht.2.le⟩, ht.2⟩)
  exact le_inf inf_le_left (le_principal_iff.mpr hs)

/-- A global finite variation bound restricts to any contained compact
interval. -/
theorem bv_on_compact_of_variation_bound
    {f : ℝ → ℝ} {s : Set ℝ} {a b C : ℝ}
    (hC : eVariationOn f s ≤ ENNReal.ofReal C)
    (hsub : Icc a b ⊆ s) : BoundedVariationOn f (Icc a b) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((eVariationOn.mono f hsub).trans hC)

/-- Both source expansions have the same left trace at the upper endpoint of
any nontrivial common outgoing segment. -/
theorem source_lam_left_trace_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u a b : ℝ} (hab : a < b)
    (hseg : outSeg u a b ⊆ U₁ ∩ U₂) :
    ∃ l : ℝ, Tendsto (S₁.lam u) (𝓝[<] b) (𝓝 l) ∧
      Tendsto (S₂.lam u) (𝓝[<] b) (𝓝 l) := by
  obtain ⟨C₁, hC₁, _⟩ := h₁.item1
  obtain ⟨C₂, hC₂, _⟩ := h₂.item1
  have hsub₁ : Icc a b ⊆ {v | (u, v) ∈ U₁} :=
    fun v hv => (hseg (by simp [outSeg, hv])).1
  have hsub₂ : Icc a b ⊆ {v | (u, v) ∈ U₂} :=
    fun v hv => (hseg (by simp [outSeg, hv])).2
  obtain ⟨l₁, hl₁⟩ := exists_left_trace_of_bv_compact hab
    (bv_on_compact_of_variation_bound (hC₁ u) hsub₁)
  obtain ⟨l₂, hl₂⟩ := exists_left_trace_of_bv_compact hab
    (bv_on_compact_of_variation_bound (hC₂ u) hsub₂)
  have heq := left_trace_eq_of_ae_eq hab
    ((source_lam_ae_on_overlap h₁ h₂ hdata hab.le hseg).mono
      (fun _ ht hIoo => ht ⟨hIoo.1.le, hIoo.2.le⟩)) hl₁ hl₂
  exact ⟨l₁, hl₁, heq ▸ hl₂⟩

/-- The scalar-radius outgoing density has finite variation on every compact
source segment, as `α = θ + λφ`. -/
theorem source_alpha_bv_on_compact
    {U : Set (ℝ × ℝ)} {S : Fields} (hS : IsBVSolution U S)
    {u a b : ℝ} (hseg : outSeg u a b ⊆ U) :
    BoundedVariationOn (S.alpha u) (Icc a b) := by
  obtain ⟨C_lam, hC_lam, _⟩ := hS.item1
  obtain ⟨C_phi, hC_phi, _⟩ := hS.item3_variation
  obtain ⟨C_theta, hC_theta, _⟩ := hS.item5
  have hsub : Icc a b ⊆ {v | (u, v) ∈ U} :=
    fun v hv => hseg (by simp [outSeg, hv])
  have hLamBV : BoundedVariationOn (S.lam u) (Icc a b) :=
    bv_on_compact_of_variation_bound (hC_lam u) hsub
  have hPhiBV : BoundedVariationOn (S.phi u) (Icc a b) :=
    bv_on_compact_of_variation_bound (hC_phi u) hsub
  have hThetaBV : BoundedVariationOn (S.theta u) (Icc a b) :=
    bv_on_compact_of_variation_bound (hC_theta u) hsub
  have hα : S.alpha u = S.theta u + S.lam u * S.phi u := by
    funext v
    simp only [Pi.add_apply, Pi.mul_apply, Fields.theta]
    ring
  rw [hα]
  exact hThetaBV.add (hLamBV.mul hPhiBV)

/-- Both scalar-radius outgoing densities have the same left trace at the
upper endpoint of any nontrivial common outgoing segment. -/
theorem source_alpha_left_trace_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u a b : ℝ} (hab : a < b)
    (hseg : outSeg u a b ⊆ U₁ ∩ U₂) :
    ∃ l : ℝ, Tendsto (S₁.alpha u) (𝓝[<] b) (𝓝 l) ∧
      Tendsto (S₂.alpha u) (𝓝[<] b) (𝓝 l) := by
  obtain ⟨l₁, hl₁⟩ := exists_left_trace_of_bv_compact hab
    (source_alpha_bv_on_compact h₁ (fun p hp => (hseg hp).1))
  obtain ⟨l₂, hl₂⟩ := exists_left_trace_of_bv_compact hab
    (source_alpha_bv_on_compact h₂ (fun p hp => (hseg hp).2))
  have heq := left_trace_eq_of_ae_eq hab
    ((source_alpha_ae_on_overlap h₁ h₂ hdata hab.le hseg).mono
      (fun _ ht hIoo => ht ⟨hIoo.1.le, hIoo.2.le⟩)) hl₁ hl₂
  exact ⟨l₁, hl₁, heq ▸ hl₂⟩

/-- Almost-everywhere equal densities with right limits have the same right
trace at the lower endpoint. -/
theorem right_trace_eq_of_ae_eq
    {f g : ℝ → ℝ} {a b lf lg : ℝ} (hab : a < b)
    (hfg : ∀ᵐ t ∂volume, t ∈ Ioc a b → f t = g t)
    (hf : Tendsto f (𝓝[>] a) (𝓝 lf))
    (hg : Tendsto g (𝓝[>] a) (𝓝 lg)) : lf = lg := by
  let good : Set ℝ := {t | t ∈ Ioc a b → f t = g t}
  have hdense : Dense good := volume.dense_of_ae hfg
  let s : Set ℝ := good ∩ Ioo a b
  have hacl : a ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  have hscl : a ∈ closure s := by
    rw [mem_closure_iff]
    intro V hV haV
    obtain ⟨t, htV, htI⟩ := (mem_closure_iff.mp hacl) V hV haV
    obtain ⟨y, hygood, hyopen⟩ :=
      hdense.exists_mem_open (isOpen_Ioo.inter hV) ⟨t, htI, htV⟩
    exact ⟨y, hyopen.2, ⟨hygood, hyopen.1⟩⟩
  have hne : (𝓝[s] a).NeBot := mem_closure_iff_clusterPt.mp hscl
  have hsgt : s ⊆ Ioi a := fun _ ht => ht.2.1
  have hEq : EqOn f g s := by
    intro y hy
    exact hy.1 ⟨hy.2.1, hy.2.2.le⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left (nhdsWithin_mono a hsgt))
    (hg.mono_left (nhdsWithin_mono a hsgt))
    (hEq.eventuallyEq_of_mem self_mem_nhdsWithin)

/-- The outgoing scalar-radius density is BV on the whole source slice. -/
theorem source_alpha_bv_on_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (hS : IsBVSolution U S)
    (u : ℝ) : BoundedVariationOn (S.alpha u) {v | (u, v) ∈ U} := by
  obtain ⟨C_lam, hC_lam, _⟩ := hS.item1
  obtain ⟨C_phi, hC_phi, _⟩ := hS.item3_variation
  obtain ⟨C_theta, hC_theta, _⟩ := hS.item5
  have hLamBV : BoundedVariationOn (S.lam u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC_lam u)
  have hPhiBV : BoundedVariationOn (S.phi u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC_phi u)
  have hThetaBV : BoundedVariationOn (S.theta u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC_theta u)
  have hα : S.alpha u = S.theta u + S.lam u * S.phi u := by
    funext v
    simp only [Pi.add_apply, Pi.mul_apply, Fields.theta]
    ring
  rw [hα]
  exact hThetaBV.add (hLamBV.mul hPhiBV)

/-- The outgoing scalar-radius density has a finite axis-side trace on every
actual outgoing slice. -/
theorem exists_alpha_axis_trace_out
    {U : Set (ℝ × ℝ)} {S : Fields} (hS : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ A : ℝ, Tendsto (S.alpha u) (𝓝[>] u) (𝓝 A) := by
  obtain ⟨A, hA⟩ := (source_alpha_bv_on_slice hS u).exists_tendsto_right u
  refine ⟨A, ?_⟩
  have hfilter : 𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u = 𝓝[>] u := by
    calc
      𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u =
          𝓝[>] u ⊓ 𝓟 {t | (u, t) ∈ U} := by
            simp only [nhdsWithin, ← Filter.inf_principal]
            ac_rfl
      _ = 𝓝[>] u := hS.solution.development.axis_filter_eq huv
  simpa only [hfilter] using hA

/-- The two source densities have common right traces at every common axis
slice, despite possible exceptional pointwise representative values. -/
theorem source_axis_right_traces_match
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    (∃ L : ℝ, Tendsto (S₁.lam u) (𝓝[>] u) (𝓝 L) ∧
      Tendsto (S₂.lam u) (𝓝[>] u) (𝓝 L)) ∧
    (∃ A : ℝ, Tendsto (S₁.alpha u) (𝓝[>] u) (𝓝 A) ∧
      Tendsto (S₂.alpha u) (𝓝[>] u) (𝓝 A)) := by
  have huv : u < v := (h₁.solution.development.wedge hp.1).2
  have hdata' (t : ℝ) (hut : u < t) (htv : t ≤ v) :
      S₁.r u t = S₂.r u t ∧ S₁.phi u t = S₂.phi u t := by
    obtain ⟨hr, hφ, _⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata (u, t)
      ⟨h₁.solution.development.outgoing_mem hp.1 hut htv,
        h₂.solution.development.outgoing_mem hp.2 hut htv⟩
    exact ⟨hr, hφ⟩
  have hae := h₁.initial_lam_alpha_ae h₂ hp.1 hp.2 hdata'
  obtain ⟨L₁, hL₁⟩ := h₁.exists_lam_axis_limit_out hp.1
  obtain ⟨L₂, hL₂⟩ := h₂.exists_lam_axis_limit_out hp.2
  obtain ⟨A₁, hA₁⟩ := exists_alpha_axis_trace_out h₁ hp.1
  obtain ⟨A₂, hA₂⟩ := exists_alpha_axis_trace_out h₂ hp.2
  have hL : L₁ = L₂ := right_trace_eq_of_ae_eq huv
    (hae.mono (fun t ht htv => (ht htv).1)) hL₁ hL₂
  have hA : A₁ = A₂ := right_trace_eq_of_ae_eq huv
    (hae.mono (fun t ht htv => (ht htv).2)) hA₁ hA₂
  exact ⟨⟨L₁, hL₁, hL ▸ hL₂⟩, ⟨A₁, hA₁, hA ▸ hA₂⟩⟩

/-- The linear outgoing coefficient for `ν` is determined almost everywhere
by the common primary fields and the radius density. -/
theorem source_nuCoeff_ae_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    ∀ᵐ t ∂volume, t ∈ Ioc u v →
      IsBVSolution.nuCoeff S₁ u t = IsBVSolution.nuCoeff S₂ u t := by
  have hdata' (t : ℝ) (hut : u < t) (htv : t ≤ v) :
      S₁.r u t = S₂.r u t ∧ S₁.phi u t = S₂.phi u t := by
    obtain ⟨hr, hφ, _⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata (u, t)
      ⟨h₁.solution.development.outgoing_mem hp.1 hut htv,
        h₂.solution.development.outgoing_mem hp.2 hut htv⟩
    exact ⟨hr, hφ⟩
  have hae := h₁.initial_lam_alpha_ae h₂ hp.1 hp.2 hdata'
  filter_upwards [hae] with t ht htv
  obtain ⟨hr, _, hm⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata (u, t)
    ⟨h₁.solution.development.outgoing_mem hp.1 htv.1 htv.2,
      h₂.solution.development.outgoing_mem hp.2 htv.1 htv.2⟩
  have hlam := (ht htv).1
  simp only [IsBVSolution.nuCoeff, IsBVSolution.gap, hr, hm, hlam]

/-- The outgoing expansion `ν` agrees pointwise on the overlap. The source
representatives of `λ` need only agree almost everywhere. -/
theorem source_nu_eq_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    S₁.nu u v = S₂.nu u v := by
  obtain ⟨⟨L, hL₁, hL₂⟩, _⟩ := source_axis_right_traces_match h₁ h₂ hdata hp
  obtain ⟨L₁, hLam₁, hNu₁⟩ := h₁.nu_axis_exponential hp.1
  obtain ⟨L₂, hLam₂, hNu₂⟩ := h₂.nu_axis_exponential hp.2
  have hL₁eq : L₁ = L := tendsto_nhds_unique hLam₁ hL₁
  have hL₂eq : L₂ = L := tendsto_nhds_unique hLam₂ hL₂
  have huv : u ≤ v := (h₁.solution.development.wedge hp.1).2.le
  have hInt : (∫ t in u..v, IsBVSolution.nuCoeff S₁ u t) =
      ∫ t in u..v, IsBVSolution.nuCoeff S₂ u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [source_nuCoeff_ae_on_overlap h₁ h₂ hdata hp]
      with t ht htv
    exact ht (by simpa only [uIoc_of_le huv] using htv)
  rw [hL₁eq, hInt] at hNu₁
  rw [hL₂eq] at hNu₂
  exact hNu₁.trans hNu₂.symm

/-- The outgoing `β` forcing terms agree almost everywhere on a common
characteristic. The equality uses the pointwise common `ν` just established. -/
theorem source_beta_density_ae_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    ∀ᵐ t ∂volume, t ∈ Ioc u v →
      IsBVSolution.radiusCoeff S₁ u t * S₁.phi u t =
        IsBVSolution.radiusCoeff S₂ u t * S₂.phi u t := by
  filter_upwards [source_nuCoeff_ae_on_overlap h₁ h₂ hdata hp]
    with t hcoeff htv
  have ht₁ := h₁.solution.development.outgoing_mem hp.1 htv.1 htv.2
  have ht₂ := h₂.solution.development.outgoing_mem hp.2 htv.1 htv.2
  obtain ⟨_, hphi, _⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata
    (u, t) ⟨ht₁, ht₂⟩
  have hnu := source_nu_eq_on_overlap h₁ h₂ hdata (show (u, t) ∈ U₁ ∩ U₂ from
    ⟨ht₁, ht₂⟩)
  rw [IsBVSolution.radius_coeff_eq_nu_coeff_mul_nu h₁.solution.development h₁ ht₁,
    IsBVSolution.radius_coeff_eq_nu_coeff_mul_nu h₂.solution.development h₂ ht₂,
    hcoeff htv, hnu, hphi]

/-- The difference of the source `β` representatives is constant along each
compact overlap segment. -/
theorem source_beta_difference_constant
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u a v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂)
    (hua : u < a) (hav : a ≤ v) :
    S₁.beta u v - S₂.beta u v = S₁.beta u a - S₂.beta u a := by
  have hseg₁ : outSeg u a v ⊆ U₁ :=
    h₁.solution.development.out_seg_subset hp.1 hua hav le_rfl
  have hseg₂ : outSeg u a v ⊆ U₂ :=
    h₂.solution.development.out_seg_subset hp.2 hua hav le_rfl
  have hprim₁ := h₁.solution.beta_out u a v hav hseg₁
  have hprim₂ := h₂.solution.beta_out u a v hav hseg₂
  have hInt : (∫ t in a..v,
      IsBVSolution.radiusCoeff S₁ u t * S₁.phi u t) =
      ∫ t in a..v, IsBVSolution.radiusCoeff S₂ u t * S₂.phi u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [source_beta_density_ae_on_overlap h₁ h₂ hdata hp]
      with t ht htv
    have htv' : t ∈ Ioc u v := by
      rw [uIoc_of_le hav] at htv
      exact ⟨hua.trans_le htv.1.le, htv.2⟩
    change IsBVSolution.radiusCoeff S₁ u t * S₁.phi u t =
      IsBVSolution.radiusCoeff S₂ u t * S₂.phi u t
    exact ht htv'
  have heq₁ : S₁.beta u v - S₁.beta u a =
      ∫ t in a..v, IsBVSolution.radiusCoeff S₁ u t * S₁.phi u t :=
    hprim₁.2
  have heq₂ : S₂.beta u v - S₂.beta u a =
      ∫ t in a..v, IsBVSolution.radiusCoeff S₂ u t * S₂.phi u t :=
    hprim₂.2
  linarith only [heq₁, heq₂, hInt]

/-- The incoming scalar-radius density `β` agrees pointwise on the overlap. -/
theorem source_beta_eq_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    S₁.beta u v = S₂.beta u v := by
  obtain ⟨_, ⟨A, hAlpha₁, hAlpha₂⟩⟩ :=
    source_axis_right_traces_match h₁ h₂ hdata hp
  have haxis₁ : Tendsto (fun t => S₁.alpha u t + S₁.beta u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [h₁.solution.development.axis_filter_eq hp.1] using
      h₁.item6 u (h₁.solution.development.axis_mem hp.1)
  have haxis₂ : Tendsto (fun t => S₂.alpha u t + S₂.beta u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [h₂.solution.development.axis_filter_eq hp.2] using
      h₂.item6 u (h₂.solution.development.axis_mem hp.2)
  have hBeta₁ : Tendsto (S₁.beta u) (𝓝[>] u) (𝓝 (-A)) := by
    simpa only [add_sub_cancel_left, zero_sub] using haxis₁.sub hAlpha₁
  have hBeta₂ : Tendsto (S₂.beta u) (𝓝[>] u) (𝓝 (-A)) := by
    simpa only [add_sub_cancel_left, zero_sub] using haxis₂.sub hAlpha₂
  have hDiff : Tendsto (fun t => S₁.beta u t - S₂.beta u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hBeta₁.sub hBeta₂
  have huv : u < v := (h₁.solution.development.wedge hp.1).2
  have hconst : ∀ᶠ a in 𝓝[>] u,
      S₁.beta u v - S₂.beta u v = S₁.beta u a - S₂.beta u a := by
    filter_upwards [Ioo_mem_nhdsGT huv] with a ha
    exact source_beta_difference_constant h₁ h₂ hdata hp ha.1 ha.2.le
  have hlim : Tendsto (fun _ : ℝ => S₁.beta u v - S₂.beta u v)
      (𝓝[>] u) (𝓝 (0 : ℝ)) :=
    hDiff.congr' (hconst.mono fun _ h => h.symm)
  have hzero : S₁.beta u v - S₂.beta u v = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  linarith only [hzero]

/-- The left outgoing traces of the two source radius densities agree at an
overlap point. This is the representative value used on a terminal edge. -/
theorem source_lam_leftLim_eq_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    (S₁.lam u).leftLim v = (S₂.lam u).leftLim v := by
  let a := (u + v) / 2
  have huv : u < v := (h₁.solution.development.wedge hp.1).2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hseg : outSeg u a v ⊆ U₁ ∩ U₂ := fun p h =>
    ⟨h₁.solution.development.out_seg_subset hp.1 hua hav.le le_rfl h,
      h₂.solution.development.out_seg_subset hp.2 hua hav.le le_rfl h⟩
  obtain ⟨l, hl₁, hl₂⟩ := source_lam_left_trace_on_overlap h₁ h₂ hdata hav hseg
  exact (leftLim_eq_of_tendsto hl₁).trans (leftLim_eq_of_tendsto hl₂).symm

/-- The left outgoing traces of the two source scalar-radius densities agree
at every overlap point. -/
theorem source_alpha_leftLim_eq_on_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∩ U₂) :
    (S₁.alpha u).leftLim v = (S₂.alpha u).leftLim v := by
  let a := (u + v) / 2
  have huv : u < v := (h₁.solution.development.wedge hp.1).2
  have hua : u < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hseg : outSeg u a v ⊆ U₁ ∩ U₂ := fun p h =>
    ⟨h₁.solution.development.out_seg_subset hp.1 hua hav.le le_rfl h,
      h₂.solution.development.out_seg_subset hp.2 hua hav.le le_rfl h⟩
  obtain ⟨l, hl₁, hl₂⟩ := source_alpha_left_trace_on_overlap h₁ h₂ hdata hav hseg
  exact (leftLim_eq_of_tendsto hl₁).trans (leftLim_eq_of_tendsto hl₂).symm

/-- The canonical outgoing radius density uses its left trace at every actual
union point. Outside the union the arbitrary second-source trace is chosen. -/
noncomputable def commonLam (U₁ : Set (ℝ × ℝ)) (S₁ S₂ : Fields)
    (u v : ℝ) : ℝ := by
  classical
  exact if (u, v) ∈ U₁ then (S₁.lam u).leftLim v else (S₂.lam u).leftLim v

/-- The canonical outgoing scalar-radius density uses the same left-trace
convention. -/
noncomputable def commonAlpha (U₁ : Set (ℝ × ℝ)) (S₁ S₂ : Fields)
    (u v : ℝ) : ℝ := by
  classical
  exact if (u, v) ∈ U₁ then (S₁.alpha u).leftLim v else (S₂.alpha u).leftLim v

/-- On the first domain the canonical values are its source left traces. -/
theorem common_lam_alpha_eq_first
    {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    commonLam U₁ S₁ S₂ u v = (S₁.lam u).leftLim v ∧
      commonAlpha U₁ S₁ S₂ u v = (S₁.alpha u).leftLim v := by
  classical
  simp [commonLam, commonAlpha, hp]

/-- On the second domain the canonical values are its source left traces,
including points of the overlap. -/
theorem common_lam_alpha_eq_second
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    commonLam U₁ S₁ S₂ u v = (S₂.lam u).leftLim v ∧
      commonAlpha U₁ S₁ S₂ u v = (S₂.alpha u).leftLim v := by
  classical
  by_cases hmem : (u, v) ∈ U₁
  · simpa only [commonLam, commonAlpha, hmem, ↓reduceIte] using
      ⟨source_lam_leftLim_eq_on_overlap h₁ h₂ hdata ⟨hmem, hp⟩,
        source_alpha_leftLim_eq_on_overlap h₁ h₂ hdata ⟨hmem, hp⟩⟩
  · simp [commonLam, commonAlpha, hmem]

/-- A BV function on `(a,b]` tends to its left-limit at `b`, including when
its supplied value at `b` differs from that trace. -/
theorem leftLim_tendsto_of_bv_Ioc
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Ioc a b)) :
    Tendsto f (𝓝[<] b) (𝓝 (f.leftLim b)) := by
  obtain ⟨l, hl⟩ := hf.exists_tendsto_left b
  have hs : Ioc a b ∩ Iio b ∈ 𝓝[<] b :=
    mem_of_superset (Ioo_mem_nhdsLT hab)
      (fun _ ht => ⟨⟨ht.1, ht.2.le⟩, ht.2⟩)
  have hlim : Tendsto f (𝓝[<] b) (𝓝 l) :=
    hl.mono_left (le_inf inf_le_left (le_principal_iff.mpr hs))
  rw [leftLim_eq_of_tendsto hlim]
  exact hlim

/-- Replacing all values on `(a,b]` by their left traces adds no outgoing
variation cost, including at the right endpoint. -/
theorem eVariationOn_leftLim_Ioc_le
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Ioc a b)) :
    eVariationOn f.leftLim (Ioc a b) ≤ eVariationOn f (Ioc a b) := by
  have hcont : ContinuousWithinAt f.leftLim (Iic b) b :=
    continuousWithinAt_leftLim_Iic (leftLim_tendsto_of_bv_Ioc hab hf)
  calc
    eVariationOn f.leftLim (Ioc a b) = eVariationOn f.leftLim (Ioo a b) :=
      eVariationOn.Ioc_eq_Ioo_of_continuousWithinAt hab hcont
    _ ≤ eVariationOn f (Ioo a b) := eVariationOn.eVariationOn_leftLim_le isOpen_Ioo
    _ ≤ eVariationOn f (Ioc a b) :=
      eVariationOn.mono f (fun _ ht => ⟨ht.1, ht.2.le⟩)

/-- The left-trace radius density on a source outgoing segment has no more
variation than the original BV representative on its full slice. -/
theorem source_lam_leftLim_variation_outgoing_le
    {U : Set (ℝ × ℝ)} {S : Fields} (hS : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    eVariationOn (S.lam u).leftLim (Ioc u v) ≤
      eVariationOn (S.lam u) {t | (u, t) ∈ U} := by
  have huvlt : u < v := (hS.solution.development.wedge huv).2
  have hsub : Ioc u v ⊆ {t | (u, t) ∈ U} := fun t ht =>
    hS.solution.development.outgoing_mem huv ht.1 ht.2
  have hFull : BoundedVariationOn (S.lam u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hS.item1.choose_spec.1 u)
  have hBV : BoundedVariationOn (S.lam u) (Ioc u v) := hFull.mono hsub
  exact (eVariationOn_leftLim_Ioc_le huvlt hBV).trans
    (eVariationOn.mono (S.lam u) hsub)

/-- The same zero-cost terminal convention applies to the outgoing scalar
amplitude `θ`, whose variation is a defining BV-class bound. -/
theorem source_theta_leftLim_variation_outgoing_le
    {U : Set (ℝ × ℝ)} {S : Fields} (hS : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    eVariationOn (S.theta u).leftLim (Ioc u v) ≤
      eVariationOn (S.theta u) {t | (u, t) ∈ U} := by
  have huvlt : u < v := (hS.solution.development.wedge huv).2
  have hsub : Ioc u v ⊆ {t | (u, t) ∈ U} := fun t ht =>
    hS.solution.development.outgoing_mem huv ht.1 ht.2
  have hFull : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hS.item5.choose_spec.1 u)
  have hBV : BoundedVariationOn (S.theta u) (Ioc u v) := hFull.mono hsub
  exact (eVariationOn_leftLim_Ioc_le huvlt hBV).trans
    (eVariationOn.mono (S.theta u) hsub)

/-- The scalar-radius density also pays no extra outgoing variation at an
included terminal point. Its source variation is finite on every slice. -/
theorem source_alpha_leftLim_variation_outgoing_le
    {U : Set (ℝ × ℝ)} {S : Fields} (hS : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    eVariationOn (S.alpha u).leftLim (Ioc u v) ≤
      eVariationOn (S.alpha u) {t | (u, t) ∈ U} := by
  have huvlt : u < v := (hS.solution.development.wedge huv).2
  have hsub : Ioc u v ⊆ {t | (u, t) ∈ U} := fun t ht =>
    hS.solution.development.outgoing_mem huv ht.1 ht.2
  have hBV : BoundedVariationOn (S.alpha u) (Ioc u v) :=
    (source_alpha_bv_on_slice hS u).mono hsub
  exact (eVariationOn_leftLim_Ioc_le huvlt hBV).trans
    (eVariationOn.mono (S.alpha u) hsub)

/-- A BV source slice has a genuine left trace at `b` whenever it contains a
punctured interval below `b`; membership at `b` is unnecessary. -/
theorem exists_left_trace_of_bv_punctured_slice
    {f : ℝ → ℝ} {s : Set ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f s)
    (hnear : Ioo a b ⊆ s) :
    ∃ l : ℝ, Tendsto f (𝓝[<] b) (𝓝 l) := by
  obtain ⟨l, hl⟩ := hf.exists_tendsto_left b
  have hs : s ∩ Iio b ∈ 𝓝[<] b :=
    mem_of_superset (Ioo_mem_nhdsLT hab)
      (fun _ ht => ⟨hnear ht, ht.2⟩)
  exact ⟨l, hl.mono_left (le_inf inf_le_left (le_principal_iff.mpr hs))⟩

/-- Radius and scalar-radius densities agree almost everywhere on an open
outgoing slice contained in the overlap, even when its upper endpoint belongs
to only one source. -/
theorem source_lam_alpha_ae_on_punctured_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (_huv : u < v)
    (hcommon : ∀ t ∈ Ioo u v, (u, t) ∈ U₁ ∩ U₂) :
    ∀ᵐ t ∂volume, t ∈ Ioo u v →
      S₁.lam u t = S₂.lam u t ∧ S₁.alpha u t = S₂.alpha u t := by
  have hq : ∀ q : ℚ, ∀ᵐ t ∂volume,
      u < (q : ℝ) → (q : ℝ) < v → t ∈ Ioc u (q : ℝ) →
        S₁.lam u t = S₂.lam u t ∧ S₁.alpha u t = S₂.alpha u t := by
    intro q
    by_cases huq : u < (q : ℝ)
    · by_cases hqv : (q : ℝ) < v
      · have hqp := hcommon (q : ℝ) ⟨huq, hqv⟩
        have hdata' (t : ℝ) (hut : u < t) (htq : t ≤ (q : ℝ)) :
            S₁.r u t = S₂.r u t ∧ S₁.phi u t = S₂.phi u t := by
          obtain ⟨hr, hphi, _⟩ := theorem3_1_unique U₁ U₂ S₁ S₂ h₁ h₂ hdata
            (u, t) (hcommon t ⟨hut, htq.trans_lt hqv⟩)
          exact ⟨hr, hphi⟩
        exact (h₁.initial_lam_alpha_ae h₂ hqp.1 hqp.2 hdata').mono
          (fun _ ht _ _ hti => ht hti)
      · exact Filter.Eventually.of_forall (fun _ _ h => (hqv h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (huq h).elim)
  filter_upwards [eventually_countable_forall.mpr hq] with t ht htv
  obtain ⟨q, htq, hqv⟩ := exists_rat_btwn htv.2
  exact ht q (htv.1.trans htq) hqv ⟨htv.1, htq.le⟩

/-- A strict overlap below a terminal outgoing coordinate determines the
same left traces, regardless of which source includes the terminal point. -/
theorem source_lam_alpha_leftLim_eq_of_punctured_overlap
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v)
    {u v : ℝ} (huv : u < v)
    (hcommon : ∀ t ∈ Ioo u v, (u, t) ∈ U₁ ∩ U₂) :
    (S₁.lam u).leftLim v = (S₂.lam u).leftLim v ∧
      (S₁.alpha u).leftLim v = (S₂.alpha u).leftLim v := by
  have hae := source_lam_alpha_ae_on_punctured_overlap h₁ h₂ hdata huv hcommon
  have hnear₁ : Ioo u v ⊆ {t | (u, t) ∈ U₁} :=
    fun t ht => (hcommon t ht).1
  have hnear₂ : Ioo u v ⊆ {t | (u, t) ∈ U₂} :=
    fun t ht => (hcommon t ht).2
  have hLamBV₁ : BoundedVariationOn (S₁.lam u) {t | (u, t) ∈ U₁} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₁.item1.choose_spec.1 u)
  have hLamBV₂ : BoundedVariationOn (S₂.lam u) {t | (u, t) ∈ U₂} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₂.item1.choose_spec.1 u)
  obtain ⟨L₁, hL₁⟩ := exists_left_trace_of_bv_punctured_slice huv hLamBV₁ hnear₁
  obtain ⟨L₂, hL₂⟩ := exists_left_trace_of_bv_punctured_slice huv hLamBV₂ hnear₂
  obtain ⟨A₁, hA₁⟩ := exists_left_trace_of_bv_punctured_slice huv
    (source_alpha_bv_on_slice h₁ u) hnear₁
  obtain ⟨A₂, hA₂⟩ := exists_left_trace_of_bv_punctured_slice huv
    (source_alpha_bv_on_slice h₂ u) hnear₂
  have hLamAE : ∀ᵐ t ∂volume, t ∈ Ioo u v →
      S₁.lam u t = S₂.lam u t :=
    hae.mono (fun _ ht htv => (ht htv).1)
  have hAlphaAE : ∀ᵐ t ∂volume, t ∈ Ioo u v →
      S₁.alpha u t = S₂.alpha u t :=
    hae.mono (fun _ ht htv => (ht htv).2)
  have hLeq := left_trace_eq_of_ae_eq huv hLamAE hL₁ hL₂
  have hAeq := left_trace_eq_of_ae_eq huv hAlphaAE hA₁ hA₂
  exact ⟨(leftLim_eq_of_tendsto hL₁).trans
      (hLeq.trans (leftLim_eq_of_tendsto hL₂).symm),
    (leftLim_eq_of_tendsto hA₁).trans
      (hAeq.trans (leftLim_eq_of_tendsto hA₂).symm)⟩

end ChristodoulouBV.Uniqueness

end
