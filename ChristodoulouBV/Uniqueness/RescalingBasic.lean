module

public import ChristodoulouBV.Frozen.IsBVSolution
public import ChristodoulouBV.Uniqueness.Triangle
import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus

/-!
# Affine rescaling of BV solutions

The translated positive affine chart sends `(u,v)` to
`(a + h*u, a + h*v)`. Radius and mass have weight minus one; the
remaining reduced fields have weight zero. The new carrier retains the
initial outgoing edge required by `IsDomainOfDevelopment`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The positive affine change of one null coordinate. -/
def affineCoordinate (a h t : ℝ) : ℝ := a + h * t

/-- The rescaled domain, cut off at its new initial outgoing edge. -/
def rescaledDomain (U : Set (ℝ × ℝ)) (a h : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ (affineCoordinate a h p.1, affineCoordinate a h p.2) ∈ U}

/-- The reduced fields in the positive affine chart. -/
noncomputable def rescaledFields (S : Fields) (a h : ℝ) : Fields :=
  { r := fun u v => S.r (affineCoordinate a h u) (affineCoordinate a h v) / h
    phi := fun u v => S.phi (affineCoordinate a h u) (affineCoordinate a h v)
    m := fun u v => S.m (affineCoordinate a h u) (affineCoordinate a h v) / h
    lam := fun u v => S.lam (affineCoordinate a h u) (affineCoordinate a h v)
    nu := fun u v => S.nu (affineCoordinate a h u) (affineCoordinate a h v)
    alpha := fun u v => S.alpha (affineCoordinate a h u) (affineCoordinate a h v)
    beta := fun u v => S.beta (affineCoordinate a h u) (affineCoordinate a h v) }

/-- The affine coordinate is strictly increasing for a positive scale. -/
theorem affineCoordinate_strictMono {a h : ℝ} (hh : 0 < h) :
    StrictMono (affineCoordinate a h) := by
  intro x y hxy
  unfold affineCoordinate
  simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left hxy hh) a

/-- The chart maps a new development point to the old one. -/
theorem mapped_mem_of_mem_rescaledDomain {U : Set (ℝ × ℝ)} {a h u v : ℝ}
    (hp : (u, v) ∈ rescaledDomain U a h) :
    (affineCoordinate a h u, affineCoordinate a h v) ∈ U := hp.2

/-- The rescaled carrier remains a domain of development. -/
theorem rescaledDomain_isDomainOfDevelopment {U : Set (ℝ × ℝ)}
    (hU : IsDomainOfDevelopment U) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    IsDomainOfDevelopment (rescaledDomain U a h) := by
  constructor
  · intro p hp
    rcases p with ⟨u, v⟩
    exact ⟨hp.1, (affineCoordinate_strictMono hh).lt_iff_lt.mp
      ((hU.wedge hp.2).2)⟩
  · intro p hp q hq
    rcases p with ⟨u, v⟩
    rcases q with ⟨s, t⟩
    rcases hq with ⟨⟨hs, hsu⟩, ⟨hst, htv⟩⟩
    refine ⟨hs, hU.past_mem hp.2 ?_ ?_ ?_ ?_⟩
    · unfold affineCoordinate
      nlinarith
    · exact (affineCoordinate_strictMono hh).monotone hsu
    · exact affineCoordinate_strictMono hh hst
    · exact affineCoordinate_strictMono hh htv

/-- The mass ratio has weight zero. -/
theorem rescaled_mass_ratio (S : Fields) {a h : ℝ} (hh : 0 < h) (u v : ℝ) :
    2 * (rescaledFields S a h).m u v / (rescaledFields S a h).r u v =
      2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
        S.r (affineCoordinate a h u) (affineCoordinate a h v) := by
  simp only [rescaledFields]
  field_simp

/-- The outgoing scalar amplitude has weight zero. -/
theorem rescaled_theta (S : Fields) (a h u v : ℝ) :
    (rescaledFields S a h).theta u v =
      S.theta (affineCoordinate a h u) (affineCoordinate a h v) := rfl

/-- The incoming scalar amplitude has weight zero. -/
theorem rescaled_zeta (S : Fields) (a h u v : ℝ) :
    (rescaledFields S a h).zeta u v =
      S.zeta (affineCoordinate a h u) (affineCoordinate a h v) := rfl

/-- Variation decreases upon restricting a slice and applying a positive affine chart. -/
theorem eVariationOn_affine_le {f : ℝ → ℝ} {s t : Set ℝ}
    {a h : ℝ} (hh : 0 < h)
    (hmap : MapsTo (affineCoordinate a h) t s) :
    eVariationOn (fun x => f (affineCoordinate a h x)) t ≤ eVariationOn f s := by
  exact eVariationOn.comp_le_of_monotoneOn f (affineCoordinate a h)
    ((affineCoordinate_strictMono hh).monotone.monotoneOn t) hmap

/-- An interval primitive is covariant under an increasing affine chart. -/
theorem intervalPrimitive_affine {f g : ℝ → ℝ} {a h x y : ℝ}
    (hh : 0 < h)
    (hf : IntervalPrimitive f g (affineCoordinate a h x)
      (affineCoordinate a h y)) :
    IntervalPrimitive (fun t => f (affineCoordinate a h t))
      (fun t => h * g (affineCoordinate a h t)) x y := by
  have hI : IntervalIntegrable (fun t => g (affineCoordinate a h t))
      MeasureTheory.volume x y := by
    have h₁ := hf.1.comp_add_left a
    have h₂ := h₁.comp_mul_left (c := h)
    simpa [affineCoordinate, hh.ne'] using h₂
  constructor
  · exact hI.const_mul h
  · simp only [affineCoordinate] at hf ⊢
    rw [hf.2, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.mul_integral_comp_add_mul]

/-- Scaling both a primitive and its density preserves its integral identity. -/
theorem intervalPrimitive_div {f g : ℝ → ℝ} {x y h : ℝ}
    (hf : IntervalPrimitive f g x y) :
    IntervalPrimitive (fun t => f t / h) (fun t => g t / h) x y := by
  constructor
  · exact hf.1.div_const h
  · simpa only [div_sub_div_same, intervalIntegral.integral_div] using
      congrArg (fun t : ℝ => t / h) hf.2

/-- The primitive of a field of scale weight minus one has an unscaled density. -/
theorem intervalPrimitive_affine_div {f g : ℝ → ℝ} {a h x y : ℝ}
    (hh : 0 < h)
    (hf : IntervalPrimitive f g (affineCoordinate a h x)
      (affineCoordinate a h y)) :
    IntervalPrimitive (fun t => f (affineCoordinate a h t) / h)
      (fun t => g (affineCoordinate a h t)) x y := by
  convert intervalPrimitive_div (h := h) (intervalPrimitive_affine hh hf) using 1
  funext t
  simp only [mul_div_cancel_left₀ _ hh.ne']

/-- Absolute continuity is preserved by a positive affine reparametrization. -/
theorem absolutelyContinuousOnInterval_affine {f : ℝ → ℝ} {a h x y : ℝ}
    (hh : 0 < h) (hxy : x ≤ y)
    (hf : AbsolutelyContinuousOnInterval f
      (affineCoordinate a h x) (affineCoordinate a h y)) :
    AbsolutelyContinuousOnInterval (fun t => f (affineCoordinate a h t)) x y := by
  let g : ℝ → ℝ := fun t => h * deriv f (affineCoordinate a h t)
  have hprim : IntervalPrimitive (fun t => f (affineCoordinate a h t)) g x y :=
    intervalPrimitive_affine hh ⟨hf.intervalIntegrable_deriv,
      hf.integral_deriv_eq_sub.symm⟩
  apply AbsolutelyContinuousOnInterval.of_integral_eq_sub hprim.1
  intro t ht
  rw [uIcc_of_le hxy] at ht
  have hxt : x ≤ t := ht.1
  have hty : t ≤ y := ht.2
  have hAt : affineCoordinate a h x ≤ affineCoordinate a h t :=
    (affineCoordinate_strictMono hh).monotone hxt
  have hTy : affineCoordinate a h t ≤ affineCoordinate a h y :=
    (affineCoordinate_strictMono hh).monotone hty
  have hsub : AbsolutelyContinuousOnInterval f
      (affineCoordinate a h x) (affineCoordinate a h t) :=
    hf.mono (by
      rw [uIcc_of_le ((affineCoordinate_strictMono hh).monotone hxy),
        uIcc_of_le hAt]
      exact Icc_subset_Icc le_rfl hTy)
  exact (intervalPrimitive_affine hh
    (show IntervalPrimitive f (deriv f)
      (affineCoordinate a h x) (affineCoordinate a h t) from
      ⟨hsub.intervalIntegrable_deriv, hsub.integral_deriv_eq_sub.symm⟩)).2

/-- An outgoing segment in the new chart maps inside an old outgoing segment. -/
theorem mapped_outSeg_subset {U : Set (ℝ × ℝ)} {a h u x y : ℝ}
    (hh : 0 < h) (hseg : outSeg u x y ⊆ rescaledDomain U a h) :
    outSeg (affineCoordinate a h u) (affineCoordinate a h x)
      (affineCoordinate a h y) ⊆ U := by
  intro p hp
  rcases p with ⟨s, t⟩
  have hs : s = affineCoordinate a h u := hp.1
  subst s
  have hxy : affineCoordinate a h x ≤ t ∧ t ≤ affineCoordinate a h y := hp.2
  let z := (t - a) / h
  have hz : affineCoordinate a h z = t := by
    dsimp [affineCoordinate, z]
    field_simp [hh.ne']
    ring
  have hx : x ≤ z := (affineCoordinate_strictMono hh).le_iff_le.mp (by
    calc
      affineCoordinate a h x ≤ t := hxy.1
      _ = affineCoordinate a h z := hz.symm)
  have hy : z ≤ y := (affineCoordinate_strictMono hh).le_iff_le.mp (by
    calc
      affineCoordinate a h z = t := hz
      _ ≤ affineCoordinate a h y := hxy.2)
  have hzs : (u, z) ∈ outSeg u x y := by
    simp only [outSeg, mem_prod, mem_singleton_iff, mem_Icc]
    exact ⟨trivial, hx, hy⟩
  simpa only [hz] using (hseg hzs).2

/-- An incoming segment in the new chart maps inside an old incoming segment. -/
theorem mapped_inSeg_subset {U : Set (ℝ × ℝ)} {a h v x y : ℝ}
    (hh : 0 < h) (hseg : inSeg v x y ⊆ rescaledDomain U a h) :
    inSeg (affineCoordinate a h v) (affineCoordinate a h x)
      (affineCoordinate a h y) ⊆ U := by
  intro p hp
  rcases p with ⟨s, t⟩
  have ht : t = affineCoordinate a h v := hp.2
  subst t
  have hxy : affineCoordinate a h x ≤ s ∧ s ≤ affineCoordinate a h y := hp.1
  let z := (s - a) / h
  have hz : affineCoordinate a h z = s := by
    dsimp [affineCoordinate, z]
    field_simp [hh.ne']
    ring
  have hx : x ≤ z := (affineCoordinate_strictMono hh).le_iff_le.mp (by
    calc
      affineCoordinate a h x ≤ s := hxy.1
      _ = affineCoordinate a h z := hz.symm)
  have hy : z ≤ y := (affineCoordinate_strictMono hh).le_iff_le.mp (by
    calc
      affineCoordinate a h z = s := hz
      _ ≤ affineCoordinate a h y := hxy.2)
  have hzs : (z, v) ∈ inSeg v x y := by
    simp only [inSeg, mem_prod, mem_singleton_iff, mem_Icc]
    exact ⟨⟨hx, hy⟩, trivial⟩
  simpa only [hz] using (hseg hzs).2

/-- The outgoing radius primitive survives rescaling. -/
theorem rescaled_radius_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ u x y, x ≤ y → outSeg u x y ⊆ rescaledDomain U a h →
      IntervalPrimitive ((rescaledFields S a h).r u)
        ((rescaledFields S a h).lam u) x y := by
  intro u x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.radius_out _ _ _ hxy' (mapped_outSeg_subset hh hseg)
  exact intervalPrimitive_affine_div hh hold

/-- The incoming radius primitive survives rescaling. -/
theorem rescaled_radius_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ v x y, x ≤ y → inSeg v x y ⊆ rescaledDomain U a h →
      IntervalPrimitive (fun u => (rescaledFields S a h).r u v)
        (fun u => (rescaledFields S a h).nu u v) x y := by
  intro v x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.radius_in _ _ _ hxy' (mapped_inSeg_subset hh hseg)
  exact intervalPrimitive_affine_div hh hold

/-- The outgoing scalar-radius primitive survives rescaling. -/
theorem rescaled_scalar_radius_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ u x y, x ≤ y → outSeg u x y ⊆ rescaledDomain U a h →
      IntervalPrimitive
        (fun v => (rescaledFields S a h).r u v * (rescaledFields S a h).phi u v)
        ((rescaledFields S a h).alpha u) x y := by
  intro u x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.scalar_radius_out _ _ _ hxy' (mapped_outSeg_subset hh hseg)
  convert intervalPrimitive_affine_div hh hold using 1
  · funext v
    simp only [rescaledFields]
    ring
  · rfl

/-- The incoming scalar-radius primitive survives rescaling. -/
theorem rescaled_scalar_radius_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ v x y, x ≤ y → inSeg v x y ⊆ rescaledDomain U a h →
      IntervalPrimitive
        (fun u => (rescaledFields S a h).r u v * (rescaledFields S a h).phi u v)
        (fun u => (rescaledFields S a h).beta u v) x y := by
  intro v x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.scalar_radius_in _ _ _ hxy' (mapped_inSeg_subset hh hseg)
  convert intervalPrimitive_affine_div hh hold using 1
  · funext u
    simp only [rescaledFields]
    ring
  · rfl

/-- Dividing the denominator by the positive scale multiplies a quotient by it. -/
theorem div_div_scale {h : ℝ} (hh : 0 < h) (x d : ℝ) :
    x / (d / h) = h * (x / d) := by
  by_cases hd : d = 0
  · simp [hd]
  · field_simp [hh.ne', hd]

/-- The coefficient in the four mixed transport equations has scale weight one. -/
theorem rescaled_interaction (S : Fields) {a h : ℝ} (hh : 0 < h) (u v : ℝ) :
    (2 * (rescaledFields S a h).m u v / (rescaledFields S a h).r u v) *
        (rescaledFields S a h).lam u v * (rescaledFields S a h).nu u v /
        ((1 - 2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) * (rescaledFields S a h).r u v) =
      h * ((2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
        S.r (affineCoordinate a h u) (affineCoordinate a h v)) *
        S.lam (affineCoordinate a h u) (affineCoordinate a h v) *
        S.nu (affineCoordinate a h u) (affineCoordinate a h v) /
        ((1 - 2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
          S.r (affineCoordinate a h u) (affineCoordinate a h v)) *
          S.r (affineCoordinate a h u) (affineCoordinate a h v))) := by
  rw [rescaled_mass_ratio S hh u v]
  change (2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
      S.r (affineCoordinate a h u) (affineCoordinate a h v)) *
      S.lam (affineCoordinate a h u) (affineCoordinate a h v) *
      S.nu (affineCoordinate a h u) (affineCoordinate a h v) /
      ((1 - 2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
        S.r (affineCoordinate a h u) (affineCoordinate a h v)) *
        (S.r (affineCoordinate a h u) (affineCoordinate a h v) / h)) = _
  rw [show (1 - 2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
        S.r (affineCoordinate a h u) (affineCoordinate a h v)) *
        (S.r (affineCoordinate a h u) (affineCoordinate a h v) / h) =
      ((1 - 2 * S.m (affineCoordinate a h u) (affineCoordinate a h v) /
        S.r (affineCoordinate a h u) (affineCoordinate a h v)) *
        S.r (affineCoordinate a h u) (affineCoordinate a h v)) / h by ring]
  exact div_div_scale hh _ _

/-- The outgoing mass primitive survives rescaling. -/
theorem rescaled_mass_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ u x y, x ≤ y → outSeg u x y ⊆ rescaledDomain U a h →
      IntervalPrimitive ((rescaledFields S a h).m u)
        (fun v => (1 - 2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) *
          ((rescaledFields S a h).theta u v) ^ 2 /
          (2 * (rescaledFields S a h).lam u v)) x y := by
  intro u x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.mass_out _ _ _ hxy' (mapped_outSeg_subset hh hseg)
  convert intervalPrimitive_affine_div hh hold using 1
  · rfl
  · funext t
    rw [rescaled_mass_ratio S hh u t, rescaled_theta]
    rfl

/-- The incoming mass primitive survives rescaling. -/
theorem rescaled_mass_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ v x y, x ≤ y → inSeg v x y ⊆ rescaledDomain U a h →
      IntervalPrimitive (fun u => (rescaledFields S a h).m u v)
        (fun u => (1 - 2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) *
          ((rescaledFields S a h).zeta u v) ^ 2 /
          (2 * (rescaledFields S a h).nu u v)) x y := by
  intro v x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.mass_in _ _ _ hxy' (mapped_inSeg_subset hh hseg)
  convert intervalPrimitive_affine_div hh hold using 1
  · rfl
  · funext t
    rw [rescaled_mass_ratio S hh t v, rescaled_zeta]
    rfl

/-- The incoming `λ` primitive survives rescaling. -/
theorem rescaled_lam_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ v x y, x ≤ y → inSeg v x y ⊆ rescaledDomain U a h →
      IntervalPrimitive (fun u => (rescaledFields S a h).lam u v)
        (fun u => (2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) *
          (rescaledFields S a h).lam u v * (rescaledFields S a h).nu u v /
          ((1 - 2 * (rescaledFields S a h).m u v /
            (rescaledFields S a h).r u v) * (rescaledFields S a h).r u v)) x y := by
  intro v x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.lam_in _ _ _ hxy' (mapped_inSeg_subset hh hseg)
  convert intervalPrimitive_affine hh hold using 1
  · rfl
  · funext t
    exact rescaled_interaction S hh t v

/-- The outgoing `ν` primitive survives rescaling. -/
theorem rescaled_nu_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ u x y, x ≤ y → outSeg u x y ⊆ rescaledDomain U a h →
      IntervalPrimitive ((rescaledFields S a h).nu u)
        (fun v => (2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) *
          (rescaledFields S a h).lam u v * (rescaledFields S a h).nu u v /
          ((1 - 2 * (rescaledFields S a h).m u v /
            (rescaledFields S a h).r u v) * (rescaledFields S a h).r u v)) x y := by
  intro u x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.nu_out _ _ _ hxy' (mapped_outSeg_subset hh hseg)
  convert intervalPrimitive_affine hh hold using 1
  · rfl
  · funext t
    exact rescaled_interaction S hh u t

/-- The incoming `α` primitive survives rescaling. -/
theorem rescaled_alpha_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ v x y, x ≤ y → inSeg v x y ⊆ rescaledDomain U a h →
      IntervalPrimitive (fun u => (rescaledFields S a h).alpha u v)
        (fun u => ((2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) *
          (rescaledFields S a h).lam u v * (rescaledFields S a h).nu u v /
          ((1 - 2 * (rescaledFields S a h).m u v /
            (rescaledFields S a h).r u v) * (rescaledFields S a h).r u v)) *
          (rescaledFields S a h).phi u v) x y := by
  intro v x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.alpha_in _ _ _ hxy' (mapped_inSeg_subset hh hseg)
  convert intervalPrimitive_affine hh hold using 1
  · rfl
  · funext t
    rw [rescaled_interaction S hh t v]
    simp only [rescaledFields]
    ring

/-- The outgoing `β` primitive survives rescaling. -/
theorem rescaled_beta_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ u x y, x ≤ y → outSeg u x y ⊆ rescaledDomain U a h →
      IntervalPrimitive ((rescaledFields S a h).beta u)
        (fun v => ((2 * (rescaledFields S a h).m u v /
          (rescaledFields S a h).r u v) *
          (rescaledFields S a h).lam u v * (rescaledFields S a h).nu u v /
          ((1 - 2 * (rescaledFields S a h).m u v /
            (rescaledFields S a h).r u v) * (rescaledFields S a h).r u v)) *
          (rescaledFields S a h).phi u v) x y := by
  intro u x y hxy hseg
  have hxy' := (affineCoordinate_strictMono (a := a) hh).monotone hxy
  have hold := hS.beta_out _ _ _ hxy' (mapped_outSeg_subset hh hseg)
  convert intervalPrimitive_affine hh hold using 1
  · rfl
  · funext t
    rw [rescaled_interaction S hh u t]
    simp only [rescaledFields]
    ring

/-- An axis point adjacent to the new domain maps to an old adjacent axis point. -/
theorem affineCoordinate_mem_adjacentAxis {U : Set (ℝ × ℝ)} {a h b : ℝ}
    (hb : b ∈ adjacentAxis (rescaledDomain U a h)) :
    affineCoordinate a h b ∈ adjacentAxis U := by
  change (affineCoordinate a h b, affineCoordinate a h b) ∈ closure U
  have hc : ContinuousAt
      (fun p : ℝ × ℝ =>
        (affineCoordinate a h p.1, affineCoordinate a h p.2)) (b, b) := by
    change ContinuousAt (fun p : ℝ × ℝ => (a + h * p.1, a + h * p.2)) (b, b)
    fun_prop
  have hb' : (b, b) ∈ closure (rescaledDomain U a h) := hb
  have him := mem_closure_image hc hb'
  apply (closure_mono (s :=
    (fun p : ℝ × ℝ =>
      (affineCoordinate a h p.1, affineCoordinate a h p.2)) ''
      rescaledDomain U a h) ?_) him
  rintro p ⟨q, hq, rfl⟩
  exact hq.2

/-- The right axis filter in the new chart maps into the original slice filter. -/
theorem affine_axis_filter {U : Set (ℝ × ℝ)} {a h b : ℝ} (hh : 0 < h) :
    Tendsto (affineCoordinate a h)
      (𝓝[>] b ⊓ 𝓟 {t | (b, t) ∈ rescaledDomain U a h})
      (𝓝[>] (affineCoordinate a h b) ⊓
        𝓟 {t | (affineCoordinate a h b, t) ∈ U}) := by
  apply tendsto_inf.mpr
  constructor
  · apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact ((show Continuous (affineCoordinate a h) by
        change Continuous (fun t : ℝ => a + h * t)
        fun_prop).tendsto b).mono_left
        (le_trans inf_le_left inf_le_left)
    · have hright : Set.Ioi b ∈
          (𝓝[>] b ⊓ 𝓟 {t | (b, t) ∈ rescaledDomain U a h}) :=
        mem_inf_of_left self_mem_nhdsWithin
      filter_upwards [hright] with t ht
      exact affineCoordinate_strictMono hh ht
  · apply tendsto_principal.mpr
    have hslice : {t | (b, t) ∈ rescaledDomain U a h} ∈
        (𝓝[>] b ⊓ 𝓟 {t | (b, t) ∈ rescaledDomain U a h}) :=
      mem_inf_of_right (mem_principal_self _)
    filter_upwards [hslice] with t ht
    exact ht.2

/-- Every clause of the reduced solution predicate is affine covariant. -/
theorem rescaled_isSolution {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) :
    IsSolution (rescaledDomain U a h) (rescaledFields S a h) := by
  refine {
    development := rescaledDomain_isDomainOfDevelopment hS.development ha hh
    radius_out := rescaled_radius_out hS hh
    radius_in := rescaled_radius_in hS hh
    scalar_radius_out := rescaled_scalar_radius_out hS hh
    scalar_radius_in := rescaled_scalar_radius_in hS hh
    mass_out := rescaled_mass_out hS hh
    mass_in := rescaled_mass_in hS hh
    lam_in := rescaled_lam_in hS hh
    nu_out := rescaled_nu_out hS hh
    alpha_in := rescaled_alpha_in hS hh
    beta_out := rescaled_beta_out hS hh
    radius_axis := ?_
    mass_axis := ?_
    radius_pos := ?_
    lam_pos := ?_
    conformal := ?_ }
  · intro b hb
    have hold := hS.radius_axis _ (affineCoordinate_mem_adjacentAxis hb)
    have hlim := (hold.comp (affine_axis_filter (U := U) (a := a) hh)).div_const h
    simpa only [rescaledFields, Function.comp_def, zero_div] using hlim
  · intro b hb
    have hold := hS.mass_axis _ (affineCoordinate_mem_adjacentAxis hb)
    have hlim := (hold.comp (affine_axis_filter (U := U) (a := a) hh)).div_const h
    simpa only [rescaledFields, Function.comp_def, zero_div] using hlim
  · intro p hp
    exact div_pos (hS.radius_pos _ hp.2) hh
  · intro p hp
    exact hS.lam_pos _ hp.2
  · intro p hp
    obtain ⟨Ω, hΩ, hcon⟩ := hS.conformal _ hp.2
    refine ⟨Ω, hΩ, ?_⟩
    rw [rescaled_mass_ratio S hh p.1 p.2]
    exact hcon

/-- An outgoing slice of the new domain maps into the old outgoing slice. -/
theorem affine_outSlice_mapsTo {U : Set (ℝ × ℝ)} {a h u : ℝ} :
    MapsTo (affineCoordinate a h)
      {v | (u, v) ∈ rescaledDomain U a h}
      {v | (affineCoordinate a h u, v) ∈ U} := by
  intro v hv
  exact hv.2

/-- An incoming slice of the new domain maps into the old incoming slice. -/
theorem affine_inSlice_mapsTo {U : Set (ℝ × ℝ)} {a h v : ℝ} :
    MapsTo (affineCoordinate a h)
      {u | (u, v) ∈ rescaledDomain U a h}
      {u | (u, affineCoordinate a h v) ∈ U} := by
  intro u hu
  exact hu.2

/-- Outgoing slice variation does not increase under the chart. -/
theorem rescaled_outVariation_le {U : Set (ℝ × ℝ)}
    {f : ℝ → ℝ → ℝ} {a h : ℝ} (hh : 0 < h) (u : ℝ) :
    eVariationOn (fun v => f (affineCoordinate a h u) (affineCoordinate a h v))
        {v | (u, v) ∈ rescaledDomain U a h} ≤
      eVariationOn (f (affineCoordinate a h u))
        {v | (affineCoordinate a h u, v) ∈ U} := by
  exact eVariationOn_affine_le (f := f (affineCoordinate a h u))
    (s := {v | (affineCoordinate a h u, v) ∈ U})
    (t := {v | (u, v) ∈ rescaledDomain U a h})
    hh (affine_outSlice_mapsTo (U := U) (u := u))

/-- Incoming slice variation does not increase under the chart. -/
theorem rescaled_inVariation_le {U : Set (ℝ × ℝ)}
    {f : ℝ → ℝ → ℝ} {a h : ℝ} (hh : 0 < h) (v : ℝ) :
    eVariationOn (fun u => f (affineCoordinate a h u) (affineCoordinate a h v))
        {u | (u, v) ∈ rescaledDomain U a h} ≤
      eVariationOn (fun u => f u (affineCoordinate a h v))
        {u | (u, affineCoordinate a h v) ∈ U} := by
  exact eVariationOn_affine_le (f := fun u => f u (affineCoordinate a h v))
    (s := {u | (u, affineCoordinate a h v) ∈ U})
    (t := {u | (u, v) ∈ rescaledDomain U a h})
    hh (affine_inSlice_mapsTo (U := U) (v := v))

/-- The first uniform BV constant is unchanged by positive affine rescaling. -/
theorem rescaled_item1 {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ,
      (∀ u, eVariationOn ((rescaledFields S a h).lam u)
        {v | (u, v) ∈ rescaledDomain U a h} ≤ ENNReal.ofReal C) ∧
      (∀ v, eVariationOn (fun u => (rescaledFields S a h).nu u v)
        {u | (u, v) ∈ rescaledDomain U a h} ≤ ENNReal.ofReal C) := by
  obtain ⟨C, hCout, hCin⟩ := hS.item1
  refine ⟨C, ?_, ?_⟩
  · intro u
    exact (rescaled_outVariation_le (f := S.lam) hh u).trans
      (hCout (affineCoordinate a h u))
  · intro v
    exact (rescaled_inVariation_le (f := S.nu) hh v).trans
      (hCin (affineCoordinate a h v))

/-- The third uniform BV constant is unchanged by positive affine rescaling. -/
theorem rescaled_item3_variation {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ,
      (∀ u, eVariationOn ((rescaledFields S a h).phi u)
        {v | (u, v) ∈ rescaledDomain U a h} ≤ ENNReal.ofReal C) ∧
      (∀ v, eVariationOn (fun u => (rescaledFields S a h).phi u v)
        {u | (u, v) ∈ rescaledDomain U a h} ≤ ENNReal.ofReal C) := by
  obtain ⟨C, hCout, hCin⟩ := hS.item3_variation
  refine ⟨C, ?_, ?_⟩
  · intro u
    exact (rescaled_outVariation_le (f := S.phi) hh u).trans
      (hCout (affineCoordinate a h u))
  · intro v
    exact (rescaled_inVariation_le (f := S.phi) hh v).trans
      (hCin (affineCoordinate a h v))

/-- The fifth uniform BV constant is unchanged by positive affine rescaling. -/
theorem rescaled_item5 {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ,
      (∀ u, eVariationOn ((rescaledFields S a h).theta u)
        {v | (u, v) ∈ rescaledDomain U a h} ≤ ENNReal.ofReal C) ∧
      (∀ v, eVariationOn (fun u => (rescaledFields S a h).zeta u v)
        {u | (u, v) ∈ rescaledDomain U a h} ≤ ENNReal.ofReal C) := by
  obtain ⟨C, hCout, hCin⟩ := hS.item5
  refine ⟨C, ?_, ?_⟩
  · intro u
    change eVariationOn (fun v => S.theta (affineCoordinate a h u)
      (affineCoordinate a h v)) _ ≤ _
    exact (rescaled_outVariation_le (f := S.theta) hh u).trans
      (hCout (affineCoordinate a h u))
  · intro v
    change eVariationOn (fun u => S.zeta (affineCoordinate a h u)
      (affineCoordinate a h v)) _ ≤ _
    exact (rescaled_inVariation_le (f := S.zeta) hh v).trans
      (hCin (affineCoordinate a h v))

/-- Absolute continuity on outgoing slices is preserved. -/
theorem rescaled_item3_ac_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ u x y, x ≤ y → outSeg u x y ⊆ rescaledDomain U a h →
      AbsolutelyContinuousOnInterval ((rescaledFields S a h).phi u) x y := by
  intro u x y hxy hseg
  have hOld := hS.item3_ac_out (affineCoordinate a h u)
    (affineCoordinate a h x) (affineCoordinate a h y)
    ((affineCoordinate_strictMono (a := a) hh).monotone hxy)
    (mapped_outSeg_subset hh hseg)
  exact absolutelyContinuousOnInterval_affine
    (f := S.phi (affineCoordinate a h u)) hh hxy hOld

/-- Absolute continuity on incoming slices is preserved. -/
theorem rescaled_item3_ac_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ v x y, x ≤ y → inSeg v x y ⊆ rescaledDomain U a h →
      AbsolutelyContinuousOnInterval
        (fun u => (rescaledFields S a h).phi u v) x y := by
  intro v x y hxy hseg
  have hOld := hS.item3_ac_in (affineCoordinate a h v)
    (affineCoordinate a h x) (affineCoordinate a h y)
    ((affineCoordinate_strictMono (a := a) hh).monotone hxy)
    (mapped_inSeg_subset hh hseg)
  exact absolutelyContinuousOnInterval_affine
    (f := fun u => S.phi u (affineCoordinate a h v)) hh hxy hOld

/-- The axis relation `ν+λ→0` is preserved. -/
theorem rescaled_item2 {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ b ∈ adjacentAxis (rescaledDomain U a h),
      Tendsto (fun v => (rescaledFields S a h).nu b v +
        (rescaledFields S a h).lam b v)
        (𝓝[>] b ⊓ 𝓟 {v | (b, v) ∈ rescaledDomain U a h}) (𝓝 (0 : ℝ)) := by
  intro b hb
  have hold := hS.item2 _ (affineCoordinate_mem_adjacentAxis hb)
  simpa only [rescaledFields, Function.comp_def] using
    hold.comp (affine_axis_filter (U := U) (a := a) hh)

/-- The axis relation `α+β→0` is preserved. -/
theorem rescaled_item6 {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ b ∈ adjacentAxis (rescaledDomain U a h),
      Tendsto (fun v => (rescaledFields S a h).alpha b v +
        (rescaledFields S a h).beta b v)
        (𝓝[>] b ⊓ 𝓟 {v | (b, v) ∈ rescaledDomain U a h}) (𝓝 (0 : ℝ)) := by
  intro b hb
  have hold := hS.item6 _ (affineCoordinate_mem_adjacentAxis hb)
  simpa only [rescaledFields, Function.comp_def] using
    hold.comp (affine_axis_filter (U := U) (a := a) hh)

end ChristodoulouBV.Uniqueness

end
