module

public import ChristodoulouBV.BVSolution.Signs
public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Primitive

/-!
# Calculus of the frozen characteristic primitives

Every frozen interval primitive yields an absolutely continuous field and its
specified derivative almost everywhere on a closed off-axis segment. The scalar
identities use the product rule and the BV class's scalar absolute continuity.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV

/-- An ordered family of frozen primitives gives absolute continuity and its
a.e. derivative on the enclosing closed interval. -/
theorem IntervalPrimitive.ac_ae_of_subsegments {F g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive F g x y) :
    AbsolutelyContinuousOnInterval F a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b → deriv F t = g t := by
  have hg x y (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      IntervalIntegrable g volume x y := (h x y hax hxy hyb).1
  have hF x y (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      F y - F x = ∫ t in x..y, g t := (h x y hax hxy hyb).2
  exact ⟨AbsolutelyContinuousOnInterval.of_integral_eq_sub_of_le hab hg hF,
    AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub_of_le hab hg hF⟩

/-- Two frozen densities of the same primitive agree almost everywhere. -/
theorem IntervalPrimitive.same_primitive_ae {F g h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive F g x y)
    (hh : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive F h x y) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → g t = h t := by
  filter_upwards [(ac_ae_of_subsegments hab hg).2,
    (ac_ae_of_subsegments hab hh).2] with t hgt hht ht
  exact (hgt ht).symm.trans (hht ht)

/-- Densities agree almost everywhere when their primitives agree pointwise on
the enclosing segment. -/
theorem IntervalPrimitive.same_primitive_ae_of_eqOn
    {F G g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive F g x y)
    (hG : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalPrimitive G h x y)
    (hEq : EqOn F G (Icc a b)) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → g t = h t := by
  apply same_primitive_ae hab hF
  intro x y hax hxy hyb
  obtain ⟨hint, heq⟩ := hG x y hax hxy hyb
  refine ⟨hint, ?_⟩
  rw [hEq ⟨hax.trans hxy, hyb⟩, hEq ⟨hax, hxy.trans hyb⟩]
  exact heq

/-- A closed outgoing subsegment lies in its enclosing outgoing segment. -/
theorem outSeg_subsegment {u a b x y : ℝ}
    (hax : a ≤ x) (_hxy : x ≤ y) (hyb : y ≤ b) :
    outSeg u x y ⊆ outSeg u a b := by
  intro p hp
  rcases p with ⟨s, t⟩
  have ⟨hs, ht⟩ : s = u ∧ t ∈ Icc x y := by
    simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
  subst s
  exact ⟨rfl, ⟨hax.trans ht.1, ht.2.trans hyb⟩⟩

/-- A closed incoming subsegment lies in its enclosing incoming segment. -/
theorem inSeg_subsegment {v a b x y : ℝ}
    (hax : a ≤ x) (_hxy : x ≤ y) (hyb : y ≤ b) :
    inSeg v x y ⊆ inSeg v a b := by
  intro p hp
  rcases p with ⟨s, t⟩
  have ⟨hs, ht⟩ : s ∈ Icc x y ∧ t = v := by
    simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
  subst t
  exact ⟨⟨hax.trans hs.1, hs.2.trans hyb⟩, rfl⟩

namespace IsSolution

/-- The outgoing radius has derivative `λ` almost everywhere. -/
theorem radius_out_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    AbsolutelyContinuousOnInterval (S.r u) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b → deriv (S.r u) t = S.lam u t := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.radius_out u x y hxy ((outSeg_subsegment hax hxy hyb).trans hseg)

/-- The incoming radius has derivative `ν` almost everywhere. -/
theorem radius_in_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun u => S.r u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun x => S.r x v) u = S.nu u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.radius_in v x y hxy ((inSeg_subsegment hax hxy hyb).trans hseg)

/-- The outgoing derivative of `rφ` is `α` almost everywhere. -/
theorem scalar_radius_out_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun v => S.r u v * S.phi u v) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b →
        deriv (fun t => S.r u t * S.phi u t) v = S.alpha u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.scalar_radius_out u x y hxy ((outSeg_subsegment hax hxy hyb).trans hseg)

/-- The incoming derivative of `rφ` is `β` almost everywhere. -/
theorem scalar_radius_in_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun u => S.r u v * S.phi u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun x => S.r x v * S.phi x v) u = S.beta u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.scalar_radius_in v x y hxy ((inSeg_subsegment hax hxy hyb).trans hseg)

/-- The outgoing mass derivative is the frozen nonnegative density. -/
theorem mass_out_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    AbsolutelyContinuousOnInterval (S.m u) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b →
        deriv (S.m u) v = IsBVSolution.massV S u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.mass_out u x y hxy ((outSeg_subsegment hax hxy hyb).trans hseg)

/-- The incoming mass derivative is its frozen signed density. -/
theorem mass_in_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun u => S.m u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun x => S.m x v) u =
          (1 - 2 * S.m u v / S.r u v) * (S.zeta u v) ^ 2 / (2 * S.nu u v) := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.mass_in v x y hxy ((inSeg_subsegment hax hxy hyb).trans hseg)

/-- The incoming derivative of `λ` is the frozen mixed coefficient. -/
theorem lam_in_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun u => S.lam u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun x => S.lam x v) u = IsBVSolution.radiusCoeff S u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.lam_in v x y hxy ((inSeg_subsegment hax hxy hyb).trans hseg)

/-- The outgoing derivative of `ν` is the frozen mixed coefficient. -/
theorem nu_out_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    AbsolutelyContinuousOnInterval (S.nu u) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b →
        deriv (S.nu u) v = IsBVSolution.radiusCoeff S u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.nu_out u x y hxy ((outSeg_subsegment hax hxy hyb).trans hseg)

/-- The incoming derivative of `α` is the mixed coefficient times `φ`. -/
theorem alpha_in_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun u => S.alpha u v) a b ∧
      ∀ᵐ u ∂volume, u ∈ Icc a b →
        deriv (fun x => S.alpha x v) u =
          IsBVSolution.radiusCoeff S u v * S.phi u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.alpha_in v x y hxy ((inSeg_subsegment hax hxy hyb).trans hseg)

/-- The outgoing derivative of `β` is the mixed coefficient times `φ`. -/
theorem beta_out_ac_ae {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    AbsolutelyContinuousOnInterval (S.beta u) a b ∧
      ∀ᵐ v ∂volume, v ∈ Icc a b →
        deriv (S.beta u) v = IsBVSolution.radiusCoeff S u v * S.phi u v := by
  apply IntervalPrimitive.ac_ae_of_subsegments hab
  intro x y hax hxy hyb
  exact hS.beta_out u x y hxy ((outSeg_subsegment hax hxy hyb).trans hseg)

end IsSolution

namespace IsBVSolution

/-- A fixed-endpoint frozen primitive gives absolute continuity. -/
theorem primitive_ac {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, IntervalPrimitive f g a t) :
    AbsolutelyContinuousOnInterval f a b :=
  absolutely_continuous_on_interval_of_primitive hab h

/-- The outgoing scalar derivative is `θ/r` almost everywhere off the axis. -/
theorem ae_deriv_phi_out {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    ∀ᵐ v ∂volume, v ∈ Icc a b →
      deriv (S.phi u) v = S.theta u v / S.r u v := by
  have hR := hS.solution.radius_out_ac_ae hab hseg
  have hP := hS.solution.scalar_radius_out_ac_ae hab hseg
  have hPhi := hS.item3_ac_out u a b hab hseg
  filter_upwards [hR.2, hP.2, hR.1.ae_deriv_mul hPhi] with v hrd hpd hmul hv
  have hvU : (u, v) ∈ U := hseg ⟨rfl, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (hS.solution.radius_pos (u, v) hvU)
  have hθ : S.r u v * deriv (S.phi u) v = S.theta u v := by
    have hp := hmul (by simpa only [uIcc_of_le hab] using hv)
    rw [hpd hv, hrd hv] at hp
    dsimp [Fields.theta]
    linarith
  exact (eq_div_iff hr).2 (by simpa only [mul_comm] using hθ)

/-- The incoming scalar derivative is `ζ/r` almost everywhere off the axis. -/
theorem ae_deriv_phi_in {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ u ∂volume, u ∈ Icc a b →
      deriv (fun x => S.phi x v) u = S.zeta u v / S.r u v := by
  have hR := hS.solution.radius_in_ac_ae hab hseg
  have hP := hS.solution.scalar_radius_in_ac_ae hab hseg
  have hPhi := hS.item3_ac_in v a b hab hseg
  filter_upwards [hR.2, hP.2, hR.1.ae_deriv_mul hPhi] with u hrd hpd hmul hu
  have huU : (u, v) ∈ U := hseg ⟨hu, rfl⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (hS.solution.radius_pos (u, v) huU)
  have hζ : S.r u v * deriv (fun x => S.phi x v) u = S.zeta u v := by
    have hp := hmul (by simpa only [uIcc_of_le hab] using hu)
    rw [hpd hu, hrd hu] at hp
    dsimp [Fields.zeta]
    linarith
  exact (eq_div_iff hr).2 (by simpa only [mul_comm] using hζ)

/-- The frozen `θ` equals `r ∂ᵥφ` almost everywhere on a closed outgoing segment. -/
theorem ae_theta_eq_radius_mul_deriv_phi
    {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    ∀ᵐ v ∂volume, v ∈ Icc a b →
      S.theta u v = S.r u v * deriv (S.phi u) v := by
  filter_upwards [hS.ae_deriv_phi_out hab hseg] with v hd hv
  have hvU : (u, v) ∈ U := hseg ⟨rfl, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (hS.solution.radius_pos (u, v) hvU)
  rw [hd hv]
  field_simp

/-- The frozen `ζ` equals `r ∂ᵤφ` almost everywhere on a closed incoming segment. -/
theorem ae_zeta_eq_radius_mul_deriv_phi
    {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ u ∂volume, u ∈ Icc a b →
      S.zeta u v = S.r u v * deriv (fun x => S.phi x v) u := by
  filter_upwards [hS.ae_deriv_phi_in hab hseg] with u hd hu
  have huU : (u, v) ∈ U := hseg ⟨hu, rfl⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (hS.solution.radius_pos (u, v) huU)
  rw [hd hu]
  field_simp

/-- The outgoing mass equation uses the scalar derivative in the original
quadratic density almost everywhere. -/
theorem ae_mass_out_phi_deriv
    {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U) :
    ∀ᵐ v ∂volume, v ∈ Icc a b →
      deriv (S.m u) v =
        (1 - 2 * S.m u v / S.r u v) *
          (S.r u v * deriv (S.phi u) v) ^ 2 / (2 * S.lam u v) := by
  filter_upwards [(hS.solution.mass_out_ac_ae hab hseg).2,
    hS.ae_theta_eq_radius_mul_deriv_phi hab hseg] with v hm hθ hv
  rw [hm hv, IsBVSolution.massV, hθ hv]

/-- The incoming mass equation uses the scalar derivative in the original
quadratic density almost everywhere. -/
theorem ae_mass_in_phi_deriv
    {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ u ∂volume, u ∈ Icc a b →
      deriv (fun x => S.m x v) u =
        (1 - 2 * S.m u v / S.r u v) *
          (S.r u v * deriv (fun x => S.phi x v) u) ^ 2 / (2 * S.nu u v) := by
  filter_upwards [(hS.solution.mass_in_ac_ae hab hseg).2,
    hS.ae_zeta_eq_radius_mul_deriv_phi hab hseg] with u hm hζ hu
  rw [hm hu, hζ hu]

end IsBVSolution

end ChristodoulouBV

end
