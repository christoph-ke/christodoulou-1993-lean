module

public import Mathlib
public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import ChristodoulouBV.C1Solution.FrozenBridgeXY
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Classical to frozen local solution bridge

The differential equations are assumed in their classical one-variable form.
The ten frozen interval primitives then follow from the fundamental theorem of
calculus on closed characteristic segments.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.C1Solution

/-- The frozen development has the expected closed triangular closure. -/
theorem closure_developmentWithInitialEdge_eq_closedCoordTriangle
    {b : ℝ} (hb : 0 < b) :
    closure (developmentWithInitialEdge b) = closedCoordTriangle 0 b := by
  exact closure_initialEdgeTriangle hb

/-- At the terminal diagonal parameter, the outgoing in-domain filter is empty. -/
theorem terminal_axis_filter_eq_bot (b : ℝ) :
    nhdsWithin b (Ioi b) ⊓
      Filter.principal {v | (b, v) ∈ developmentWithInitialEdge b} = ⊥ := by
  have hEmpty : {v | (b, v) ∈ developmentWithInitialEdge b} = (∅ : Set ℝ) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hv
    exact (lt_irrefl b) (hv.2.1.trans hv.2.2)
  rw [hEmpty]
  simp

/-- The initial-edge development is closed under its prescribed causal past. -/
theorem developmentWithInitialEdge_isDomainOfDevelopment (b : ℝ) :
    IsDomainOfDevelopment (developmentWithInitialEdge b) := by
  constructor
  · intro p hp
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp q hq
    exact ⟨hq.1.1, hq.2.1, lt_trans hq.2.2 hp.2.2⟩

/-- Continuity of a density and its classical derivative identity give a frozen primitive. -/
theorem intervalPrimitive_of_hasDerivAt {F g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (g x) x) :
    IntervalPrimitive F g a b := by
  have hint : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab
  exact ⟨hint, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hF hderiv hint).symm⟩

/-- A compact closed triangle supplies the uniform bounds required by the frozen C¹ class. -/
theorem closed_triangle_field_bounds {b : ℝ} (hb : 0 < b) (S : Fields)
    (hlam : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 b))
    (hnu : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 b))
    (hlam_pos : ∀ p ∈ closedCoordTriangle 0 b, 0 < S.lam p.1 p.2) :
    (∃ c : ℝ, 0 < c ∧ ∀ p ∈ developmentWithInitialEdge b, c ≤ S.lam p.1 p.2) ∧
    (∃ N : ℝ, ∀ p ∈ developmentWithInitialEdge b, -S.nu p.1 p.2 ≤ N) := by
  have hU : developmentWithInitialEdge b ⊆ closedCoordTriangle 0 b := by
    intro p hp
    change 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b
    exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hc := (isCompact_closedCoordTriangle 0 b).exists_forall_le' hlam hlam_pos
  obtain ⟨c, hcpos, hcle⟩ := hc
  have hKne : (closedCoordTriangle 0 b).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ b
    exact ⟨le_refl _, le_refl _, hb.le⟩
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedCoordTriangle 0 b).exists_isMaxOn
    hKne hnu.neg
  refine ⟨⟨c, hcpos, fun q hq => hcle q (hU hq)⟩,
    ⟨-S.nu p.1 p.2, fun q hq => ?_⟩⟩
  exact hmax (hU hq)

/-- On the development, the positive conformal factor is determined by the three signs. -/
theorem conformal_of_signs {r m lam nu : ℝ}
    (_hr : 0 < r) (hlam : 0 < lam) (hnu : nu < 0)
    (hA : 0 < 1 - 2 * m / r) :
    ∃ Ω : ℝ, 0 < Ω ∧
      (1 - 2 * m / r) * Ω ^ 2 = -(4 * lam * nu) := by
  let A : ℝ := 1 - 2 * m / r
  have hq : 0 < -(4 * lam * nu) / A := by
    apply div_pos
    · nlinarith [mul_neg_of_pos_of_neg hlam hnu]
    · exact hA
  refine ⟨Real.sqrt (-(4 * lam * nu) / A), Real.sqrt_pos.2 hq, ?_⟩
  rw [Real.sq_sqrt hq.le]
  change A * (-(4 * lam * nu) / A) = -(4 * lam * nu)
  exact mul_div_cancel₀ _ (ne_of_gt hA)

/-- A continuous total field vanishing on the axis has the required outgoing axis limit. -/
theorem axis_limit_of_continuousOn_closed_triangle {b a : ℝ} (hb : 0 < b)
    {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (closedCoordTriangle 0 b))
    (ha : a ∈ adjacentAxis (developmentWithInitialEdge b))
    (hzero : F (a, a) = 0) :
    Tendsto (fun v => F (a, v))
      (nhdsWithin a (Ioi a) ⊓ Filter.principal {v | (a, v) ∈ developmentWithInitialEdge b})
      (𝓝 (0 : ℝ)) := by
  have haa : (a, a) ∈ closedCoordTriangle 0 b := by
    change (a, a) ∈ closure (developmentWithInitialEdge b) at ha
    rw [closure_developmentWithInitialEdge_eq_closedCoordTriangle hb] at ha
    exact ha
  have hs : ContinuousOn (fun v => F (a, v)) (Icc a b) := by
    apply hF.comp (continuous_const.prodMk continuous_id).continuousOn
    intro v hv
    change 0 ≤ a ∧ a ≤ v ∧ v ≤ b
    exact ⟨haa.1, hv.1, hv.2⟩
  have haa' : a ∈ Icc a b := ⟨le_refl a, haa.2.2⟩
  have hwithin := (hs a haa').tendsto
  have hle :
      (nhdsWithin a (Ioi a) ⊓ Filter.principal
        {v | (a, v) ∈ developmentWithInitialEdge b}) ≤
        nhdsWithin a (Icc a b) := by
    rw [nhdsWithin, nhdsWithin]
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    refine le_trans inf_le_right ?_
    apply Filter.principal_mono.mpr
    intro v hv
    exact ⟨hv.2.1.le, hv.2.2.le⟩
  rw [← hzero]
  exact hwithin.mono_left hle

/-- Classical outgoing differentiation converts to a primitive on every frozen segment. -/
theorem outgoing_intervalPrimitive {b u a c : ℝ} {F G : ℝ × ℝ → ℝ}
    (hac : a ≤ c)
    (hseg : outSeg u a c ⊆ developmentWithInitialEdge b)
    (hF : ContinuousOn F (developmentWithInitialEdge b))
    (hG : ContinuousOn G (developmentWithInitialEdge b))
    (hderiv : ∀ v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => F (u, w)) (G (u, v)) v) :
    IntervalPrimitive (fun v => F (u, v)) (fun v => G (u, v)) a c := by
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc a c)
      (developmentWithInitialEdge b) := by
    intro v hv
    apply hseg
    exact ⟨rfl, hv⟩
  have hFc : ContinuousOn (fun v => F (u, v)) (Icc a c) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hGc : ContinuousOn (fun v => G (u, v)) (Icc a c) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  apply intervalPrimitive_of_hasDerivAt hac hFc hGc
  intro v hv
  exact hderiv v (hmap ⟨hv.1.le, hv.2.le⟩)

/-- Classical incoming differentiation converts to a primitive on every frozen segment. -/
theorem incoming_intervalPrimitive {b v a c : ℝ} {F G : ℝ × ℝ → ℝ}
    (hac : a ≤ c)
    (hseg : inSeg v a c ⊆ developmentWithInitialEdge b)
    (hF : ContinuousOn F (developmentWithInitialEdge b))
    (hG : ContinuousOn G (developmentWithInitialEdge b))
    (hderiv : ∀ u, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => F (w, v)) (G (u, v)) u) :
    IntervalPrimitive (fun u => F (u, v)) (fun u => G (u, v)) a c := by
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc a c)
      (developmentWithInitialEdge b) := by
    intro u hu
    apply hseg
    exact ⟨hu, rfl⟩
  have hFc : ContinuousOn (fun u => F (u, v)) (Icc a c) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hGc : ContinuousOn (fun u => G (u, v)) (Icc a c) :=
    hG.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  apply intervalPrimitive_of_hasDerivAt hac hFc hGc
  intro u hu
  have haU := hmap ⟨le_refl a, hac⟩
  exact hderiv u (lt_of_le_of_lt haU.1 hu.1)
    (hmap ⟨hu.1.le, hu.2.le⟩)

/-- The classical reduced equations on the initial-edge development imply the
frozen integral solution and frozen C¹ solution. The `m` equations are (1.15)
solved for the derivatives using `λ > 0` and `ν < 0`; (1.16) is stated as well,
although the primitive conversion uses its equivalent (1.18) form. -/
theorem isSolution_and_isC1Solution_of_classical {b : ℝ} (hb : 0 < b)
    (S : Fields)
    (hrC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.r p.1 p.2)
      (closedCoordTriangle 0 b))
    (hphiC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 b))
    (hmC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.m p.1 p.2)
      (closedCoordTriangle 0 b))
    (hlamC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 b))
    (hnuC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 b))
    (halphaC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
      (closedCoordTriangle 0 b))
    (hbetaC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2)
      (closedCoordTriangle 0 b))
    (hrv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.r u) (S.lam u v) v)
    (hru : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.r w v) (S.nu u v) u)
    (hpsiv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.r u w * S.phi u w) (S.alpha u v) v)
    (hpsiu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.r w v * S.phi w v) (S.beta u v) u)
    (hmv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.m u)
        ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
          (2 * S.lam u v)) v)
    (hmu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.m w v)
        ((1 - 2 * S.m u v / S.r u v) * (S.zeta u v)^2 /
          (2 * S.nu u v)) u)
    (hlamu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.lam w v)
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u)
    (hnuv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.nu u)
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v)
    (_hthetau : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.theta w v)
        (-(S.lam u v / S.r u v * S.zeta u v)) u)
    (_hzetav : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.zeta u)
        (-(S.nu u v / S.r u v * S.theta u v)) v)
    (halphau : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => S.alpha w v)
        (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) u)
    (hbetav : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (S.beta u)
        (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) v)
    (haxisr : ∀ a, 0 ≤ a → a ≤ b → S.r a a = 0)
    (haxism : ∀ a, 0 ≤ a → a ≤ b → S.m a a = 0)
    (hrpos : ∀ p ∈ developmentWithInitialEdge b, 0 < S.r p.1 p.2)
    (hlampos : ∀ p ∈ closedCoordTriangle 0 b, 0 < S.lam p.1 p.2)
    (hnuneg : ∀ p ∈ developmentWithInitialEdge b, S.nu p.1 p.2 < 0)
    (hApos : ∀ p ∈ developmentWithInitialEdge b,
      0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) :
    IsSolution (developmentWithInitialEdge b) S ∧
      IsC1Solution (developmentWithInitialEdge b) S := by
  let U := developmentWithInitialEdge b
  let K := closedCoordTriangle 0 b
  have hUK : U ⊆ K := by
    intro p hp
    exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hcl : closure U = K := closure_developmentWithInitialEdge_eq_closedCoordTriangle hb
  have hr : ContinuousOn (fun p : ℝ × ℝ => S.r p.1 p.2) U :=
    hrC1.continuousOn.mono hUK
  have hm : ContinuousOn (fun p : ℝ × ℝ => S.m p.1 p.2) U :=
    hmC1.continuousOn.mono hUK
  have hlam : ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2) U :=
    hlamC1.continuousOn.mono hUK
  have hnu : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2) U :=
    hnuC1.continuousOn.mono hUK
  have hphi : ContinuousOn (fun p : ℝ × ℝ => S.phi p.1 p.2) U :=
    hphiC1.continuousOn.mono hUK
  have halpha : ContinuousOn (fun p : ℝ × ℝ => S.alpha p.1 p.2) U :=
    halphaC1.continuousOn.mono hUK
  have hbeta : ContinuousOn (fun p : ℝ × ℝ => S.beta p.1 p.2) U :=
    hbetaC1.continuousOn.mono hUK
  have hthetaC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) K := by
    have h := halphaC1.sub (hlamC1.mul hphiC1)
    apply h.congr
    intro p hp
    simp only [Fields.theta]
  have hzetaC1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.zeta p.1 p.2) K := by
    have h := hbetaC1.sub (hnuC1.mul hphiC1)
    apply h.congr
    intro p hp
    simp only [Fields.zeta]
  have htheta : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2) U :=
    hthetaC1.continuousOn.mono hUK
  have hzeta : ContinuousOn (fun p : ℝ × ℝ => S.zeta p.1 p.2) U :=
    hzetaC1.continuousOn.mono hUK
  have hmuRatio : ContinuousOn (fun p : ℝ × ℝ =>
      2 * S.m p.1 p.2 / S.r p.1 p.2) U := by
    exact ((continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => (2 : ℝ)) U).mul hm).div
      hr (fun p hp => ne_of_gt (hrpos p hp))
  have hA : ContinuousOn (fun p : ℝ × ℝ =>
      1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) U :=
    continuousOn_const.sub hmuRatio
  have hLden : ContinuousOn (fun p : ℝ × ℝ => 2 * S.lam p.1 p.2) U :=
    continuousOn_const.mul hlam
  have hNden : ContinuousOn (fun p : ℝ × ℝ => 2 * S.nu p.1 p.2) U :=
    continuousOn_const.mul hnu
  have hmassV : ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * (S.theta p.1 p.2)^2 /
        (2 * S.lam p.1 p.2)) U := by
    exact (hA.mul (htheta.pow 2)).div hLden
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_gt (hlampos p (hUK hp))))
  have hmassU : ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * (S.zeta p.1 p.2)^2 /
        (2 * S.nu p.1 p.2)) U := by
    exact (hA.mul (hzeta.pow 2)).div hNden
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_lt (hnuneg p hp)))
  have hGden : ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2) U := hA.mul hr
  have hgrav : ContinuousOn (fun p : ℝ × ℝ =>
      (2 * S.m p.1 p.2 / S.r p.1 p.2) * S.lam p.1 p.2 * S.nu p.1 p.2 /
        ((1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2)) U := by
    exact ((hmuRatio.mul hlam).mul hnu).div hGden
      (fun p hp => mul_ne_zero (ne_of_gt (hApos p hp)) (ne_of_gt (hrpos p hp)))
  have hgravphi : ContinuousOn (fun p : ℝ × ℝ =>
      ((2 * S.m p.1 p.2 / S.r p.1 p.2) * S.lam p.1 p.2 * S.nu p.1 p.2 /
        ((1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2)) *
        S.phi p.1 p.2) U := hgrav.mul hphi
  have hpsic : ContinuousOn (fun p : ℝ × ℝ =>
      S.r p.1 p.2 * S.phi p.1 p.2) U := hr.mul hphi
  obtain ⟨hlambound, hnubound⟩ :=
    closed_triangle_field_bounds hb S hlamC1.continuousOn hnuC1.continuousOn hlampos
  have hsol : IsSolution U S := {
    development := developmentWithInitialEdge_isDomainOfDevelopment b
    radius_out := by
      intro u a c hac hseg
      exact outgoing_intervalPrimitive hac hseg hr hlam (hrv u)
    radius_in := by
      intro v a c hac hseg
      exact incoming_intervalPrimitive hac hseg hr hnu (fun u hu => hru u v hu)
    scalar_radius_out := by
      intro u a c hac hseg
      exact outgoing_intervalPrimitive hac hseg hpsic halpha (hpsiv u)
    scalar_radius_in := by
      intro v a c hac hseg
      exact incoming_intervalPrimitive hac hseg hpsic hbeta (fun u hu => hpsiu u v hu)
    mass_out := by
      intro u a c hac hseg
      exact outgoing_intervalPrimitive hac hseg hm hmassV (hmv u)
    mass_in := by
      intro v a c hac hseg
      exact incoming_intervalPrimitive hac hseg hm hmassU (fun u hu => hmu u v hu)
    lam_in := by
      intro v a c hac hseg
      exact incoming_intervalPrimitive hac hseg hlam hgrav (fun u hu => hlamu u v hu)
    nu_out := by
      intro u a c hac hseg
      exact outgoing_intervalPrimitive hac hseg hnu hgrav (hnuv u)
    alpha_in := by
      intro v a c hac hseg
      exact incoming_intervalPrimitive hac hseg halpha hgravphi (fun u hu => halphau u v hu)
    beta_out := by
      intro u a c hac hseg
      exact outgoing_intervalPrimitive hac hseg hbeta hgravphi (hbetav u)
    radius_axis := by
      intro a ha
      have haa : (a, a) ∈ K := by
        rw [← hcl]
        change (a, a) ∈ closure (developmentWithInitialEdge b) at ha
        exact ha
      exact axis_limit_of_continuousOn_closed_triangle hb hrC1.continuousOn ha
        (haxisr a haa.1 haa.2.2)
    mass_axis := by
      intro a ha
      have haa : (a, a) ∈ K := by
        rw [← hcl]
        change (a, a) ∈ closure (developmentWithInitialEdge b) at ha
        exact ha
      exact axis_limit_of_continuousOn_closed_triangle hb hmC1.continuousOn ha
        (haxism a haa.1 haa.2.2)
    radius_pos := hrpos
    lam_pos := fun p hp => hlampos p (hUK hp)
    conformal := by
      intro p hp
      exact conformal_of_signs (hrpos p hp) (hlampos p (hUK hp))
        (hnuneg p hp) (hApos p hp)
  }
  refine ⟨hsol, ?_⟩
  exact {
    solution := hsol
    nu_bounded_below := hnubound
    lam_bounded_below := hlambound
    lam_c1 := hcl ▸ hlamC1
    nu_c1 := hcl ▸ hnuC1
    phi_c1 := hcl ▸ hphiC1
    theta_c1 := hcl ▸ hthetaC1
    zeta_c1 := hcl ▸ hzetaC1
  }

/-- A frozen primitive depends only on both fields along its closed segment. -/
theorem intervalPrimitive_congr_of_eqOn {F F' G G' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : EqOn F F' (Icc a b)) (hG : EqOn G G' (Icc a b)) :
    IntervalPrimitive F G a b ↔ IntervalPrimitive F' G' a b := by
  constructor <;> intro h
  · refine ⟨h.1.congr_uIoo ?_, ?_⟩
    · intro x hx
      exact hG (Ioo_subset_Icc_self (by simpa only [uIoo_of_le hab] using hx))
    · rw [← hF ⟨hab, le_rfl⟩, ← hF ⟨le_rfl, hab⟩]
      rw [← intervalIntegral.integral_congr (by simpa only [uIcc_of_le hab] using hG)]
      exact h.2
  · refine ⟨h.1.congr_uIoo ?_, ?_⟩
    · intro x hx
      exact (hG (Ioo_subset_Icc_self (by simpa only [uIoo_of_le hab] using hx))).symm
    · rw [hF ⟨hab, le_rfl⟩, hF ⟨le_rfl, hab⟩]
      rw [intervalIntegral.integral_congr (by simpa only [uIcc_of_le hab] using hG)]
      exact h.2

/-- Every clause of `IsSolution` uses only field values inside the development. -/
theorem isSolution_congr_on_development {b : ℝ} {S T : Fields}
    (hEq : ∀ p ∈ developmentWithInitialEdge b,
      S.r p.1 p.2 = T.r p.1 p.2 ∧
      S.phi p.1 p.2 = T.phi p.1 p.2 ∧
      S.m p.1 p.2 = T.m p.1 p.2 ∧
      S.lam p.1 p.2 = T.lam p.1 p.2 ∧
      S.nu p.1 p.2 = T.nu p.1 p.2 ∧
      S.alpha p.1 p.2 = T.alpha p.1 p.2 ∧
      S.beta p.1 p.2 = T.beta p.1 p.2) :
    IsSolution (developmentWithInitialEdge b) S ↔
      IsSolution (developmentWithInitialEdge b) T := by
  let U := developmentWithInitialEdge b
  have transfer (A B : Fields)
      (hAB : ∀ p ∈ U,
        A.r p.1 p.2 = B.r p.1 p.2 ∧
        A.phi p.1 p.2 = B.phi p.1 p.2 ∧
        A.m p.1 p.2 = B.m p.1 p.2 ∧
        A.lam p.1 p.2 = B.lam p.1 p.2 ∧
        A.nu p.1 p.2 = B.nu p.1 p.2 ∧
        A.alpha p.1 p.2 = B.alpha p.1 p.2 ∧
        A.beta p.1 p.2 = B.beta p.1 p.2)
      (H : IsSolution U A) : IsSolution U B := by
    have hr p hp := (hAB p hp).1
    have hphi p hp := (hAB p hp).2.1
    have hm p hp := (hAB p hp).2.2.1
    have hlam p hp := (hAB p hp).2.2.2.1
    have hnu p hp := (hAB p hp).2.2.2.2.1
    have halpha p hp := (hAB p hp).2.2.2.2.2.1
    have hbeta p hp := (hAB p hp).2.2.2.2.2.2
    have htheta (p : ℝ × ℝ) (hp : p ∈ U) :
        A.theta p.1 p.2 = B.theta p.1 p.2 := by
      simp only [Fields.theta, halpha p hp, hlam p hp, hphi p hp]
    have hzeta (p : ℝ × ℝ) (hp : p ∈ U) :
        A.zeta p.1 p.2 = B.zeta p.1 p.2 := by
      simp only [Fields.zeta, hbeta p hp, hnu p hp, hphi p hp]
    have hpsi (p : ℝ × ℝ) (hp : p ∈ U) :
        A.r p.1 p.2 * A.phi p.1 p.2 =
          B.r p.1 p.2 * B.phi p.1 p.2 := by
      rw [hr p hp, hphi p hp]
    have hmassV (p : ℝ × ℝ) (hp : p ∈ U) :
        (1 - 2 * A.m p.1 p.2 / A.r p.1 p.2) * (A.theta p.1 p.2)^2 /
          (2 * A.lam p.1 p.2) =
        (1 - 2 * B.m p.1 p.2 / B.r p.1 p.2) * (B.theta p.1 p.2)^2 /
          (2 * B.lam p.1 p.2) := by
      rw [hm p hp, hr p hp, htheta p hp, hlam p hp]
    have hmassU (p : ℝ × ℝ) (hp : p ∈ U) :
        (1 - 2 * A.m p.1 p.2 / A.r p.1 p.2) * (A.zeta p.1 p.2)^2 /
          (2 * A.nu p.1 p.2) =
        (1 - 2 * B.m p.1 p.2 / B.r p.1 p.2) * (B.zeta p.1 p.2)^2 /
          (2 * B.nu p.1 p.2) := by
      rw [hm p hp, hr p hp, hzeta p hp, hnu p hp]
    have hgrav (p : ℝ × ℝ) (hp : p ∈ U) :
        (2 * A.m p.1 p.2 / A.r p.1 p.2) * A.lam p.1 p.2 * A.nu p.1 p.2 /
          ((1 - 2 * A.m p.1 p.2 / A.r p.1 p.2) * A.r p.1 p.2) =
        (2 * B.m p.1 p.2 / B.r p.1 p.2) * B.lam p.1 p.2 * B.nu p.1 p.2 /
          ((1 - 2 * B.m p.1 p.2 / B.r p.1 p.2) * B.r p.1 p.2) := by
      rw [hm p hp, hr p hp, hlam p hp, hnu p hp]
    have hgravphi (p : ℝ × ℝ) (hp : p ∈ U) :
        ((2 * A.m p.1 p.2 / A.r p.1 p.2) * A.lam p.1 p.2 * A.nu p.1 p.2 /
          ((1 - 2 * A.m p.1 p.2 / A.r p.1 p.2) * A.r p.1 p.2)) *
          A.phi p.1 p.2 =
        ((2 * B.m p.1 p.2 / B.r p.1 p.2) * B.lam p.1 p.2 * B.nu p.1 p.2 /
          ((1 - 2 * B.m p.1 p.2 / B.r p.1 p.2) * B.r p.1 p.2)) *
          B.phi p.1 p.2 := by
      rw [hgrav p hp, hphi p hp]
    have out {u a c : ℝ} {F F' G G' : ℝ × ℝ → ℝ}
        (hac : a ≤ c) (hseg : outSeg u a c ⊆ U)
        (hF : ∀ p ∈ U, F p = F' p) (hG : ∀ p ∈ U, G p = G' p)
        (h : IntervalPrimitive (fun x => F (u, x)) (fun x => G (u, x)) a c) :
        IntervalPrimitive (fun x => F' (u, x)) (fun x => G' (u, x)) a c := by
      apply (intervalPrimitive_congr_of_eqOn hac ?_ ?_).mp h
      · intro x hx
        exact hF (u, x) (hseg ⟨rfl, hx⟩)
      · intro x hx
        exact hG (u, x) (hseg ⟨rfl, hx⟩)
    have incoming {v a c : ℝ} {F F' G G' : ℝ × ℝ → ℝ}
        (hac : a ≤ c) (hseg : inSeg v a c ⊆ U)
        (hF : ∀ p ∈ U, F p = F' p) (hG : ∀ p ∈ U, G p = G' p)
        (h : IntervalPrimitive (fun x => F (x, v)) (fun x => G (x, v)) a c) :
        IntervalPrimitive (fun x => F' (x, v)) (fun x => G' (x, v)) a c := by
      apply (intervalPrimitive_congr_of_eqOn hac ?_ ?_).mp h
      · intro x hx
        exact hF (x, v) (hseg ⟨hx, rfl⟩)
      · intro x hx
        exact hG (x, v) (hseg ⟨hx, rfl⟩)
    refine {
      development := H.development
      radius_out := by
        intro u a c hac hseg
        exact out hac hseg hr hlam (H.radius_out u a c hac hseg)
      radius_in := by
        intro v a c hac hseg
        exact incoming hac hseg hr hnu (H.radius_in v a c hac hseg)
      scalar_radius_out := by
        intro u a c hac hseg
        exact out hac hseg hpsi halpha (H.scalar_radius_out u a c hac hseg)
      scalar_radius_in := by
        intro v a c hac hseg
        exact incoming hac hseg hpsi hbeta (H.scalar_radius_in v a c hac hseg)
      mass_out := by
        intro u a c hac hseg
        exact out hac hseg hm hmassV (H.mass_out u a c hac hseg)
      mass_in := by
        intro v a c hac hseg
        exact incoming hac hseg hm hmassU (H.mass_in v a c hac hseg)
      lam_in := by
        intro v a c hac hseg
        exact incoming hac hseg hlam hgrav (H.lam_in v a c hac hseg)
      nu_out := by
        intro u a c hac hseg
        exact out hac hseg hnu hgrav (H.nu_out u a c hac hseg)
      alpha_in := by
        intro v a c hac hseg
        exact incoming hac hseg halpha hgravphi (H.alpha_in v a c hac hseg)
      beta_out := by
        intro u a c hac hseg
        exact out hac hseg hbeta hgravphi (H.beta_out u a c hac hseg)
      radius_axis := by
        intro a ha
        have heq : A.r a =ᶠ[nhdsWithin a (Ioi a) ⊓
            Filter.principal {v | (a, v) ∈ U}] B.r a := by
          have hdom : ∀ᶠ v in Filter.principal {v | (a, v) ∈ U},
              (a, v) ∈ U := Filter.mem_principal_self _
          filter_upwards [hdom.filter_mono inf_le_right] with v hv
          exact hr (a, v) hv
        exact (H.radius_axis a ha).congr' heq
      mass_axis := by
        intro a ha
        have heq : A.m a =ᶠ[nhdsWithin a (Ioi a) ⊓
            Filter.principal {v | (a, v) ∈ U}] B.m a := by
          have hdom : ∀ᶠ v in Filter.principal {v | (a, v) ∈ U},
              (a, v) ∈ U := Filter.mem_principal_self _
          filter_upwards [hdom.filter_mono inf_le_right] with v hv
          exact hm (a, v) hv
        exact (H.mass_axis a ha).congr' heq
      radius_pos := by
        intro p hp
        rw [← hr p hp]
        exact H.radius_pos p hp
      lam_pos := by
        intro p hp
        rw [← hlam p hp]
        exact H.lam_pos p hp
      conformal := by
        intro p hp
        obtain ⟨Ω, hΩ, heq⟩ := H.conformal p hp
        refine ⟨Ω, hΩ, ?_⟩
        rw [← hm p hp, ← hr p hp, ← hlam p hp, ← hnu p hp]
        exact heq
    }
  constructor
  · intro H
    exact transfer S T hEq H
  · intro H
    apply transfer T S _ H
    intro p hp
    obtain ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta⟩ := hEq p hp
    exact ⟨hr.symm, hphi.symm, hm.symm, hlam.symm, hnu.symm,
      halpha.symm, hbeta.symm⟩

/-- Altering all seven total fields outside the closed triangle leaves both
frozen solution predicates unchanged, including their axis filters. -/
theorem isC1Solution_congr_on_closed_triangle {b : ℝ} (hb : 0 < b)
    {S T : Fields}
    (hEq : ∀ p ∈ closedCoordTriangle 0 b,
      S.r p.1 p.2 = T.r p.1 p.2 ∧
      S.phi p.1 p.2 = T.phi p.1 p.2 ∧
      S.m p.1 p.2 = T.m p.1 p.2 ∧
      S.lam p.1 p.2 = T.lam p.1 p.2 ∧
      S.nu p.1 p.2 = T.nu p.1 p.2 ∧
      S.alpha p.1 p.2 = T.alpha p.1 p.2 ∧
      S.beta p.1 p.2 = T.beta p.1 p.2) :
    IsC1Solution (developmentWithInitialEdge b) S ↔
      IsC1Solution (developmentWithInitialEdge b) T := by
  let U := developmentWithInitialEdge b
  let K := closedCoordTriangle 0 b
  have hUK : U ⊆ K := by
    intro p hp
    exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hcl : closure U = K := closure_developmentWithInitialEdge_eq_closedCoordTriangle hb
  have hEqU : ∀ p ∈ U,
      S.r p.1 p.2 = T.r p.1 p.2 ∧
      S.phi p.1 p.2 = T.phi p.1 p.2 ∧
      S.m p.1 p.2 = T.m p.1 p.2 ∧
      S.lam p.1 p.2 = T.lam p.1 p.2 ∧
      S.nu p.1 p.2 = T.nu p.1 p.2 ∧
      S.alpha p.1 p.2 = T.alpha p.1 p.2 ∧
      S.beta p.1 p.2 = T.beta p.1 p.2 := by
    intro p hp
    exact hEq p (hUK hp)
  have hsol := isSolution_congr_on_development hEqU
  have transfer (A B : Fields)
      (hAB : ∀ p ∈ K,
        A.r p.1 p.2 = B.r p.1 p.2 ∧
        A.phi p.1 p.2 = B.phi p.1 p.2 ∧
        A.m p.1 p.2 = B.m p.1 p.2 ∧
        A.lam p.1 p.2 = B.lam p.1 p.2 ∧
        A.nu p.1 p.2 = B.nu p.1 p.2 ∧
        A.alpha p.1 p.2 = B.alpha p.1 p.2 ∧
        A.beta p.1 p.2 = B.beta p.1 p.2)
      (hABsol : IsSolution U A → IsSolution U B)
      (H : IsC1Solution U A) : IsC1Solution U B := by
    have htheta (p : ℝ × ℝ) (hp : p ∈ K) :
        A.theta p.1 p.2 = B.theta p.1 p.2 := by
      obtain ⟨_, hphi, _, hlam, _, halpha, _⟩ := hAB p hp
      simp only [Fields.theta, halpha, hlam, hphi]
    have hzeta (p : ℝ × ℝ) (hp : p ∈ K) :
        A.zeta p.1 p.2 = B.zeta p.1 p.2 := by
      obtain ⟨_, hphi, _, _, hnu, _, hbeta⟩ := hAB p hp
      simp only [Fields.zeta, hbeta, hnu, hphi]
    refine {
      solution := hABsol H.solution
      nu_bounded_below := by
        obtain ⟨N, hN⟩ := H.nu_bounded_below
        refine ⟨N, ?_⟩
        intro p hp
        rw [← (hAB p (hUK hp)).2.2.2.2.1]
        exact hN p hp
      lam_bounded_below := by
        obtain ⟨c, hc, hC⟩ := H.lam_bounded_below
        refine ⟨c, hc, ?_⟩
        intro p hp
        rw [← (hAB p (hUK hp)).2.2.2.1]
        exact hC p hp
      lam_c1 := by
        apply H.lam_c1.congr
        intro p hp
        exact (hAB p (hcl ▸ hp)).2.2.2.1.symm
      nu_c1 := by
        apply H.nu_c1.congr
        intro p hp
        exact (hAB p (hcl ▸ hp)).2.2.2.2.1.symm
      phi_c1 := by
        apply H.phi_c1.congr
        intro p hp
        exact (hAB p (hcl ▸ hp)).2.1.symm
      theta_c1 := by
        apply H.theta_c1.congr
        intro p hp
        exact (htheta p (hcl ▸ hp)).symm
      zeta_c1 := by
        apply H.zeta_c1.congr
        intro p hp
        exact (hzeta p (hcl ▸ hp)).symm
    }
  constructor
  · intro H
    exact transfer S T hEq hsol.mp H
  · intro H
    apply transfer T S _ hsol.mpr H
    intro p hp
    obtain ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta⟩ := hEq p hp
    exact ⟨hr.symm, hphi.symm, hm.symm, hlam.symm, hnu.symm,
      halpha.symm, hbeta.symm⟩

/-- Coordinate clipping onto the closed initial-edge triangle. -/
@[expose] def clipToClosedTriangle (b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let u := max 0 (min b p.1)
  (u, max u (min b p.2))

/-- Clipping maps the plane into the closed triangle when the top parameter is positive. -/
theorem clipToClosedTriangle_mem {b : ℝ} (hb : 0 < b) (p : ℝ × ℝ) :
    clipToClosedTriangle b p ∈ closedCoordTriangle 0 b := by
  let u := max 0 (min b p.1)
  let v := max u (min b p.2)
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ b
  have hu0 : 0 ≤ u := le_max_left _ _
  have hub : u ≤ b := max_le hb.le (min_le_left _ _)
  exact ⟨hu0, le_max_left _ _, max_le hub (min_le_left _ _)⟩

/-- Clipping fixes every point of the closed triangle. -/
theorem clipToClosedTriangle_eq_self {b : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle 0 b) : clipToClosedTriangle b p = p := by
  change 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
  have hub : p.1 ≤ b := hp.2.1.trans hp.2.2
  ext
  · simp [clipToClosedTriangle, min_eq_right hub, max_eq_right hp.1]
  · simp [clipToClosedTriangle, min_eq_right hub, max_eq_right hp.1,
      min_eq_right hp.2.2, max_eq_right hp.2.1]

/-- Extend the seven fields to the plane by evaluating them at the clipped point. -/
@[expose] def clipFieldsToClosedTriangle (S : Fields) (b : ℝ) : Fields where
  r u v := S.r (clipToClosedTriangle b (u, v)).1 (clipToClosedTriangle b (u, v)).2
  phi u v := S.phi (clipToClosedTriangle b (u, v)).1
    (clipToClosedTriangle b (u, v)).2
  m u v := S.m (clipToClosedTriangle b (u, v)).1 (clipToClosedTriangle b (u, v)).2
  lam u v := S.lam (clipToClosedTriangle b (u, v)).1
    (clipToClosedTriangle b (u, v)).2
  nu u v := S.nu (clipToClosedTriangle b (u, v)).1
    (clipToClosedTriangle b (u, v)).2
  alpha u v := S.alpha (clipToClosedTriangle b (u, v)).1
    (clipToClosedTriangle b (u, v)).2
  beta u v := S.beta (clipToClosedTriangle b (u, v)).1
    (clipToClosedTriangle b (u, v)).2

/-- Clipped totalization preserves both frozen solution predicates. -/
theorem clipped_isSolution_and_isC1Solution_iff {b : ℝ} (hb : 0 < b) (S : Fields) :
    (IsSolution (developmentWithInitialEdge b) S ↔
      IsSolution (developmentWithInitialEdge b) (clipFieldsToClosedTriangle S b)) ∧
    (IsC1Solution (developmentWithInitialEdge b) S ↔
      IsC1Solution (developmentWithInitialEdge b) (clipFieldsToClosedTriangle S b)) := by
  have hEq : ∀ p ∈ closedCoordTriangle 0 b,
      S.r p.1 p.2 = (clipFieldsToClosedTriangle S b).r p.1 p.2 ∧
      S.phi p.1 p.2 = (clipFieldsToClosedTriangle S b).phi p.1 p.2 ∧
      S.m p.1 p.2 = (clipFieldsToClosedTriangle S b).m p.1 p.2 ∧
      S.lam p.1 p.2 = (clipFieldsToClosedTriangle S b).lam p.1 p.2 ∧
      S.nu p.1 p.2 = (clipFieldsToClosedTriangle S b).nu p.1 p.2 ∧
      S.alpha p.1 p.2 = (clipFieldsToClosedTriangle S b).alpha p.1 p.2 ∧
      S.beta p.1 p.2 = (clipFieldsToClosedTriangle S b).beta p.1 p.2 := by
    intro p hp
    simp [clipFieldsToClosedTriangle, clipToClosedTriangle_eq_self hp]
  have hUK : developmentWithInitialEdge b ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  exact ⟨isSolution_congr_on_development (fun p hp => hEq p (hUK hp)),
    isC1Solution_congr_on_closed_triangle hb hEq⟩

end ChristodoulouBV.C1Solution

end
