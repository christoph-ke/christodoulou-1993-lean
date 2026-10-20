module

public import ChristodoulouBV.AreaEstimates.LogTransportMixed
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Commuted logarithmic mixed transports

The source's integration order uses the reverse mixed partial from the
algebraic identities. The C¹ transport coefficient permits commutation
without assuming that the expansion fields are C².
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

private theorem log_mixed_commute_horizontal
    {T : Set (ℝ × ℝ)} (hT : IsOpen T)
    {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F T) (hG : ContDiffOn ℝ 1 G T)
    (hsource : ∀ p ∈ T, (fderiv ℝ F p) (1, 0) = G p)
    {a a' d d' u v : ℝ} (haa' : a < a') (hdd' : d < d')
    (hR : Icc a a' ×ˢ Icc d d' ⊆ T)
    (hu : u ∈ Ioo a a') (hv : v ∈ Ioo d d') :
    deriv (fun x => deriv (fun y => F (x, y)) v) u =
      deriv (fun y => deriv (fun x => F (x, y)) u) v := by
  have hp : (u, v) ∈ T := hR ⟨⟨hu.1.le, hu.2.le⟩, ⟨hv.1.le, hv.2.le⟩⟩
  have hFdiff (p : ℝ × ℝ) (hp : p ∈ T) : DifferentiableAt ℝ F p :=
    (hF.differentiableOn (by norm_num) p hp).differentiableAt (hT.mem_nhds hp)
  have hGdiff : DifferentiableAt ℝ G (u, v) :=
    (hG.differentiableOn (by norm_num) (u, v) hp).differentiableAt (hT.mem_nhds hp)
  have hReg := mixed_horizontal_on_rectangle hT hF hG hsource haa' hdd' hR
    ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hv.2.le⟩
  have hLeft : (fun x => deriv (fun y => F (x, y)) v) =ᶠ[𝓝 u]
      (fun x => (fderiv ℝ F (x, v)) (0, 1)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    have hxp : (x, v) ∈ T := hR
      ⟨⟨hx.1.le, hx.2.le⟩, ⟨hv.1.le, hv.2.le⟩⟩
    have hpath : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) v :=
      (hasDerivAt_const v x).prodMk (hasDerivAt_id' v)
    exact ((hFdiff (x, v) hxp).hasFDerivAt.comp_hasDerivAt v hpath).deriv
  have hRight : (fun y => deriv (fun x => F (x, y)) u) =ᶠ[𝓝 v]
      (fun y => G (u, y)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with y hy
    have hyp : (u, y) ∈ T := hR
      ⟨⟨hu.1.le, hu.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩
    have hpath : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u y)
    have hjet := ((hFdiff (u, y) hyp).hasFDerivAt.comp_hasDerivAt u hpath).deriv
    rw [hsource (u, y) hyp] at hjet
    exact hjet
  have hGpath : HasDerivAt (fun y => G (u, y))
      ((fderiv ℝ G (u, v)) (0, 1)) v :=
    hGdiff.hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id' v))
  calc
    deriv (fun x => deriv (fun y => F (x, y)) v) u =
        (fderiv ℝ G (u, v)) (0, 1) := by
      rw [hLeft.deriv_eq]
      exact (hReg.hasDerivAt (Icc_mem_nhds hu.1 hu.2)).deriv
    _ = deriv (fun y => deriv (fun x => F (x, y)) u) v := by
      rw [hRight.deriv_eq, hGpath.deriv]

private theorem log_mixed_commute_vertical
    {T : Set (ℝ × ℝ)} (hT : IsOpen T)
    {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F T) (hG : ContDiffOn ℝ 1 G T)
    (hsource : ∀ p ∈ T, (fderiv ℝ F p) (0, 1) = G p)
    {a a' d d' u v : ℝ} (haa' : a < a') (hdd' : d < d')
    (hR : Icc a a' ×ˢ Icc d d' ⊆ T)
    (hu : u ∈ Ioo a a') (hv : v ∈ Ioo d d') :
    deriv (fun y => deriv (fun x => F (x, y)) u) v =
      deriv (fun x => deriv (fun y => F (x, y)) v) u := by
  have hp : (u, v) ∈ T := hR ⟨⟨hu.1.le, hu.2.le⟩, ⟨hv.1.le, hv.2.le⟩⟩
  have hFdiff (p : ℝ × ℝ) (hp : p ∈ T) : DifferentiableAt ℝ F p :=
    (hF.differentiableOn (by norm_num) p hp).differentiableAt (hT.mem_nhds hp)
  have hGdiff : DifferentiableAt ℝ G (u, v) :=
    (hG.differentiableOn (by norm_num) (u, v) hp).differentiableAt (hT.mem_nhds hp)
  have hReg := mixed_vertical_on_rectangle hT hF hG hsource haa' hdd' hR
    ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hv.2.le⟩
  have hLeft : (fun y => deriv (fun x => F (x, y)) u) =ᶠ[𝓝 v]
      (fun y => (fderiv ℝ F (u, y)) (1, 0)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with y hy
    have hyp : (u, y) ∈ T := hR
      ⟨⟨hu.1.le, hu.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩
    have hpath : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u y)
    exact ((hFdiff (u, y) hyp).hasFDerivAt.comp_hasDerivAt u hpath).deriv
  have hRight : (fun x => deriv (fun y => F (x, y)) v) =ᶠ[𝓝 u]
      (fun x => G (x, v)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    have hxp : (x, v) ∈ T := hR
      ⟨⟨hx.1.le, hx.2.le⟩, ⟨hv.1.le, hv.2.le⟩⟩
    have hpath : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) v :=
      (hasDerivAt_const v x).prodMk (hasDerivAt_id' v)
    have hjet := ((hFdiff (x, v) hxp).hasFDerivAt.comp_hasDerivAt v hpath).deriv
    rw [hsource (x, v) hxp] at hjet
    exact hjet
  have hGpath : HasDerivAt (fun x => G (x, v))
      ((fderiv ℝ G (u, v)) (1, 0)) u :=
    hGdiff.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v))
  calc
    deriv (fun y => deriv (fun x => F (x, y)) u) v =
        (fderiv ℝ G (u, v)) (1, 0) := by
      rw [hLeft.deriv_eq]
      exact (hReg.hasDerivAt (Icc_mem_nhds hv.1 hv.2)).deriv
    _ = deriv (fun x => deriv (fun y => F (x, y)) v) u := by
      rw [hRight.deriv_eq, hGpath.deriv]

private theorem interior_rectangle {B u v : ℝ}
    (hp : (u, v) ∈ openCoordTriangle 0 B) :
    ∃ a a' d d' : ℝ,
      0 < a ∧ a < u ∧ u < a' ∧ a' < d ∧ d < v ∧ v < d' ∧ d' < B := by
  refine ⟨u / 2, (u + v) / 2, (u + 3 * v) / 4, (v + B) / 2, ?_⟩
  rcases hp with ⟨hu, huv, hv⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem log_lam_mixed_commute {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun x => deriv (fun y => Real.log (S.lam x y)) v) u =
      deriv (fun y => deriv (fun x => Real.log (S.lam x y)) u) v := by
  let T := openCoordTriangle 0 B
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ closedCoordTriangle 0 B := by
    intro p hp
    exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hF : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) T :=
    ((C1Solution.five_fields_contDiffOn hB hB1 H).1.mono hsub).log
      (fun p hp => (H.solution.lam_pos p
        ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩).ne')
  have hG := (log_transport_coefficients_contDiffOn hB hB1 H).1
  have hsource (p : ℝ × ℝ) (hp : p ∈ T) :=
    (log_transport_first_jets hB hB1 H hp).1
  obtain ⟨a, a', d, d', ha0, hau, hua', ha'd, hdv, hvd', hd'B⟩ :=
    interior_rectangle hp
  have hR : Icc a a' ×ˢ Icc d d' ⊆ T := by
    intro p hpR
    exact ⟨ha0.trans_le hpR.1.1,
      (hpR.1.2.trans_lt ha'd).trans_le hpR.2.1,
      hpR.2.2.trans_lt hd'B⟩
  exact log_mixed_commute_horizontal hT hF hG hsource
    (hau.trans hua') (hdv.trans hvd') hR ⟨hau, hua'⟩ ⟨hdv, hvd'⟩

private theorem log_nu_mixed_commute {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun y => deriv (fun x => Real.log (-S.nu x y)) u) v =
      deriv (fun x => deriv (fun y => Real.log (-S.nu x y)) v) u := by
  let T := openCoordTriangle 0 B
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ closedCoordTriangle 0 B := by
    intro p hp
    exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hF : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) T :=
    (((C1Solution.five_fields_contDiffOn hB hB1 H).2.1.mono hsub).neg).log
      (fun p hp => neg_ne_zero.mpr
        (C1Solution.nu_neg_closed_triangle hB hB1 H (hsub hp)).ne)
  have hG := (log_transport_coefficients_contDiffOn hB hB1 H).2
  have hsource (p : ℝ × ℝ) (hp : p ∈ T) :=
    (log_transport_first_jets hB hB1 H hp).2
  obtain ⟨a, a', d, d', ha0, hau, hua', ha'd, hdv, hvd', hd'B⟩ :=
    interior_rectangle hp
  have hR : Icc a a' ×ˢ Icc d d' ⊆ T := by
    intro p hpR
    exact ⟨ha0.trans_le hpR.1.1,
      (hpR.1.2.trans_lt ha'd).trans_le hpR.2.1,
      hpR.2.2.trans_lt hd'B⟩
  exact log_mixed_commute_vertical hT hF hG hsource
    (hau.trans hua') (hdv.trans hvd') hR ⟨hau, hua'⟩ ⟨hdv, hvd'⟩

/-- Equation (4.11a) in the integration order used by the source. -/
theorem eq4_11a {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun x => deriv (fun y => Real.log (S.lam x y)) v) u =
      deriv (fun t =>
        (2 * S.m t v / S.r t v) / (1 - 2 * S.m t v / S.r t v) *
          (S.lam t v / S.r t v) - sourceLogCorrection S t v) u +
      sourceJacobianPhiBetaNu S u v := by
  rw [log_lam_mixed_commute hB hB1 H hp]
  exact eq4_11a_uncommuted hB hB1 H hrGauge hcenter hboot hp

/-- Sign-corrected (4.11b): the derivative of the mass term contains `+ f*`.
The printed `- f*` follows the erroneous sign in the displayed `∂ᵥf*`. -/
theorem eq4_11b_corrected {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun y => deriv (fun x => Real.log (-S.nu x y)) u) v =
      deriv (fun t =>
        (2 * S.m u t / S.r u t) / (1 - 2 * S.m u t / S.r u t) *
          (S.nu u t / S.r u t) + sourceLogCorrectionStar S u t) v -
      sourceJacobianPhiAlphaLam S u v := by
  rw [log_nu_mixed_commute hB hB1 H hp]
  exact eq4_11b_corrected_uncommuted hB hB1 H hrGauge hcenter hboot hp

end ChristodoulouBV

end
