module

public import ChristodoulouBV.C1Solution.UniquenessFinal
public import ChristodoulouBV.C1Solution.ExtractionMass
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
import ChristodoulouBV.C1Solution.ExtractionJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The off-axis transport identities in the extension proof

The fields `r` and `m` are used only in the development. Their canonical
extensions supply the differentiability needed for the mass-ratio calculation.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The points at which the paper's outgoing derivative `α′` is defined. -/
def AlphaPrimeDomain (S : Fields) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < p.2 ∧ 0 < S.lam p.1 p.2}

/-- The paper's `α′ = λ⁻¹ ∂ᵥ(α/λ)`, restricted to positive outgoing
expansion and the off-axis region. Christodoulou (1993), p. 1173. -/
noncomputable def alphaPrime (S : Fields) (p : AlphaPrimeDomain S) : ℝ :=
  deriv (fun t => S.alpha p.1.1 t / S.lam p.1.1 t) p.1.2 /
    S.lam p.1.1 p.1.2

/-- At every point of its domain, `alphaPrime` is exactly the outgoing
quotient derivative divided by the positive outgoing expansion. -/
theorem alphaPrime_eq_deriv (S : Fields) (p : AlphaPrimeDomain S) :
    alphaPrime S p =
      deriv (fun t => S.alpha p.1.1 t / S.lam p.1.1 t) p.1.2 /
        S.lam p.1.1 p.1.2 := rfl

private theorem vertical_hasDerivAt_of_closed_jet {B : ℝ}
    (hB : 0 < B) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {u v g : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B)
    (hjet : (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (0, 1) = g) :
    HasDerivAt (fun t => F (u, t)) g v := by
  let K := closedCoordTriangle 0 B
  have hqi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) (u, v) (interior_subset hqi)) hdiff
  have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hcomp : HasDerivAt (fun t => F (u, t))
      (fderiv ℝ F (u, v) (0, 1)) v := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt v hpair
  rw [hwithin] at hjet
  rwa [hjet] at hcomp

private theorem horizontal_hasDerivAt_of_closed_jet {B : ℝ}
    (hB : 0 < B) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {u v g : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B)
    (hjet : (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (1, 0) = g) :
    HasDerivAt (fun t => F (t, v)) g u := by
  let K := closedCoordTriangle 0 B
  have hqi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) (u, v) (interior_subset hqi)) hdiff
  have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun t => F (t, v))
      (fderiv ℝ F (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  rw [hwithin] at hjet
  rwa [hjet] at hcomp

/-- The displayed quotient transport equation (4.10a) at an off-axis point.
The C¹ quotient jet is extracted from the frozen incoming primitives. -/
theorem outgoing_quotient_deriv_u {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    deriv (fun s => S.alpha s v / S.lam s v) u =
      -((2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v / S.r u v) * (S.theta u v / S.lam u v) := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hjet := C1Solution.outgoingQuotient_horizontal_jet hB hBb H
    (show (u, v) ∈ closedCoordTriangle 0 B from ⟨hu.le, huv.le, hvB.le⟩)
  have hder := horizontal_hasDerivAt_of_closed_jet hB
    (C1Solution.alpha_div_lam_contDiffOn hB hBb H) hpK hjet
  have hr : S.r u v ≠ 0 :=
    ne_of_gt (H.solution.radius_pos (u, v) ⟨hu.le, huv, hv⟩)
  have hl : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v) ⟨hu.le, huv, hv⟩)
  have hg : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hpos : 0 < 1 - 2 * S.m u v / S.r u v := by
      have hgap := C1Solution.mass_gap_pos hB hBb H hu.le huv hvB.le
      have hrad := H.solution.radius_pos (u, v) ⟨hu.le, huv, hv⟩
      have heq : 1 - 2 * S.m u v / S.r u v =
          (S.r u v - 2 * S.m u v) / S.r u v := by field_simp
      rw [heq]
      exact div_pos hgap hrad
    exact ne_of_gt hpos
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    hu.le huv hvB.le
  rw [C1Solution.canonicalQuotientSource, hcoeff] at hder
  have htheta : S.phi u v - S.alpha u v / S.lam u v =
      -(S.theta u v / S.lam u v) := by
    rw [Fields.theta]
    field_simp
    ring
  have h := hder.deriv
  change deriv (fun s => S.alpha s v / S.lam s v) u = _ at h
  change deriv (fun s => S.alpha s v / S.lam s v) u =
    (2 * S.m u v / S.r u v * S.lam u v * S.nu u v /
      ((1 - 2 * S.m u v / S.r u v) * S.r u v)) *
      (S.phi u v - S.alpha u v / S.lam u v) / S.lam u v at h
  rw [htheta] at h
  convert h using 1 <;> field_simp

/-- Differentiate `μ=2m/r` in the outgoing direction using canonical C¹
mass and radius. This is the identity at p. 1173, lines 50–53. -/
theorem mass_ratio_deriv_v {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    deriv (fun t => 2 * S.m u t / S.r u t) v =
      (1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (S.r u v * S.lam u v) -
      (2 * S.m u v / S.r u v) * S.lam u v / S.r u v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hl : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hm := C1Solution.canonicalMass_vertical_hasDerivAt hB hBb H hpK
  have hmass : HasDerivAt (S.m u)
      ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (2 * S.lam u v)) v := by
    have hEq : (fun t => C1Solution.canonicalMass b S (u, t)) =ᶠ[𝓝 v] S.m u := by
      filter_upwards [Ioo_mem_nhds huv hvB] with t ht
      exact C1Solution.canonicalMass_eq_mass
        (show (u, t) ∈ developmentWithInitialEdge b from
          ⟨hu.le, ht.1, ht.2.trans hBb⟩)
    have h := hm.congr_of_eventuallyEq hEq.symm
    rw [C1Solution.canonicalMassOutgoingDensity,
      C1Solution.canonicalMassRatio_eq_mass_ratio H hpU] at h
    exact h
  have hradius := vertical_hasDerivAt_of_closed_jet hB
    (C1Solution.canonicalRadius_contDiffOn hB hBb H) hpK
    (C1Solution.canonicalRadius_vertical_jet hB hBb H
      (show (u, v) ∈ closedCoordTriangle 0 B from ⟨hu.le, huv.le, hvB.le⟩))
  have hractual : HasDerivAt (S.r u) (S.lam u v) v := by
    have hEq : (fun t => C1Solution.canonicalRadius S (u, t)) =ᶠ[𝓝 v] S.r u := by
      filter_upwards [Ioo_mem_nhds huv hvB] with t ht
      exact C1Solution.canonicalRadius_eq_radius hB hBb H hu.le ht.1 ht.2.le
    exact hradius.congr_of_eventuallyEq hEq.symm
  have hder := ((hmass.const_mul 2).div hractual hr).deriv
  convert hder using 1 <;> field_simp

/-- The outgoing quotient derivative splits into the scalar jet and the
derivative of `θ/λ`; this is the identity used at p. 1173, lines 54–57. -/
theorem alpha_ratio_deriv_v {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    deriv (fun t => S.alpha u t / S.lam u t) v =
      S.theta u v / S.r u v +
        deriv (fun t => S.theta u t / S.lam u t) v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu.le, huv.le, hvB.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hl : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hphiJet := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hBb H hpKC
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le] at hphiJet
  have hphijetval :
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (0, 1) =
      S.theta u v / S.r u v := by
    apply (eq_div_iff hr).2
    linear_combination -hphiJet
  have hphi := vertical_hasDerivAt_of_closed_jet hB
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1 hpK hphijetval
  have hratioC1 : ContDiffOn ℝ 1
      (fun q : ℝ × ℝ => S.theta q.1 q.2 / S.lam q.1 q.2)
      (closedCoordTriangle 0 B) := by
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
    exact (C1Solution.five_fields_contDiffOn hB hBb H).2.2.2.1.div
      (C1Solution.five_fields_contDiffOn hB hBb H).1
      (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))
  have hratio := vertical_hasDerivAt_of_closed_jet hB hratioC1 hpK
    (g := (fderivWithin ℝ
      (fun q : ℝ × ℝ => S.theta q.1 q.2 / S.lam q.1 q.2)
      (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hEq : (fun t => S.alpha u t / S.lam u t) =ᶠ[𝓝 v]
      (fun t => S.phi u t + S.theta u t / S.lam u t) := by
    filter_upwards [Ioo_mem_nhds huv hvB] with t ht
    have htU : (u, t) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, ht.1, ht.2.trans hBb⟩
    have hlt : S.lam u t ≠ 0 := ne_of_gt (H.solution.lam_pos (u, t) htU)
    rw [Fields.theta]
    field_simp
    ring
  have hder := (hphi.add hratio).congr_of_eventuallyEq hEq
  have hderivTheta := hratio.deriv
  have hresult := hder.deriv
  rw [← hderivTheta] at hresult
  exact hresult

private theorem mixed_partial_of_c1_horizontal_source {B : ℝ}
    (hB : 0 < B) {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle 0 B))
    (hsource : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun s => deriv (fun t => F (s, t)) v)
      (deriv (fun t => G (u, t)) v) u := by
  obtain ⟨hu, huv, hv⟩ := hp
  let a := u / 2
  let a' := (u + v) / 2
  let c := (u + 3 * v) / 4
  let d := (v + B) / 2
  have hau : a < u := by dsimp [a]; linarith
  have hua' : u < a' := by dsimp [a']; linarith
  have ha'c : a' < c := by dsimp [a', c]; linarith
  have hcv : c < v := by dsimp [c]; linarith
  have hvd : v < d := by dsimp [d]; linarith
  have hdB : d < B := by dsimp [d]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have haa' : a < a' := hau.trans hua'
  have hcd : c < d := hcv.trans hvd
  let K := closedCoordTriangle 0 B
  let R := Icc a a' ×ˢ Icc c d
  have hmap (p : ℝ × ℝ) (hpR : p ∈ R) : p ∈ openCoordTriangle 0 B := by
    change p.1 ∈ Icc a a' ∧ p.2 ∈ Icc c d at hpR
    exact ⟨ha.trans_le hpR.1.1, (hpR.1.2.trans_lt ha'c).trans_le hpR.2.1,
      hpR.2.2.trans_lt hdB⟩
  have hsub : R ⊆ K := fun p hpR =>
    let h := hmap p hpR
    ⟨h.1.le, h.2.1.le, h.2.2.le⟩
  let Fv : ℝ → ℝ → ℝ := fun x y =>
    (fderivWithin ℝ F K (x, y)) (0, 1)
  let Gv : ℝ → ℝ → ℝ := fun x y =>
    (fderivWithin ℝ G K (x, y)) (0, 1)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hFvC : ContinuousOn (fun p : ℝ × ℝ => Fv p.1 p.2) R :=
    ((hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hsub
  have hGvC : ContinuousOn (fun p : ℝ × ℝ => Gv p.1 p.2) R :=
    ((hG.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hsub
  have hFC : ContinuousOn F R :=
    hF.continuousOn.mono hsub
  have hGC : ContinuousOn G R :=
    hG.continuousOn.mono hsub
  have hFvDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => F (x, t)) (Fv x y) y := by
    exact vertical_hasDerivAt_of_closed_jet hB hF
      (hmap (x, y) ⟨hx, hy⟩) rfl
  have hGvDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => G (x, t)) (Gv x y) y := by
    exact vertical_hasDerivAt_of_closed_jet hB hG
      (hmap (x, y) ⟨hx, hy⟩) rfl
  have hGuDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => F (t, y)) (G (x, y)) x :=
    horizontal_hasDerivAt_of_closed_jet hB hF
      (hmap (x, y) ⟨hx, hy⟩)
      (hsource (x, y) (hsub ⟨hx, hy⟩))
  have hmixed := (hasDerivWithinAt_vertical_partial_of_horizontal_partial
    haa' hcd hFC hFvC hGC hGvC
    (fun x hx y hy => (hFvDeriv x hx y hy).hasDerivWithinAt)
    (fun x hx y hy => (hGuDeriv x hx y hy).hasDerivWithinAt)
    (fun x hx y hy => (hGvDeriv x hx y hy).hasDerivWithinAt)).2.2 u
    (show u ∈ Icc a a' from ⟨hau.le, hua'.le⟩)
    v
    (show v ∈ Icc c d from ⟨hcv.le, hvd.le⟩)
  have hmixedAt : HasDerivAt (fun x => Fv x v) (Gv u v) u :=
    hmixed.hasDerivAt (Icc_mem_nhds hau hua')
  have hEq : (fun x => deriv (fun t => F (x, t)) v) =ᶠ[𝓝 u]
      (fun x => Fv x v) := by
    filter_upwards [Ioo_mem_nhds hau hua'] with x hx
    exact (hFvDeriv x ⟨hx.1.le, hx.2.le⟩ v ⟨hcv.le, hvd.le⟩).deriv
  have hGv : Gv u v = deriv (fun t => G (u, t)) v :=
    (hGvDeriv u ⟨hau.le, hua'.le⟩ v ⟨hcv.le, hvd.le⟩).deriv.symm
  rw [hGv] at hmixedAt
  exact hmixedAt.congr_of_eventuallyEq hEq

/-- The mixed-partial bridge for `F=α/λ`: C¹ regularity of its incoming
source supplies the derivative of its outgoing derivative, with no C² premise.
This is the calculus step between (4.10a) and (5.2). -/
theorem alpha_ratio_mixed_partial_bridge {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt
      (fun s => deriv (fun t => S.alpha s t / S.lam s t) v)
      (deriv (fun t => C1Solution.canonicalQuotientSource b S (u, t)) v) u := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  exact mixed_partial_of_c1_horizontal_source hB
    (C1Solution.alpha_div_lam_contDiffOn hB hBb H)
    (C1Solution.canonicalQuotientSource_contDiffOn hB hBb H)
    (fun p hpK => C1Solution.outgoingQuotient_horizontal_jet hB hBb H hpK)
    ⟨hu, huv, hvB⟩

/-- The unrestricted formula used only as a local coordinate expression for
the subtype-valued `alphaPrime`. Its derivative is taken on an off-axis
neighborhood where this formula agrees with the source definition. -/
private noncomputable def alphaPrimeFormula (S : Fields) (u v : ℝ) : ℝ :=
  deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v

private theorem alphaPrime_eq_formula (S : Fields)
    (p : AlphaPrimeDomain S) :
    alphaPrime S p = alphaPrimeFormula S p.1.1 p.1.2 := rfl

private theorem offaxis_transport_jets {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun t => S.r u t) (S.lam u v) v ∧
    HasDerivAt (fun s => S.lam s v)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u ∧
    HasDerivAt (fun t => S.nu u t)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v ∧
    HasDerivAt (fun t => 2 * S.m u t / S.r u t)
      ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (S.r u v * S.lam u v) -
       (2 * S.m u v / S.r u v) * S.lam u v / S.r u v) v ∧
    HasDerivAt (fun t => S.theta u t / S.lam u t)
      (S.lam u v * alphaPrimeFormula S u v - S.theta u v / S.r u v) v := by
  have hp0 := hp
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu.le, huv.le, hvB.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hl : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hradiusCanon := vertical_hasDerivAt_of_closed_jet hB
    (C1Solution.canonicalRadius_contDiffOn hB hBb H) hpK
    (C1Solution.canonicalRadius_vertical_jet hB hBb H hpKC)
  have hradius : HasDerivAt (fun t => S.r u t) (S.lam u v) v := by
    have hEq : (fun t => S.r u t) =ᶠ[𝓝 v]
        (fun t => C1Solution.canonicalRadius S (u, t)) := by
      filter_upwards [Ioo_mem_nhds huv hvB] with t ht
      exact (C1Solution.canonicalRadius_eq_radius hB hBb H hu.le ht.1 ht.2.le).symm
    exact hradiusCanon.congr_of_eventuallyEq hEq
  have hfour := C1Solution.four_mixed_coordinate_jets hB hBb H hpKC
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    hu.le huv hvB.le
  have hlam : HasDerivAt (fun s => S.lam s v)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u := by
    convert horizontal_hasDerivAt_of_closed_jet hB
      (C1Solution.five_fields_contDiffOn hB hBb H).1 hpK hfour.1 using 1
    exact hcoeff.symm
  have hnu : HasDerivAt (fun t => S.nu u t)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v := by
    convert vertical_hasDerivAt_of_closed_jet hB
      (C1Solution.five_fields_contDiffOn hB hBb H).2.1 hpK hfour.2.1 using 1
    exact hcoeff.symm
  have hmassCanon := vertical_hasDerivAt_of_closed_jet hB
    (C1Solution.canonicalMassRatio_contDiffOn hB hBb H) hpK
    (g := (fderivWithin ℝ (C1Solution.canonicalMassRatio b S)
      (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hmassDiff : DifferentiableAt ℝ
      (fun t => 2 * S.m u t / S.r u t) v := by
    have hEq : (fun t => 2 * S.m u t / S.r u t) =ᶠ[𝓝 v]
        (fun t => C1Solution.canonicalMassRatio b S (u, t)) := by
      filter_upwards [Ioo_mem_nhds huv hvB] with t ht
      exact (C1Solution.canonicalMassRatio_eq_mass_ratio H
        (show (u, t) ∈ developmentWithInitialEdge b from
          ⟨hu.le, ht.1, ht.2.trans hBb⟩)).symm
    exact (hmassCanon.congr_of_eventuallyEq hEq).differentiableAt
  have hmass := hmassDiff.hasDerivAt
  rw [mass_ratio_deriv_v H hp0] at hmass
  have hθratioC1 : ContDiffOn ℝ 1
      (fun q : ℝ × ℝ => S.theta q.1 q.2 / S.lam q.1 q.2)
      (closedCoordTriangle 0 B) := by
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hBb H
    exact (C1Solution.five_fields_contDiffOn hB hBb H).2.2.2.1.div
      (C1Solution.five_fields_contDiffOn hB hBb H).1
      (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))
  have hθratio := vertical_hasDerivAt_of_closed_jet hB hθratioC1 hpK
    (g := (fderivWithin ℝ
      (fun q : ℝ × ℝ => S.theta q.1 q.2 / S.lam q.1 q.2)
      (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hthetaDeriv := alpha_ratio_deriv_v H hp0
  have hθval : deriv (fun t => S.theta u t / S.lam u t) v =
      S.lam u v * alphaPrimeFormula S u v - S.theta u v / S.r u v := by
    dsimp [alphaPrimeFormula]
    rw [hthetaDeriv]
    field_simp
    ring
  have hθratio' := hθratio.differentiableAt.hasDerivAt
  rw [hθval] at hθratio'
  exact ⟨hradius, hlam, hnu, hmass, hθratio'⟩

private theorem quotientSource_eq_offaxis {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    C1Solution.canonicalQuotientSource b S (u, v) =
      -((2 * S.m u v / S.r u v) /
          (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v / S.r u v) *
        (S.theta u v / S.lam u v) := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hl : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hg : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hgap := C1Solution.mass_gap_pos hB hBb H hu.le huv hvB.le
    have hrad := H.solution.radius_pos (u, v) hpU
    have heq : 1 - 2 * S.m u v / S.r u v =
        (S.r u v - 2 * S.m u v) / S.r u v := by field_simp
    rw [heq]
    exact ne_of_gt (div_pos hgap hrad)
  rw [C1Solution.canonicalQuotientSource,
    C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H hu.le huv hvB.le,
    C1Solution.outgoingQuotient, Fields.theta]
  field_simp
  ring

/-- Equation (5.2) for the local coordinate expression of `α′`. The
subtype-valued `alphaPrime` agrees with this expression throughout the
off-axis neighborhood used to take the derivative. -/
theorem alphaPrime_deriv_u {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    deriv (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v) u =
      -2 * (S.nu u v / S.r u v) *
        ((2 * S.m u v / S.r u v) /
          (1 - 2 * S.m u v / S.r u v)) *
          (deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v) +
      3 * (S.nu u v / (S.r u v)^2) *
        ((2 * S.m u v / S.r u v) /
          (1 - 2 * S.m u v / S.r u v)) *
        (S.theta u v / S.lam u v) -
      (S.nu u v / (S.r u v)^2) *
        (1 / (1 - 2 * S.m u v / S.r u v)) *
        (S.theta u v / S.lam u v)^3 := by
  have hp0 := hp
  obtain ⟨⟨hu, hub⟩, ⟨huv, hv⟩⟩ := hp
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hl : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hg : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hgap := C1Solution.mass_gap_pos hB hBb H hu.le huv hvB.le
    have hrad := H.solution.radius_pos (u, v) hpU
    have heq : 1 - 2 * S.m u v / S.r u v =
        (S.r u v - 2 * S.m u v) / S.r u v := by field_simp
    rw [heq]
    exact ne_of_gt (div_pos hgap hrad)
  obtain ⟨hradius, hlam, hnu, hmass, htheta⟩ := offaxis_transport_jets H hp0
  have hgapDer : HasDerivAt
      (fun t => 1 - 2 * S.m u t / S.r u t)
      (-((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
          (S.r u v * S.lam u v) -
        (2 * S.m u v / S.r u v) * S.lam u v / S.r u v)) v := by
    convert (hasDerivAt_const v (1 : ℝ)).sub hmass using 1 <;> ring
  have hmuFrac := hmass.div hgapDer hg
  have hnuFrac := hnu.div hradius hr
  have hsourceRHS := ((hmuFrac.mul hnuFrac).mul htheta).neg
  have hsource := hsourceRHS.congr_of_eventuallyEq
    (by
      filter_upwards [Ioo_mem_nhds huv hv] with t ht
      simp only [Pi.neg_apply, Pi.mul_apply, Pi.div_apply]
      convert quotientSource_eq_offaxis H
        (show (u, t) ∈ openDevelopment 0 b from ⟨⟨hu, hub⟩, ⟨ht.1, ht.2⟩⟩)
        using 1 <;> ring)
  have hbridge := alpha_ratio_mixed_partial_bridge H hp0
  have hsourceVal := hsource.deriv
  rw [hsourceVal] at hbridge
  have hprime := hbridge.div hlam hl
  have hprimeVal := hprime.deriv
  change deriv (fun s => alphaPrimeFormula S s v) u = _ at hprimeVal
  dsimp [alphaPrimeFormula] at hprimeVal
  have hgapR : S.r u v - 2 * S.m u v ≠ 0 :=
    ne_of_gt (C1Solution.mass_gap_pos hB hBb H hu.le huv hvB.le)
  convert hprimeVal using 1 <;> field_simp [hr, hl, hg, hgapR] <;> ring

/-- A continuous closed-triangle representative of the incoming derivative
of `α′`. This form supplies integrability on every actual incoming segment. -/
theorem alphaPrime_deriv_u_eq_closed_jet {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    deriv (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v) u =
      (((fderivWithin ℝ (C1Solution.canonicalQuotientSource b S)
          (closedCoordTriangle 0 B) (u, v)) (0, 1)) * S.lam u v -
        ((fderivWithin ℝ (C1Solution.outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, v)) (0, 1)) *
          C1Solution.canonicalMixedCoefficient b S (u, v)) /
        (S.lam u v)^2 := by
  have hp0 := hp
  obtain ⟨hu, huv, hv⟩ := hp
  have hpU : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, huv.trans (hv.trans hBb)⟩, ⟨huv, hv.trans hBb⟩⟩
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hu.le, huv.le, hv.le⟩
  have hl : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v)
      ⟨hu.le, huv, hv.trans hBb⟩)
  have hF := vertical_hasDerivAt_of_closed_jet hB
    (C1Solution.alpha_div_lam_contDiffOn hB hBb H) hp0
    (g := (fderivWithin ℝ (C1Solution.outgoingQuotient S)
      (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hG := vertical_hasDerivAt_of_closed_jet hB
    (C1Solution.canonicalQuotientSource_contDiffOn hB hBb H) hp0
    (g := (fderivWithin ℝ (C1Solution.canonicalQuotientSource b S)
      (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hbridge := alpha_ratio_mixed_partial_bridge H hpU
  rw [hG.deriv] at hbridge
  have hLam := horizontal_hasDerivAt_of_closed_jet hB
    (C1Solution.five_fields_contDiffOn hB hBb H).1 hp0
    (C1Solution.four_mixed_coordinate_jets hB hBb H hpK).1
  have hPrime := hbridge.div hLam hl
  have hFval := hF.deriv
  have hPrimeVal := hPrime.deriv
  rw [hFval] at hPrimeVal
  convert hPrimeVal using 1

/-- Equation (5.2) as a `HasDerivAt` statement, for integration along an
incoming closed segment. -/
theorem alphaPrime_hasDerivAt_u {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt
      (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v)
      (-2 * (S.nu u v / S.r u v) *
        ((2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v)) *
          (deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v) +
       3 * (S.nu u v / (S.r u v)^2) *
        ((2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v)) *
          (S.theta u v / S.lam u v) -
       (S.nu u v / (S.r u v)^2) *
        (1 / (1 - 2 * S.m u v / S.r u v)) *
          (S.theta u v / S.lam u v)^3) u := by
  have hp0 := hp
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hu.le, huv.le, hvB.le⟩
  have hl : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v)
      ⟨hu.le, huv, hv⟩)
  have hjet := (C1Solution.four_mixed_coordinate_jets hB hBb H hpK).1
  have hlam := horizontal_hasDerivAt_of_closed_jet hB
    (C1Solution.five_fields_contDiffOn hB hBb H).1
    (show (u, v) ∈ openCoordTriangle 0 B from ⟨hu, huv, hvB⟩) hjet
  have hprime := (alpha_ratio_mixed_partial_bridge H hp0).div hlam hl
  have hderiv := hprime.differentiableAt.hasDerivAt
  change HasDerivAt
    (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v)
    (deriv (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v) u) u
      at hderiv
  rw [alphaPrime_deriv_u H hp0] at hderiv
  exact hderiv

end ChristodoulouBV.Uniqueness

end
