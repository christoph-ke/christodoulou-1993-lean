module

public import ChristodoulouBV.AreaEstimates.GaugeAxis
public import ChristodoulouBV.AreaEstimates.FieldTransportJacobian
import ChristodoulouBV.C1Solution.FrozenBridge
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Mixed derivatives for the Section 4 field transports

The frozen C¹ condition supplies first derivatives only. The characteristic
equations give C¹ transport densities in the strict triangle, allowing the
mixed derivatives used in (4.4) and (4.5) to be recovered locally.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The map whose analytic Jacobian gives the outgoing `(λ, φ)` area. -/
@[expose] def sourceLamPhiMap (S : Fields) (p : ℝ × ℝ) : ℝ × ℝ :=
  (S.lam p.1 p.2, S.phi p.1 p.2)

/-- The map whose analytic Jacobian gives the incoming `(ν, φ)` area. -/
@[expose] def sourceNuPhiMap (S : Fields) (p : ℝ × ℝ) : ℝ × ℝ :=
  (S.nu p.1 p.2, S.phi p.1 p.2)

/-- The `(λ, φ)` map is C¹ on the closed unit triangle. -/
theorem sourceLamPhiMap_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (sourceLamPhiMap S) (closedCoordTriangle 0 1) := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hLam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.lam_c1
  have hPhi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  exact hLam.prodMk hPhi

/-- The `(ν, φ)` map is C¹ on the closed unit triangle. -/
theorem sourceNuPhiMap_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (sourceNuPhiMap S) (closedCoordTriangle 0 1) := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hNu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.nu_c1
  have hPhi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  exact hNu.prodMk hPhi

/-- Differentiate the vertical initial edge using the closed-triangle
Fréchet derivative, including its one-sided boundary point. -/
theorem vertical_edge_hasDerivAt {B : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) B) :
    HasDerivAt (fun t => F (0, t))
      ((fderivWithin ℝ F (closedCoordTriangle 0 B) (0, v)) (0, 1)) v := by
  let K := closedCoordTriangle 0 B
  have hpK : (0, v) ∈ K := ⟨le_refl _, hv.1.le, hv.2.le⟩
  have hdiff : DifferentiableWithinAt ℝ F K (0, v) :=
    hF.differentiableOn (by norm_num) (0, v) hpK
  have hpair : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) v :=
    (hasDerivAt_const v 0).prodMk (hasDerivAt_id' v)
  have hnear : ∀ᶠ t in 𝓝 v, (0, t) ∈ K := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
    exact ⟨le_refl _, ht.1.le, ht.2.le⟩
  simpa only [Function.comp_def] using
    hdiff.hasFDerivWithinAt.comp_hasDerivAt v hpair hnear

/-- The four commuted mixed derivatives at a strict point of the normalized
unit development. These are the pointwise form of `mixed_regularities`. -/
theorem s4_mixed_partial_at {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    let g := C1Solution.canonicalMixedCoefficient 1 S
    HasDerivAt
      (fun x => (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (x, v)) (0, 1))
      ((fderiv ℝ g (u, v)) (0, 1)) u ∧
    HasDerivAt
      (fun y => (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, y)) (1, 0))
      ((fderiv ℝ g (u, v)) (1, 0)) v ∧
    HasDerivAt
      (fun x => (fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2) (x, v)) (0, 1))
      ((fderiv ℝ (fun p => g p * S.phi p.1 p.2) (u, v)) (0, 1)) u ∧
    HasDerivAt
      (fun y => (fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, y)) (1, 0))
      ((fderiv ℝ (fun p => g p * S.phi p.1 p.2) (u, v)) (1, 0)) v := by
  let B : ℝ := (v + 1) / 2
  let a : ℝ := u / 2
  let a' : ℝ := (2 * u + v) / 3
  let d : ℝ := (u + 2 * v) / 3
  let d' : ℝ := (v + B) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have haa' : a < a' := by dsimp [a, a']; linarith
  have hdd' : d < d' := by dsimp [d, d', B]; linarith
  have haU : a < u := by dsimp [a]; linarith
  have hUa' : u < a' := by dsimp [a']; linarith
  have hdV : d < v := by dsimp [d]; linarith
  have hVd' : v < d' := by dsimp [d', B]; linarith
  have hApos : 0 < a := by dsimp [a]; linarith
  have ha'd : a' < d := by dsimp [a', d]; linarith
  have hd'B : d' < B := by dsimp [d', B]; linarith
  have hR : Icc a a' ×ˢ Icc d d' ⊆ openCoordTriangle 0 B := by
    intro p hp
    change p.1 ∈ Icc a a' ∧ p.2 ∈ Icc d d' at hp
    exact ⟨hApos.trans_le hp.1.1,
      (hp.1.2.trans_lt ha'd).trans_le hp.2.1,
      hp.2.2.trans_lt hd'B⟩
  have huI : u ∈ Icc a a' := ⟨haU.le, hUa'.le⟩
  have hvI : v ∈ Icc d d' := ⟨hdV.le, hVd'.le⟩
  obtain ⟨hLam, hNu, hAlpha, hBeta⟩ :=
    mixed_regularities hB hBb H haa' hdd' hR huI hvI
  exact ⟨hLam.hasDerivAt (Icc_mem_nhds haU hUa'),
    hNu.hasDerivAt (Icc_mem_nhds hdV hVd'),
    hAlpha.hasDerivAt (Icc_mem_nhds haU hUa'),
    hBeta.hasDerivAt (Icc_mem_nhds hdV hVd')⟩

/-- The incoming residual `βᵤ − νᵤφ` has vertical derivative equal to the
negative Jacobian of `(ν, φ)`. This is the differentiated identity preceding
(4.5a), including the `β` transport equation. -/
theorem eq4_beta_jacobian {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    HasDerivAt
      (fun y =>
        (fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, y)) (1, 0) -
          (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, y)) (1, 0) * S.phi u y)
      (-(fderiv ℝ (fun p : ℝ × ℝ => (S.nu p.1 p.2, S.phi p.1 p.2))
        (u, v)).det) v := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let T := openCoordTriangle 0 B
  let g := C1Solution.canonicalMixedCoefficient 1 S
  let nu : ℝ × ℝ → ℝ := fun p => S.nu p.1 p.2
  let phi : ℝ × ℝ → ℝ := fun p => S.phi p.1 p.2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpT : (u, v) ∈ T := ⟨hu, huv, hvB⟩
  have hpK : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hpInt : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hpT
  have hnhds : K ∈ 𝓝 (u, v) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  have hGdiff : DifferentiableAt ℝ g (u, v) :=
    ((mixed_coefficient_contDiffOn hB hBb H).differentiableOn
      (by norm_num) (u, v) hpT).differentiableAt
        (by simpa only [K, interior_closedCoordTriangle] using
          isOpen_interior.mem_nhds hpInt)
  obtain ⟨_, hNuK, hPhiK, _, _⟩ := C1Solution.five_fields_contDiffOn hB hBb H
  have hNudiff : DifferentiableAt ℝ nu (u, v) :=
    ((hNuK.differentiableOn (by norm_num) (u, v) hpK).differentiableAt
      hnhds)
  have hPhidiff : DifferentiableAt ℝ phi (u, v) :=
    ((hPhiK.differentiableOn (by norm_num) (u, v) hpK).differentiableAt
      hnhds)
  have hPhiV : HasDerivAt (fun y => phi (u, y))
      ((fderiv ℝ phi (u, v)) (0, 1)) v := by
    have hpair : HasDerivAt (fun y : ℝ => (u, y)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    simpa only [Function.comp_def] using
      hPhidiff.hasFDerivAt.comp_hasDerivAt v hpair
  have hProdJet :
      (fderiv ℝ (fun p => g p * phi p) (u, v)) (1, 0) =
        (fderiv ℝ g (u, v)) (1, 0) * phi (u, v) +
          g (u, v) * (fderiv ℝ phi (u, v)) (1, 0) := by
    change (fderiv ℝ (g * phi) (u, v)) (1, 0) = _
    rw [fderiv_mul hGdiff hPhidiff]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    ring
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hNuV : (fderiv ℝ nu (u, v)) (0, 1) = g (u, v) := by
    have hjet := ((mixed_coordinate_jets hB hBb H).2 (u, v) hpT).2.1
    rw [fderivWithin_eq_fderiv (hUnique (u, v) hpK) hNudiff] at hjet
    exact hjet
  have hDet := det_fderiv_prodMk hNudiff hPhidiff
  have hM := s4_mixed_partial_at H hu huv hv
  have hRes := hM.2.2.2.sub (hM.2.1.mul hPhiV)
  have hCoeff : -(fderiv ℝ (sourceNuPhiMap S) (u, v)).det =
      (fderiv ℝ (fun p => g p * phi p) (u, v)) (1, 0) -
        ((fderiv ℝ g (u, v)) (1, 0) * phi (u, v) +
          (fderiv ℝ nu (u, v)) (1, 0) * (fderiv ℝ phi (u, v)) (0, 1)) := by
    change -(fderiv ℝ (fun q => (nu q, phi q)) (u, v)).det = _
    rw [hProdJet, hDet, hNuV]
    ring
  have hRes' := hRes
  rw [← hCoeff] at hRes'
  convert hRes' using 1 <;> rfl

/-- The outgoing residual `αᵥ − λᵥφ` has horizontal derivative equal to the
Jacobian of `(λ, φ)`. -/
theorem eq4_alpha_jacobian {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    HasDerivAt
      (fun x =>
        (fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2) (x, v)) (0, 1) -
          (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (x, v)) (0, 1) * S.phi x v)
      ((fderiv ℝ (fun p : ℝ × ℝ => (S.lam p.1 p.2, S.phi p.1 p.2))
        (u, v)).det) u := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let T := openCoordTriangle 0 B
  let g := C1Solution.canonicalMixedCoefficient 1 S
  let lam : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let phi : ℝ × ℝ → ℝ := fun p => S.phi p.1 p.2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpT : (u, v) ∈ T := ⟨hu, huv, hvB⟩
  have hpK : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hpInt : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hpT
  have hnhds : K ∈ 𝓝 (u, v) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  have hGdiff : DifferentiableAt ℝ g (u, v) :=
    ((mixed_coefficient_contDiffOn hB hBb H).differentiableOn
      (by norm_num) (u, v) hpT).differentiableAt
        (by simpa only [K, interior_closedCoordTriangle] using
          isOpen_interior.mem_nhds hpInt)
  obtain ⟨hLamK, _, hPhiK, _, _⟩ := C1Solution.five_fields_contDiffOn hB hBb H
  have hLamdiff : DifferentiableAt ℝ lam (u, v) :=
    ((hLamK.differentiableOn (by norm_num) (u, v) hpK).differentiableAt
      hnhds)
  have hPhidiff : DifferentiableAt ℝ phi (u, v) :=
    ((hPhiK.differentiableOn (by norm_num) (u, v) hpK).differentiableAt
      hnhds)
  have hPhiU : HasDerivAt (fun x => phi (x, v))
      ((fderiv ℝ phi (u, v)) (1, 0)) u := by
    have hpair : HasDerivAt (fun x : ℝ => (x, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    simpa only [Function.comp_def] using
      hPhidiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hProdJet :
      (fderiv ℝ (fun p => g p * phi p) (u, v)) (0, 1) =
        (fderiv ℝ g (u, v)) (0, 1) * phi (u, v) +
          g (u, v) * (fderiv ℝ phi (u, v)) (0, 1) := by
    change (fderiv ℝ (g * phi) (u, v)) (0, 1) = _
    rw [fderiv_mul hGdiff hPhidiff]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    ring
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hLamU : (fderiv ℝ lam (u, v)) (1, 0) = g (u, v) := by
    have hjet := ((mixed_coordinate_jets hB hBb H).2 (u, v) hpT).1
    rw [fderivWithin_eq_fderiv (hUnique (u, v) hpK) hLamdiff] at hjet
    exact hjet
  have hDet := det_fderiv_prodMk hLamdiff hPhidiff
  have hM := s4_mixed_partial_at H hu huv hv
  have hRes := hM.2.2.1.sub (hM.1.mul hPhiU)
  have hCoeff : (fderiv ℝ (sourceLamPhiMap S) (u, v)).det =
      (fderiv ℝ (fun p => g p * phi p) (u, v)) (0, 1) -
        ((fderiv ℝ g (u, v)) (0, 1) * phi (u, v) +
          (fderiv ℝ lam (u, v)) (0, 1) * (fderiv ℝ phi (u, v)) (1, 0)) := by
    change (fderiv ℝ (fun q => (lam q, phi q)) (u, v)).det = _
    rw [hProdJet, hDet, hLamU]
    ring
  have hRes' := hRes
  rw [← hCoeff] at hRes'
  convert hRes' using 1 <;> rfl

/-- Equation (4.4a): the outgoing residual is bounded by its initial-edge
value and the absolute `(λ, φ)` Jacobian on the preceding horizontal segment. -/
theorem eq4_4a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ENNReal.ofReal
      |deriv (S.alpha u) v - deriv (S.lam u) v * S.phi u v| ≤
      ENNReal.ofReal
        |deriv (S.alpha 0) v - deriv (S.lam 0) v * S.phi 0 v| +
      ∫⁻ x in Ioo 0 u,
        ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (x, v)).det| := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let alpha : ℝ × ℝ → ℝ := fun p => S.alpha p.1 p.2
  let lam : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let phi : ℝ × ℝ → ℝ := fun p => S.phi p.1 p.2
  let alphaV : ℝ → ℝ := fun x => (fderivWithin ℝ alpha K (x, v)) (0, 1)
  let lamV : ℝ → ℝ := fun x => (fderivWithin ℝ lam K (x, v)) (0, 1)
  let lamU : ℝ → ℝ := fun x => (fderivWithin ℝ lam K (x, v)) (1, 0)
  let phiV : ℝ → ℝ := fun x => (fderivWithin ℝ phi K (x, v)) (0, 1)
  let phiU : ℝ → ℝ := fun x => (fderivWithin ℝ phi K (x, v)) (1, 0)
  let R : ℝ → ℝ := fun x => alphaV x - lamV x * phi (x, v)
  let J : ℝ → ℝ := fun x => lamU x * phiV x - lamV x * phiU x
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hvPos : 0 < v := hu.trans huv
  have hmap : MapsTo (fun x : ℝ => (x, v)) (Icc 0 u) K := by
    intro x hx
    exact ⟨hx.1, hx.2.trans huv.le, hvB.le⟩
  obtain ⟨hLamK, _, hPhiK, _, _⟩ := C1Solution.five_fields_contDiffOn hB hBb H
  have hAlphaK := C1Solution.alpha_contDiffOn hB hBb H
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hLine : Continuous (fun x : ℝ => (x, v)) :=
    continuous_id.prodMk continuous_const
  have hJetCont {f : ℝ × ℝ → ℝ}
      (hf : ContDiffOn ℝ 1 f K) (e : ℝ × ℝ) :
      ContinuousOn (fun x => (fderivWithin ℝ f K (x, v)) e) (Icc 0 u) := by
    have hC : ContinuousOn (fun p => (fderivWithin ℝ f K p) e) K :=
      ((hf.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply
        continuousOn_const)
    exact hC.comp hLine.continuousOn hmap
  have hPhiLine : ContinuousOn (fun x => phi (x, v)) (Icc 0 u) :=
    hPhiK.continuousOn.comp hLine.continuousOn hmap
  have hRCont : ContinuousOn R (Icc 0 u) :=
    (hJetCont hAlphaK (0, 1)).sub
      ((hJetCont hLamK (0, 1)).mul hPhiLine)
  have hJCont : ContinuousOn J (Icc 0 u) :=
    ((hJetCont hLamK (1, 0)).mul (hJetCont hPhiK (0, 1))).sub
      ((hJetCont hLamK (0, 1)).mul (hJetCont hPhiK (1, 0)))
  have hJetEq (x : ℝ) (hx : 0 < x ∧ x ≤ u) :
      R x = (fderiv ℝ alpha (x, v)) (0, 1) -
        (fderiv ℝ lam (x, v)) (0, 1) * phi (x, v) ∧
      J x = (fderiv ℝ (sourceLamPhiMap S) (x, v)).det := by
    have hxv : x < v := hx.2.trans_lt huv
    have hpK : (x, v) ∈ K := ⟨hx.1.le, hxv.le, hvB.le⟩
    have hpInt : (x, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨hx.1, hxv, hvB⟩
    have hnhds : K ∈ 𝓝 (x, v) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
    have hAlphaDiff : DifferentiableAt ℝ alpha (x, v) :=
      (hAlphaK.differentiableOn (by norm_num) (x, v) hpK).differentiableAt hnhds
    have hLamDiff : DifferentiableAt ℝ lam (x, v) :=
      (hLamK.differentiableOn (by norm_num) (x, v) hpK).differentiableAt hnhds
    have hPhiDiff : DifferentiableAt ℝ phi (x, v) :=
      (hPhiK.differentiableOn (by norm_num) (x, v) hpK).differentiableAt hnhds
    have haEq := fderivWithin_eq_fderiv (hUnique (x, v) hpK) hAlphaDiff
    have hlEq := fderivWithin_eq_fderiv (hUnique (x, v) hpK) hLamDiff
    have hpEq := fderivWithin_eq_fderiv (hUnique (x, v) hpK) hPhiDiff
    constructor
    · simp only [R, alphaV, lamV, haEq, hlEq]
    · simp only [J, lamU, lamV, phiV, phiU, hlEq, hpEq]
      exact (det_fderiv_prodMk hLamDiff hPhiDiff).symm
  have hRDeriv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) u) :
      HasDerivAt R (J x) x := by
    have hEq : R =ᶠ[𝓝 x] (fun y =>
        (fderiv ℝ alpha (y, v)) (0, 1) -
          (fderiv ℝ lam (y, v)) (0, 1) * phi (y, v)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact (hJetEq y ⟨hy.1, hy.2.le⟩).1
    have hDeriv := eq4_alpha_jacobian H
      hx.1 (hx.2.trans huv) hv
    have hJx := (hJetEq x ⟨hx.1, hx.2.le⟩).2
    rw [hJx]
    exact hDeriv.congr_of_eventuallyEq hEq
  have hBound := ofReal_abs_endpoint_le_initial_add_lintegral
    hu.le hRCont hJCont hRDeriv
  have hRu := (hJetEq u ⟨hu, le_rfl⟩).1
  have hRu' : R u = deriv (S.alpha u) v -
      deriv (S.lam u) v * S.phi u v := by
    rw [hRu]
    have hpInt : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu, huv, hvB⟩
    have hnhds : K ∈ 𝓝 (u, v) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
    have hαDiff : DifferentiableAt ℝ alpha (u, v) :=
      (hAlphaK.differentiableOn (by norm_num) (u, v)
        ⟨hu.le, huv.le, hvB.le⟩).differentiableAt hnhds
    have hLamDiff : DifferentiableAt ℝ lam (u, v) :=
      (hLamK.differentiableOn (by norm_num) (u, v)
        ⟨hu.le, huv.le, hvB.le⟩).differentiableAt hnhds
    have hαPair : HasDerivAt (fun t => alpha (u, t))
        ((fderiv ℝ alpha (u, v)) (0, 1)) v := by
      have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
        (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
      simpa only [Function.comp_def] using
        hαDiff.hasFDerivAt.comp_hasDerivAt v hpair
    have hLamPair : HasDerivAt (fun t => lam (u, t))
        ((fderiv ℝ lam (u, v)) (0, 1)) v := by
      have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
        (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
      simpa only [Function.comp_def] using
        hLamDiff.hasFDerivAt.comp_hasDerivAt v hpair
    rw [← hαPair.deriv, ← hLamPair.deriv]
  have hR0 : R 0 = deriv (S.alpha 0) v -
      deriv (S.lam 0) v * S.phi 0 v := by
    have hvI : v ∈ Ioo (0 : ℝ) B := ⟨hvPos, hvB⟩
    have hα := (vertical_edge_hasDerivAt hAlphaK hvI).deriv
    have hLamEdge := (vertical_edge_hasDerivAt hLamK hvI).deriv
    have hα' : deriv (S.alpha 0) v = alphaV 0 := by
      simpa only [alphaV, alpha, K] using hα
    have hLamEdge' : deriv (S.lam 0) v = lamV 0 := by
      simpa only [lamV, lam, K] using hLamEdge
    rw [hα', hLamEdge']
  have hJIntegral :
      (∫⁻ x in Ioo 0 u, ENNReal.ofReal |J x|) =
        ∫⁻ x in Ioo 0 u,
          ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (x, v)).det| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [(hJetEq x ⟨hx.1, hx.2.le⟩).2]
  simpa only [hRu', hR0, hJIntegral] using hBound

end ChristodoulouBV

end
