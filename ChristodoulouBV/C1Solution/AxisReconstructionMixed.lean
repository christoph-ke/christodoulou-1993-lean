module

public import ChristodoulouBV.C1Solution.AxisReconstructionMass
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Off-axis mixed mass regularity

On any closed rectangle strictly inside the open axis triangle, the
continuous first jet of the outgoing mass derivative permits the mixed
partial theorem to differentiate the horizontal mass derivative in `v`.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- On every compact off-axis rectangle, the horizontal mass derivative
has a vertical derivative. It equals the horizontal derivative of the
outgoing mass derivative. This is the mixed regularity needed by the field reconstruction. -/
theorem Box.mass_u_vertical_derivative {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {u₀ u₁ v₀ v₁ : ℝ}
    (ha : a < u₀) (hu : u₀ < u₁) (hgap : u₁ < v₀)
    (hv : v₀ < v₁) (hb : v₁ < b)
    {u v : ℝ} (huv : u ∈ Icc u₀ u₁) (hvv : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt
      (fun t => (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) (u, t)) (1, 0))
      ((fderivWithin ℝ
        (fun q => (fderivWithin ℝ x.1.toTriple.mass
          (closedCoordTriangle a b) q) (0, 1))
        (closedCoordTriangle a b) (u, v)) (1, 0))
      (Icc v₀ v₁) v := by
  let K := closedCoordTriangle a b
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  let F := x.1.toTriple.mass
  let U : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ F K p) (1, 0)
  let V : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ F K p) (0, 1)
  let W : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ V K p) (1, 0)
  have hR : R ⊆ interior K := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rw [interior_closedCoordTriangle]
    exact ⟨ha.trans_le hs.1, (hs.2.trans_lt hgap).trans_le ht.1,
      ht.2.trans_lt hb⟩
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hFcont : ContinuousOn F R :=
    (x.mass_c1 hab).continuousOn.mono (hR.trans interior_subset)
  have hJet := (x.mass_c1 hab).continuousOn_fderivWithin hUnique (by norm_num)
  have hUcont : ContinuousOn U R :=
    (hJet.clm_apply continuousOn_const).mono (hR.trans interior_subset)
  have hVcont : ContinuousOn V R :=
    (x.mass_v_c1 hab).continuousOn.mono (hR.trans interior_subset)
  have hWcont : ContinuousOn W R :=
    ((x.mass_v_c1 hab).continuousOn_fderivWithin hUnique (by norm_num)
      |>.clm_apply continuousOn_const).mono (hR.trans interior_subset)
  have hAtF (s t : ℝ) (hs : s ∈ Icc u₀ u₁) (ht : t ∈ Icc v₀ v₁) :
      DifferentiableAt ℝ F (s, t) := by
    have hi : (s, t) ∈ interior K := hR (show (s, t) ∈ R from ⟨hs, ht⟩)
    have hKn : K ∈ 𝓝 (s, t) :=
      mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
    exact ((x.mass_c1 hab).differentiableOn (by norm_num) _ (interior_subset hi))
      |>.differentiableAt hKn
  have hAtV (s t : ℝ) (hs : s ∈ Icc u₀ u₁) (ht : t ∈ Icc v₀ v₁) :
      DifferentiableAt ℝ V (s, t) := by
    have hi : (s, t) ∈ interior K := hR (show (s, t) ∈ R from ⟨hs, ht⟩)
    have hKn : K ∈ 𝓝 (s, t) :=
      mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
    exact ((x.mass_v_c1 hab).differentiableOn (by norm_num) _ (interior_subset hi))
      |>.differentiableAt hKn
  have hHor (s t : ℝ) (hs : s ∈ Icc u₀ u₁) (ht : t ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun z => F (z, t)) (U (s, t)) (Icc u₀ u₁) s := by
    have hpath : HasDerivAt (fun z : ℝ => (z, t)) (1, 0) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s t)
    have h := (hAtF s t hs ht).hasFDerivAt.comp_hasDerivAt s hpath
    have hi : (s, t) ∈ interior K := hR (show (s, t) ∈ R from ⟨hs, ht⟩)
    have hKn : K ∈ 𝓝 (s, t) :=
      mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
    change HasDerivAt (fun z => F (z, t))
      ((fderiv ℝ F (s, t)) (1, 0)) s at h
    rw [← fderivWithin_of_mem_nhds hKn] at h
    exact h.hasDerivWithinAt
  have hVer (s t : ℝ) (hs : s ∈ Icc u₀ u₁) (ht : t ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun z => F (s, z)) (V (s, t)) (Icc v₀ v₁) t := by
    have hpath : HasDerivAt (fun z : ℝ => (s, z)) (0, 1) t :=
      (hasDerivAt_const t s).prodMk (hasDerivAt_id' t)
    have h := (hAtF s t hs ht).hasFDerivAt.comp_hasDerivAt t hpath
    have hi : (s, t) ∈ interior K := hR (show (s, t) ∈ R from ⟨hs, ht⟩)
    have hKn : K ∈ 𝓝 (s, t) :=
      mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
    change HasDerivAt (fun z => F (s, z))
      ((fderiv ℝ F (s, t)) (0, 1)) t at h
    rw [← fderivWithin_of_mem_nhds hKn] at h
    exact h.hasDerivWithinAt
  have hVHor (s t : ℝ) (hs : s ∈ Icc u₀ u₁) (ht : t ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun z => V (z, t)) (W (s, t)) (Icc u₀ u₁) s := by
    have hpath : HasDerivAt (fun z : ℝ => (z, t)) (1, 0) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s t)
    have h := (hAtV s t hs ht).hasFDerivAt.comp_hasDerivAt s hpath
    have hi : (s, t) ∈ interior K := hR (show (s, t) ∈ R from ⟨hs, ht⟩)
    have hKn : K ∈ 𝓝 (s, t) :=
      mem_of_superset (isOpen_interior.mem_nhds hi) interior_subset
    change HasDerivAt (fun z => V (z, t))
      ((fderiv ℝ V (s, t)) (1, 0)) s at h
    rw [← fderivWithin_of_mem_nhds hKn] at h
    exact h.hasDerivWithinAt
  have hMixed := hasDerivWithinAt_vertical_of_horizontal_partial
    hu hv (f := fun s t => F (s, t))
    (g := fun s t => U (s, t))
    (G := fun s t => V (s, t))
    (Gu := fun s t => W (s, t))
    hFcont hUcont hVcont hWcont
    (fun s hs t ht => hHor s t hs ht)
    (fun s hs t ht => hVer s t hs ht)
    (fun s hs t ht => hVHor s t hs ht)
    huv hvv
  exact hMixed

end ChristodoulouBV.AxisPicard

end
