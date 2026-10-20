module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith

/-!
# Closing full first jets on a terminal rectangle

The compact rectangle criterion turns jointly continuous candidate coordinate
jets into the full relative first jet at the terminal edge. This is the final
analytic step after the old family supplies the two coordinate derivatives
on the strict interior.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The continuous linear map determined by two scalar coordinate jets. -/
@[expose] def rectangleScalarJet (du dv : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  du • ContinuousLinearMap.fst ℝ ℝ ℝ +
    dv • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The two evaluations of the scalar rectangle jet. -/
@[simp] theorem rectangleScalarJet_apply_first (du dv : ℝ) :
    rectangleScalarJet du dv (1, 0) = du := by
  simp [rectangleScalarJet]

/-- The outgoing coordinate evaluation of the scalar rectangle jet. -/
@[simp] theorem rectangleScalarJet_apply_second (du dv : ℝ) :
    rectangleScalarJet du dv (0, 1) = dv := by
  simp [rectangleScalarJet]

/-- Continuous coordinate jets on a closed rectangle determine its full
relative first jet, provided they are the ordinary interior derivatives. -/
theorem rectangle_scalar_full_jet_of_interior
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    {f du dv : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hdu : ContinuousOn du (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hdv : ContinuousOn dv (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hdiff : ∀ p ∈ Ioo u₀ u₁ ×ˢ Ioo v₀ v₁,
      DifferentiableAt ℝ f p)
    (hderiv_u : ∀ p ∈ Ioo u₀ u₁ ×ˢ Ioo v₀ v₁,
      (fderiv ℝ f p) (1, 0) = du p)
    (hderiv_v : ∀ p ∈ Ioo u₀ u₁ ×ˢ Ioo v₀ v₁,
      (fderiv ℝ f p) (0, 1) = dv p) :
    ContDiffOn ℝ 1 f (Icc u₀ u₁ ×ˢ Icc v₀ v₁) ∧
      ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
        HasFDerivWithinAt f (rectangleScalarJet (du p) (dv p))
          (Icc u₀ u₁ ×ˢ Icc v₀ v₁) p := by
  let K : Set (ℝ × ℝ) := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  let J : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
    fun p => rectangleScalarJet (du p) (dv p)
  have hJ : ContinuousOn J K := by
    unfold J rectangleScalarJet
    exact (hdu.smul continuousOn_const).add (hdv.smul continuousOn_const)
  have hint : interior K = Ioo u₀ u₁ ×ˢ Ioo v₀ v₁ := by
    change interior (Icc u₀ u₁ ×ˢ Icc v₀ v₁) = _
    rw [interior_prod_eq, interior_Icc, interior_Icc]
  have hnonempty : (interior K).Nonempty := by
    rw [hint]
    exact (nonempty_Ioo.mpr hu).prod (nonempty_Ioo.mpr hv)
  have hF : ∀ p ∈ interior K, fderiv ℝ f p = J p := by
    intro p hp
    have hp' : p ∈ Ioo u₀ u₁ ×ˢ Ioo v₀ v₁ := hint ▸ hp
    apply ContinuousLinearMap.ext
    intro z
    have hz : z = z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hz, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    rw [hderiv_u p hp', hderiv_v p hp']
    simp [J]
  have hdiffOn : DifferentiableOn ℝ f (interior K) := by
    intro p hp
    exact (hdiff p (hint ▸ hp)).differentiableWithinAt
  have hconv : Convex ℝ K := (convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁)
  have hclosed : IsClosed K := isClosed_Icc.prod isClosed_Icc
  exact ⟨hconv.contDiffOn_one_of_continuousOn_fderiv
      hclosed hnonempty hf hJ hdiffOn hF,
    fun p hp => hconv.hasFDerivWithinAt_of_continuousOn_fderiv
      hclosed hnonempty hf hJ hdiffOn hF hp⟩

/-- A compatible family of finite old fields supplies the interior jets of
the terminal rectangle. Continuity of the value and both proposed jets then
closes the full first jet at all four edges. -/
theorem rectangle_scalar_full_jet_of_compatible_family
    {a vBar vStar : ℝ} (ha : 0 < a) (haBar : a < vBar)
    (hBarStar : vBar < vStar)
    {F : ℝ → ℝ × ℝ → ℝ} {f du dv : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 a ×ˢ Icc vBar vStar))
    (hdu : ContinuousOn du (Icc 0 a ×ˢ Icc vBar vStar))
    (hdv : ContinuousOn dv (Icc 0 a ×ˢ Icc vBar vStar))
    (hmatch : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
        f (u, v) = F b (u, v))
    (hfinite : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u ∈ Ioo 0 a, ∀ v ∈ Ioo vBar b,
        DifferentiableAt ℝ (F b) (u, v) ∧
        (fderiv ℝ (F b) (u, v)) (1, 0) = du (u, v) ∧
        (fderiv ℝ (F b) (u, v)) (0, 1) = dv (u, v)) :
    ContDiffOn ℝ 1 f (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt f (rectangleScalarJet (du p) (dv p))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  have hlocal (u v : ℝ) (hu : u ∈ Ioo 0 a)
      (hv : v ∈ Ioo vBar vStar) :
      ∃ b ∈ Ioo (0 : ℝ) vStar,
        v < b ∧ f =ᶠ[𝓝 (u, v)] F b := by
    let b := (v + vStar) / 2
    have hvb : v < b := by dsimp [b]; linarith only [hv.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      dsimp [b]
      constructor <;> linarith only [ha, haBar, hv.1, hv.2]
    refine ⟨b, hb, hvb, ?_⟩
    have hmem : (u, v) ∈ Ioo 0 a ×ˢ Ioo vBar b :=
      ⟨hu, ⟨hv.1, hvb⟩⟩
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hmem] with p hp
    exact hmatch b hb p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2
      ⟨hp.2.1.le, hp.2.2⟩
  have hpoint (p : ℝ × ℝ) (hp : p ∈ Ioo 0 a ×ˢ Ioo vBar vStar) :
      DifferentiableAt ℝ f p ∧
      (fderiv ℝ f p) (1, 0) = du p ∧
      (fderiv ℝ f p) (0, 1) = dv p := by
    obtain ⟨u, v⟩ := p
    obtain ⟨b, hb, hvb, heq⟩ := hlocal u v hp.1 hp.2
    obtain ⟨hfd, hfu, hfv⟩ := hfinite b hb u hp.1 v ⟨hp.2.1, hvb⟩
    refine ⟨hfd.congr_of_eventuallyEq heq, ?_, ?_⟩
    · rw [heq.fderiv_eq]
      exact hfu
    · rw [heq.fderiv_eq]
      exact hfv
  apply rectangle_scalar_full_jet_of_interior ha hBarStar hf hdu hdv
  · intro p hp
    exact (hpoint p hp).1
  · intro p hp
    exact (hpoint p hp).2.1
  · intro p hp
    exact (hpoint p hp).2.2

/-- An ordinary horizontal slice derivative evaluates the full derivative
on the first coordinate vector. -/
theorem fderiv_apply_first_of_hasDerivAt
    {f : ℝ × ℝ → ℝ} {u v d : ℝ}
    (hf : DifferentiableAt ℝ f (u, v))
    (h : HasDerivAt (fun s => f (s, v)) d u) :
    (fderiv ℝ f (u, v)) (1, 0) = d := by
  have hp : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hc := hf.hasFDerivAt.comp_hasDerivAt u hp
  have hc' : HasDerivAt (fun s => f (s, v))
      ((fderiv ℝ f (u, v)) (1, 0)) u := by
    simpa only [Function.comp_def] using hc
  exact hc'.unique h

/-- The analogous evaluation on the outgoing coordinate vector. -/
theorem fderiv_apply_second_of_hasDerivAt
    {f : ℝ × ℝ → ℝ} {u v d : ℝ}
    (hf : DifferentiableAt ℝ f (u, v))
    (h : HasDerivAt (fun s => f (u, s)) d v) :
    (fderiv ℝ f (u, v)) (0, 1) = d := by
  have hp : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hc := hf.hasFDerivAt.comp_hasDerivAt v hp
  have hc' : HasDerivAt (fun s => f (u, s))
      ((fderiv ℝ f (u, v)) (0, 1)) v := by
    simpa only [Function.comp_def] using hc
  exact hc'.unique h

end ChristodoulouBV.Uniqueness

end
