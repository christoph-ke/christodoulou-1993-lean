module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.ODE.GoursatC1TransverseLinearFields
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Integral identities from continuous coordinate jets

A continuous relative derivative on a closed rectangle integrates to the
corresponding characteristic difference, including the endpoint cases.
These identities can be passed to uniform limits of functions and jets.
-/

public section

open Set Filter intervalIntegral
open scoped Topology

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- A continuous vertical jet on the closed rectangle integrates to the
vertical difference from its bottom edge. -/
theorem eq_bottom_add_integral_of_vertical_jet
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (hX : Continuous X)
    (P : C(rectangle u₀ u₁ v₀ v₁, E))
    (hjet : ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
      HasDerivWithinAt (fun t => X (u, t))
        (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v)
    (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
    (v : ℝ) (hv' : v ∈ Icc v₀ v₁) :
    X (u, v) = X (u, v₀) +
      ∫ t in v₀..v, P (clippedPoint hu hv (u, t)) := by
  have hPcont : Continuous (fun t : ℝ => P (clippedPoint hu hv (u, t))) :=
    P.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_const.prodMk continuous_id))
  have hXslice : ContinuousOn (fun t => X (u, t)) (Icc v₀ v) :=
    (hX.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hderiv : ∀ t ∈ Ioo v₀ v,
      HasDerivAt (fun w => X (u, w))
        (P (clippedPoint hu hv (u, t))) t := by
    intro t ht
    have htI : t ∈ Icc v₀ v₁ := ⟨ht.1.le, ht.2.le.trans hv'.2⟩
    have htOpen : t ∈ Ioo v₀ v₁ := ⟨ht.1, ht.2.trans_le hv'.2⟩
    have hnear : Icc v₀ v₁ ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds htOpen.1 htOpen.2)
        Ioo_subset_Icc_self
    simpa only [clippedPoint_eq_self hu hv
      ⟨(u, t), pair_mem_rectangle hu' htI⟩] using
      (hjet u hu' t htI).hasDerivAt hnear
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv'.1 hXslice hderiv (hPcont.intervalIntegrable _ _)
  rw [hFTC]
  abel

/-- A continuous horizontal jet on the closed rectangle integrates to the
horizontal difference from its left edge. -/
theorem eq_left_add_integral_of_horizontal_jet
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (hX : Continuous X)
    (P : C(rectangle u₀ u₁ v₀ v₁, E))
    (hjet : ∀ (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
      HasDerivWithinAt (fun s => X (s, v))
        (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u)
    (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
    (v : ℝ) (hv' : v ∈ Icc v₀ v₁) :
    X (u, v) = X (u₀, v) +
      ∫ s in u₀..u, P (clippedPoint hu hv (s, v)) := by
  have hPcont : Continuous (fun s : ℝ => P (clippedPoint hu hv (s, v))) :=
    P.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_id.prodMk continuous_const))
  have hXslice : ContinuousOn (fun s => X (s, v)) (Icc u₀ u) :=
    (hX.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hderiv : ∀ s ∈ Ioo u₀ u,
      HasDerivAt (fun w => X (w, v))
        (P (clippedPoint hu hv (s, v))) s := by
    intro s hs
    have hsI : s ∈ Icc u₀ u₁ := ⟨hs.1.le, hs.2.le.trans hu'.2⟩
    have hsOpen : s ∈ Ioo u₀ u₁ := ⟨hs.1, hs.2.trans_le hu'.2⟩
    have hnear : Icc u₀ u₁ ∈ 𝓝 s :=
      Filter.mem_of_superset (Ioo_mem_nhds hsOpen.1 hsOpen.2)
        Ioo_subset_Icc_self
    simpa only [clippedPoint_eq_self hu hv
      ⟨(s, v), pair_mem_rectangle hsI hv'⟩] using
      (hjet s hsI v hv').hasDerivAt hnear
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hu'.1 hXslice hderiv (hPcont.intervalIntegrable _ _)
  rw [hFTC]
  abel


/-- Uniform convergence of continuous functions and their continuous vertical
jets passes the relative vertical derivative to the limit on every edge. -/
theorem hasDerivWithinAt_vertical_of_tendsto_jets
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Xn Pn : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (X P : C(rectangle u₀ u₁ v₀ v₁, E))
    (hX : Tendsto Xn atTop (𝓝 X)) (hP : Tendsto Pn atTop (𝓝 P))
    (hjet : ∀ n (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
      HasDerivWithinAt
        (fun t => Xn n (clippedPoint hu hv (u, t)))
        (Pn n ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v)
    {u v : ℝ} (hu' : u ∈ Icc u₀ u₁) (hv' : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt (fun t => X ⟨(u, clip v₀ v₁ t),
      pair_mem_rectangle hu' (clip_mem_Icc hv t)⟩)
      (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc v₀ v₁) v := by
  have heq : ∀ n (s : ℝ) (hs : s ∈ Icc u₀ u₁)
      (t : ℝ) (ht : t ∈ Icc v₀ v₁),
      Xn n ⟨(s, t), pair_mem_rectangle hs ht⟩ =
        Xn n ⟨(s, v₀), pair_mem_rectangle hs ⟨le_rfl, hv⟩⟩ +
        ∫ w in v₀..t, Pn n ⟨(s, clip v₀ v₁ w),
          pair_mem_rectangle hs (clip_mem_Icc hv w)⟩ := by
    intro n s hs t ht
    let Z : ℝ × ℝ → E := fun p => Xn n (clippedPoint hu hv p)
    have hZ : Continuous Z :=
      (Xn n).continuous.comp (continuous_clippedPoint hu hv)
    have hprim := eq_bottom_add_integral_of_vertical_jet hu hv
      Z hZ (Pn n) (hjet n) s hs t ht
    have hleft : Z (s, t) = Xn n ⟨(s, t), pair_mem_rectangle hs ht⟩ := by
      exact congrArg (Xn n) (clippedPoint_eq_self hu hv
        ⟨(s, t), pair_mem_rectangle hs ht⟩)
    have hbase : Z (s, v₀) =
        Xn n ⟨(s, v₀), pair_mem_rectangle hs ⟨le_rfl, hv⟩⟩ := by
      exact congrArg (Xn n) (clippedPoint_eq_self hu hv
        ⟨(s, v₀), pair_mem_rectangle hs ⟨le_rfl, hv⟩⟩)
    rw [hleft, hbase] at hprim
    convert hprim using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro w hw
    have hq : (s, clip v₀ v₁ w) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hs (clip_mem_Icc hv w)
    have hclip : clippedPoint hu hv (s, w) =
        ⟨(s, clip v₀ v₁ w), hq⟩ := by
      apply Subtype.ext
      exact Prod.ext (clip_eq_self hs) rfl
    exact congrArg (Pn n) hclip.symm
  exact hasDerivWithinAt_vertical_of_tendsto_integral_eq hv Xn Pn
    X P hX hP heq hu' hv'


/-- Uniform convergence of continuous functions and their continuous
horizontal jets passes the relative horizontal derivative to the limit. -/
theorem hasDerivWithinAt_horizontal_of_tendsto_jets
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Xn Pn : ℕ → C(rectangle u₀ u₁ v₀ v₁, E))
    (X P : C(rectangle u₀ u₁ v₀ v₁, E))
    (hX : Tendsto Xn atTop (𝓝 X)) (hP : Tendsto Pn atTop (𝓝 P))
    (hjet : ∀ n (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Icc v₀ v₁),
      HasDerivWithinAt
        (fun s => Xn n (clippedPoint hu hv (s, v)))
        (Pn n ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u)
    {u v : ℝ} (hu' : u ∈ Icc u₀ u₁) (hv' : v ∈ Icc v₀ v₁) :
    HasDerivWithinAt (fun s => X ⟨(clip u₀ u₁ s, v),
      pair_mem_rectangle (clip_mem_Icc hu s) hv'⟩)
      (P ⟨(u, v), pair_mem_rectangle hu' hv'⟩) (Icc u₀ u₁) u := by
  have heq : ∀ n (s : ℝ) (hs : s ∈ Icc u₀ u₁)
      (t : ℝ) (ht : t ∈ Icc v₀ v₁),
      Xn n ⟨(s, t), pair_mem_rectangle hs ht⟩ =
        Xn n ⟨(u₀, t), pair_mem_rectangle ⟨le_rfl, hu⟩ ht⟩ +
        ∫ w in u₀..s, Pn n ⟨(clip u₀ u₁ w, t),
          pair_mem_rectangle (clip_mem_Icc hu w) ht⟩ := by
    intro n s hs t ht
    let Z : ℝ × ℝ → E := fun p => Xn n (clippedPoint hu hv p)
    have hZ : Continuous Z :=
      (Xn n).continuous.comp (continuous_clippedPoint hu hv)
    have hprim := eq_left_add_integral_of_horizontal_jet hu hv
      Z hZ (Pn n) (hjet n) s hs t ht
    have hleft : Z (s, t) = Xn n ⟨(s, t), pair_mem_rectangle hs ht⟩ := by
      exact congrArg (Xn n) (clippedPoint_eq_self hu hv
        ⟨(s, t), pair_mem_rectangle hs ht⟩)
    have hbase : Z (u₀, t) =
        Xn n ⟨(u₀, t), pair_mem_rectangle ⟨le_rfl, hu⟩ ht⟩ := by
      exact congrArg (Xn n) (clippedPoint_eq_self hu hv
        ⟨(u₀, t), pair_mem_rectangle ⟨le_rfl, hu⟩ ht⟩)
    rw [hleft, hbase] at hprim
    convert hprim using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro w hw
    have hq : (clip u₀ u₁ w, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle (clip_mem_Icc hu w) ht
    have hclip : clippedPoint hu hv (w, t) =
        ⟨(clip u₀ u₁ w, t), hq⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl (clip_eq_self ht)
    exact congrArg (Pn n) hclip.symm
  exact hasDerivWithinAt_horizontal_of_tendsto_integral_eq hu Xn Pn
    X P hX hP heq hu' hv'

end Goursat

end
