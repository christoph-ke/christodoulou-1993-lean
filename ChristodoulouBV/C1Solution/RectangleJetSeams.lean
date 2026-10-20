module

public import ChristodoulouBV.C1Solution.RectangleSeams
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartialBanach
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Coordinate jets on off-axis rectangle seams

Relative `C¹` regularity gives both coordinate derivatives on every closed
edge. The Goursat equations then identify the incoming transverse jet and
the outgoing tangential jet from a common vertical state trace.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The full relative derivative of a Banach-valued field on a closed
rectangle gives both coordinate derivatives, including at the corners. -/
theorem coordinate_derivatives_of_contDiffOn_rectangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a₀ a₁ b₀ b₁ : ℝ} (_haa : a₀ < a₁) (_hbb : b₀ < b₁)
    {f : ℝ × ℝ → E}
    (hf : ContDiffOn ℝ 1 f (Goursat.rectangle a₀ a₁ b₀ b₁))
    {u v : ℝ} (hu : u ∈ Icc a₀ a₁) (hv : v ∈ Icc b₀ b₁) :
    HasDerivWithinAt (fun s => f (s, v))
      ((fderivWithin ℝ f (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0))
      (Icc a₀ a₁) u ∧
    HasDerivWithinAt (fun t => f (u, t))
      ((fderivWithin ℝ f (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (0, 1))
      (Icc b₀ b₁) v := by
  let R := Goursat.rectangle a₀ a₁ b₀ b₁
  have hfd := (hf.differentiableOn (by norm_num) (u, v)
    (Goursat.pair_mem_rectangle hu hv)).hasFDerivWithinAt
  constructor
  · have hpath : HasDerivWithinAt (fun s : ℝ => (s, v)) (1, 0)
        (Icc a₀ a₁) u :=
      ((hasDerivAt_id' u).hasDerivWithinAt).prodMk
        ((hasDerivAt_const u v).hasDerivWithinAt)
    have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc a₀ a₁) R := by
      intro s hs
      exact Goursat.pair_mem_rectangle hs hv
    exact hfd.comp_hasDerivWithinAt u hpath hmap
  · have hpath : HasDerivWithinAt (fun t : ℝ => (u, t)) (0, 1)
        (Icc b₀ b₁) v :=
      ((hasDerivAt_const v u).hasDerivWithinAt).prodMk
        ((hasDerivAt_id' v).hasDerivWithinAt)
    have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc b₀ b₁) R := by
      intro t ht
      exact Goursat.pair_mem_rectangle hu ht
    exact hfd.comp_hasDerivWithinAt v hpath hmap

/-- The Banach-valued mixed-partial interchange on a closed rectangle. A
continuous horizontal jet of `f` and a continuous horizontal derivative of
its vertical density determine the vertical derivative of that jet, including
at the endpoints. -/
theorem hasDerivWithinAt_horizontal_jet_of_vertical_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    {f fu G Gu : ℝ → ℝ → E}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hGu : ContinuousOn (fun p : ℝ × ℝ => Gu p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hfu_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => f s v) (fu u v) (Icc a₀ a₁) u)
    (hG_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (f u) (G u v) (Icc b₀ b₁) v)
    (hGu_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => G s v) (Gu u v) (Icc a₀ a₁) u)
    {u v : ℝ} (hu : u ∈ Icc a₀ a₁) (hv : v ∈ Icc b₀ b₁) :
    HasDerivWithinAt (fu u) (Gu u v) (Icc b₀ b₁) v := by
  have hslice {H : ℝ → ℝ → E}
      (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
        (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
      (x : ℝ) (hx : x ∈ Icc a₀ a₁) : ContinuousOn (H x) (Icc b₀ b₁) :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx, ht⟩)
  have hfirst (x : ℝ) (hx : x ∈ Icc a₀ a₁)
      (t : ℝ) (ht : t ∈ Icc b₀ b₁) :
      f x t = f x b₀ + ∫ w in b₀..t, G x w := by
    have hderiv : ∀ w ∈ Ioo b₀ t, HasDerivAt (f x) (G x w) w := by
      intro w hw
      exact (hG_deriv x hx w ⟨hw.1.le, hw.2.le.trans ht.2⟩).hasDerivAt
        (Icc_mem_nhds hw.1 (hw.2.trans_le ht.2))
    have hf' : ContinuousOn (f x) (Icc b₀ t) :=
      (hslice hf x hx).mono (Icc_subset_Icc le_rfl ht.2)
    have hint : IntervalIntegrable (G x) MeasureTheory.volume b₀ t :=
      ((hslice hG x hx).mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc
        ht.1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      ht.1 hf' hderiv hint
    calc
      f x t = f x b₀ + (f x t - f x b₀) := by abel
      _ = f x b₀ + ∫ w in b₀..t, G x w := by rw [← hFTC]
  have hparam := intervalIntegral.hasDerivWithinAt_integral_of_continuousOn_rectangle_banach
    haa hu hv hG hGu (by
      intro x hx t ht
      exact (hGu_deriv x ⟨hx.1.le, hx.2.le⟩ t ht).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2))
  have hbase := hfu_deriv u hu b₀ ⟨le_rfl, hbb.le⟩
  have hsum := hbase.add hparam
  have hsum' : HasDerivWithinAt
      (fun x => f x b₀ + ∫ t in b₀..v, G x t)
      (fu u b₀ + ∫ t in b₀..v, Gu u t) (Icc a₀ a₁) u := by
    convert hsum using 1
  have hresult : HasDerivWithinAt (fun x => f x v)
      (fu u b₀ + ∫ t in b₀..v, Gu u t) (Icc a₀ a₁) u :=
    hsum'.congr (fun x hx => hfirst x hx v hv)
      (hfirst u hu v hv)
  have hidentity : fu u v = fu u b₀ + ∫ t in b₀..v, Gu u t := by
    exact ((hfu_deriv u hu v hv).derivWithin ((uniqueDiffOn_Icc haa) u hu)).symm.trans
      (hresult.derivWithin ((uniqueDiffOn_Icc haa) u hu))
  have hGu_slice : ContinuousOn (Gu u) (Icc b₀ b₁) := hslice hGu u hu
  have hint : IntervalIntegrable (Gu u) MeasureTheory.volume b₀ v :=
    (hGu_slice.mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable_of_Icc hv.1
  have hFTC : HasDerivWithinAt (fun w => ∫ t in b₀..w, Gu u t)
      (Gu u v) (Icc b₀ b₁) v :=
    @intervalIntegral.integral_hasDerivWithinAt_right E _ _ _ (Gu u) b₀ v hint
      (Icc b₀ b₁) (Icc b₀ b₁) (@intervalIntegral.FTCFilter.nhdsIcc v b₀ b₁ ⟨hv⟩)
      (hGu_slice.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v)
      (hGu_slice v hv)
  have hsumv :=
    (hasDerivWithinAt_const (s := Icc b₀ b₁) (x := v) (c := fu u b₀)).add hFTC
  have hsumv' : HasDerivWithinAt
      (fun w => fu u b₀ + ∫ t in b₀..w, Gu u t)
      (Gu u v) (Icc b₀ b₁) v := by
    have hfunc : ((fun _ : ℝ => fu u b₀) +
        fun w => ∫ t in b₀..w, Gu u t) =
        (fun w => fu u b₀ + ∫ t in b₀..w, Gu u t) := by
      funext w
      rfl
    rw [hfunc] at hsumv
    simpa only [zero_add] using hsumv
  have hident (w : ℝ) (hw : w ∈ Icc b₀ b₁) :
      fu u w = fu u b₀ + ∫ t in b₀..w, Gu u t := by
    have hparamw := intervalIntegral.hasDerivWithinAt_integral_of_continuousOn_rectangle_banach
      haa hu hw hG hGu (by
        intro x hx t ht
        exact (hGu_deriv x ⟨hx.1.le, hx.2.le⟩ t ht).hasDerivAt
          (Icc_mem_nhds hx.1 hx.2))
    have hsumw := (hfu_deriv u hu b₀ ⟨le_rfl, hbb.le⟩).add hparamw
    have hsumw' : HasDerivWithinAt (fun x => f x w)
        (fu u b₀ + ∫ t in b₀..w, Gu u t) (Icc a₀ a₁) u := by
      have hbasew : HasDerivWithinAt
          (fun x => f x b₀ + ∫ t in b₀..w, G x t)
          (fu u b₀ + ∫ t in b₀..w, Gu u t) (Icc a₀ a₁) u := by
        convert hsumw using 1
      exact hbasew.congr (fun x hx => hfirst x hx w hw)
        (hfirst u hu w hw)
    exact ((hfu_deriv u hu w hw).derivWithin ((uniqueDiffOn_Icc haa) u hu)).symm.trans
      (hsumw'.derivWithin ((uniqueDiffOn_Icc haa) u hu))
  exact hsumv'.congr (fun w hw => hident w hw) hidentity

/-- A nondegenerate closed rectangle has unique relative first derivatives. -/
theorem uniqueDiffOn_rectangle
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁) :
    UniqueDiffOn ℝ (Goursat.rectangle a₀ a₁ b₀ b₁) := by
  have hconv : Convex ℝ (Goursat.rectangle a₀ a₁ b₀ b₁) :=
    by simpa only [Goursat.rectangle] using
      (convex_Icc a₀ a₁).prod (convex_Icc b₀ b₁)
  have hinterior : (interior (Goursat.rectangle a₀ a₁ b₀ b₁)).Nonempty := by
    change (interior (Icc a₀ a₁ ×ˢ Icc b₀ b₁)).Nonempty
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    refine ⟨((a₀ + a₁) / 2, (b₀ + b₁) / 2), ?_⟩
    exact ⟨by constructor <;> linarith, by constructor <;> linarith⟩
  exact uniqueDiffOn_convex hconv hinterior

/-- The horizontal coordinate of the full outgoing jet is continuous across
the entire closed rectangle. -/
theorem continuousOn_outgoing_horizontal_jet
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    {Y : ℝ × ℝ → OutgoingState}
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁)) :
    ContinuousOn
      (fun p => (fderivWithin ℝ Y (Goursat.rectangle a₀ a₁ b₀ b₁) p) (1, 0))
      (Goursat.rectangle a₀ a₁ b₀ b₁) :=
  (hY.continuousOn_fderivWithin (uniqueDiffOn_rectangle haa hbb)
    (by norm_num)).clm_apply continuousOn_const

/-- Differentiating the outgoing equation in the horizontal direction gives
the linear transverse-jet equation on every vertical line, including both
endpoints. -/
theorem outgoing_horizontal_jet_vertical_equation
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (B : SafeRectangleBox)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (hX : ContDiffOn ℝ 1 X (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hball : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      (X p, Y p) ∈ B.carrier)
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    {u v : ℝ} (hu : u ∈ Icc a₀ a₁) (hv : v ∈ Icc b₀ b₁) :
    HasDerivWithinAt
      (fun t => (fderivWithin ℝ Y
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, t)) (1, 0))
      ((fderiv ℝ rectangleG (X (u, v), Y (u, v)))
        (rectangleF (X (u, v), Y (u, v)),
          (fderivWithin ℝ Y
            (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0)))
      (Icc b₀ b₁) v := by
  let R := Goursat.rectangle a₀ a₁ b₀ b₁
  let Z : ℝ × ℝ → RectangleState := fun p => (X p, Y p)
  let q : ℝ × ℝ → OutgoingState := fun p =>
    (fderivWithin ℝ Y R p) (1, 0)
  let G : ℝ → ℝ → OutgoingState := fun s t => rectangleG (Z (s, t))
  let Gu : ℝ → ℝ → OutgoingState := fun s t =>
    (fderiv ℝ rectangleG (Z (s, t)))
      (rectangleF (Z (s, t)), q (s, t))
  have hZcont : ContinuousOn Z R := hX.continuousOn.prodMk hY.continuousOn
  have hqcont : ContinuousOn q R :=
    continuousOn_outgoing_horizontal_jet haa hbb hY
  have hFbox : ContinuousOn rectangleF B.carrier := by
    intro z hz
    exact ((contDiffAt_rectangleF (B.safe hz)).continuousAt).continuousWithinAt
  have hGbox : ContinuousOn rectangleG B.carrier := by
    intro z hz
    exact ((contDiffAt_rectangleG (B.safe hz)).continuousAt).continuousWithinAt
  have hDGbox : ContinuousOn (fderiv ℝ rectangleG) B.carrier := by
    intro z hz
    exact ((contDiffAt_rectangleG (B.safe hz)).continuousAt_fderiv
      (by decide)).continuousWithinAt
  have hFcont : ContinuousOn (fun p => rectangleF (Z p)) R :=
    hFbox.comp hZcont hball
  have hGcont : ContinuousOn (fun p => G p.1 p.2) R :=
    hGbox.comp hZcont hball
  have hDGcont : ContinuousOn (fun p => fderiv ℝ rectangleG (Z p)) R :=
    hDGbox.comp hZcont hball
  have hGucont : ContinuousOn (fun p => Gu p.1 p.2) R := by
    exact hDGcont.clm_apply (hFcont.prodMk hqcont)
  have hqderiv (s : ℝ) (hs : s ∈ Icc a₀ a₁)
      (t : ℝ) (ht : t ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun x => Y (x, t)) (q (s, t))
        (Icc a₀ a₁) s :=
    (coordinate_derivatives_of_contDiffOn_rectangle haa hbb hY hs ht).1
  have hGuderiv (s : ℝ) (hs : s ∈ Icc a₀ a₁)
      (t : ℝ) (ht : t ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun x => G x t) (Gu s t) (Icc a₀ a₁) s := by
    have hZu : HasDerivWithinAt (fun x => Z (x, t))
        (rectangleF (Z (s, t)), q (s, t)) (Icc a₀ a₁) s :=
      (hjet s hs t ht).1.prodMk (hqderiv s hs t ht)
    have hstate := B.safe (hball (s, t) (Goursat.pair_mem_rectangle hs ht))
    have hDG := (contDiffAt_rectangleG hstate).differentiableAt_one.hasFDerivAt
    exact hDG.comp_hasDerivWithinAt s hZu
  exact hasDerivWithinAt_horizontal_jet_of_vertical_equation
    (f := fun s t => Y (s, t)) (fu := fun s t => q (s, t))
    (G := G) (Gu := Gu) haa hbb
    (by simpa only [R, Goursat.rectangle] using hY.continuousOn)
    (by simpa only [R, Goursat.rectangle] using hGcont)
    (by simpa only [R, Goursat.rectangle] using hGucont)
    hqderiv
    (fun s hs t ht => (hjet s hs t ht).2) hGuderiv hu hv

/-- On a shared vertical edge, equality of the full state values and the
Goursat equations forces equality of the complete incoming first jet and of
the outgoing tangential coordinate jet. The result holds at both corners. -/
theorem incoming_full_jet_eq_of_common_vertical_trace
    {a₀ a a₁ b₀ b₁ : ℝ}
    (ha₀ : a₀ < a) (ha₁ : a < a₁) (hbb : b₀ < b₁)
    (X₁ : ℝ × ℝ → IncomingState) (Y₁ : ℝ × ℝ → OutgoingState)
    (X₂ : ℝ × ℝ → IncomingState) (Y₂ : ℝ × ℝ → OutgoingState)
    (hX₁ : ContDiffOn ℝ 1 X₁ (Goursat.rectangle a₀ a b₀ b₁))
    (hY₁ : ContDiffOn ℝ 1 Y₁ (Goursat.rectangle a₀ a b₀ b₁))
    (hX₂ : ContDiffOn ℝ 1 X₂ (Goursat.rectangle a a₁ b₀ b₁))
    (hY₂ : ContDiffOn ℝ 1 Y₂ (Goursat.rectangle a a₁ b₀ b₁))
    (hjet₁ : ∀ u ∈ Icc a₀ a, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X₁ (s, v))
        (rectangleF (X₁ (u, v), Y₁ (u, v))) (Icc a₀ a) u ∧
      HasDerivWithinAt (fun t => Y₁ (u, t))
        (rectangleG (X₁ (u, v), Y₁ (u, v))) (Icc b₀ b₁) v)
    (hjet₂ : ∀ u ∈ Icc a a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X₂ (s, v))
        (rectangleF (X₂ (u, v), Y₂ (u, v))) (Icc a a₁) u ∧
      HasDerivWithinAt (fun t => Y₂ (u, t))
        (rectangleG (X₂ (u, v), Y₂ (u, v))) (Icc b₀ b₁) v)
    (htrace : ∀ v ∈ Icc b₀ b₁,
      (X₁ (a, v), Y₁ (a, v)) = (X₂ (a, v), Y₂ (a, v)))
    {v : ℝ} (hv : v ∈ Icc b₀ b₁) :
    fderivWithin ℝ X₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v) =
      fderivWithin ℝ X₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v) ∧
    (fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v)) (0, 1) =
      (fderivWithin ℝ Y₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v)) (0, 1) := by
  have haL : a ∈ Icc a₀ a := ⟨ha₀.le, le_rfl⟩
  have haR : a ∈ Icc a a₁ := ⟨le_rfl, ha₁.le⟩
  have hXcoord₁ := coordinate_derivatives_of_contDiffOn_rectangle
    ha₀ hbb hX₁ haL hv
  have hXcoord₂ := coordinate_derivatives_of_contDiffOn_rectangle
    ha₁ hbb hX₂ haR hv
  have hYcoord₁ := coordinate_derivatives_of_contDiffOn_rectangle
    ha₀ hbb hY₁ haL hv
  have hYcoord₂ := coordinate_derivatives_of_contDiffOn_rectangle
    ha₁ hbb hY₂ haR hv
  have hXu₁ :
      (fderivWithin ℝ X₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v)) (1, 0) =
        rectangleF (X₁ (a, v), Y₁ (a, v)) := by
    exact (hXcoord₁.1.derivWithin ((uniqueDiffOn_Icc ha₀) a haL)).symm.trans
      ((hjet₁ a haL v hv).1.derivWithin ((uniqueDiffOn_Icc ha₀) a haL))
  have hXu₂ :
      (fderivWithin ℝ X₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v)) (1, 0) =
        rectangleF (X₂ (a, v), Y₂ (a, v)) := by
    exact (hXcoord₂.1.derivWithin ((uniqueDiffOn_Icc ha₁) a haR)).symm.trans
      ((hjet₂ a haR v hv).1.derivWithin ((uniqueDiffOn_Icc ha₁) a haR))
  have hXv :
      (fderivWithin ℝ X₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v)) (0, 1) =
      (fderivWithin ℝ X₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v)) (0, 1) := by
    have htraceX (t : ℝ) (ht : t ∈ Icc b₀ b₁) : X₁ (a, t) = X₂ (a, t) :=
      congrArg Prod.fst (htrace t ht)
    have h := hXcoord₁.2.congr
      (fun t ht => (htraceX t ht).symm) (htraceX v hv).symm
    exact (h.derivWithin ((uniqueDiffOn_Icc hbb) v hv)).symm.trans
      (hXcoord₂.2.derivWithin ((uniqueDiffOn_Icc hbb) v hv))
  have hYv₁ :
      (fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v)) (0, 1) =
        rectangleG (X₁ (a, v), Y₁ (a, v)) := by
    exact (hYcoord₁.2.derivWithin ((uniqueDiffOn_Icc hbb) v hv)).symm.trans
      ((hjet₁ a haL v hv).2.derivWithin ((uniqueDiffOn_Icc hbb) v hv))
  have hYv₂ :
      (fderivWithin ℝ Y₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v)) (0, 1) =
        rectangleG (X₂ (a, v), Y₂ (a, v)) := by
    exact (hYcoord₂.2.derivWithin ((uniqueDiffOn_Icc hbb) v hv)).symm.trans
      ((hjet₂ a haR v hv).2.derivWithin ((uniqueDiffOn_Icc hbb) v hv))
  constructor
  · apply full_first_jet_eq_of_coordinate_jets
    · rw [hXu₁, hXu₂, htrace v hv]
    · exact hXv
  · rw [hYv₁, hYv₂, htrace v hv]

/-- Two adjacent off-axis rectangle solutions with a common vertical state
trace and matching corner transverse jet have matching full first jets along
the entire seam. The outgoing transverse jet is derived from its linearized
vertical equation. -/
theorem full_first_jets_eq_on_vertical_seam
    {a₀ a a₁ b₀ b₁ : ℝ}
    (ha₀ : a₀ < a) (ha₁ : a < a₁) (hbb : b₀ < b₁)
    (B₁ B₂ : SafeRectangleBox)
    (X₁ : ℝ × ℝ → IncomingState) (Y₁ : ℝ × ℝ → OutgoingState)
    (X₂ : ℝ × ℝ → IncomingState) (Y₂ : ℝ × ℝ → OutgoingState)
    (hX₁ : ContDiffOn ℝ 1 X₁ (Goursat.rectangle a₀ a b₀ b₁))
    (hY₁ : ContDiffOn ℝ 1 Y₁ (Goursat.rectangle a₀ a b₀ b₁))
    (hX₂ : ContDiffOn ℝ 1 X₂ (Goursat.rectangle a a₁ b₀ b₁))
    (hY₂ : ContDiffOn ℝ 1 Y₂ (Goursat.rectangle a a₁ b₀ b₁))
    (hball₁ : ∀ p ∈ Goursat.rectangle a₀ a b₀ b₁,
      (X₁ p, Y₁ p) ∈ B₁.carrier)
    (hball₂ : ∀ p ∈ Goursat.rectangle a a₁ b₀ b₁,
      (X₂ p, Y₂ p) ∈ B₂.carrier)
    (hjet₁ : ∀ u ∈ Icc a₀ a, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X₁ (s, v))
        (rectangleF (X₁ (u, v), Y₁ (u, v))) (Icc a₀ a) u ∧
      HasDerivWithinAt (fun t => Y₁ (u, t))
        (rectangleG (X₁ (u, v), Y₁ (u, v))) (Icc b₀ b₁) v)
    (hjet₂ : ∀ u ∈ Icc a a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X₂ (s, v))
        (rectangleF (X₂ (u, v), Y₂ (u, v))) (Icc a a₁) u ∧
      HasDerivWithinAt (fun t => Y₂ (u, t))
        (rectangleG (X₂ (u, v), Y₂ (u, v))) (Icc b₀ b₁) v)
    (htrace : ∀ v ∈ Icc b₀ b₁,
      (X₁ (a, v), Y₁ (a, v)) = (X₂ (a, v), Y₂ (a, v)))
    (hcorner :
      (fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a b₀ b₁) (a, b₀)) (1, 0) =
      (fderivWithin ℝ Y₂ (Goursat.rectangle a a₁ b₀ b₁) (a, b₀)) (1, 0)) :
    ∀ v ∈ Icc b₀ b₁,
      fderivWithin ℝ X₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v) =
        fderivWithin ℝ X₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v) ∧
      fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v) =
        fderivWithin ℝ Y₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v) := by
  let z : ℝ → RectangleState := fun v => (X₁ (a, v), Y₁ (a, v))
  let q₁ : ℝ → OutgoingState := fun v =>
    (fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v)) (1, 0)
  let q₂ : ℝ → OutgoingState := fun v =>
    (fderivWithin ℝ Y₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v)) (1, 0)
  let L : OutgoingState →L[ℝ] RectangleState :=
    ContinuousLinearMap.inr ℝ IncomingState OutgoingState
  let A : ℝ → OutgoingState →L[ℝ] OutgoingState := fun v =>
    (fderiv ℝ rectangleG (z v)).comp L
  let h : ℝ → OutgoingState := fun v =>
    (fderiv ℝ rectangleG (z v)) (rectangleF (z v), 0)
  have haL : a ∈ Icc a₀ a := ⟨ha₀.le, le_rfl⟩
  have haR : a ∈ Icc a a₁ := ⟨le_rfl, ha₁.le⟩
  have hzcont : ContinuousOn z (Icc b₀ b₁) := by
    have hZ : ContinuousOn
        (fun p => (X₁ p, Y₁ p)) (Goursat.rectangle a₀ a b₀ b₁) :=
      hX₁.continuousOn.prodMk hY₁.continuousOn
    exact hZ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => Goursat.pair_mem_rectangle haL hv)
  have hzball : ∀ v ∈ Icc b₀ b₁, z v ∈ B₁.carrier := by
    intro v hv
    exact hball₁ (a, v) (Goursat.pair_mem_rectangle haL hv)
  have hDGbox : ContinuousOn (fderiv ℝ rectangleG) B₁.carrier := by
    intro w hw
    exact ((contDiffAt_rectangleG (B₁.safe hw)).continuousAt_fderiv
      (by decide)).continuousWithinAt
  have hDG : ContinuousOn (fun v => fderiv ℝ rectangleG (z v))
      (Icc b₀ b₁) := hDGbox.comp hzcont hzball
  have hFbox : ContinuousOn rectangleF B₁.carrier := by
    intro w hw
    exact ((contDiffAt_rectangleF (B₁.safe hw)).continuousAt).continuousWithinAt
  have hF : ContinuousOn (fun v => rectangleF (z v)) (Icc b₀ b₁) :=
    hFbox.comp hzcont hzball
  have hA : ContinuousOn A (Icc b₀ b₁) :=
    hDG.clm_comp continuousOn_const
  have hh : ContinuousOn h (Icc b₀ b₁) :=
    hDG.clm_apply (hF.prodMk continuousOn_const)
  have hq₁ : ContinuousOn q₁ (Icc b₀ b₁) :=
    (continuousOn_outgoing_horizontal_jet ha₀ hbb hY₁).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => Goursat.pair_mem_rectangle haL hv)
  have hq₂ : ContinuousOn q₂ (Icc b₀ b₁) :=
    (continuousOn_outgoing_horizontal_jet ha₁ hbb hY₂).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => Goursat.pair_mem_rectangle haR hv)
  have hsplit (v : ℝ) (hv : v ∈ Icc b₀ b₁) (q : OutgoingState) :
      (fderiv ℝ rectangleG (z v)) (rectangleF (z v), q) =
        A v q + h v := by
    have hdecomp : (rectangleF (z v), q) =
        (rectangleF (z v), (0 : OutgoingState)) + L q := by
      ext <;> simp [L]
    rw [hdecomp, map_add]
    exact add_comm _ _
  have hODE₁ (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt q₁ (A v (q₁ v) + h v) (Icc b₀ b₁) v := by
    have h := outgoing_horizontal_jet_vertical_equation ha₀ hbb B₁ X₁ Y₁
      hX₁ hY₁ hball₁ hjet₁ haL hv
    exact (hsplit v hv (q₁ v)) ▸ h
  have hODE₂ (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt q₂ (A v (q₂ v) + h v) (Icc b₀ b₁) v := by
    have h := outgoing_horizontal_jet_vertical_equation ha₁ hbb B₂ X₂ Y₂
      hX₂ hY₂ hball₂ hjet₂ haR hv
    have hz : (X₂ (a, v), Y₂ (a, v)) = z v := (htrace v hv).symm
    rw [hz] at h
    exact (hsplit v hv (q₂ v)) ▸ h
  have hqeq := eq_on_of_linear_vertical_edge_equations hbb.le hq₁ hq₂
    hA hODE₁ hODE₂ hcorner
  intro v hv
  obtain ⟨hX, hYv⟩ := incoming_full_jet_eq_of_common_vertical_trace
    ha₀ ha₁ hbb X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ hjet₁ hjet₂ htrace hv
  refine ⟨hX, ?_⟩
  exact full_first_jet_eq_of_coordinate_jets (hqeq v hv) hYv

/-- The corner transverse-jet equality required by the vertical seam theorem
is forced by matching tangential derivatives of the lower-edge outgoing data.
Thus no transverse seam jet is prescribed along the shared edge. -/
theorem full_first_jets_eq_on_vertical_seam_of_corner_data
    {a₀ a a₁ b₀ b₁ : ℝ}
    (ha₀ : a₀ < a) (ha₁ : a < a₁) (hbb : b₀ < b₁)
    (B₁ B₂ : SafeRectangleBox)
    (X₁ : ℝ × ℝ → IncomingState) (Y₁ : ℝ × ℝ → OutgoingState)
    (X₂ : ℝ × ℝ → IncomingState) (Y₂ : ℝ × ℝ → OutgoingState)
    (hX₁ : ContDiffOn ℝ 1 X₁ (Goursat.rectangle a₀ a b₀ b₁))
    (hY₁ : ContDiffOn ℝ 1 Y₁ (Goursat.rectangle a₀ a b₀ b₁))
    (hX₂ : ContDiffOn ℝ 1 X₂ (Goursat.rectangle a a₁ b₀ b₁))
    (hY₂ : ContDiffOn ℝ 1 Y₂ (Goursat.rectangle a a₁ b₀ b₁))
    (hball₁ : ∀ p ∈ Goursat.rectangle a₀ a b₀ b₁,
      (X₁ p, Y₁ p) ∈ B₁.carrier)
    (hball₂ : ∀ p ∈ Goursat.rectangle a a₁ b₀ b₁,
      (X₂ p, Y₂ p) ∈ B₂.carrier)
    (hjet₁ : ∀ u ∈ Icc a₀ a, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X₁ (s, v))
        (rectangleF (X₁ (u, v), Y₁ (u, v))) (Icc a₀ a) u ∧
      HasDerivWithinAt (fun t => Y₁ (u, t))
        (rectangleG (X₁ (u, v), Y₁ (u, v))) (Icc b₀ b₁) v)
    (hjet₂ : ∀ u ∈ Icc a a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X₂ (s, v))
        (rectangleF (X₂ (u, v), Y₂ (u, v))) (Icc a a₁) u ∧
      HasDerivWithinAt (fun t => Y₂ (u, t))
        (rectangleG (X₂ (u, v), Y₂ (u, v))) (Icc b₀ b₁) v)
    (htrace : ∀ v ∈ Icc b₀ b₁,
      (X₁ (a, v), Y₁ (a, v)) = (X₂ (a, v), Y₂ (a, v)))
    (q₀ : OutgoingState)
    (hcorner₁ : HasDerivWithinAt (fun s => Y₁ (s, b₀)) q₀ (Icc a₀ a) a)
    (hcorner₂ : HasDerivWithinAt (fun s => Y₂ (s, b₀)) q₀ (Icc a a₁) a) :
    ∀ v ∈ Icc b₀ b₁,
      fderivWithin ℝ X₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v) =
        fderivWithin ℝ X₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v) ∧
      fderivWithin ℝ Y₁ (Goursat.rectangle a₀ a b₀ b₁) (a, v) =
        fderivWithin ℝ Y₂ (Goursat.rectangle a a₁ b₀ b₁) (a, v) := by
  have haL : a ∈ Icc a₀ a := ⟨ha₀.le, le_rfl⟩
  have haR : a ∈ Icc a a₁ := ⟨le_rfl, ha₁.le⟩
  have hb : b₀ ∈ Icc b₀ b₁ := ⟨le_rfl, hbb.le⟩
  have hq₁ := (coordinate_derivatives_of_contDiffOn_rectangle
    ha₀ hbb hY₁ haL hb).1
  have hq₂ := (coordinate_derivatives_of_contDiffOn_rectangle
    ha₁ hbb hY₂ haR hb).1
  have hq₁eq := (hq₁.derivWithin ((uniqueDiffOn_Icc ha₀) a haL)).symm.trans
    (hcorner₁.derivWithin ((uniqueDiffOn_Icc ha₀) a haL))
  have hq₂eq := (hq₂.derivWithin ((uniqueDiffOn_Icc ha₁) a haR)).symm.trans
    (hcorner₂.derivWithin ((uniqueDiffOn_Icc ha₁) a haR))
  exact full_first_jets_eq_on_vertical_seam ha₀ ha₁ hbb B₁ B₂
    X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ hball₁ hball₂ hjet₁ hjet₂
    htrace (hq₁eq.trans hq₂eq.symm)

end ChristodoulouBV.C1Solution

end
