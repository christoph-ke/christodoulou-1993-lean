module

public import ChristodoulouBV.C1Solution.RectangleSolution
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Propagation of constraints on an off-axis rectangle

The scalar homogeneous equation used for the incoming mass defect is recorded
here with relative derivatives at both endpoints. The remaining statements
are algebraic identities for the seven-state rectangle system.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- A continuous scalar field with zero initial value and a homogeneous linear
vertical equation vanishes on the entire closed edge. -/
theorem eq_zero_of_linear_vertical_equation
    {b₀ b₁ : ℝ} (hbb : b₀ ≤ b₁)
    {e c : ℝ → ℝ}
    (he : ContinuousOn e (Icc b₀ b₁))
    (hc : ContinuousOn c (Icc b₀ b₁))
    (hderiv : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt e (c v * e v) (Icc b₀ b₁) v)
    (hinit : e b₀ = 0) :
    ∀ v ∈ Icc b₀ b₁, e v = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hM0 : 0 ≤ M :=
    (norm_nonneg (c b₀)).trans (hM b₀ ⟨le_rfl, hbb⟩)
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (K := M) (f' := fun v => c v * e v) he ?_ hinit
  · intro v hv
    have hbound := hM v ⟨hv.1, hv.2.le⟩
    calc
      ‖c v * e v‖ = ‖c v‖ * ‖e v‖ := norm_mul _ _
      _ ≤ M * ‖e v‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  · intro v hv
    exact (hderiv v ⟨hv.1, hv.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hv)

/-- If the vertical derivative of a continuous defect vanishes and its lower
edge trace is zero, then the defect vanishes on the closed rectangle. -/
theorem eq_zero_of_zero_vertical_derivative
    {b₀ b₁ : ℝ} (_hbb : b₀ ≤ b₁)
    {e : ℝ → ℝ} (he : ContinuousOn e (Icc b₀ b₁))
    (hderiv : ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt e 0 (Icc b₀ b₁) v)
    (hinit : e b₀ = 0) :
    ∀ v ∈ Icc b₀ b₁, e v = 0 := by
  have hconst := constant_of_has_deriv_right_zero he (fun v hv =>
    (hderiv v ⟨hv.1, hv.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hv))
  intro v hv
  rw [hconst v hv, hinit]

/-- If `f_v = G`, `G_u = H`, and a second field has vertical derivative
`H`, then the horizontal derivative of `f` equals that field wherever it
agrees on the lower edge. This is the rectangle mechanism for the radius and
scalar-radius incoming constraints. The mixed partial is proved by the
continuous-jet interchange theorem. -/
theorem horizontal_partial_eq_of_vertical_equations
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    {f fu G H n : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hfu : ContinuousOn (fun p : ℝ × ℝ => fu p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hn : ContinuousOn (fun p : ℝ × ℝ => n p.1 p.2)
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (hfu_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun x => f x v) (fu u v) (Icc a₀ a₁) u)
    (hG_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (f u) (G u v) (Icc b₀ b₁) v)
    (hH_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun x => G x v) (H u v) (Icc a₀ a₁) u)
    (hn_deriv : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (n u) (H u v) (Icc b₀ b₁) v)
    (hbottom : ∀ u ∈ Icc a₀ a₁, fu u b₀ = n u b₀) :
    ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁, fu u v = n u v := by
  have hmixed := hasDerivWithinAt_horizontal_partial_of_vertical_partial
    haa hbb hf hfu hG hH hfu_deriv hG_deriv hH_deriv
  intro u hu v hv
  have hfu_slice : ContinuousOn (fu u) (Icc b₀ b₁) :=
    hfu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, ht⟩)
  have hn_slice : ContinuousOn (n u) (Icc b₀ b₁) :=
    hn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hu, ht⟩)
  apply eq_of_has_deriv_right_eq
    (f' := H u)
    (fun t ht => (hmixed.2.2 u hu t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => (hn_deriv u hu t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    hfu_slice hn_slice (hbottom u hu) v hv

/-- A relative `C¹` function on a nondegenerate closed rectangle has a
continuous horizontal coordinate derivative, represented by its full first
jet even at the boundary. -/
theorem horizontal_partial_of_contDiffOn_rectangle
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a₀ a₁ ×ˢ Icc b₀ b₁)) :
    ContinuousOn
      (fun p => (fderivWithin ℝ f (Icc a₀ a₁ ×ˢ Icc b₀ b₁) p) (1, 0))
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁) ∧
    (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun x => f (x, v))
        ((fderivWithin ℝ f (Icc a₀ a₁ ×ˢ Icc b₀ b₁) (u, v)) (1, 0))
        (Icc a₀ a₁) u) := by
  let R := Icc a₀ a₁ ×ˢ Icc b₀ b₁
  have hconv : Convex ℝ R :=
    (convex_Icc a₀ a₁).prod (convex_Icc b₀ b₁)
  have hinterior : (interior R).Nonempty := by
    change (interior (Icc a₀ a₁ ×ˢ Icc b₀ b₁)).Nonempty
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    refine ⟨((a₀ + a₁) / 2, (b₀ + b₁) / 2), ?_⟩
    exact ⟨by constructor <;> linarith, by constructor <;> linarith⟩
  have hunique : UniqueDiffOn ℝ R := uniqueDiffOn_convex hconv hinterior
  constructor
  · exact (hf.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  · intro u hu v hv
    have hpath : HasDerivWithinAt (fun x : ℝ => (x, v)) (1, 0)
        (Icc a₀ a₁) u :=
      ((hasDerivAt_id' u).hasDerivWithinAt).prodMk
        ((hasDerivAt_const u v).hasDerivWithinAt)
    have hmap : MapsTo (fun x : ℝ => (x, v)) (Icc a₀ a₁) R := by
      intro x hx
      exact ⟨hx, hv⟩
    have hfd :=
      (hf.differentiableOn (by norm_num) (u, v) ⟨hu, hv⟩).hasFDerivWithinAt
    exact hfd.comp_hasDerivWithinAt u hpath hmap

/-- The horizontal jet of a `C¹` rectangle field on the lower edge is the
ordinary tangential derivative of its prescribed edge trace. -/
theorem horizontal_jet_eq_of_bottom_trace
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    {f : ℝ × ℝ → ℝ} {g g' : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a₀ a₁ ×ˢ Icc b₀ b₁))
    (htrace : ∀ u ∈ Icc a₀ a₁, f (u, b₀) = g u)
    (hg : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt g (g' u) (Icc a₀ a₁) u)
    {u : ℝ} (hu : u ∈ Icc a₀ a₁) :
    (fderivWithin ℝ f (Icc a₀ a₁ ×ˢ Icc b₀ b₁) (u, b₀)) (1, 0) = g' u := by
  have hjet := (horizontal_partial_of_contDiffOn_rectangle haa hbb hf).2
    u hu b₀ ⟨le_rfl, hbb.le⟩
  have hjet' : HasDerivWithinAt g
      ((fderivWithin ℝ f (Icc a₀ a₁ ×ˢ Icc b₀ b₁) (u, b₀)) (1, 0))
      (Icc a₀ a₁) u :=
    hjet.congr (fun x hx => (htrace x hx).symm) (htrace u hu).symm
  have hunique := (uniqueDiffOn_Icc haa) u hu
  exact (hjet'.derivWithin hunique).symm.trans ((hg u hu).derivWithin hunique)

/-- The lower-edge horizontal jet of any linear component of the outgoing
state is the corresponding component of the prescribed lower-edge derivative. -/
theorem projected_outgoing_bottom_jet_eq
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (P : OutgoingState →L[ℝ] ℝ)
    (Y : ℝ × ℝ → OutgoingState) (y₀ y₀' : ℝ → OutgoingState)
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hYedge : ∀ u ∈ Icc a₀ a₁, Y (u, b₀) = y₀ u)
    (hdy₀ : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc a₀ a₁) u)
    {u : ℝ} (hu : u ∈ Icc a₀ a₁) :
    (fderivWithin ℝ (fun p => P (Y p))
      (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) = P (y₀' u) := by
  have hP : ContDiffOn ℝ 1 (fun p => P (Y p))
      (Icc a₀ a₁ ×ˢ Icc b₀ b₁) := by
    simpa only [Goursat.rectangle, Function.comp_def] using
      P.contDiff.comp_contDiffOn hY
  have htrace (x : ℝ) (hx : x ∈ Icc a₀ a₁) :
      P (Y (x, b₀)) = P (y₀ x) := congrArg P (hYedge x hx)
  have hg (x : ℝ) (hx : x ∈ Icc a₀ a₁) :
      HasDerivWithinAt (fun t => P (y₀ t)) (P (y₀' x))
        (Icc a₀ a₁) x := by
    simpa only [Function.comp_def] using
      P.hasFDerivAt.comp_hasDerivWithinAt x (hdy₀ x hx)
  simpa only [Goursat.rectangle] using
    horizontal_jet_eq_of_bottom_trace haa hbb hP htrace hg hu

/-- The gravitational source can be written using the mass gap. -/
theorem stateGrav_eq_massGap (z : RectangleState) :
    stateGrav z = 2 * stateMass z * stateLam z * stateNu z /
      (stateRadius z * (stateRadius z - 2 * stateMass z)) := by
  rfl

/-- The incoming right-hand side is Lipschitz on a safe rectangle box, with
the derivative bound already certified by the established existence theorem. -/
theorem SafeRectangleBox.dist_rectangleF_le (B : SafeRectangleBox)
    {z z' : RectangleState} (hz : z ∈ B.carrier) (hz' : z' ∈ B.carrier) :
    dist (rectangleF z) (rectangleF z') ≤
      (B.derivBound : ℝ) * dist z z' := by
  apply Goursat.dist_nonlinearity_le_of_fderiv_le rectangleF
    B.center B.radius B.derivBound
  · intro w hw
    exact (contDiffAt_rectangleF (B.safe hw)).differentiableAt_one
  · intro w hw
    exact B.norm_fderiv_rectangleF_le hw
  · exact hz
  · exact hz'

/-- The outgoing right-hand side is Lipschitz on a safe rectangle box. -/
theorem SafeRectangleBox.dist_rectangleG_le (B : SafeRectangleBox)
    {z z' : RectangleState} (hz : z ∈ B.carrier) (hz' : z' ∈ B.carrier) :
    dist (rectangleG z) (rectangleG z') ≤
      (B.derivBound : ℝ) * dist z z' := by
  apply Goursat.dist_nonlinearity_le_of_fderiv_le rectangleG
    B.center B.radius B.derivBound
  · intro w hw
    exact (contDiffAt_rectangleG (B.safe hw)).differentiableAt_one
  · intro w hw
    exact B.norm_fderiv_rectangleG_le hw
  · exact hz
  · exact hz'

/-- The algebra behind propagation of the incoming mass constraint. Here
`d` is the horizontal mass derivative, `P` the outgoing mass density, and
`K` the gravitational source. The identity is valid at every safe state. -/
theorem mass_defect_vertical_algebra
    (m r lam nu theta zeta d : ℝ)
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0)
    (hgap : r - 2 * m ≠ 0) :
    let A := 1 - 2 * m / r
    let K := 2 * m * lam * nu / (r * (r - 2 * m))
    let P := A * theta ^ 2 / (2 * lam)
    ((-2 * d / r + 2 * m * nu / r ^ 2) * theta ^ 2 /
        (2 * lam) + A * (2 * theta * (-lam * zeta / r)) /
        (2 * lam) - A * theta ^ 2 * K / (2 * lam ^ 2)) -
      ((-2 * P / r + 2 * m * lam / r ^ 2) * zeta ^ 2 /
        (2 * nu) + A * (2 * zeta * (-nu * theta / r)) /
        (2 * nu) - A * zeta ^ 2 * K / (2 * nu ^ 2)) =
      -theta ^ 2 / (r * lam) * (d - A * zeta ^ 2 / (2 * nu)) := by
  dsimp
  field_simp
  ring

/-- On a safe off-axis rectangle, the radial incoming equation propagates
from the lower edge. The horizontal radius jet is obtained from the established
relative `C¹` rectangle solution; its vertical derivative is the common
mixed partial of `r_v = λ` and `λ_u = ν_v`. -/
theorem rectangle_radius_incoming_constraint
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
    (hbottom : ∀ u ∈ Icc a₀ a₁,
      (fderivWithin ℝ (fun p => stateRadius (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) =
        stateNu (X (u, b₀), Y (u, b₀))) :
    ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => stateRadius (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
        stateNu (X (u, v), Y (u, v)) := by
  let R := Goursat.rectangle a₀ a₁ b₀ b₁
  let rProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  let lamProj : IncomingState →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let nuProj : OutgoingState →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ)))
  have hrvalue (p : ℝ × ℝ) : rProj (Y p) = stateRadius (X p, Y p) := rfl
  have hlamvalue (p : ℝ × ℝ) : lamProj (X p) = stateLam (X p, Y p) := rfl
  have hnuvalue (p : ℝ × ℝ) : nuProj (Y p) = stateNu (X p, Y p) := rfl
  have hR : ContDiffOn ℝ 1 (fun p => stateRadius (X p, Y p)) R := by
    change ContDiffOn ℝ 1 (fun p => rProj (Y p)) R
    exact rProj.contDiff.comp_contDiffOn hY
  have hRdata := horizontal_partial_of_contDiffOn_rectangle haa hbb
    (by simpa only [R, Goursat.rectangle] using hR)
  have hXcont : ContinuousOn X R := hX.continuousOn
  have hYcont : ContinuousOn Y R := hY.continuousOn
  have hKbox : ContinuousOn stateGrav B.carrier := by
    intro z hz
    have h := (contDiffAt_rectangleF (B.safe hz)).continuousAt.fst
    simpa only [rectangleF] using h.continuousWithinAt
  have hK : ContinuousOn
      (fun p => stateGrav (X p, Y p)) R :=
    hKbox.comp (hXcont.prodMk hYcont) hball
  have hLam : ContinuousOn
      (fun p => stateLam (X p, Y p)) R := by
    change ContinuousOn (fun p => lamProj (X p)) R
    simpa only [Function.comp_def] using lamProj.continuous.comp_continuousOn hXcont
  have hNu : ContinuousOn
      (fun p => stateNu (X p, Y p)) R := by
    change ContinuousOn (fun p => nuProj (Y p)) R
    simpa only [Function.comp_def] using nuProj.continuous.comp_continuousOn hYcont
  have hR_v (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun t => stateRadius (X (u, t), Y (u, t)))
        (stateLam (X (u, v), Y (u, v))) (Icc b₀ b₁) v := by
    have h := rProj.hasFDerivAt.comp_hasDerivWithinAt v (hjet u hu v hv).2
    convert h using 1 <;> rfl
  have hLam_u (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun s => stateLam (X (s, v), Y (s, v)))
        (stateGrav (X (u, v), Y (u, v))) (Icc a₀ a₁) u := by
    have h := lamProj.hasFDerivAt.comp_hasDerivWithinAt u (hjet u hu v hv).1
    convert h using 1 <;> rfl
  have hNu_v (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun t => stateNu (X (u, t), Y (u, t)))
        (stateGrav (X (u, v), Y (u, v))) (Icc b₀ b₁) v := by
    have h := nuProj.hasFDerivAt.comp_hasDerivWithinAt v (hjet u hu v hv).2
    convert h using 1 <;> rfl
  exact horizontal_partial_eq_of_vertical_equations haa hbb
    hR.continuousOn hRdata.1 hLam hK hNu hRdata.2 hR_v hLam_u hNu_v hbottom

/-- The scalar-radius incoming equation propagates from the lower edge of a
safe off-axis rectangle. Its mixed partial is the common derivative of
`ψ_v = α` and `α_u = β_v`. -/
theorem rectangle_scalar_radius_incoming_constraint
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
    (hbottom : ∀ u ∈ Icc a₀ a₁,
      (fderivWithin ℝ (fun p => statePsi (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) =
        stateBeta (X (u, b₀), Y (u, b₀))) :
    ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => statePsi (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
        stateBeta (X (u, v), Y (u, v)) := by
  let R := Goursat.rectangle a₀ a₁ b₀ b₁
  let psiProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  let alphaProj : IncomingState →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let betaProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × (ℝ × ℝ))).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))
  have hPsi : ContDiffOn ℝ 1 (fun p => statePsi (X p, Y p)) R := by
    change ContDiffOn ℝ 1 (fun p => psiProj (Y p)) R
    exact psiProj.contDiff.comp_contDiffOn hY
  have hPsiData := horizontal_partial_of_contDiffOn_rectangle haa hbb
    (by simpa only [R, Goursat.rectangle] using hPsi)
  have hXcont : ContinuousOn X R := hX.continuousOn
  have hYcont : ContinuousOn Y R := hY.continuousOn
  have hKphiBox : ContinuousOn
      (fun z => stateGrav z * statePhi z) B.carrier := by
    intro z hz
    have h := (contDiffAt_rectangleF (B.safe hz)).continuousAt.snd
    simpa only [rectangleF] using h.continuousWithinAt
  have hKphi : ContinuousOn
      (fun p => stateGrav (X p, Y p) * statePhi (X p, Y p)) R :=
    hKphiBox.comp (hXcont.prodMk hYcont) hball
  have hAlpha : ContinuousOn
      (fun p => stateAlpha (X p, Y p)) R := by
    change ContinuousOn (fun p => alphaProj (X p)) R
    simpa only [Function.comp_def] using alphaProj.continuous.comp_continuousOn hXcont
  have hBeta : ContinuousOn
      (fun p => stateBeta (X p, Y p)) R := by
    change ContinuousOn (fun p => betaProj (Y p)) R
    simpa only [Function.comp_def] using betaProj.continuous.comp_continuousOn hYcont
  have hPsi_v (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun t => statePsi (X (u, t), Y (u, t)))
        (stateAlpha (X (u, v), Y (u, v))) (Icc b₀ b₁) v := by
    have h := psiProj.hasFDerivAt.comp_hasDerivWithinAt v (hjet u hu v hv).2
    convert h using 1 <;> rfl
  have hAlpha_u (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun s => stateAlpha (X (s, v), Y (s, v)))
        (stateGrav (X (u, v), Y (u, v)) *
          statePhi (X (u, v), Y (u, v))) (Icc a₀ a₁) u := by
    have h := alphaProj.hasFDerivAt.comp_hasDerivWithinAt u (hjet u hu v hv).1
    convert h using 1 <;> rfl
  have hBeta_v (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt (fun t => stateBeta (X (u, t), Y (u, t)))
        (stateGrav (X (u, v), Y (u, v)) *
          statePhi (X (u, v), Y (u, v))) (Icc b₀ b₁) v := by
    have h := betaProj.hasFDerivAt.comp_hasDerivWithinAt v (hjet u hu v hv).2
    convert h using 1 <;> rfl
  exact horizontal_partial_eq_of_vertical_equations haa hbb
    hPsi.continuousOn hPsiData.1 hAlpha hKphi hBeta
    hPsiData.2 hPsi_v hAlpha_u hBeta_v hbottom

/-- The first two incoming constraints follow from the two tangential
lower-edge equations for the prescribed outgoing trace `y₀`. This is the
source-facing form used with the minimal-data rectangle solution. -/
theorem rectangle_radius_scalar_radius_constraints_of_lower_edge
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (B : SafeRectangleBox)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (y₀ y₀' : ℝ → OutgoingState)
    (hX : ContDiffOn ℝ 1 X (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hball : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      (X p, Y p) ∈ B.carrier)
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    (hYedge : ∀ u ∈ Icc a₀ a₁, Y (u, b₀) = y₀ u)
    (hdy₀ : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc a₀ a₁) u)
    (hrdata : ∀ u ∈ Icc a₀ a₁, (y₀' u).2.2.2.1 = (y₀ u).1)
    (hpsidata : ∀ u ∈ Icc a₀ a₁, (y₀' u).2.2.2.2 = (y₀ u).2.1) :
    (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => stateRadius (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
        stateNu (X (u, v), Y (u, v))) ∧
    (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => statePsi (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
        stateBeta (X (u, v), Y (u, v))) := by
  let rProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  let psiProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  have hrbottom (u : ℝ) (hu : u ∈ Icc a₀ a₁) :
      (fderivWithin ℝ (fun p => stateRadius (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) =
        stateNu (X (u, b₀), Y (u, b₀)) := by
    calc
      _ = rProj (y₀' u) :=
        projected_outgoing_bottom_jet_eq haa hbb rProj Y y₀ y₀' hY
          hYedge hdy₀ hu
      _ = (y₀ u).1 := hrdata u hu
      _ = stateNu (X (u, b₀), Y (u, b₀)) := by
        rw [hYedge u hu]
        rfl
  have hpsibottom (u : ℝ) (hu : u ∈ Icc a₀ a₁) :
      (fderivWithin ℝ (fun p => statePsi (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) =
        stateBeta (X (u, b₀), Y (u, b₀)) := by
    calc
      _ = psiProj (y₀' u) :=
        projected_outgoing_bottom_jet_eq haa hbb psiProj Y y₀ y₀' hY
          hYedge hdy₀ hu
      _ = (y₀ u).2.1 := hpsidata u hu
      _ = stateBeta (X (u, b₀), Y (u, b₀)) := by
        rw [hYedge u hu]
        rfl
  exact ⟨rectangle_radius_incoming_constraint haa hbb B X Y hX hY hball
      hjet hrbottom,
    rectangle_scalar_radius_incoming_constraint haa hbb B X Y hX hY hball
      hjet hpsibottom⟩

end ChristodoulouBV.C1Solution

end
