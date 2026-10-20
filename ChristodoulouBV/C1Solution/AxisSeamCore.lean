module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
public import ChristodoulouBV.C1Solution.ExtractionAxisJets
import Mathlib.Analysis.ODE.Gronwall
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Adjacent-axis seam

The transverse jets on an outgoing edge obey linear equations.  The lemmas
below isolate their uniqueness and derive the edge equations by commuting the
two coordinate derivatives on closed rectangles.
-/

public section

open Set Filter
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The horizontal component of a relative first jet on a closed region. -/
@[expose] noncomputable def horizontalJet (K : Set (ℝ × ℝ))
    (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ f K p) (1, 0)

/-- Two continuous scalar edge jets with the same linear vertical equation and
the same corner value agree on the whole closed edge. -/
theorem edge_jets_eq_of_linear_ode {a b : ℝ} (_hab : a < b)
    {x y A B : ℝ → ℝ}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hA : ContinuousOn A (Icc a b))
    (hxeq : ∀ v ∈ Ico a b,
      HasDerivWithinAt x (A v * x v + B v) (Ici v) v)
    (hyeq : ∀ v ∈ Ico a b,
      HasDerivWithinAt y (A v * y v + B v) (Ici v) v)
    (hcorner : x a = y a) : EqOn x y (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hdiff : ContinuousOn (fun v => x v - y v) (Icc a b) := hx.sub hy
  have hderiv : ∀ v ∈ Ico a b,
      HasDerivWithinAt (fun w => x w - y w)
        (A v * (x v - y v)) (Ici v) v := by
    intro v hv
    convert (hxeq v hv).sub (hyeq v hv) using 1; ring
  have hbound : ∀ v ∈ Ico a b,
      ‖A v * (x v - y v)‖ ≤ max C 0 * ‖x v - y v‖ := by
    intro v hv
    have hAv : ‖A v‖ ≤ C := hC v (mem_Icc_of_Ico hv)
    calc
      ‖A v * (x v - y v)‖ = ‖A v‖ * ‖x v - y v‖ := norm_mul _ _
      _ ≤ C * ‖x v - y v‖ := mul_le_mul_of_nonneg_right hAv (norm_nonneg _)
      _ ≤ max C 0 * ‖x v - y v‖ :=
        mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hdiff hderiv (sub_eq_zero.mpr hcorner) hbound
  intro v hv
  exact sub_eq_zero.mp (hzero v hv)

/-- A common continuous vertical source gives equal edge jets when their
corner values agree. -/
theorem edge_jets_eq_of_common_derivative {a b : ℝ} (_hab : a < b)
    {x y F : ℝ → ℝ}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxeq : ∀ v ∈ Ico a b, HasDerivWithinAt x (F v) (Ici v) v)
    (hyeq : ∀ v ∈ Ico a b, HasDerivWithinAt y (F v) (Ici v) v)
    (hcorner : x a = y a) : EqOn x y (Icc a b) :=
  eq_of_has_deriv_right_eq hxeq hyeq hx hy hcorner

/-- A continuous derivative on the open edge extends as a right derivative
to the corner.  This is the endpoint step needed for the removable axis. -/
theorem hasDerivWithinAt_edge_corner_of_open_derivative
    {a b : ℝ} (hab : a < b) {x F : ℝ → ℝ}
    (hx : ContinuousOn x (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hderiv : ∀ v ∈ Ioo a b, HasDerivAt x (F v) v) :
    HasDerivWithinAt x (F a) (Ici a) a := by
  have hdiff : DifferentiableOn ℝ x (Ioo a b) :=
    fun v hv => (hderiv v hv).differentiableAt.differentiableWithinAt
  have hxlim : ContinuousWithinAt x (Ioo a b) a :=
    (hx a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hFlim : Tendsto F (𝓝[>] a) (𝓝 (F a)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact (hF a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hderivlim : Tendsto (fun v => deriv x v) (𝓝[>] a) (𝓝 (F a)) := by
    apply hFlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with v hv
    exact (hderiv v hv).deriv.symm
  exact hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hxlim
    (Ioo_mem_nhdsGT hab) hderivlim

/-- Linear edge ODE uniqueness still holds when the differential equation is
known only away from the axis corner.  Continuity supplies its corner limit. -/
theorem edge_jets_eq_of_linear_ode_on_open {a b : ℝ} (hab : a < b)
    {x y A B : ℝ → ℝ}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hxeq : ∀ v ∈ Ioo a b,
      HasDerivAt x (A v * x v + B v) v)
    (hyeq : ∀ v ∈ Ioo a b,
      HasDerivAt y (A v * y v + B v) v)
    (hcorner : x a = y a) : EqOn x y (Icc a b) := by
  have hFx : ContinuousOn (fun v => A v * x v + B v) (Icc a b) :=
    (hA.mul hx).add hB
  have hFy : ContinuousOn (fun v => A v * y v + B v) (Icc a b) :=
    (hA.mul hy).add hB
  have hxcorner := hasDerivWithinAt_edge_corner_of_open_derivative hab hx hFx hxeq
  have hycorner := hasDerivWithinAt_edge_corner_of_open_derivative hab hy hFy hyeq
  have hxall : ∀ v ∈ Ico a b,
      HasDerivWithinAt x (A v * x v + B v) (Ici v) v := by
    intro v hv
    rcases eq_or_lt_of_le hv.1 with rfl | hva
    · exact hxcorner
    · exact (hxeq v ⟨hva, hv.2⟩).hasDerivWithinAt.mono (subset_univ _)
  have hyall : ∀ v ∈ Ico a b,
      HasDerivWithinAt y (A v * y v + B v) (Ici v) v := by
    intro v hv
    rcases eq_or_lt_of_le hv.1 with rfl | hva
    · exact hycorner
    · exact (hyeq v ⟨hva, hv.2⟩).hasDerivWithinAt.mono (subset_univ _)
  exact edge_jets_eq_of_linear_ode hab hx hy hA hxall hyall hcorner

/-- The horizontal jet of a `C¹` field satisfies the vertical edge ODE
obtained by differentiating its vertical evolution equation.  The mixed
derivative is a consequence of the closed-rectangle hypotheses. -/
theorem horizontal_jet_edge_ode_of_vertical_equation
    {u₀ u₁ a b : ℝ} (hu : u₀ < u₁) (hv : a < b)
    {f fu K Ku : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hfu : ContinuousOn (fun p : ℝ × ℝ => fu p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hK : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hKu : ContinuousOn (fun p : ℝ × ℝ => Ku p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hfu_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (fun t => f t v) (fu u v) (Icc u₀ u₁) u)
    (hK_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (f u) (K u v) (Icc a b) v)
    (hKu_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (fun t => K t v) (Ku u v) (Icc u₀ u₁) u)
    {u : ℝ} (hu_mem : u ∈ Icc u₀ u₁) :
    ∀ v ∈ Icc a b, HasDerivWithinAt (fu u) (Ku u v) (Icc a b) v := by
  exact (hasDerivWithinAt_horizontal_partial_of_vertical_partial hu hv
    hf hfu hK hKu hfu_eq hK_eq hKu_eq).2.2 u hu_mem

/-- Differentiating the linear vertical equation `f_v = A f + B` produces
the edge ODE for `f_u`.  In particular the transverse ODE is derived from
the original equation and continuous first jets, not posited separately. -/
theorem horizontal_jet_edge_ode_of_linear_vertical_equation
    {u₀ u₁ a b : ℝ} (hu : u₀ < u₁) (hv : a < b)
    {f fu A Au B Bu : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hfu : ContinuousOn (fun p : ℝ × ℝ => fu p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hAu : ContinuousOn (fun p : ℝ × ℝ => Au p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hBu : ContinuousOn (fun p : ℝ × ℝ => Bu p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b))
    (hfu_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (fun t => f t v) (fu u v) (Icc u₀ u₁) u)
    (hA_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (fun t => A t v) (Au u v) (Icc u₀ u₁) u)
    (hB_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (fun t => B t v) (Bu u v) (Icc u₀ u₁) u)
    (hfv_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (f u) (A u v * f u v + B u v) (Icc a b) v)
    {u : ℝ} (hu_mem : u ∈ Icc u₀ u₁) :
    ∀ v ∈ Icc a b,
      HasDerivWithinAt (fu u)
        (Au u v * f u v + A u v * fu u v + Bu u v) (Icc a b) v := by
  let K : ℝ → ℝ → ℝ := fun u v => A u v * f u v + B u v
  let Ku : ℝ → ℝ → ℝ := fun u v =>
    Au u v * f u v + A u v * fu u v + Bu u v
  have hK : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b) := (hA.mul hf).add hB
  have hKu : ContinuousOn (fun p : ℝ × ℝ => Ku p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc a b) := ((hAu.mul hf).add (hA.mul hfu)).add hBu
  have hKu_eq : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc a b,
      HasDerivWithinAt (fun t => K t v) (Ku u v) (Icc u₀ u₁) u := by
    intro u hu' v hv'
    convert ((hA_eq u hu' v hv').mul (hfu_eq u hu' v hv')).add
      (hB_eq u hu' v hv') using 1
  exact horizontal_jet_edge_ode_of_vertical_equation hu hv hf hfu hK hKu
    hfu_eq hfv_eq hKu_eq hu_mem

/-- The horizontal derivative of the removable gravitational product
`A λ ν Z`; here `A = 2m/r²` and `Z = (1-2m/r)⁻¹` off the axis. -/
theorem hasDerivWithinAt_grav_product
    {s : Set ℝ} {u : ℝ} {A L N Z : ℝ → ℝ} {Au Lu Nu Zu : ℝ}
    (hA : HasDerivWithinAt A Au s u)
    (hL : HasDerivWithinAt L Lu s u)
    (hN : HasDerivWithinAt N Nu s u)
    (hZ : HasDerivWithinAt Z Zu s u) :
    HasDerivWithinAt (fun t => A t * L t * N t * Z t)
      (Au * L u * N u * Z u + A u * Lu * N u * Z u +
        A u * L u * Nu * Z u + A u * L u * N u * Zu) s u := by
  convert (((hA.mul hL).mul hN).mul hZ) using 1
  simp only [Pi.mul_apply]
  ring

/-- Once the regular factors and their incoming jets agree on a seam, the
only difference in the gravitational incoming jet is linear in `ν_u`. -/
theorem grav_horizontal_jet_difference
    {A₁ A₂ Au₁ Au₂ L₁ L₂ Lu₁ Lu₂ N₁ N₂ Nu₁ Nu₂ Z₁ Z₂ Zu₁ Zu₂ : ℝ}
    (hA : A₁ = A₂) (hAu : Au₁ = Au₂)
    (hL : L₁ = L₂) (hLu : Lu₁ = Lu₂)
    (hN : N₁ = N₂) (hZ : Z₁ = Z₂) (hZu : Zu₁ = Zu₂) :
    (Au₁ * L₁ * N₁ * Z₁ + A₁ * Lu₁ * N₁ * Z₁ +
        A₁ * L₁ * Nu₁ * Z₁ + A₁ * L₁ * N₁ * Zu₁) -
      (Au₂ * L₂ * N₂ * Z₂ + A₂ * Lu₂ * N₂ * Z₂ +
        A₂ * L₂ * Nu₂ * Z₂ + A₂ * L₂ * N₂ * Zu₂) =
      A₁ * L₁ * Z₁ * (Nu₁ - Nu₂) := by
  subst A₂
  subst Au₂
  subst L₂
  subst Lu₂
  subst N₂
  subst Z₂
  subst Zu₂
  ring

/-- The diagonal identity of a `C¹` field on an adjacent axis triangle
determines the sum of its two coordinate jets, including at the lower
vertex `(a,a)`. -/
theorem adjacent_diagonal_coordinate_jets_sum_zero
    {a b : ℝ} (hab : a < b) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle a b))
    (haxis : ∀ t ∈ Icc a b, F (t, t) = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    (fderivWithin ℝ F (closedCoordTriangle a b) (t, t)) (1, 0) +
      (fderivWithin ℝ F (closedCoordTriangle a b) (t, t)) (0, 1) = 0 := by
  let K := closedCoordTriangle a b
  have hopen : ∀ s ∈ Ioo a b,
      (fderivWithin ℝ F K (s, s)) (1, 0) +
        (fderivWithin ℝ F K (s, s)) (0, 1) = 0 := by
    intro s hs
    have hsK : (s, s) ∈ K := ⟨hs.1.le, le_rfl, hs.2.le⟩
    have hdiff : DifferentiableWithinAt ℝ F K (s, s) :=
      hF.differentiableOn (by norm_num) (s, s) hsK
    have hpair : HasDerivAt (fun x : ℝ => (x, x)) (1, 1) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_id' s)
    have hnear : ∀ᶠ x in 𝓝 s, (x, x) ∈ K := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
      exact ⟨hx.1.le, le_rfl, hx.2.le⟩
    have hcomp : HasDerivAt (fun x => F (x, x))
        ((fderivWithin ℝ F K (s, s)) (1, 1)) s := by
      simpa only [Function.comp_def] using
        (hdiff.hasFDerivWithinAt.comp_hasDerivAt
          (f := fun x : ℝ => (x, x)) s hpair hnear)
    have hzero : HasDerivAt (fun x => F (x, x)) 0 s := by
      have heq : (fun x => F (x, x)) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
        filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
        exact haxis x ⟨hx.1.le, hx.2.le⟩
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
    have hvec : ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
      ext <;> norm_num
    rw [hvec, map_add] at hcomp
    exact hcomp.unique hzero
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjet : ContinuousOn (fun p => fderivWithin ℝ F K p) K :=
    hF.continuousOn_fderivWithin hunique (by norm_num)
  have hcont : ContinuousOn (fun s =>
      (fderivWithin ℝ F K (s, s)) (1, 0) +
        (fderivWithin ℝ F K (s, s)) (0, 1)) (Icc a b) :=
    ((hjet.clm_apply continuousOn_const).add
      (hjet.clm_apply continuousOn_const)).comp
      (continuous_id.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs.1, le_rfl, hs.2⟩)
  have heq : EqOn (fun s =>
      (fderivWithin ℝ F K (s, s)) (1, 0) +
        (fderivWithin ℝ F K (s, s)) (0, 1)) (fun _ => 0)
      (Icc a b) :=
    (show EqOn (fun s =>
      (fderivWithin ℝ F K (s, s)) (1, 0) +
        (fderivWithin ℝ F K (s, s)) (0, 1)) (fun _ => 0)
      (Ioo a b) from hopen).of_subset_closure hcont continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact heq ht

/-- The regular-axis relations and the two mixed reduced equations determine
`ν_u` and `β_u` at the adjacent triangle's corner.  These transverse values
are consequences of the C¹ equations and are not seam data. -/
theorem adjacent_axis_incoming_corner_jets
    {a b : ℝ} (hab : a < b)
    {lam nu alpha beta K : ℝ × ℝ → ℝ}
    (hlam : ContDiffOn ℝ 1 lam (closedCoordTriangle a b))
    (hnu : ContDiffOn ℝ 1 nu (closedCoordTriangle a b))
    (halpha : ContDiffOn ℝ 1 alpha (closedCoordTriangle a b))
    (hbeta : ContDiffOn ℝ 1 beta (closedCoordTriangle a b))
    (haxis_lam : ∀ t ∈ Icc a b, nu (t, t) = -lam (t, t))
    (haxis_alpha : ∀ t ∈ Icc a b, beta (t, t) = -alpha (t, t))
    (hKaxis : K (a, a) = 0)
    (hlam_u : (fderivWithin ℝ lam (closedCoordTriangle a b) (a, a)) (1, 0) =
      K (a, a))
    (hnu_v : (fderivWithin ℝ nu (closedCoordTriangle a b) (a, a)) (0, 1) =
      K (a, a))
    (halpha_u :
      (fderivWithin ℝ alpha (closedCoordTriangle a b) (a, a)) (1, 0) =
        K (a, a) * alpha (a, a) / lam (a, a))
    (hbeta_v :
      (fderivWithin ℝ beta (closedCoordTriangle a b) (a, a)) (0, 1) =
        K (a, a) * alpha (a, a) / lam (a, a)) :
    (fderivWithin ℝ nu (closedCoordTriangle a b) (a, a)) (1, 0) =
      -(fderivWithin ℝ lam (closedCoordTriangle a b) (a, a)) (0, 1) ∧
    (fderivWithin ℝ beta (closedCoordTriangle a b) (a, a)) (1, 0) =
      -(fderivWithin ℝ alpha (closedCoordTriangle a b) (a, a)) (0, 1) := by
  let T := closedCoordTriangle a b
  have hp : (a, a) ∈ T := ⟨le_rfl, le_rfl, hab.le⟩
  have hunique : UniqueDiffWithinAt ℝ T (a, a) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      (a, a) hp
  have hR := adjacent_diagonal_coordinate_jets_sum_zero hab (hnu.add hlam)
    (fun t ht => by rw [haxis_lam t ht]; ring) ⟨le_rfl, hab.le⟩
  have hP := adjacent_diagonal_coordinate_jets_sum_zero hab (hbeta.add halpha)
    (fun t ht => by rw [haxis_alpha t ht]; ring) ⟨le_rfl, hab.le⟩
  have hld := hlam.differentiableOn (by norm_num) (a, a) hp
  have hnd := hnu.differentiableOn (by norm_num) (a, a) hp
  have had := halpha.differentiableOn (by norm_num) (a, a) hp
  have hbd := hbeta.differentiableOn (by norm_num) (a, a) hp
  change (fderivWithin ℝ (nu + lam) T (a, a)) (1, 0) +
    (fderivWithin ℝ (nu + lam) T (a, a)) (0, 1) = 0 at hR
  change (fderivWithin ℝ (beta + alpha) T (a, a)) (1, 0) +
    (fderivWithin ℝ (beta + alpha) T (a, a)) (0, 1) = 0 at hP
  rw [fderivWithin_add hunique hnd hld] at hR
  rw [fderivWithin_add hunique hbd had] at hP
  simp only [add_apply] at hR hP
  rw [hlam_u, hnu_v, hKaxis] at hR
  rw [halpha_u, hbeta_v, hKaxis] at hP
  simp only [zero_mul, zero_div, zero_add, add_zero] at hR hP
  constructor <;> linarith

/-- On a closed coordinate triangle, the continuous incoming jet of a field
whose outgoing jet is `G` has vertical derivative `G_u` at every off-axis
point of a vertical seam.  A small closed rectangle inside the triangle
allows the mixed partial theorem to be applied without assuming `C²`. -/
theorem triangle_horizontal_jet_hasDerivAt_of_vertical_jet_eq
    {a b : ℝ} (hab : a < b) {f G : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle a b))
    (hfv : ∀ p ∈ closedCoordTriangle a b,
      (fderivWithin ℝ f (closedCoordTriangle a b) p) (0, 1) = G p)
    {s v : ℝ} (has : a ≤ s) (hsv : s < v) (hvb : v < b) :
    HasDerivAt
      (fun t => (fderivWithin ℝ f (closedCoordTriangle a b) (s, t)) (1, 0))
      ((fderivWithin ℝ G (closedCoordTriangle a b) (s, v)) (1, 0)) v := by
  let T := closedCoordTriangle a b
  let u₁ := (s + v) / 2
  let v₀ := (s + v) / 2
  let v₁ := (v + b) / 2
  have hsu₁ : s < u₁ := by dsimp [u₁]; linarith
  have hv₀v : v₀ < v := by dsimp [v₀]; linarith
  have hvv₁ : v < v₁ := by dsimp [v₁]; linarith
  have hv₁b : v₁ < b := by dsimp [v₁]; linarith
  have hR : Icc s u₁ ×ˢ Icc v₀ v₁ ⊆ T := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨has.trans hx.1, hx.2.trans (by exact hy.1), hy.2.trans hv₁b.le⟩
  have hunique : UniqueDiffOn ℝ T :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hfc : ContinuousOn f T := hf.continuousOn
  have hGc : ContinuousOn G T := hG.continuousOn
  have hfu : ContinuousOn
      (fun p => (fderivWithin ℝ f T p) (1, 0)) T :=
    (hf.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hGu : ContinuousOn
      (fun p => (fderivWithin ℝ G T p) (1, 0)) T :=
    (hG.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hslice_u {F : ℝ × ℝ → ℝ}
      (hF : ContDiffOn ℝ 1 F T)
      (x : ℝ) (hx : x ∈ Icc s u₁)
      (y : ℝ) (hy : y ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun t => F (t, y))
        ((fderivWithin ℝ F T (x, y)) (1, 0)) (Icc s u₁) x := by
    have hp : (x, y) ∈ T := hR ⟨hx, hy⟩
    have hmap : MapsTo (fun t : ℝ => (t, y)) (Icc s u₁) T :=
      fun t ht => hR ⟨ht, hy⟩
    have hpair : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
    have hFd := (hF.differentiableOn (by norm_num) (x, y) hp).hasFDerivWithinAt
    simpa only [Function.comp_def] using
      hFd.comp_hasDerivWithinAt x hpair.hasDerivWithinAt hmap
  have hslice_v (x : ℝ) (hx : x ∈ Icc s u₁)
      (y : ℝ) (hy : y ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun t => f (x, t)) (G (x, y)) (Icc v₀ v₁) y := by
    have hp : (x, y) ∈ T := hR ⟨hx, hy⟩
    have hmap : MapsTo (fun t : ℝ => (x, t)) (Icc v₀ v₁) T :=
      fun t ht => hR ⟨hx, ht⟩
    have hpair : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
    have hFd := (hf.differentiableOn (by norm_num) (x, y) hp).hasFDerivWithinAt
    have hcomp := hFd.comp_hasDerivWithinAt y hpair.hasDerivWithinAt hmap
    simpa only [Function.comp_def, hfv (x, y) hp] using hcomp
  have hODE := hasDerivWithinAt_horizontal_partial_of_vertical_partial
    hsu₁ (hv₀v.trans hvv₁)
    (hfc.mono hR) (hfu.mono hR) (hGc.mono hR) (hGu.mono hR)
    (fun x hx y hy => hslice_u hf x hx y hy)
    hslice_v (fun x hx y hy => hslice_u hG x hx y hy)
  have hs : s ∈ Icc s u₁ := ⟨le_rfl, hsu₁.le⟩
  have hv : v ∈ Icc v₀ v₁ := ⟨hv₀v.le, hvv₁.le⟩
  have h := hODE.2.2 s hs v hv
  exact h.hasDerivAt (Icc_mem_nhds hv₀v hvv₁)

/-- The horizontal jet of a product on a closed triangle is the usual
product rule, including along the boundary. -/
theorem horizontalJet_mul_on_triangle {a b : ℝ} (hab : a < b)
    {f g : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hg : ContDiffOn ℝ 1 g (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    horizontalJet (closedCoordTriangle a b) (f * g) p =
      f p * horizontalJet (closedCoordTriangle a b) g p +
        g p * horizontalJet (closedCoordTriangle a b) f p := by
  let T := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ T p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      p hp
  have hfd := hf.differentiableOn (by norm_num) p hp
  have hgd := hg.differentiableOn (by norm_num) p hp
  unfold horizontalJet
  rw [fderivWithin_mul hunique hfd hgd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp only [T]

/-- If two regular outgoing equations have the same coefficient and the same
incoming coefficient jet on a shared axis edge, their `ν_u` jets agree there.
The vertical equations and triangle C¹ regularity supply the edge ODEs. -/
theorem incoming_jet_eq_on_adjacent_axis_edge
    {a₀ a T B : ℝ} (ha₀a : a₀ ≤ a) (haT : a < T) (hTB : T ≤ B)
    {nuOld nuNew QOld QNew : ℝ × ℝ → ℝ}
    (hnuOld : ContDiffOn ℝ 1 nuOld (closedCoordTriangle a₀ B))
    (hnuNew : ContDiffOn ℝ 1 nuNew (closedCoordTriangle a T))
    (hQOld : ContDiffOn ℝ 1 QOld (closedCoordTriangle a₀ B))
    (hQNew : ContDiffOn ℝ 1 QNew (closedCoordTriangle a T))
    (hnuOld_v : ∀ p ∈ closedCoordTriangle a₀ B,
      (fderivWithin ℝ nuOld (closedCoordTriangle a₀ B) p) (0, 1) =
        QOld p * nuOld p)
    (hnuNew_v : ∀ p ∈ closedCoordTriangle a T,
      (fderivWithin ℝ nuNew (closedCoordTriangle a T) p) (0, 1) =
        QNew p * nuNew p)
    (hnu_trace : ∀ v ∈ Icc a T, nuOld (a, v) = nuNew (a, v))
    (hQ_trace : ∀ v ∈ Icc a T, QOld (a, v) = QNew (a, v))
    (hQu_trace : ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) QOld (a, v) =
        horizontalJet (closedCoordTriangle a T) QNew (a, v))
    (hcorner : horizontalJet (closedCoordTriangle a₀ B) nuOld (a, a) =
      horizontalJet (closedCoordTriangle a T) nuNew (a, a)) :
    ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) nuOld (a, v) =
        horizontalJet (closedCoordTriangle a T) nuNew (a, v) := by
  let KOld := closedCoordTriangle a₀ B
  let KNew := closedCoordTriangle a T
  have ha₀B : a₀ < B := lt_of_le_of_lt ha₀a (lt_of_lt_of_le haT hTB)
  have hXOldAll : ContinuousOn (horizontalJet KOld nuOld) KOld :=
    (hnuOld.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a₀ B)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty ha₀B))
      (by norm_num)).clm_apply continuousOn_const
  have hXNewAll : ContinuousOn (horizontalJet KNew nuNew) KNew :=
    (hnuNew.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a T)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty haT))
      (by norm_num)).clm_apply continuousOn_const
  have hXOld : ContinuousOn
      (fun v => horizontalJet KOld nuOld (a, v)) (Icc a T) :=
    hXOldAll.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨ha₀a, hv.1, hv.2.trans hTB⟩)
  have hXNew : ContinuousOn
      (fun v => horizontalJet KNew nuNew (a, v)) (Icc a T) :=
    hXNewAll.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hA : ContinuousOn (fun v => QOld (a, v)) (Icc a T) :=
    hQOld.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨ha₀a, hv.1, hv.2.trans hTB⟩)
  have hB : ContinuousOn
      (fun v => horizontalJet KOld QOld (a, v) * nuOld (a, v))
      (Icc a T) := by
    have hQu : ContinuousOn (horizontalJet KOld QOld) KOld :=
      (hQOld.continuousOn_fderivWithin
        (uniqueDiffOn_convex (convex_closedCoordTriangle a₀ B)
          (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty ha₀B))
        (by norm_num)).clm_apply continuousOn_const
    exact (hQu.mul hnuOld.continuousOn).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨ha₀a, hv.1, hv.2.trans hTB⟩)
  have hOldDeriv : ∀ v ∈ Ioo a T,
      HasDerivAt (fun t => horizontalJet KOld nuOld (a, t))
        (QOld (a, v) * horizontalJet KOld nuOld (a, v) +
          horizontalJet KOld QOld (a, v) * nuOld (a, v)) v := by
    intro v hv
    have hp : (a, v) ∈ KOld := ⟨ha₀a, hv.1.le, hv.2.le.trans hTB⟩
    have h := triangle_horizontal_jet_hasDerivAt_of_vertical_jet_eq
      ha₀B hnuOld (hQOld.mul hnuOld) (by
        intro p hp'
        exact hnuOld_v p hp') ha₀a hv.1 (hv.2.trans_le hTB)
    change HasDerivAt (fun t => horizontalJet KOld nuOld (a, t))
      (horizontalJet KOld (QOld * nuOld) (a, v)) v at h
    rw [horizontalJet_mul_on_triangle ha₀B hQOld hnuOld hp]
      at h
    convert h using 1; ring
  have hNewDeriv : ∀ v ∈ Ioo a T,
      HasDerivAt (fun t => horizontalJet KNew nuNew (a, t))
        (QOld (a, v) * horizontalJet KNew nuNew (a, v) +
          horizontalJet KOld QOld (a, v) * nuOld (a, v)) v := by
    intro v hv
    have hp : (a, v) ∈ KNew := ⟨le_rfl, hv.1.le, hv.2.le⟩
    have h := triangle_horizontal_jet_hasDerivAt_of_vertical_jet_eq
      haT hnuNew (hQNew.mul hnuNew) (by
        intro p hp'
        exact hnuNew_v p hp') le_rfl hv.1 hv.2
    change HasDerivAt (fun t => horizontalJet KNew nuNew (a, t))
      (horizontalJet KNew (QNew * nuNew) (a, v)) v at h
    rw [horizontalJet_mul_on_triangle haT hQNew hnuNew hp] at h
    rw [hQ_trace v ⟨hv.1.le, hv.2.le⟩,
      hQu_trace v ⟨hv.1.le, hv.2.le⟩,
      hnu_trace v ⟨hv.1.le, hv.2.le⟩]
    convert h using 1; ring
  exact edge_jets_eq_of_linear_ode_on_open haT hXOld hXNew hA hB
    hOldDeriv hNewDeriv hcorner

/-- Equal horizontal jets of two outgoing source terms determine equal
incoming jets on the adjacent seam from one common corner value.  This is
the comparison used for `β_u` after `K_u` has been matched. -/
theorem incoming_jet_eq_of_source_jet_eq_on_adjacent_axis_edge
    {a₀ a T B : ℝ} (ha₀a : a₀ ≤ a) (haT : a < T) (hTB : T ≤ B)
    {fOld fNew GOld GNew : ℝ × ℝ → ℝ}
    (hfOld : ContDiffOn ℝ 1 fOld (closedCoordTriangle a₀ B))
    (hfNew : ContDiffOn ℝ 1 fNew (closedCoordTriangle a T))
    (hGOld : ContDiffOn ℝ 1 GOld (closedCoordTriangle a₀ B))
    (hGNew : ContDiffOn ℝ 1 GNew (closedCoordTriangle a T))
    (hfOld_v : ∀ p ∈ closedCoordTriangle a₀ B,
      (fderivWithin ℝ fOld (closedCoordTriangle a₀ B) p) (0, 1) = GOld p)
    (hfNew_v : ∀ p ∈ closedCoordTriangle a T,
      (fderivWithin ℝ fNew (closedCoordTriangle a T) p) (0, 1) = GNew p)
    (hGu_trace : ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) GOld (a, v) =
        horizontalJet (closedCoordTriangle a T) GNew (a, v))
    (hcorner : horizontalJet (closedCoordTriangle a₀ B) fOld (a, a) =
      horizontalJet (closedCoordTriangle a T) fNew (a, a)) :
    ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) fOld (a, v) =
        horizontalJet (closedCoordTriangle a T) fNew (a, v) := by
  let KOld := closedCoordTriangle a₀ B
  let KNew := closedCoordTriangle a T
  have ha₀B : a₀ < B := lt_of_le_of_lt ha₀a (lt_of_lt_of_le haT hTB)
  have hXOldAll : ContinuousOn (horizontalJet KOld fOld) KOld :=
    (hfOld.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a₀ B)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty ha₀B))
      (by norm_num)).clm_apply continuousOn_const
  have hXNewAll : ContinuousOn (horizontalJet KNew fNew) KNew :=
    (hfNew.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a T)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty haT))
      (by norm_num)).clm_apply continuousOn_const
  have hXOld : ContinuousOn
      (fun v => horizontalJet KOld fOld (a, v)) (Icc a T) :=
    hXOldAll.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨ha₀a, hv.1, hv.2.trans hTB⟩)
  have hXNew : ContinuousOn
      (fun v => horizontalJet KNew fNew (a, v)) (Icc a T) :=
    hXNewAll.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hGOldu : ContinuousOn (horizontalJet KOld GOld) KOld :=
    (hGOld.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a₀ B)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty ha₀B))
      (by norm_num)).clm_apply continuousOn_const
  have hB : ContinuousOn
      (fun v => horizontalJet KOld GOld (a, v)) (Icc a T) :=
    hGOldu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨ha₀a, hv.1, hv.2.trans hTB⟩)
  have hOldDeriv : ∀ v ∈ Ioo a T,
      HasDerivAt (fun t => horizontalJet KOld fOld (a, t))
        (horizontalJet KOld GOld (a, v)) v := by
    intro v hv
    exact triangle_horizontal_jet_hasDerivAt_of_vertical_jet_eq
      ha₀B hfOld hGOld hfOld_v ha₀a hv.1 (hv.2.trans_le hTB)
  have hNewDeriv : ∀ v ∈ Ioo a T,
      HasDerivAt (fun t => horizontalJet KNew fNew (a, t))
        (horizontalJet KOld GOld (a, v)) v := by
    intro v hv
    have h := triangle_horizontal_jet_hasDerivAt_of_vertical_jet_eq
      haT hfNew hGNew hfNew_v le_rfl hv.1 hv.2
    rw [hGu_trace v ⟨hv.1.le, hv.2.le⟩]
    exact h
  exact edge_jets_eq_of_linear_ode_on_open haT hXOld hXNew
    (A := fun _ => 0) (B := fun v => horizontalJet KOld GOld (a, v))
    continuousOn_const hB
    (by simpa only [zero_mul, zero_add] using hOldDeriv)
    (by simpa only [zero_mul, zero_add] using hNewDeriv) hcorner

/-- The incoming jet of `β - ν φ` is determined by the incoming jets of its
three factors on the closed triangle. -/
theorem horizontalJet_sub_mul_on_triangle {a b : ℝ} (hab : a < b)
    {beta nu phi : ℝ × ℝ → ℝ}
    (hbeta : ContDiffOn ℝ 1 beta (closedCoordTriangle a b))
    (hnu : ContDiffOn ℝ 1 nu (closedCoordTriangle a b))
    (hphi : ContDiffOn ℝ 1 phi (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    horizontalJet (closedCoordTriangle a b) (beta - nu * phi) p =
      horizontalJet (closedCoordTriangle a b) beta p -
        (nu p * horizontalJet (closedCoordTriangle a b) phi p +
          phi p * horizontalJet (closedCoordTriangle a b) nu p) := by
  let T := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ T p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      p hp
  have hbd := hbeta.differentiableOn (by norm_num) p hp
  have hnd := hnu.differentiableOn (by norm_num) p hp
  have hpd := hphi.differentiableOn (by norm_num) p hp
  have hprod := horizontalJet_mul_on_triangle hab hnu hphi hp
  unfold horizontalJet at hprod ⊢
  rw [fderivWithin_sub hunique hbd (hnd.mul hpd)]
  simp only [sub_apply]
  exact congrArg (fun x => (fderivWithin ℝ beta T p) (1, 0) - x) hprod

/-- Matching values and incoming jets of `β`, `ν`, and `φ` match the
incoming jet of `ζ = β - ν φ` on the axis edge, including the corner. -/
theorem zeta_incoming_jet_eq_of_factor_jets_eq
    {a₀ a T B : ℝ} (ha₀a : a₀ ≤ a) (haT : a < T) (hTB : T ≤ B)
    {betaOld betaNew nuOld nuNew phiOld phiNew : ℝ × ℝ → ℝ}
    (hbetaOld : ContDiffOn ℝ 1 betaOld (closedCoordTriangle a₀ B))
    (hbetaNew : ContDiffOn ℝ 1 betaNew (closedCoordTriangle a T))
    (hnuOld : ContDiffOn ℝ 1 nuOld (closedCoordTriangle a₀ B))
    (hnuNew : ContDiffOn ℝ 1 nuNew (closedCoordTriangle a T))
    (hphiOld : ContDiffOn ℝ 1 phiOld (closedCoordTriangle a₀ B))
    (hphiNew : ContDiffOn ℝ 1 phiNew (closedCoordTriangle a T))
    (hnu : ∀ v ∈ Icc a T, nuOld (a, v) = nuNew (a, v))
    (hphi : ∀ v ∈ Icc a T, phiOld (a, v) = phiNew (a, v))
    (hbeta_u : ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) betaOld (a, v) =
        horizontalJet (closedCoordTriangle a T) betaNew (a, v))
    (hnu_u : ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) nuOld (a, v) =
        horizontalJet (closedCoordTriangle a T) nuNew (a, v))
    (hphi_u : ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B) phiOld (a, v) =
        horizontalJet (closedCoordTriangle a T) phiNew (a, v)) :
    ∀ v ∈ Icc a T,
      horizontalJet (closedCoordTriangle a₀ B)
        (betaOld - nuOld * phiOld) (a, v) =
        horizontalJet (closedCoordTriangle a T)
          (betaNew - nuNew * phiNew) (a, v) := by
  have ha₀B : a₀ < B := lt_of_le_of_lt ha₀a (lt_of_lt_of_le haT hTB)
  intro v hv
  have hpOld : (a, v) ∈ closedCoordTriangle a₀ B :=
    ⟨ha₀a, hv.1, hv.2.trans hTB⟩
  have hpNew : (a, v) ∈ closedCoordTriangle a T :=
    ⟨le_rfl, hv.1, hv.2⟩
  rw [horizontalJet_sub_mul_on_triangle ha₀B hbetaOld hnuOld hphiOld hpOld,
    horizontalJet_sub_mul_on_triangle haT hbetaNew hnuNew hphiNew hpNew,
    hnu v hv, hphi v hv, hbeta_u v hv, hnu_u v hv, hphi_u v hv]

end ChristodoulouBV.C1Solution

end
