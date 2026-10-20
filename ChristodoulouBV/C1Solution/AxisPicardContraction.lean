module

public import ChristodoulouBV.C1Solution.AxisPicardBoxNonempty
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedCoordTriangleJetDistance
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxVolterra
import Mathlib.Tactic

/-!
# Metric comparison for the axis Picard contraction

The coefficient estimates use the sum of the three coordinate suprema of a
scalar first jet. The complete Picard box inherits the product metric of
bounded continuous full jets. These lemmas relate the two norms without
changing the fixed-point space.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- A linear functional on the coordinate plane has operator norm at most
the sum of its two coordinate values. -/
theorem linearMap_norm_le_abs_axes (F : (ℝ × ℝ) →L[ℝ] ℝ) :
    ‖F‖ ≤ |F (1, 0)| + |F (0, 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound F
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
  intro p
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by
    ext <;> simp
  have h₁ : |p.1| ≤ ‖p‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_left _ _
  have h₂ : |p.2| ≤ ‖p‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_max_right _ _
  calc
    ‖F p‖ = |p.1 * F (1, 0) + p.2 * F (0, 1)| := by
      rw [hp, map_add, map_smul, map_smul]
      simp [smul_eq_mul, Real.norm_eq_abs]
    _ ≤ |p.1 * F (1, 0)| + |p.2 * F (0, 1)| := abs_add_le _ _
    _ = |p.1| * |F (1, 0)| + |p.2| * |F (0, 1)| := by
      rw [abs_mul, abs_mul]
    _ ≤ (|F (1, 0)| + |F (0, 1)|) * ‖p‖ := by
      nlinarith [mul_le_mul_of_nonneg_right h₁ (abs_nonneg (F (1, 0))),
        mul_le_mul_of_nonneg_right h₂ (abs_nonneg (F (0, 1)))]

/-- On a nondegenerate triangle, the relative derivative of an explicit
segment jet equals its stored full derivative, including on the boundary. -/
theorem ScalarJet.fderivWithin_eq_extendDerivative {a b : ℝ}
    (hab : a < b) (f : ScalarJet a b)
    (hexplicit : (convex_closedCoordTriangle a b).IsExplicitSegmentJet f.1)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    fderivWithin ℝ f.extendValue (closedCoordTriangle a b) p =
      f.extendDerivative p := by
  have hunique : UniqueDiffWithinAt ℝ (closedCoordTriangle a b) p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact
        openCoordTriangle_nonempty hab)) p hp
  exact (f.hasFDerivWithinAt_of_explicit hexplicit hp).fderivWithin hunique

/-- The outgoing stored jet is the actual relative derivative of its
value representative. -/
theorem Box.lam_fderivWithin {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    fderivWithin ℝ x.1.1.extendValue (closedCoordTriangle a b) p =
      x.1.1.extendDerivative p :=
  x.1.1.fderivWithin_eq_extendDerivative hab x.2.2.1 hp

/-- The incoming stored jet is the actual relative derivative of its
value representative. -/
theorem Box.nu_fderivWithin {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    fderivWithin ℝ x.1.2.1.extendValue (closedCoordTriangle a b) p =
      x.1.2.1.extendDerivative p :=
  x.1.2.1.fderivWithin_eq_extendDerivative hab x.2.2.2.1 hp

/-- The scalar stored jet is the actual relative derivative of its
value representative. -/
theorem Box.h_fderivWithin {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    fderivWithin ℝ x.1.2.2.extendValue (closedCoordTriangle a b) p =
      x.1.2.2.extendDerivative p :=
  x.1.2.2.fderivWithin_eq_extendDerivative hab x.2.2.2.2 hp

/-- The outgoing field has the value interval required by the removable
coefficient estimates. -/
theorem Box.lam_value_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    (1 / 4 : ℝ) ≤ x.1.1.extendValue p ∧
      x.1.1.extendValue p ≤ 3 / 4 := by
  have h := (x.2.1.1 ⟨p, hp⟩)
  simpa only [x.1.1.extendValue_eq hp] using ⟨h.1, h.2.1⟩

/-- The incoming field has the absolute value bound required by the
removable coefficient estimates. -/
theorem Box.nu_value_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    |x.1.2.1.extendValue p| ≤ 3 / 4 := by
  have h := (x.2.1.1 ⟨p, hp⟩).2.2.1
  simpa only [x.1.2.1.extendValue_eq hp] using h

/-- The scalar field has the absolute value bound in the Picard box. -/
theorem Box.h_value_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    |x.1.2.2.extendValue p| ≤ 2 * M := by
  have h := (x.2.1.1 ⟨p, hp⟩).2.2.2.1
  simpa only [x.1.2.2.extendValue_eq hp] using h

/-- Both coordinate components of the scalar field obey the Picard-box
first-jet bound. -/
theorem Box.h_coordinate_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (i : Fin 2) :
    |(x.1.2.2.extendDerivative p) (coordinateDirection i)| ≤ 2 * M := by
  have h := ((x.2.1.1 ⟨p, hp⟩).2.2.2.2 i).2.2
  simpa only [x.1.2.2.extendDerivative_eq hp] using h

/-- A scalar jet's value representative is continuous on its triangle. -/
theorem ScalarJet.continuousOn_extendValue {a b : ℝ} (f : ScalarJet a b) :
    ContinuousOn f.extendValue (closedCoordTriangle a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.1.1.continuous using 1
  funext p
  exact f.extendValue_eq p.2

/-- A scalar jet's derivative representative is continuous on its triangle. -/
theorem ScalarJet.continuousOn_extendDerivative {a b : ℝ} (f : ScalarJet a b) :
    ContinuousOn f.extendDerivative (closedCoordTriangle a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.1.2.continuous using 1
  funext p
  exact f.extendDerivative_eq p.2

/-- An explicit segment jet has the stored ordinary derivative at each
interior point of a nondegenerate triangle. -/
theorem ScalarJet.fderiv_eq_extendDerivative_interior {a b : ℝ}
    (hab : a < b) (f : ScalarJet a b)
    (hexplicit : (convex_closedCoordTriangle a b).IsExplicitSegmentJet f.1)
    {p : ℝ × ℝ} (hp : p ∈ interior (closedCoordTriangle a b)) :
    fderiv ℝ f.extendValue p = f.extendDerivative p := by
  rw [← f.fderivWithin_eq_extendDerivative hab hexplicit (interior_subset hp)]
  exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hp)).symm

/-- A boxed input's quadratic mass kernel has the precise one-input value
and coordinate-jet bounds used by the cubic Volterra coefficient box. -/
theorem Box.massSource_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    let w := x.1.1.extendValue
    let f := x.1.2.2.extendValue
    |intervalIntegral.weightedDiagonalQuadraticKernel w f p| ≤
      intervalIntegral.weightedDiagonalQuadraticValueCoefficient (3 / 4) (2 * M) *
        (p.2 - p.1) ^ 2 ∧
    |(fderivWithin ℝ (intervalIntegral.weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) (1, 0)| ≤
      intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient
        (1 / 4) (3 / 4) (2 * M) (2 * M) * (p.2 - p.1) ∧
    |(fderivWithin ℝ (intervalIntegral.weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) (0, 1)| ≤
      intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient
        (1 / 4) (3 / 4) (2 * M) (2 * M) * (p.2 - p.1) := by
  let K := closedCoordTriangle a b
  let w := x.1.1.extendValue
  let f := x.1.2.2.extendValue
  let Gw := x.1.1.extendDerivative
  let Gf := x.1.2.2.extendDerivative
  have hw : ContinuousOn w K := x.1.1.continuousOn_extendValue
  have hf : ContinuousOn f K := x.1.2.2.continuousOn_extendValue
  have hGw : ContinuousOn Gw K := x.1.1.continuousOn_extendDerivative
  have hGf : ContinuousOn Gf K := x.1.2.2.continuousOn_extendDerivative
  have hdw : DifferentiableOn ℝ w (interior K) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ f (interior K) :=
    (x.h_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ p ∈ interior K, fderiv ℝ w p = Gw p := by
    intro q hq
    exact x.1.1.fderiv_eq_extendDerivative_interior hab x.2.2.1 hq
  have hderivf : ∀ p ∈ interior K, fderiv ℝ f p = Gf p := by
    intro q hq
    exact x.1.2.2.fderiv_eq_extendDerivative_interior hab x.2.2.2.2 hq
  have hweight : ∀ q ∈ K, (1 / 4 : ℝ) ≤ w q ∧ w q ≤ 3 / 4 := by
    intro q hq
    exact x.lam_value_bounds hq
  have hGwU : ∀ q ∈ K, |Gw q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa only [Gw, coordinateDirection, ↓reduceIte] using
      x.lam_coordinate_bound hq (0 : Fin 2)
  have hGwV : ∀ q ∈ K, |Gw q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [Gw, coordinateDirection] using
      x.lam_coordinate_bound hq (1 : Fin 2)
  have hGfU : ∀ q ∈ K, |Gf q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [Gf, coordinateDirection] using
      x.h_coordinate_bound hq (0 : Fin 2)
  have hGfV : ∀ q ∈ K, |Gf q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [Gf, coordinateDirection] using
      x.h_coordinate_bound hq (1 : Fin 2)
  have hpos : 0 ≤ 2 * M := by linarith only [hM]
  exact intervalIntegral.weightedDiagonalQuadraticKernel_bounds_on_jetBox
    hab hsize hw hf hGw hGf hdw hdf hderivw hderivf hweight
    hGwU hGwV hGfU hGfV (by norm_num) hpos hpos hp

/-- A boxed input's attenuation kernel is nonnegative and has the precise
linear value and uniform coordinate-jet bounds from the quotient lemma. -/
theorem Box.attenuation_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    let w := x.1.1.extendValue
    let f := x.1.2.2.extendValue
    0 ≤ intervalIntegral.weightedDiagonalQuotientKernel w f p ∧
    intervalIntegral.weightedDiagonalQuotientKernel w f p ≤
      intervalIntegral.weightedDiagonalQuotientValueCoefficient
        (1 / 4) (3 / 4) (2 * M) * (p.2 - p.1) ∧
    |(fderivWithin ℝ (intervalIntegral.weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p) (1, 0)| ≤
      intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient
        (1 / 4) (3 / 4) (2 * M) (2 * M) (3 / 4 + 2 * M) ∧
    |(fderivWithin ℝ (intervalIntegral.weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p) (0, 1)| ≤
      intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient
        (1 / 4) (3 / 4) (2 * M) (2 * M) (3 / 4 + 2 * M) := by
  let K := closedCoordTriangle a b
  let w := x.1.1.extendValue
  let f := x.1.2.2.extendValue
  let Gw := x.1.1.extendDerivative
  let Gf := x.1.2.2.extendDerivative
  have hw : ContinuousOn w K := x.1.1.continuousOn_extendValue
  have hf : ContinuousOn f K := x.1.2.2.continuousOn_extendValue
  have hGw : ContinuousOn Gw K := x.1.1.continuousOn_extendDerivative
  have hGf : ContinuousOn Gf K := x.1.2.2.continuousOn_extendDerivative
  have hdw : DifferentiableOn ℝ w (interior K) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ f (interior K) :=
    (x.h_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ q ∈ interior K, fderiv ℝ w q = Gw q := by
    intro q hq
    exact x.1.1.fderiv_eq_extendDerivative_interior hab x.2.2.1 hq
  have hderivf : ∀ q ∈ interior K, fderiv ℝ f q = Gf q := by
    intro q hq
    exact x.1.2.2.fderiv_eq_extendDerivative_interior hab x.2.2.2.2 hq
  have hweight : ∀ q ∈ K, (1 / 4 : ℝ) ≤ w q ∧ w q ≤ 3 / 4 := by
    intro q hq
    exact x.lam_value_bounds hq
  have hGwU : ∀ q ∈ K, |Gw q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [Gw, coordinateDirection] using x.lam_coordinate_bound hq (0 : Fin 2)
  have hGwV : ∀ q ∈ K, |Gw q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [Gw, coordinateDirection] using x.lam_coordinate_bound hq (1 : Fin 2)
  have hGfU : ∀ q ∈ K, |Gf q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [Gf, coordinateDirection] using x.h_coordinate_bound hq (0 : Fin 2)
  have hGfV : ∀ q ∈ K, |Gf q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [Gf, coordinateDirection] using x.h_coordinate_bound hq (1 : Fin 2)
  have hjetf : ∀ q ∈ K, HasFDerivWithinAt f (Gf q) K q := by
    intro q hq
    exact x.1.2.2.hasFDerivWithinAt_of_explicit x.2.2.2.2 hq
  have hpos : 0 ≤ 2 * M := by linarith only [hM]
  have hval := intervalIntegral.weightedDiagonalQuotientKernel_bounds_on_jetBox
    hw hf hweight (by norm_num : (0 : ℝ) < 1 / 4) hpos hjetf hGfV hp
  have hderiv := intervalIntegral.weightedDiagonalQuotientKernel_derivative_bounds_on_jetBox
    hab hsize hw hf hGw hGf hdw hdf hderivw hderivf hweight
    hGwU hGwV hGfU hGfV (by norm_num) hpos hpos hp
  exact ⟨hval.1, hval.2, hderiv.1, hderiv.2⟩

/-- Each boxed input supplies the one-input removable cubic coefficient box.
The Volterra numerator and weighted radius are exactly those in the Picard
update. -/
@[expose] def Box.toCubicRationalTriangleBox {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M) (hsize : b - a ≤ 1) :
    intervalIntegral.CubicRationalTriangleBox a b (1 / 4) := by
  let w := x.1.1.extendValue
  let f := x.1.2.2.extendValue
  let z := x.1.2.1.extendValue
  let j₀ := intervalIntegral.weightedDiagonalQuadraticValueCoefficient (3 / 4) (2 * M)
  let j₁ := intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M)
  let k₀ := intervalIntegral.weightedDiagonalQuotientValueCoefficient
    (1 / 4) (3 / 4) (2 * M)
  let k₁ := intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M) (3 / 4 + 2 * M)
  have hw : ∀ p ∈ closedCoordTriangle a b, (1 / 4 : ℝ) ≤ w p := by
    intro p hp
    exact (x.lam_value_bounds hp).1
  have hz : ∀ u ∈ Icc a b, z (u, u) = -w (u, u) := by
    intro u hu
    exact x.nu_axis ⟨u, hu⟩
  have hMpos : 0 ≤ 2 * M := by linarith only [hM]
  have hj₀ : 0 ≤ j₀ := by
    dsimp [j₀, intervalIntegral.weightedDiagonalQuadraticValueCoefficient]
    positivity
  have hj₁ : 0 ≤ j₁ := by
    dsimp [j₁, intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeCoefficient]
    positivity
  have hk₀ : 0 ≤ k₀ := by
    dsimp [k₀, intervalIntegral.weightedDiagonalQuotientValueCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueCoefficient]
    positivity
  have hk₁ : 0 ≤ k₁ := by
    dsimp [k₁, intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient,
      intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeCoefficient]
    positivity
  have hjbound : ∀ p ∈ closedCoordTriangle a b,
      intervalIntegral.weightedDiagonalQuadraticKernel w f p ≤
        j₀ * (p.2 - p.1) ^ 2 := by
    intro p hp
    exact (le_abs_self _).trans (x.massSource_bounds hab hM hsize hp).1
  have hjubound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (intervalIntegral.weightedDiagonalQuadraticKernel w f)
        (closedCoordTriangle a b) p) (1, 0)| ≤ j₁ * (p.2 - p.1) := by
    intro p hp
    exact (x.massSource_bounds hab hM hsize hp).2.1
  have hkbound : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ intervalIntegral.weightedDiagonalQuotientKernel w f p ∧
        intervalIntegral.weightedDiagonalQuotientKernel w f p ≤
          k₀ * (p.2 - p.1) := by
    intro p hp
    exact ⟨(x.attenuation_bounds hab hM hsize hp).1,
      (x.attenuation_bounds hab hM hsize hp).2.1⟩
  have hkubound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ (intervalIntegral.weightedDiagonalQuotientKernel w f)
        (closedCoordTriangle a b) p) (1, 0)| ≤ k₁ := by
    intro p hp
    exact (x.attenuation_bounds hab hM hsize hp).2.2.1
  exact intervalIntegral.weightedDiagonalCubicRationalTriangleBox
    hab (by norm_num) x.lam_c1 x.h_c1 x.nu_c1 hw hz
    hj₀ hj₁ hk₀ hk₁ hjbound hjubound hkbound hkubound

/-- The coordinate distance used by the coefficient boxes for two scalar
jets, evaluated on their total representatives. -/
@[expose] def ScalarJet.coordinateDistance {a b : ℝ}
    (f g : ScalarJet a b) : ℝ :=
  coordinateJetDistanceOn (closedCoordTriangle a b)
    f.extendValue g.extendValue f.extendDerivative g.extendDerivative

/-- The scalar coordinate distance is at most three times the metric of the
complete scalar-jet space. -/
theorem ScalarJet.coordinateDistance_le_three_dist {a b : ℝ}
    (hab : a ≤ b) (f g : ScalarJet a b) :
    f.coordinateDistance g ≤ 3 * dist f g := by
  let K := closedCoordTriangle a b
  have hne : K.Nonempty := by
    let aa : Icc a b := ⟨a, le_refl _, hab⟩
    exact ⟨(edgePoint aa).1, (edgePoint aa).2⟩
  have hval : uniformAbsOn K (f.extendValue - g.extendValue) ≤ dist f g := by
    apply csSup_le (hne.image (fun p => |(f.extendValue - g.extendValue) p|))
    rintro z ⟨p, hp, rfl⟩
    have heval := (f.1.1 - g.1.1).norm_coe_le_norm ⟨p, hp⟩
    have hdist : dist f.1.1 g.1.1 ≤ dist f g := by
      rw [Subtype.dist_eq, Prod.dist_eq]
      exact le_max_left _ _
    calc
      |(f.extendValue - g.extendValue) p| = ‖(f.1.1 - g.1.1) ⟨p, hp⟩‖ := by
        simp [Pi.sub_apply, f.extendValue_eq hp, g.extendValue_eq hp,
          Real.norm_eq_abs]
      _ ≤ ‖f.1.1 - g.1.1‖ := heval
      _ = dist f.1.1 g.1.1 := (dist_eq_norm _ _).symm
      _ ≤ dist f g := hdist
  have hcoord (e : ℝ × ℝ) (he : ‖e‖ = 1) :
      uniformAbsOn K (fun p => f.extendDerivative p e - g.extendDerivative p e) ≤
        dist f g := by
    apply csSup_le (hne.image (fun p =>
      |f.extendDerivative p e - g.extendDerivative p e|))
    rintro z ⟨p, hp, rfl⟩
    have heval := (f.1.2 - g.1.2).norm_coe_le_norm ⟨p, hp⟩
    have hdist : dist f.1.2 g.1.2 ≤ dist f g := by
      rw [Subtype.dist_eq, Prod.dist_eq]
      exact le_max_right _ _
    calc
      |f.extendDerivative p e - g.extendDerivative p e| =
          ‖(f.1.2 - g.1.2) ⟨p, hp⟩ e‖ := by
        simp [f.extendDerivative_eq hp, g.extendDerivative_eq hp,
          Real.norm_eq_abs]
      _ ≤ ‖(f.1.2 - g.1.2) ⟨p, hp⟩‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖f.1.2 - g.1.2‖ := by
        rw [he]
        simpa using heval
      _ = dist f.1.2 g.1.2 := (dist_eq_norm _ _).symm
      _ ≤ dist f g := hdist
  have he₁ : ‖((1, 0) : ℝ × ℝ)‖ = 1 := by simp [Prod.norm_def]
  have he₂ : ‖((0, 1) : ℝ × ℝ)‖ = 1 := by simp [Prod.norm_def]
  dsimp only [ScalarJet.coordinateDistance, coordinateJetDistanceOn]
  linarith only [hval, hcoord (1, 0) he₁, hcoord (0, 1) he₂]

/-- The metric of the complete scalar-jet space is at most the coordinate
sum distance used by the coefficient estimates. -/
theorem ScalarJet.dist_le_coordinateDistance {a b : ℝ}
    (hab : a ≤ b) (f g : ScalarJet a b) :
    dist f g ≤ f.coordinateDistance g := by
  let K := closedCoordTriangle a b
  have hK : IsCompact K := isCompact_closedCoordTriangle a b
  have hne : K.Nonempty := by
    let aa : Icc a b := ⟨a, le_refl _, hab⟩
    exact ⟨(edgePoint aa).1, (edgePoint aa).2⟩
  have hf := f.continuousOn_extendValue
  have hg := g.continuousOn_extendValue
  have hF := f.continuousOn_extendDerivative
  have hG := g.continuousOn_extendDerivative
  let V := uniformAbsOn K (f.extendValue - g.extendValue)
  let U := uniformAbsOn K
    (fun p => f.extendDerivative p (1, 0) - g.extendDerivative p (1, 0))
  let W := uniformAbsOn K
    (fun p => f.extendDerivative p (0, 1) - g.extendDerivative p (0, 1))
  have hV : 0 ≤ V := uniformAbsOn_nonneg hK hne (hf.sub hg)
  have hU : 0 ≤ U := uniformAbsOn_nonneg hK hne
    ((hF.clm_apply continuousOn_const).sub (hG.clm_apply continuousOn_const))
  have hW : 0 ≤ W := uniformAbsOn_nonneg hK hne
    ((hF.clm_apply continuousOn_const).sub (hG.clm_apply continuousOn_const))
  have hval : dist f.1.1 g.1.1 ≤ V := by
    rw [dist_eq_norm]
    apply (BoundedContinuousFunction.norm_le hV).mpr
    intro p
    have h := abs_le_uniformAbsOn hK (hf.sub hg) p.2
    simpa only [Real.norm_eq_abs, BoundedContinuousFunction.coe_sub,
      Pi.sub_apply, f.extendValue_eq p.2, g.extendValue_eq p.2] using h
  have hderiv : dist f.1.2 g.1.2 ≤ U + W := by
    rw [dist_eq_norm]
    apply (BoundedContinuousFunction.norm_le (add_nonneg hU hW)).mpr
    intro p
    let F := (f.1.2 - g.1.2) p
    have h₁ := abs_le_uniformAbsOn hK
      ((hF.clm_apply continuousOn_const).sub (hG.clm_apply continuousOn_const)) p.2
      (f := fun q => f.extendDerivative q (1, 0) - g.extendDerivative q (1, 0))
    have h₂ := abs_le_uniformAbsOn hK
      ((hF.clm_apply continuousOn_const).sub (hG.clm_apply continuousOn_const)) p.2
      (f := fun q => f.extendDerivative q (0, 1) - g.extendDerivative q (0, 1))
    have h₁' : |F (1, 0)| ≤ U := by
      simpa only [F, U, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
        sub_apply, f.extendDerivative_eq p.2,
        g.extendDerivative_eq p.2] using h₁
    have h₂' : |F (0, 1)| ≤ W := by
      simpa only [F, W, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
        sub_apply, f.extendDerivative_eq p.2,
        g.extendDerivative_eq p.2] using h₂
    exact (linearMap_norm_le_abs_axes F).trans (add_le_add h₁' h₂')
  have hsum : max (dist f.1.1 g.1.1) (dist f.1.2 g.1.2) ≤ V + U + W := by
    apply max_le
    · linarith only [hval, hU, hW]
    · linarith only [hderiv, hV]
  simpa only [ScalarJet.coordinateDistance, coordinateJetDistanceOn,
    Subtype.dist_eq, Prod.dist_eq, V, U, W] using hsum

/-- The three-field coordinate distance used in all two-input coefficient
boxes, evaluated on total representatives of the stored jets. -/
@[expose] def TripleJet.coordinateDistance {a b : ℝ}
    (x y : TripleJet a b) : ℝ :=
  threeJetDistanceOn (closedCoordTriangle a b)
    x.1.extendValue y.1.extendValue
    x.2.1.extendValue y.2.1.extendValue
    x.2.2.extendValue y.2.2.extendValue
    x.1.extendDerivative y.1.extendDerivative
    x.2.1.extendDerivative y.2.1.extendDerivative
    x.2.2.extendDerivative y.2.2.extendDerivative

/-- The coefficient distance is at most three times the complete metric on
triples. -/
theorem TripleJet.coordinateDistance_le_three_dist {a b : ℝ}
    (hab : a ≤ b) (x y : TripleJet a b) :
    x.coordinateDistance y ≤ 3 * dist x y := by
  have h₁ : dist x.1 y.1 ≤ dist x y := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h₂ : dist x.2.1 y.2.1 ≤ dist x y := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : dist x.2.2 y.2.2 ≤ dist x y := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have h₁' := x.1.coordinateDistance_le_three_dist hab y.1
  have h₂' := x.2.1.coordinateDistance_le_three_dist hab y.2.1
  have h₃' := x.2.2.coordinateDistance_le_three_dist hab y.2.2
  change max (x.1.coordinateDistance y.1)
    (max (x.2.1.coordinateDistance y.2.1)
      (x.2.2.coordinateDistance y.2.2)) ≤ 3 * dist x y
  exact max_le (h₁'.trans (mul_le_mul_of_nonneg_left h₁ (by norm_num)))
    (max_le (h₂'.trans (mul_le_mul_of_nonneg_left h₂ (by norm_num)))
      (h₃'.trans (mul_le_mul_of_nonneg_left h₃ (by norm_num))))

/-- The complete metric on triples is bounded by the coefficient distance. -/
theorem TripleJet.dist_le_coordinateDistance {a b : ℝ}
    (hab : a ≤ b) (x y : TripleJet a b) :
    dist x y ≤ x.coordinateDistance y := by
  have h₁ := x.1.dist_le_coordinateDistance hab y.1
  have h₂ := x.2.1.dist_le_coordinateDistance hab y.2.1
  have h₃ := x.2.2.dist_le_coordinateDistance hab y.2.2
  rw [Prod.dist_eq, Prod.dist_eq]
  change max (dist x.1 y.1) (max (dist x.2.1 y.2.1)
    (dist x.2.2 y.2.2)) ≤
    max (x.1.coordinateDistance y.1)
      (max (x.2.1.coordinateDistance y.2.1)
        (x.2.2.coordinateDistance y.2.2))
  exact max_le_max h₁ (max_le_max h₂ h₃)

/-- On the Picard box, the coefficient distance is controlled by the
subtype metric with the same factor three. -/
theorem Box.coordinateDistance_le_three_dist {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (hab : a ≤ b)
    (x y : Box a b M g hEdge) :
    x.1.coordinateDistance y.1 ≤ 3 * dist x y := by
  simpa only [Subtype.dist_eq] using
    (x.1.coordinateDistance_le_three_dist hab y.1)

/-- The box metric is controlled by the coefficient distance. -/
theorem Box.dist_le_coordinateDistance {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (hab : a ≤ b)
    (x y : Box a b M g hEdge) :
    dist x y ≤ x.1.coordinateDistance y.1 := by
  simpa only [Subtype.dist_eq] using
    (x.1.dist_le_coordinateDistance hab y.1)

/-- The completed metric comparison costs a factor three, and the explicit
lifetime still leaves a strict Banach contraction margin. -/
theorem Ledger.metric_contract_bound (B : Ledger) {M T : ℝ}
    (hM : 1 ≤ M) (hT : 0 < T) (hsmall : T ≤ B.lifetime M) :
    3 * (B.contractCoefficient * T) ≤ 6 / 25 ∧
      3 * (B.contractCoefficient * T) < 1 / 2 := by
  have h := (B.lifetime_bounds hM hT hsmall).2.2.2.2.2.2.2
  constructor <;> linarith only [h]

end ChristodoulouBV.AxisPicard

end
