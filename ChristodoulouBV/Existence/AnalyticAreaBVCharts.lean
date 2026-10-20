module

public import ChristodoulouBV.Existence.AnalyticAreaBVSectionGeometry
public import ChristodoulouBV.AreaEstimates.FieldTransportJacobian
import Mathlib.Tactic

/-!
# The two unit-square area charts

These are the literal coordinate maps at pp. 1190--1191. Their
Jacobians give the corrected factors `(a-δ)²(1-y)` and `(a-δ)²y`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The two coordinate maps printed before (6.4a) and (6.4c). -/
@[expose] def areaUnitMap (k : AreaSectionPair) (a δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if k.incoming then ((a - δ) * p.1 * p.2, δ + (a - δ) * p.2)
  else ((a - δ) * p.2, a - (a - δ) * (1 - p.2) * p.1)

/-- The signed inner derivative in the source's unit chart. -/
@[expose] def areaUnitInnerFactor (k : AreaSectionPair) (a δ y : ℝ) : ℝ :=
  if k.incoming then (a - δ) * y else -((a - δ) * (1 - y))

private theorem fderiv_first_of_hasDerivAt {f : ℝ × ℝ → ℝ} {x y d : ℝ}
    (hf : DifferentiableAt ℝ f (x, y)) (hd : HasDerivAt (fun t => f (t, y)) d x) :
    (fderiv ℝ f (x, y)) (1, 0) = d := by
  have hp := (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
  have hc := hf.hasFDerivAt.comp_hasDerivAt x hp
  change HasDerivAt (fun t => f (t, y)) _ x at hc
  exact hc.unique hd

private theorem fderiv_second_of_hasDerivAt {f : ℝ × ℝ → ℝ} {x y d : ℝ}
    (hf : DifferentiableAt ℝ f (x, y)) (hd : HasDerivAt (fun t => f (x, t)) d y) :
    (fderiv ℝ f (x, y)) (0, 1) = d := by
  have hp := (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
  have hc := hf.hasFDerivAt.comp_hasDerivAt y hp
  change HasDerivAt (fun t => f (x, t)) _ y at hc
  exact hc.unique hd

/-- The determinant of each literal source chart. -/
theorem areaUnitMap_det (k : AreaSectionPair) (a δ x y : ℝ) :
    (fderiv ℝ (areaUnitMap k a δ) (x, y)).det =
      if k.incoming then (a - δ) ^ 2 * y else (a - δ) ^ 2 * (1 - y) := by
  change (fderiv ℝ (fun p => areaUnitMap k a δ p) (x, y)).det = _
  let L := a - δ
  cases hki : k.incoming with
  | false =>
    let f := fun p : ℝ × ℝ => L * p.2
    let g := fun p : ℝ × ℝ => a - L * (1 - p.2) * p.1
    have hf : DifferentiableAt ℝ f (x, y) := by dsimp only [f]; fun_prop
    have hg : DifferentiableAt ℝ g (x, y) := by dsimp only [g]; fun_prop
    have hfx : HasDerivAt (fun t => f (t, y)) 0 x := hasDerivAt_const x (L * y)
    have hfy : HasDerivAt (fun t => f (x, t)) L y := by
      simpa only [mul_one] using (hasDerivAt_id' y).const_mul L
    have hgx : HasDerivAt (fun t => g (t, y)) (-(L * (1 - y))) x := by
      simpa only [mul_one] using ((hasDerivAt_id' x).const_mul (L * (1 - y))).const_sub a
    have hgy : HasDerivAt (fun t => g (x, t)) (L * x) y := by
      have hh := ((((hasDerivAt_id' y).const_sub 1).const_mul L).mul_const x).const_sub a
      simpa only [mul_neg_one, neg_mul, neg_neg] using hh
    simp only [areaUnitMap, hki, Bool.false_eq_true, ite_false]
    change (fderiv ℝ (fun p => (f p, g p)) (x, y)).det = L ^ 2 * (1 - y)
    rw [det_fderiv_prodMk hf hg,
      fderiv_first_of_hasDerivAt hf hfx, fderiv_second_of_hasDerivAt hf hfy,
      fderiv_first_of_hasDerivAt hg hgx, fderiv_second_of_hasDerivAt hg hgy]
    ring
  | true =>
    let f := fun p : ℝ × ℝ => L * p.1 * p.2
    let g := fun p : ℝ × ℝ => δ + L * p.2
    have hf : DifferentiableAt ℝ f (x, y) := by dsimp only [f]; fun_prop
    have hg : DifferentiableAt ℝ g (x, y) := by dsimp only [g]; fun_prop
    have hfx : HasDerivAt (fun t => f (t, y)) (L * y) x := by
      simpa only [mul_one] using ((hasDerivAt_id' x).const_mul L).mul_const y
    have hfy : HasDerivAt (fun t => f (x, t)) (L * x) y := by
      simpa only [mul_one] using (hasDerivAt_id' y).const_mul (L * x)
    have hgx : HasDerivAt (fun t => g (t, y)) 0 x := hasDerivAt_const x (δ + L * y)
    have hgy : HasDerivAt (fun t => g (x, t)) L y := by
      simpa only [mul_one] using ((hasDerivAt_id' y).const_mul L).const_add δ
    simp only [areaUnitMap, hki, ite_true]
    change (fderiv ℝ (fun p => (f p, g p)) (x, y)).det = L ^ 2 * y
    rw [det_fderiv_prodMk hf hg,
      fderiv_first_of_hasDerivAt hf hfx, fderiv_second_of_hasDerivAt hf hfy,
      fderiv_first_of_hasDerivAt hg hgx, fderiv_second_of_hasDerivAt hg hgy]
    ring

/-- The absolute Jacobians are the corrected positive weights on the
open unit square. -/
theorem areaUnitMap_abs_det (k : AreaSectionPair) (a δ x : ℝ) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    |(fderiv ℝ (areaUnitMap k a δ) (x, y)).det| =
      if k.incoming then (a - δ) ^ 2 * y else (a - δ) ^ 2 * (1 - y) := by
  rw [areaUnitMap_det]
  cases hki : k.incoming with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact abs_of_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hy.2.le))
  | true =>
    simp only [ite_true]
    exact abs_of_nonneg (mul_nonneg (sq_nonneg _) hy.1.le)

end ChristodoulouBV

end
