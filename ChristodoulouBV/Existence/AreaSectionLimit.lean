module

public import ChristodoulouBV.Existence.AreaSectionLimitPrimitive
public import ChristodoulouBV.Existence.AreaSectionLimitRegularization
public import ChristodoulouBV.Existence.AreaSectionLimitReparametrization

/-!
# Concrete area-section limits for Theorems 6.1 and 6.2

The area-section construction uses the one shared existence subsequence and the raw Helly values.

* `lemma61_applicability` proves lower semicontinuity of each of the four
  actual pointwise Stieltjes primitives on an off-axis truncation.
* `common_section_measurability` proves measurability of the limiting
  section functionals. The smooth functionals are measurable as well.
* `area_lsc_regularization` supplies equivalent triples `(1,G,0)` with
  classical all-point differentiability, uniform BV control and a common
  countable transverse exceptional set. Constant physical extension and
  positive padding preserve every section variation exactly.
* `area_regularization_remove` and `area_regularization_liminf_remove`
  remove the padding, including after the index liminf, with no increase.
  Local finiteness is proved independently of the global area estimates.

`area_section_chart_variation_eq` identifies the physical section
functionals with the corrected weighted unit-chart functionals. It
proves the signed inner coordinate factors by affine substitution.
The outer factor `a-δ`, the analytic area carrier and its global
coordinate formulas are supplied by the analytic area and area limit estimates.
-/

public section

end
