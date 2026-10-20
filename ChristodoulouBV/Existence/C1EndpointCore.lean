module

public import ChristodoulouBV.Existence.C1EndpointCutoff
public import ChristodoulouBV.Existence.C1EndpointMeasure
public import ChristodoulouBV.Existence.C1EndpointShiftArea
public import ChristodoulouBV.Existence.C1EndpointDilation
public import ChristodoulouBV.Existence.C1EndpointResidualScale
public import ChristodoulouBV.AreaEstimates.AnalyticArea
public import ChristodoulouBV.AreaEstimates.LogTransportCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Finite C¹ developments at a maximal endpoint

The C¹ family is indexed by all positive cutoffs below the maximal parameter.
The geometric area argument uses nested terminal-coordinate tails, since the
rectangles in the printed Section 6 argument are not nested.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- The finite members available below a positive finite maximal parameter,
with the exact initial traces required by Theorem 5.1. -/
theorem endpoint_family (alpha₀ : ℝ → ℝ)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {vStar : ℝ} (hStar : ENNReal.ofReal vStar = c1MaximalParameter alpha₀) :
    0 < vStar ∧
      ∃ family : ℝ → Fields,
        ∀ v₀ ∈ Ioo (0 : ℝ) vStar,
          IsC1Solution (developmentWithInitialEdge v₀) (family v₀) ∧
          (∀ v ∈ Ioo (0 : ℝ) v₀,
            (family v₀).r 0 v = v / 2 ∧
            (family v₀).alpha 0 v = alpha₀ v) ∧
          (∀ p ∈ developmentWithInitialEdge v₀,
            (1 / 3 : ℝ) + 1 / 36 ≤ (family v₀).lam p.1 p.2 ∧
            -(2 / 3 : ℝ) + 1 / 36 ≤ (family v₀).nu p.1 p.2 ∧
            2 * (family v₀).m p.1 p.2 / (family v₀).r p.1 p.2 +
              1 / 36 ≤ (1 / 3 : ℝ)) := by
  have hpos : 0 < vStar := by
    have h := c1MaximalParameter_pos alpha₀ hα
    rw [← hStar] at h
    exact ENNReal.ofReal_pos.mp h
  let family : ℝ → Fields := fun b =>
    if hb : 0 < b ∧ b < vStar then
      c1FamilyField alpha₀ b hb.1 (by
        rw [← hStar]
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hb.2)
    else Classical.choose
      ((Classical.choose_spec (exists_c1_initial_development alpha₀ hα)).2)
  refine ⟨hpos, family, ?_⟩
  intro b hb
  have hmax : ENNReal.ofReal b < c1MaximalParameter alpha₀ := by
    rw [← hStar]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hb.2
  have hfamily : family b = c1FamilyField alpha₀ b hb.1 hmax := by
    have hb' : 0 < b ∧ b < vStar := ⟨hb.1, hb.2⟩
    simp only [family, dite_eq_left hb']
  rw [hfamily]
  obtain ⟨H, hdata⟩ := c1FamilyField_spec alpha₀ hb.1 hmax
  refine ⟨H, hdata, ?_⟩
  intro p hp
  obtain ⟨B, hbB, hBStar⟩ := exists_between hb.2
  have hB : 0 < B := hb.1.trans hbB
  let C : ℝ := (B + vStar) / 2
  have hBC : B < C := by dsimp [C]; linarith
  have hCStar : C < vStar := by dsimp [C]; linarith
  have hCmax : ENNReal.ofReal C < c1MaximalParameter alpha₀ := by
    rw [← hStar]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hCStar
  let T' := c1FamilyField alpha₀ C (hB.trans hBC) hCmax
  obtain ⟨HT', hdataT'⟩ := c1FamilyField_spec alpha₀ (hB.trans hBC) hCmax
  have hmargin := no_first_exit (alpha₀ := alpha₀) hB hBC HT' hdataT' hD b hb.1 hbB
  have hpoint : (p.1 / b, p.2 / b) ∈ developmentWithInitialEdge 1 := by
    exact ⟨div_nonneg hp.1 hb.1.le, div_lt_div_of_pos_right hp.2.1 hb.1,
      (div_lt_one hb.1).mpr hp.2.2⟩
  have hT : (Uniqueness.rescaledFields T' 0 b).lam (p.1 / b) (p.2 / b) =
      T'.lam p.1 p.2 := by
    simp only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      mul_div_cancel₀ _ hb.1.ne', zero_add]
  have hTnu : (Uniqueness.rescaledFields T' 0 b).nu (p.1 / b) (p.2 / b) =
      T'.nu p.1 p.2 := by
    simp only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      mul_div_cancel₀ _ hb.1.ne', zero_add]
  have hpT : (p.1, p.2) ∈ developmentWithInitialEdge C :=
    ⟨hp.1, hp.2.1, hp.2.2.trans (hbB.trans hBC)⟩
  obtain ⟨hrEq, _, hmEq, hlamEq, hnuEq, _, _, _, _⟩ :=
    c1_developments_agree H HT' hdata hdataT' hp hpT
  have h := hmargin.2.2 (p.1 / b, p.2 / b) hpoint
  rw [hT, hTnu, Uniqueness.rescaled_mass_ratio T' (a := 0) hb.1
    (p.1 / b) (p.2 / b)] at h
  simp only [Uniqueness.affineCoordinate, mul_div_cancel₀ _ hb.1.ne',
    zero_add] at h
  rw [← hlamEq, ← hnuEq, ← hmEq, ← hrEq] at h
  exact h

/-- A total field obtained by reading the finite member whose cutoff is the
midpoint between the point's terminal coordinate and the maximal parameter.
On the endpoint development the midpoint is a valid finite cutoff. -/
@[expose] noncomputable def endpointPatch (family : ℝ → Fields)
    (vStar : ℝ) : Fields where
  r u v := (family ((v + vStar) / 2)).r u v
  phi u v := (family ((v + vStar) / 2)).phi u v
  m u v := (family ((v + vStar) / 2)).m u v
  lam u v := (family ((v + vStar) / 2)).lam u v
  nu u v := (family ((v + vStar) / 2)).nu u v
  alpha u v := (family ((v + vStar) / 2)).alpha u v
  beta u v := (family ((v + vStar) / 2)).beta u v

/-- Uniform strict bootstrap margins pass pointwise from every finite member
to the patched field on the full open endpoint development. -/
theorem endpointPatch_geometry {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ developmentWithInitialEdge b,
        (1 / 3 : ℝ) + 1 / 36 ≤ (family b).lam p.1 p.2 ∧
        -(2 / 3 : ℝ) + 1 / 36 ≤ (family b).nu p.1 p.2 ∧
        2 * (family b).m p.1 p.2 / (family b).r p.1 p.2 +
          1 / 36 ≤ (1 / 3 : ℝ)) :
    ∀ p ∈ developmentWithInitialEdge vStar,
      (1 / 3 : ℝ) + 1 / 36 ≤
        (endpointPatch family vStar).lam p.1 p.2 ∧
      -(2 / 3 : ℝ) + 1 / 36 ≤
        (endpointPatch family vStar).nu p.1 p.2 ∧
      2 * (endpointPatch family vStar).m p.1 p.2 /
          (endpointPatch family vStar).r p.1 p.2 +
        1 / 36 ≤ (1 / 3 : ℝ) := by
  intro p hp
  let b : ℝ := (p.2 + vStar) / 2
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    constructor <;> dsimp [b] <;> linarith [hp.1, hp.2.1, hp.2.2]
  have hpb : p ∈ developmentWithInitialEdge b := by
    exact ⟨hp.1, hp.2.1, by dsimp [b]; linarith [hp.2.2]⟩
  have h := hfamily b hb p hpb
  simpa only [endpointPatch, b] using h

/-- The endpoint patch agrees in all seven primitive fields with every
finite member on that member's development. -/
theorem endpointPatch_agrees {alpha₀ : ℝ → ℝ} {vStar : ℝ}
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge b) :
    let P := endpointPatch family vStar
    P.r u v = (family b).r u v ∧
      P.phi u v = (family b).phi u v ∧
      P.m u v = (family b).m u v ∧
      P.lam u v = (family b).lam u v ∧
      P.nu u v = (family b).nu u v ∧
      P.alpha u v = (family b).alpha u v ∧
      P.beta u v = (family b).beta u v := by
  let c : ℝ := (v + vStar) / 2
  have hvpos : 0 < v := hp.1.trans_lt hp.2.1
  have hvStar : v < vStar := hp.2.2.trans hb.2
  have hvc : v < c := by dsimp [c]; linarith
  have hcStar : c < vStar := by dsimp [c]; linarith
  have hc : c ∈ Ioo (0 : ℝ) vStar := ⟨hvpos.trans hvc, hcStar⟩
  have hpc : (u, v) ∈ developmentWithInitialEdge c :=
    ⟨hp.1, hp.2.1, hvc⟩
  obtain ⟨Hb, hdataB⟩ := hfamily b hb
  obtain ⟨Hc, hdataC⟩ := hfamily c hc
  obtain ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta, _, _⟩ :=
    c1_developments_agree Hc Hb hdataC hdataB hpc hp
  exact ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta⟩

/-- The patched endpoint solution has the original normalized initial data
at every point strictly before the terminal parameter. -/
theorem endpointPatch_initial_data {alpha₀ : ℝ → ℝ} {vStar : ℝ}
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) vStar) :
    (endpointPatch family vStar).r 0 v = v / 2 ∧
      (endpointPatch family vStar).alpha 0 v = alpha₀ v := by
  let b := (v + vStar) / 2
  have hvb : v < b := by dsimp [b]; linarith [hv.2]
  have hbStar : b < vStar := by dsimp [b]; linarith [hv.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hv.1.trans hvb, hbStar⟩
  simpa only [endpointPatch, b] using (hfamily b hb).2 v ⟨hv.1, hvb⟩

/-- Initial alpha variation of the endpoint patch is bounded by the
variation of the full prescribed datum. -/
theorem endpointPatch_initial_variation_le
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    eVariationOn ((endpointPatch family vStar).alpha 0)
        (Ioo (0 : ℝ) vStar) ≤
      eVariationOn alpha₀ (Ioi (0 : ℝ)) := by
  rw [eVariationOn.congr (fun v hv =>
    (endpointPatch_initial_data hfamily hv).2)]
  exact eVariationOn.mono _ Ioo_subset_Ioi_self

/-- The complete outgoing initial logarithmic residual of the patch agrees
with every finite member on its own initial edge. The derivative is local in
the terminal coordinate, so compatibility of values suffices. -/
theorem endpointPatch_initial_log_residual_eq
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) :
    sourceOutgoingLogResidual (endpointPatch family vStar) 0 v =
      sourceOutgoingLogResidual (family b) 0 v := by
  let P := endpointPatch family vStar
  have hvalues (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) :=
    endpointPatch_agrees hfamily hb
      (show ((0 : ℝ), t) ∈ developmentWithInitialEdge b from
        ⟨le_rfl, ht.1, ht.2⟩)
  obtain ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta⟩ := hvalues v hv
  have hlog : (fun t => Real.log (P.lam 0 t)) =ᶠ[𝓝 v]
      (fun t => Real.log ((family b).lam 0 t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    rw [(hvalues t ht).2.2.2.1]
  have hderiv := hlog.deriv_eq
  dsimp only [sourceOutgoingLogResidual, sourceLogCorrection,
    Fields.theta, Fields.zeta]
  rw [hderiv, hr, hphi, hm, hlam, hnu, halpha, hbeta]

/-- The complete outgoing initial residual of the endpoint patch is
integrable up to the finite terminal parameter. The proof uses the same
uniform constant on every finite cutoff and then monotone exhaustion. -/
theorem endpointPatch_initial_residual_integrable
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    IntegrableOn
      (fun v => |sourceOutgoingLogResidual (endpointPatch family vStar) 0 v|)
      (Ioo (0 : ℝ) vStar) := by
  let P := endpointPatch family vStar
  let f : ℝ → ℝ := fun v => |sourceOutgoingLogResidual P 0 v|
  let C : ℝ≥0∞ := ENNReal.ofReal
    (108 * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal ^ 2)
  have hCut (a : ℝ) (ha : 0 ≤ a) (haStar : a < vStar) :
      IntegrableOn f (Ioo (0 : ℝ) a) ∧
      (∫⁻ v in Ioo (0 : ℝ) a, ENNReal.ofReal (f v)) ≤ C := by
    rcases lt_or_eq_of_le ha with haPos | hzero
    · obtain ⟨B, haB, hBStar⟩ := exists_between haStar
      obtain ⟨b, hBb, hbStar⟩ := exists_between hBStar
      have hB : 0 < B := haPos.trans haB
      have hb : b ∈ Ioo (0 : ℝ) vStar :=
        ⟨hB.trans hBb, hbStar⟩
      obtain ⟨H, hdata⟩ := hfamily b hb
      obtain ⟨hSInt, hSBound⟩ :=
        s6_initial_residual_cutoff_packet hB hBb H hdata hD haPos haB
      have hEq : EqOn
          (fun v => |sourceOutgoingLogResidual (family b) 0 v|)
          f (Ioo (0 : ℝ) a) := by
        intro v hv
        exact congrArg abs (endpointPatch_initial_log_residual_eq
          hfamily hb ⟨hv.1, hv.2.trans (haB.trans hBb)⟩).symm
      have hPInt : IntegrableOn f (Ioo (0 : ℝ) a) :=
        (hSInt.1.mono_set Ioo_subset_Ioc_self).congr_fun hEq measurableSet_Ioo
      have hReal : (∫ v in Ioo (0 : ℝ) a, f v) =
          ∫ v in (0 : ℝ)..a,
            |sourceOutgoingLogResidual (family b) 0 v| := by
        calc
          (∫ v in Ioo (0 : ℝ) a, f v) =
              ∫ v in Ioo (0 : ℝ) a,
                |sourceOutgoingLogResidual (family b) 0 v| := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
            exact (hEq hv).symm
          _ = ∫ v in (0 : ℝ)..a,
                |sourceOutgoingLogResidual (family b) 0 v| := by
            rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]
      have hLin : (∫⁻ v in Ioo (0 : ℝ) a,
          ENNReal.ofReal (f v)) =
          ENNReal.ofReal (∫ v in Ioo (0 : ℝ) a, f v) :=
        (ofReal_integral_eq_lintegral_ofReal hPInt
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
      refine ⟨hPInt, ?_⟩
      rw [hLin, hReal]
      exact ENNReal.ofReal_le_ofReal hSBound
    · have hzero' : a = 0 := hzero.symm
      subst a
      have hempty : Ioo (0 : ℝ) 0 = ∅ := Ioo_eq_empty_of_le le_rfl
      rw [hempty]
      exact ⟨by simp, by simp [C]⟩
  have hMeas : AEStronglyMeasurable f
      (volume.restrict (Ioo (0 : ℝ) vStar)) :=
    s6_aestronglyMeasurable_of_cutoffs f hStar
      (fun a ha haStar => (hCut a ha haStar).1.aestronglyMeasurable)
  exact s6_integrableOn_of_uniform_cutoff f hStar ENNReal.ofReal_ne_top
    hMeas (fun _ => abs_nonneg _)
    (fun a ha haStar => (hCut a ha haStar).2)

/-- Each of the four analytic areas of the endpoint patch agrees with a
finite member on any smaller strict open triangle. -/
theorem endpointPatch_area_eq_on_cutoff
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {a b : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hab : a ≤ b) :
    let P := endpointPatch family vStar
    smoothAnalyticArea (sourcePhiAlphaLamMap P) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourcePhiAlphaLamMap (family b))
          (openCoordTriangle 0 a) ∧
    smoothAnalyticArea (sourcePhiBetaNuMap P) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourcePhiBetaNuMap (family b))
          (openCoordTriangle 0 a) ∧
    smoothAnalyticArea (sourceLamPhiMap P) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourceLamPhiMap (family b))
          (openCoordTriangle 0 a) ∧
    smoothAnalyticArea (sourceNuPhiMap P) (openCoordTriangle 0 a) =
        smoothAnalyticArea (sourceNuPhiMap (family b))
          (openCoordTriangle 0 a) := by
  let P := endpointPatch family vStar
  have hOpen : IsOpen (openCoordTriangle 0 a) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hpoint (p : ℝ × ℝ) (hp : p ∈ openCoordTriangle 0 a) :
      P.r p.1 p.2 = (family b).r p.1 p.2 ∧
      P.phi p.1 p.2 = (family b).phi p.1 p.2 ∧
      P.m p.1 p.2 = (family b).m p.1 p.2 ∧
      P.lam p.1 p.2 = (family b).lam p.1 p.2 ∧
      P.nu p.1 p.2 = (family b).nu p.1 p.2 ∧
      P.alpha p.1 p.2 = (family b).alpha p.1 p.2 ∧
      P.beta p.1 p.2 = (family b).beta p.1 p.2 := by
    simp only [openCoordTriangle, mem_ofPred_eq] at hp
    exact endpointPatch_agrees hfamily hb
      ⟨hp.1.le, hp.2.1, hp.2.2.trans_le hab⟩
  have hA : EqOn (sourcePhiAlphaLamMap P)
      (sourcePhiAlphaLamMap (family b)) (openCoordTriangle 0 a) := by
    intro p hp
    obtain ⟨_, hphi, _, hlam, _, halpha, _⟩ := hpoint p hp
    simp only [sourcePhiAlphaLamMap]
    rw [hphi, hlam, halpha]
  have hB : EqOn (sourcePhiBetaNuMap P)
      (sourcePhiBetaNuMap (family b)) (openCoordTriangle 0 a) := by
    intro p hp
    obtain ⟨_, hphi, _, _, hnu, _, hbeta⟩ := hpoint p hp
    simp only [sourcePhiBetaNuMap]
    rw [hphi, hnu, hbeta]
  have hL : EqOn (sourceLamPhiMap P)
      (sourceLamPhiMap (family b)) (openCoordTriangle 0 a) := by
    intro p hp
    obtain ⟨_, hphi, _, hlam, _, _, _⟩ := hpoint p hp
    simp only [sourceLamPhiMap]
    rw [hlam, hphi]
  have hN : EqOn (sourceNuPhiMap P)
      (sourceNuPhiMap (family b)) (openCoordTriangle 0 a) := by
    intro p hp
    obtain ⟨_, hphi, _, _, hnu, _, _⟩ := hpoint p hp
    simp only [sourceNuPhiMap]
    rw [hnu, hphi]
  exact ⟨smoothAnalyticArea_eq_of_eqOn_open _ _ hOpen hA,
    smoothAnalyticArea_eq_of_eqOn_open _ _ hOpen hB,
    smoothAnalyticArea_eq_of_eqOn_open _ _ hOpen hL,
    smoothAnalyticArea_eq_of_eqOn_open _ _ hOpen hN⟩

/-- Uniform Section 4 cutoff bounds give all four finite-endpoint analytic
area bounds for the *same* patched field. The constants are independent of
the datum, the family member, and the cutoff. -/
theorem endpoint_area_bounds
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    smoothAnalyticArea (sourcePhiAlphaLamMap P)
        (openCoordTriangle 0 vStar) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
    smoothAnalyticArea (sourcePhiBetaNuMap P)
        (openCoordTriangle 0 vStar) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
    smoothAnalyticArea (sourceLamPhiMap P)
        (openCoordTriangle 0 vStar) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
    smoothAnalyticArea (sourceNuPhiMap P)
        (openCoordTriangle 0 vStar) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 := by
  let P := endpointPatch family vStar
  have hcut (a : ℝ) (ha : 0 ≤ a) (haStar : a < vStar) :
      smoothAnalyticArea (sourcePhiAlphaLamMap P)
          (openCoordTriangle 0 a) ≤
            s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourcePhiBetaNuMap P)
          (openCoordTriangle 0 a) ≤
            s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourceLamPhiMap P)
          (openCoordTriangle 0 a) ≤
            s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
      smoothAnalyticArea (sourceNuPhiMap P)
          (openCoordTriangle 0 a) ≤
            s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 := by
    rcases lt_or_eq_of_le ha with haPos | hzero
    · obtain ⟨C, haC, hCStar⟩ := exists_between haStar
      obtain ⟨B, haB, hBC⟩ := exists_between haC
      have hB : 0 < B := haPos.trans haB
      have hC : C ∈ Ioo (0 : ℝ) vStar :=
        ⟨hB.trans hBC, hCStar⟩
      obtain ⟨HC, hdataC⟩ := hfamily C hC
      obtain ⟨hAe, hBe, hLe, hNe⟩ :=
        endpointPatch_area_eq_on_cutoff hfamily hC haC.le
      obtain ⟨hA, hBarea, hL, hN⟩ :=
        s6_finite_cutoff_area_bounds_original hB hBC HC hdataC hD
          haPos haB
      exact ⟨hAe.le.trans hA, hBe.le.trans hBarea,
        hLe.le.trans hL, hNe.le.trans hN⟩
    · have hzero' : a = 0 := hzero.symm
      subst a
      have hEmpty : openCoordTriangle (0 : ℝ) 0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        simp only [openCoordTriangle, mem_ofPred_eq] at hp
        linarith [hp.1, hp.2.1, hp.2.2]
      simp only [hEmpty, measure_empty]
      exact ⟨bot_le, bot_le, bot_le, bot_le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact s6_analytic_area_exhaustion_bound _ hStar
      (fun a ha haStar => (hcut a ha haStar).1)
  · exact s6_analytic_area_exhaustion_bound _ hStar
      (fun a ha haStar => (hcut a ha haStar).2.1)
  · exact s6_analytic_area_exhaustion_bound _ hStar
      (fun a ha haStar => (hcut a ha haStar).2.2.1)
  · exact s6_analytic_area_exhaustion_bound _ hStar
      (fun a ha haStar => (hcut a ha haStar).2.2.2)

/-- The four endpoint analytic areas are finite. This supplies the precise
extra premise needed for continuity from above; it follows from the uniform
Section 4 estimates, not from countable additivity alone. -/
theorem endpoint_area_finite
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    smoothAnalyticArea (sourcePhiAlphaLamMap P)
        (openCoordTriangle 0 vStar) ≠ ∞ ∧
    smoothAnalyticArea (sourcePhiBetaNuMap P)
        (openCoordTriangle 0 vStar) ≠ ∞ ∧
    smoothAnalyticArea (sourceLamPhiMap P)
        (openCoordTriangle 0 vStar) ≠ ∞ ∧
    smoothAnalyticArea (sourceNuPhiMap P)
        (openCoordTriangle 0 vStar) ≠ ∞ := by
  let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
  have hDtop : D ≠ ∞ := by
    have hE : s4Epsilon0 ≠ ∞ := by norm_num [s4Epsilon0]
    exact ne_top_of_le_ne_top hE (hD.le.trans epsilonChosen_le_s4)
  have hCtop : s4UniversalC ≠ ∞ := by norm_num [s4UniversalC]
  have hC₂ : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top hCtop (ENNReal.pow_ne_top hDtop)
  have hC₃ : s4UniversalC * D ^ 3 ≠ ∞ :=
    ENNReal.mul_ne_top hCtop (ENNReal.pow_ne_top hDtop)
  obtain ⟨hA, hB, hL, hN⟩ := endpoint_area_bounds hStar hD hfamily
  exact ⟨ne_top_of_le_ne_top hC₂ hA,
    ne_top_of_le_ne_top hC₂ hB,
    ne_top_of_le_ne_top hC₃ hL,
    ne_top_of_le_ne_top hC₃ hN⟩

/-- The moving Section 6 wedge is contained in a terminal-coordinate tail.
This is the set inclusion needed before applying finite-measure continuity. -/
theorem s6_area_tail_geometry {a u : ℝ} (_hu : u ∈ Ioo (0 : ℝ) a) :
    (Ioo (0 : ℝ) u ×ˢ Ioo u a) ∩ openCoordTriangle 0 a ⊆
      openCoordTriangle 0 a ∩ {p : ℝ × ℝ | u < p.2} := by
  rintro p ⟨⟨_, hv⟩, hp⟩
  exact ⟨hp, hv.1⟩

/-- A finite analytic area on the full open triangle has vanishing moving
wedge mass near its terminal coordinate.  The finite-area premise is the
one missing from the printed Section 4 continuity claim. -/
theorem s6_endpoint_tails (F : ℝ × ℝ → ℝ × ℝ) {a : ℝ} (ha : 0 < a)
    (hfinite : smoothAnalyticArea F (openCoordTriangle 0 a) ≠ ∞) :
    Tendsto (fun u : ℝ => smoothAnalyticArea F
      ((Ioo (0 : ℝ) u ×ˢ Ioo u a) ∩ openCoordTriangle 0 a))
      (𝓝[<] a) (𝓝 0) := by
  let A := smoothAnalyticArea F
  let E : ℝ → Set (ℝ × ℝ) := fun u =>
    openCoordTriangle 0 a ∩ {p | u < p.2}
  have hEmeas (u : ℝ) : MeasurableSet (E u) := by
    have hT : IsOpen (openCoordTriangle 0 a) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior
    exact (hT.inter (isOpen_lt continuous_const continuous_snd)).measurableSet
  have hbound (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) a) :
      A ((Ioo (0 : ℝ) u ×ˢ Ioo u a) ∩ openCoordTriangle 0 a) ≤ A (E u) :=
    measure_mono (s6_area_tail_geometry hu)
  have htail : Tendsto (fun u => A (E u)) (𝓝[<] a) (𝓝 0) := by
    let x : ℕ → ℝ := fun n => a - 1 / ((n : ℝ) + 1)
    have hxpos (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
    have hxa (n : ℕ) : x n < a := by
      dsimp [x]
      have : 0 < 1 / ((n : ℝ) + 1) := div_pos one_pos (hxpos n)
      linarith
    have hxmono : Monotone x := by
      intro n m hnm
      dsimp [x]
      have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
      have hdiv : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (hxpos n) hnm'
      linarith
    have hEmono : Antitone (fun n : ℕ => E (x n)) := by
      intro n m hnm
      exact inter_subset_inter_right _ (fun p hp => (hxmono hnm).trans_lt hp)
    have hInter : (⋂ n : ℕ, E (x n)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpT : p ∈ openCoordTriangle 0 a := (mem_iInter.mp hp 0).1
      simp only [openCoordTriangle, mem_ofPred_eq] at hpT
      have hpa : p.2 < a := hpT.2.2
      have hdelta : 0 < a - p.2 := sub_pos.mpr hpa
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (a - p.2))
      have hn' : 1 / (a - p.2) < (n : ℝ) + 1 := by
        have : (n : ℝ) < (n : ℝ) + 1 := by linarith
        exact hn.trans this
      have hfrac : 1 / ((n : ℝ) + 1) < a - p.2 := by
        rw [div_lt_iff₀ (hxpos n)]
        have hmul := (div_lt_iff₀ hdelta).mp hn'
        nlinarith
      have hpE : x n < p.2 := (mem_iInter.mp hp n).2
      dsimp [x] at hpE
      linarith
    have hfinite0 : A (E (x 0)) ≠ ∞ :=
      ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
    have hseq : Tendsto (fun n : ℕ => A (E (x n))) atTop (𝓝 0) :=
      analytic_area_continuity F (fun n => E (x n))
        (fun n => hEmeas _) hEmono hfinite0 hInter
    refine ENNReal.tendsto_nhds_zero.mpr ?_
    intro ε hε
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
      (ENNReal.tendsto_nhds_zero.mp hseq ε hε)
    filter_upwards [Ioo_mem_nhdsLT (hxa n)] with u hu
    have hsubset : E u ⊆ E (x n) := by
      exact inter_subset_inter_right _ (fun p hp => hu.1.trans hp)
    exact (measure_mono hsubset).trans (hn n le_rfl)
  have hnonneg : ∀ᶠ u in 𝓝[<] a,
      (0 : ℝ≥0∞) ≤ A ((Ioo (0 : ℝ) u ×ˢ Ioo u a) ∩ openCoordTriangle 0 a) :=
    Filter.Eventually.of_forall (fun _ => bot_le)
  have hle : ∀ᶠ u in 𝓝[<] a,
      A ((Ioo (0 : ℝ) u ×ˢ Ioo u a) ∩ openCoordTriangle 0 a) ≤ A (E u) := by
    filter_upwards [Ioo_mem_nhdsLT ha] with u hu
    exact hbound u hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htail hnonneg hle

/-- The two analytic-area wedge terms used by the outgoing transport
identities vanish at the finite terminal parameter. -/
theorem endpoint_area_tails
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ =>
      smoothAnalyticArea (sourceLamPhiMap P)
        ((Ioo (0 : ℝ) u ×ˢ Ioo u vStar) ∩
          openCoordTriangle 0 vStar))
      (𝓝[<] vStar) (𝓝 0) ∧
    Tendsto (fun u : ℝ =>
      smoothAnalyticArea (sourcePhiBetaNuMap P)
        ((Ioo (0 : ℝ) u ×ˢ Ioo u vStar) ∩
          openCoordTriangle 0 vStar))
      (𝓝[<] vStar) (𝓝 0) := by
  obtain ⟨_, hB, hL, _⟩ := endpoint_area_finite hStar hD hfamily
  exact ⟨s6_endpoint_tails _ hStar hL,
    s6_endpoint_tails _ hStar hB⟩

/-- The two initial-edge terms omitted from the printed inference to (6.1)
and (6.2) vanish separately.  The log residual is the complete outgoing
combination used in the corrected Section 4 transport identity. -/
theorem terminal_residual_tails_at (S : Fields) {a : ℝ} (ha : 0 < a)
    (hvariation : eVariationOn (S.alpha 0) (Ioo (0 : ℝ) a) ≠ ∞)
    (hresidual : IntegrableOn
      (fun v => |sourceOutgoingLogResidual S 0 v|) (Ioo (0 : ℝ) a)) :
    Tendsto (fun u : ℝ => eVariationOn (S.alpha 0) (Ioo u a))
      (𝓝[<] a) (𝓝 0) ∧
    Tendsto (fun u : ℝ =>
      ∫ v in Ioo u a, |sourceOutgoingLogResidual S 0 v|)
      (𝓝[<] a) (𝓝 0) := by
  have hfilter : 𝓝[Ioo (0 : ℝ) a] a = 𝓝[<] a := by
    rw [show Ioo (0 : ℝ) a = Ioi 0 ∩ Iio a by ext x; simp,
      nhdsWithin_inter_of_mem
        (mem_nhdsWithin_of_mem_nhds
          (Ioi_mem_nhds ha))]
  have hBV : BoundedVariationOn (S.alpha 0) (Ioo (0 : ℝ) a) :=
    hvariation
  have hvariationRaw := hBV.tendsto_eVariationOn_Ico_zero a
  rw [hfilter] at hvariationRaw
  have hvariationTail : Tendsto
      (fun u : ℝ => eVariationOn (S.alpha 0) (Ioo u a))
      (𝓝[<] a) (𝓝 0) := by
    have hle : ∀ᶠ u in 𝓝[<] a,
        eVariationOn (S.alpha 0) (Ioo u a) ≤
          eVariationOn (S.alpha 0) (Ioo (0 : ℝ) a ∩ Ico u a) := by
      filter_upwards [Ioo_mem_nhdsLT (ha)] with u hu
      exact eVariationOn.mono _ (by
        intro v hv
        exact ⟨⟨hu.1.trans hv.1, hv.2⟩, ⟨hv.1.le, hv.2⟩⟩)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hvariationRaw
      (Filter.Eventually.of_forall fun _ => bot_le) hle
  let f : ℝ → ℝ := fun v => |sourceOutgoingLogResidual S 0 v|
  let g : ℝ → ℝ := (Ioo (0 : ℝ) a).indicator f
  have hg : Integrable g volume :=
    hresidual.integrable_indicator measurableSet_Ioo
  have hvolume : Tendsto (fun u : ℝ => volume (Ioo u a))
      (𝓝[<] a) (𝓝 0) := by
    have hsub : Tendsto (fun u : ℝ => a - u)
        (𝓝[<] a) (𝓝 0) := by
      have hid : Tendsto (fun u : ℝ => u) (𝓝[<] a) (𝓝 a) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hc : Tendsto (fun _ : ℝ => a) (𝓝[<] a) (𝓝 a) :=
        tendsto_const_nhds
      simpa only [sub_self] using hc.sub hid
    simpa only [Real.volume_Ioo, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsub
  have hraw := hg.tendsto_setIntegral_nhds_zero hvolume
  have heq : (fun u : ℝ => ∫ v in Ioo u a, g v) =ᶠ[𝓝[<] a]
      (fun u : ℝ => ∫ v in Ioo u a, f v) := by
    filter_upwards [Ioo_mem_nhdsLT (ha)] with u hu
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact Set.indicator_of_mem
      (show v ∈ Ioo (0 : ℝ) a from ⟨hu.1.trans hv.1, hv.2⟩) _
  exact ⟨hvariationTail, hraw.congr' heq⟩

/-- Both initial-edge terms in the finite-endpoint outgoing estimates tend
to zero for the patched family. The residual uses the complete outgoing
combination, while the incoming analogue elsewhere has the corrected
`-f*` sign. -/
theorem terminal_residual_tails
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u : ℝ => eVariationOn (P.alpha 0) (Ioo u vStar))
      (𝓝[<] vStar) (𝓝 0) ∧
    Tendsto (fun u : ℝ =>
      ∫ v in Ioo u vStar, |sourceOutgoingLogResidual P 0 v|)
      (𝓝[<] vStar) (𝓝 0) := by
  have hDtop : eVariationOn alpha₀ (Ioi (0 : ℝ)) ≠ ∞ := by
    have hE : s4Epsilon0 ≠ ∞ := by norm_num [s4Epsilon0]
    exact ne_top_of_le_ne_top hE (hD.le.trans epsilonChosen_le_s4)
  have hVar : eVariationOn
      ((endpointPatch family vStar).alpha 0) (Ioo (0 : ℝ) vStar) ≠ ∞ :=
    ne_top_of_le_ne_top hDtop (endpointPatch_initial_variation_le hfamily)
  exact terminal_residual_tails_at (endpointPatch family vStar) hStar hVar
    (endpointPatch_initial_residual_integrable hStar hD hfamily)

end ChristodoulouBV

end
