module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyTouchingC1
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesPackage
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseJets
public import ChristodoulouBV.Uniqueness.RouteBGluingTerminalFields
import Mathlib.Tactic.Linarith

/-!
# Joining Route B incoming traces at the terminal line

The full horizontal seam jet identifies the one-sided outgoing derivatives
of scalar incoming traces at the triple corner. This is the analytic input
for joining the old and lower edge functions.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equal full relative jets on the horizontal seam give equal one-sided
vertical derivatives of traces along `u = a` at its triple corner. -/
theorem routeB_corner_vertical_trace_derivWithin_eq
    {a vBar vStar b : ℝ}
    (ha : 0 ≤ a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hStarb : vStar < b)
    {fOld fLow : ℝ × ℝ → ℝ}
    (hOldC1 : ContDiffOn ℝ 1 fOld (routeBOldRegion a vStar))
    (hLowC1 : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hJet : fderivWithin ℝ fOld (routeBOldRegion a vStar) (a, vStar) =
      fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, vStar)) :
    derivWithin (fun v => fOld (a, v)) (Icc vBar vStar) vStar =
      derivWithin (fun v => fLow (a, v)) (Icc vStar b) vStar := by
  have hpOld : (a, vStar) ∈ routeBOldRegion a vStar :=
    mem_routeBOldRegion.mpr
      ⟨ha, le_rfl, (haBar.trans hBarStar).le, le_rfl⟩
  have hpLow : (a, vStar) ∈ routeBLowerRegion a vStar b :=
    ⟨⟨ha, le_rfl⟩, ⟨le_rfl, hStarb.le⟩⟩
  have hmapOld : MapsTo (fun v : ℝ => (a, v)) (Icc vBar vStar)
      (routeBOldRegion a vStar) := by
    intro v hv
    exact mem_routeBOldRegion.mpr
      ⟨ha, le_rfl, (haBar.trans_le hv.1).le, hv.2⟩
  have hmapLow : MapsTo (fun v : ℝ => (a, v)) (Icc vStar b)
      (routeBLowerRegion a vStar b) :=
    fun v hv => ⟨⟨ha, le_rfl⟩, hv⟩
  have hpair : HasDerivAt (fun v : ℝ => (a, v)) (0, 1) vStar :=
    (hasDerivAt_const vStar a).prodMk (hasDerivAt_id' vStar)
  have hOldFd :=
    (hOldC1.differentiableOn (by norm_num) (a, vStar) hpOld).hasFDerivWithinAt
  have hLowFd :=
    (hLowC1.differentiableOn (by norm_num) (a, vStar) hpLow).hasFDerivWithinAt
  have hOldSlice : HasDerivWithinAt (fun v => fOld (a, v))
      ((fderivWithin ℝ fOld (routeBOldRegion a vStar) (a, vStar)) (0, 1))
      (Icc vBar vStar) vStar := by
    simpa only [Function.comp_def] using
      hOldFd.comp_hasDerivWithinAt vStar hpair.hasDerivWithinAt hmapOld
  have hLowSlice : HasDerivWithinAt (fun v => fLow (a, v))
      ((fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, vStar)) (0, 1))
      (Icc vStar b) vStar := by
    simpa only [Function.comp_def] using
      hLowFd.comp_hasDerivWithinAt vStar hpair.hasDerivWithinAt hmapLow
  rw [hOldSlice.derivWithin
      ((uniqueDiffOn_Icc hBarStar) vStar
        ⟨hBarStar.le, le_rfl⟩),
    hLowSlice.derivWithin
      ((uniqueDiffOn_Icc hStarb) vStar ⟨le_rfl, hStarb.le⟩)]
  exact congrArg (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (0, 1)) hJet

/-- A globally C¹ old edge and a C¹ lower field trace join when the old
edge equals the old field near the corner and the two field values and
full relative jets match there. -/
theorem exists_routeB_joined_scalar_edge_of_corner_jet
    {a vBar vStar b : ℝ}
    (ha : 0 ≤ a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hStarb : vStar < b)
    {gOld : ℝ → ℝ} {fOld fLow : ℝ × ℝ → ℝ}
    (hgOld : ContDiff ℝ 1 gOld)
    (hOldC1 : ContDiffOn ℝ 1 fOld (routeBOldRegion a vStar))
    (hLowC1 : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hOldTrace : ∀ v ∈ Icc vBar vStar, gOld v = fOld (a, v))
    (hValue : fOld (a, vStar) = fLow (a, vStar))
    (hJet : fderivWithin ℝ fOld (routeBOldRegion a vStar) (a, vStar) =
      fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, vStar)) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 1 G ∧
      (∀ v ∈ Icc a vStar, G v = gOld v) ∧
      ∀ v ∈ Icc vStar b, G v = fLow (a, v) := by
  have hLowTrace : ContDiffOn ℝ 1 (fun v => fLow (a, v))
      (Icc vStar b) :=
    hLowC1.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun v hv => ⟨⟨ha, le_rfl⟩, hv⟩)
  have hValue' : gOld vStar = fLow (a, vStar) :=
    (hOldTrace vStar ⟨hBarStar.le, le_rfl⟩).trans hValue
  have hDerivOld : derivWithin gOld (Icc vBar vStar) vStar =
      derivWithin (fun v => fOld (a, v)) (Icc vBar vStar) vStar := by
    apply derivWithin_congr (fun v hv => hOldTrace v hv)
    exact hOldTrace vStar ⟨hBarStar.le, le_rfl⟩
  have hDerivCorner := routeB_corner_vertical_trace_derivWithin_eq
    ha haBar hBarStar hStarb hOldC1 hLowC1 hJet
  have hDerivOldGlobal : deriv gOld vStar =
      derivWithin gOld (Icc vBar vStar) vStar := by
    exact ((hgOld.differentiable (by norm_num) vStar).hasDerivAt.hasDerivWithinAt)
      |>.derivWithin ((uniqueDiffOn_Icc hBarStar) vStar
        ⟨hBarStar.le, le_rfl⟩) |>.symm
  have hderiv : derivWithin gOld (Icc a vStar) vStar =
      derivWithin (fun v => fLow (a, v)) (Icc vStar b) vStar := by
    have hLeft : derivWithin gOld (Icc a vStar) vStar = deriv gOld vStar :=
      ((hgOld.differentiable (by norm_num) vStar).hasDerivAt.hasDerivWithinAt)
        |>.derivWithin ((uniqueDiffOn_Icc (haBar.trans hBarStar)) vStar
          ⟨(haBar.trans hBarStar).le, le_rfl⟩)
    exact hLeft.trans (hDerivOldGlobal.trans
      (hDerivOld.trans hDerivCorner))
  exact exists_contDiff_one_of_touching_compact_intervals
    (haBar.trans hBarStar) hStarb hgOld.contDiffOn hLowTrace
    hValue' hderiv

/-- The lower cover's full horizontal seam joins the old expansion and
outgoing amplitude to the new lower traces on `u = a`. Both joined functions
are globally C¹ and retain the construction's characteristic values below
`vStar`. -/
theorem OffAxisTerminalC1Packet.exists_routeB_joined_lam_alpha_edge
    {alpha₀ : ℝ → ℝ} {a vBar vStar b : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hStarb : vStar < b)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (SOld SLow : Fields)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hOldTop : RouteBFieldsEqOn SOld P.terminalFields
      (routeBLowerRegion a vBar vStar))
    (hOldLow : RouteBFieldsEqOn SOld SLow
      (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b))
    (hOldLowJet : RouteBFieldsJetEqOn SOld SLow
      (routeBOldRegion a vStar) (routeBLowerRegion a vStar b)) :
    ∃ G A : ℝ → ℝ,
      ContDiff ℝ 1 G ∧ ContDiff ℝ 1 A ∧
      (∀ v ∈ Icc a vStar,
        G v = P.g v ∧ A v = P.g v * P.hEdge v) ∧
      (∀ v ∈ Icc vStar b,
        G v = SLow.lam a v ∧ A v = SLow.alpha a v) := by
  let G₀ := intervalC1Extension P.g a vStar
  let H₀ := intervalC1Extension P.hEdge a vStar
  let A₀ := fun v => G₀ v * H₀ v
  have haStar : a < vStar := haBar.trans hBarStar
  have hG₀ : ContDiff ℝ 1 G₀ := intervalC1Extension_c1 haStar P.g_c1
  have hH₀ : ContDiff ℝ 1 H₀ := intervalC1Extension_c1 haStar P.h_c1
  have hA₀ : ContDiff ℝ 1 A₀ := hG₀.mul hH₀
  have htop (v : ℝ) (hv : v ∈ Icc vBar vStar) :
      (a, v) ∈ routeBLowerRegion a vBar vStar :=
    ⟨⟨ha.le, le_rfl⟩, hv⟩
  have hGTrace : ∀ v ∈ Icc vBar vStar, G₀ v = SOld.lam a v := by
    intro v hv
    have hval := hOldTop .expansion (htop v hv)
    change SOld.lam a v = P.state.lam (a, v) at hval
    change intervalC1Extension P.g a vStar v = SOld.lam a v
    rw [intervalC1Extension_eq ⟨haBar.le.trans hv.1, hv.2⟩,
      (P.top_match v hv).1]
    exact hval.symm
  have hATrace : ∀ v ∈ Icc vBar vStar, A₀ v = SOld.alpha a v := by
    intro v hv
    have hval := hOldTop .outgoing (htop v hv)
    change SOld.alpha a v = P.state.alpha (a, v) at hval
    change intervalC1Extension P.g a vStar v *
      intervalC1Extension P.hEdge a vStar v = SOld.alpha a v
    rw [intervalC1Extension_eq ⟨haBar.le.trans hv.1, hv.2⟩,
      intervalC1Extension_eq ⟨haBar.le.trans hv.1, hv.2⟩]
    obtain ⟨hl, hh, _⟩ := P.top_match v hv
    rw [hl, hh]
    exact (P.alpha_eq_lam_mul_quotient ha haBar hBarStar hfamily
      ⟨ha.le, le_rfl⟩ hv).symm.trans hval.symm
  have hpOld : (a, vStar) ∈ routeBOldRegion a vStar :=
    mem_routeBOldRegion.mpr ⟨ha.le, le_rfl, haStar.le, le_rfl⟩
  have hpLow : (a, vStar) ∈ routeBLowerRegion a vStar b :=
    ⟨⟨ha.le, le_rfl⟩, ⟨le_rfl, hStarb.le⟩⟩
  have hpInter : (a, vStar) ∈
      routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b :=
    ⟨hpOld, hpLow⟩
  have hGvalue : SOld.lam a vStar = SLow.lam a vStar := by
    have h := hOldLow .expansion hpInter
    exact h
  have hAvalue : SOld.alpha a vStar = SLow.alpha a vStar := by
    have h := hOldLow .outgoing hpInter
    exact h
  have hGjet :
      fderivWithin ℝ (fun p : ℝ × ℝ => SOld.lam p.1 p.2)
          (routeBOldRegion a vStar) (a, vStar) =
        fderivWithin ℝ (fun p : ℝ × ℝ => SLow.lam p.1 p.2)
          (routeBLowerRegion a vStar b) (a, vStar) :=
    hOldLowJet .expansion hpInter
  have hAjet :
      fderivWithin ℝ (fun p : ℝ × ℝ => SOld.alpha p.1 p.2)
          (routeBOldRegion a vStar) (a, vStar) =
        fderivWithin ℝ (fun p : ℝ × ℝ => SLow.alpha p.1 p.2)
          (routeBLowerRegion a vStar b) (a, vStar) :=
    hOldLowJet .outgoing hpInter
  obtain ⟨G, hG, hGOld, hGLow⟩ :=
    exists_routeB_joined_scalar_edge_of_corner_jet
      ha.le haBar hBarStar hStarb hG₀
      (hOldC1 .expansion) (hLowC1 .expansion)
      hGTrace hGvalue hGjet
  obtain ⟨A, hA, hAOld, hALow⟩ :=
    exists_routeB_joined_scalar_edge_of_corner_jet
      ha.le haBar hBarStar hStarb hA₀
      (hOldC1 .outgoing) (hLowC1 .outgoing)
      hATrace hAvalue hAjet
  refine ⟨G, A, hG, hA, ?_, ?_⟩
  · intro v hv
    have hG₀eq : G₀ v = P.g v := intervalC1Extension_eq hv
    have hH₀eq : H₀ v = P.hEdge v := intervalC1Extension_eq hv
    exact ⟨(hGOld v hv).trans hG₀eq,
      (hAOld v hv).trans (by
        change G₀ v * H₀ v = P.g v * P.hEdge v
        rw [hG₀eq, hH₀eq])⟩
  · intro v hv
    exact ⟨hGLow v hv, hALow v hv⟩

/-- Positive joined expansion converts the joined outgoing amplitude into
globally C¹ physical edge data `g = λ` and `h = α/λ`. The old and lower
traces are reproduced exactly on their respective closed intervals. -/
theorem OffAxisTerminalC1Packet.exists_routeB_joined_physical_edge
    {alpha₀ : ℝ → ℝ} {a vBar vStar b c : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hStarb : vStar < b) (hc : 0 < c)
    (hfloor : ∀ v ∈ Icc a vStar, c ≤ P.g v)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (SOld SLow : Fields)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hOldTop : RouteBFieldsEqOn SOld P.terminalFields
      (routeBLowerRegion a vBar vStar))
    (hOldLow : RouteBFieldsEqOn SOld SLow
      (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b))
    (hOldLowJet : RouteBFieldsJetEqOn SOld SLow
      (routeBOldRegion a vStar) (routeBLowerRegion a vStar b))
    (hLowLam : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < SLow.lam p.1 p.2) :
    ∃ g h : ℝ → ℝ,
      ContDiff ℝ 1 g ∧ ContDiff ℝ 1 h ∧
      (∀ v ∈ Icc a b, 0 < g v) ∧
      (∀ v ∈ Icc a vStar, g v = P.g v ∧ h v = P.hEdge v) ∧
      (∀ v ∈ Icc vStar b,
        g v = SLow.lam a v ∧
        h v = SLow.alpha a v / SLow.lam a v) := by
  obtain ⟨g, A, hg, hA, hOld, hLow⟩ :=
    P.exists_routeB_joined_lam_alpha_edge ha haBar hBarStar hStarb
      hfamily SOld SLow hOldC1 hLowC1 hOldTop hOldLow hOldLowJet
  have hab : a < b := (haBar.trans hBarStar).trans hStarb
  have hgpos : ∀ v ∈ Icc a b, 0 < g v := by
    intro v hv
    by_cases hvStar : v ≤ vStar
    · rw [(hOld v ⟨hv.1, hvStar⟩).1]
      exact hc.trans_le (hfloor v ⟨hv.1, hvStar⟩)
    · have hvLow : v ∈ Icc vStar b :=
        ⟨(le_of_not_ge hvStar), hv.2⟩
      rw [(hLow v hvLow).1]
      exact hLowLam (a, v) ⟨⟨ha.le, le_rfl⟩, hvLow⟩
  let h₀ : ℝ → ℝ := fun v => A v / g v
  have hh₀ : ContDiffOn ℝ 1 h₀ (Icc a b) :=
    hA.contDiffOn.div hg.contDiffOn (fun v hv => ne_of_gt (hgpos v hv))
  let h := intervalC1Extension h₀ a b
  have hh : ContDiff ℝ 1 h := intervalC1Extension_c1 hab hh₀
  refine ⟨g, h, hg, hh, hgpos, ?_, ?_⟩
  · intro v hv
    have hvab : v ∈ Icc a b := ⟨hv.1, hv.2.trans hStarb.le⟩
    have hval := hOld v hv
    have hgP : 0 < P.g v := hc.trans_le (hfloor v hv)
    refine ⟨hval.1, ?_⟩
    change intervalC1Extension h₀ a b v = P.hEdge v
    rw [intervalC1Extension_eq hvab]
    change A v / g v = P.hEdge v
    rw [hval.1, hval.2]
    exact mul_div_cancel_left₀ _ (ne_of_gt hgP)
  · intro v hv
    have hvab : v ∈ Icc a b :=
      ⟨(haBar.trans hBarStar).le.trans hv.1, hv.2⟩
    have hval := hLow v hv
    refine ⟨hval.1, ?_⟩
    change intervalC1Extension h₀ a b v = _
    rw [intervalC1Extension_eq hvab]
    change A v / g v = SLow.alpha a v / SLow.lam a v
    rw [hval.1, hval.2]

end ChristodoulouBV.Uniqueness

end
