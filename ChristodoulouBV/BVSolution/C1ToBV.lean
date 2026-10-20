module

public import ChristodoulouBV.C1Solution.ExtractionCore
public import ChristodoulouBV.Frozen.IsBVSolution
import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# C¹ solutions on finite developments belong to the BV class

The closure of a finite development is a compact convex triangle. Each of the
five C¹ fields is therefore Lipschitz there, with a single constant for every
null slice. The same bounds give the four small variation limits at the axis.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.IsC1Solution

private theorem slice_lipschitz_out {F : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    {L : NNReal} (hF : LipschitzOnWith L F K) (u : ℝ) (s : Set ℝ)
    (hs : ∀ v ∈ s, (u, v) ∈ K) :
    LipschitzOnWith L (fun v => F (u, v)) s := by
  intro v hv w hw
  simpa [Prod.edist_eq] using hF (hs v hv) (hs w hw)

private theorem slice_lipschitz_in {F : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    {L : NNReal} (hF : LipschitzOnWith L F K) (v : ℝ) (s : Set ℝ)
    (hs : ∀ u ∈ s, (u, v) ∈ K) :
    LipschitzOnWith L (fun u => F (u, v)) s := by
  intro u hu w hw
  simpa [Prod.edist_eq] using hF (hs u hu) (hs w hw)

private theorem slice_variation_le {f : ℝ → ℝ} {L : NNReal}
    {s : Set ℝ} {a b : ℝ} (hL : LipschitzOnWith L f s)
    (hs : s ⊆ Icc a b) :
    eVariationOn f s ≤ L * ENNReal.ofReal (b - a) := by
  calc
    eVariationOn f s ≤ L * eVariationOn id s := by
      simpa only [Function.comp_id] using
        (hL.comp_eVariationOn_le (g := id) (s := s) (mapsTo_id s))
    _ ≤ L * eVariationOn id (Icc a b) := by
      gcongr
      exact eVariationOn.mono id hs
    _ = L * ENNReal.ofReal (b - a) := by rw [eVariationOn_id_Icc]

private theorem slice_variation_le_of_contDiffOn {F : ℝ × ℝ → ℝ}
    {K : Set (ℝ × ℝ)} (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (hF : ContDiffOn ℝ 1 F K) :
    ∃ L : NNReal, LipschitzOnWith L F K :=
  hF.exists_lipschitzOnWith (by norm_num) hKconv hKcompact

private theorem development_subset_closed {b : ℝ} :
    developmentWithInitialEdge b ⊆ closedCoordTriangle 0 b := by
  intro p hp
  simp only [closedCoordTriangle, Set.mem_ofPred_eq]
  exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩

private theorem uniform_slice_variation {b : ℝ}
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 b)) :
    ∃ C : ℝ,
      (∀ u, eVariationOn (fun v => F (u, v))
        {v | (u, v) ∈ developmentWithInitialEdge b} ≤ ENNReal.ofReal C) ∧
      (∀ v, eVariationOn (fun u => F (u, v))
        {u | (u, v) ∈ developmentWithInitialEdge b} ≤ ENNReal.ofReal C) := by
  obtain ⟨L, hL⟩ :=
    slice_variation_le_of_contDiffOn (convex_closedCoordTriangle 0 b)
      (isCompact_closedCoordTriangle 0 b) hF
  have hfinite : (L : ENNReal) * ENNReal.ofReal b ≠ ⊤ := by finiteness
  have hC : ENNReal.ofReal ((L * ENNReal.ofReal b).toReal) =
      (L : ENNReal) * ENNReal.ofReal b := ENNReal.ofReal_toReal hfinite
  refine ⟨(L * ENNReal.ofReal b).toReal, ?_, ?_⟩
  · intro u
    have hs : {v | (u, v) ∈ developmentWithInitialEdge b} ⊆ Icc 0 b := by
      intro v hv
      have h := development_subset_closed hv
      simp only [closedCoordTriangle, Set.mem_ofPred_eq] at h
      exact ⟨h.1.trans h.2.1, h.2.2⟩
    have hslice := slice_lipschitz_out hL u _
      (fun v hv => development_subset_closed hv)
    have hbound := slice_variation_le hslice hs
    rw [sub_zero, ← hC] at hbound
    exact hbound
  · intro v
    have hs : {u | (u, v) ∈ developmentWithInitialEdge b} ⊆ Icc 0 b := by
      intro u hu
      have h := development_subset_closed hu
      simp only [closedCoordTriangle, Set.mem_ofPred_eq] at h
      exact ⟨h.1, h.2.1.trans h.2.2⟩
    have hslice := slice_lipschitz_in hL v _
      (fun u hu => development_subset_closed hu)
    have hbound := slice_variation_le hslice hs
    rw [sub_zero, ← hC] at hbound
    exact hbound

private theorem tendsto_zero_of_variation_bound {L : NNReal} {V : ℝ → ENNReal}
    (hV : ∀ ε, V ε ≤ (L : ENNReal) * ENNReal.ofReal ε) :
    Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
  have hreal : Tendsto (fun ε : ℝ => ENNReal.ofReal ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
    have hsub : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).mono_left hsub
  have hlim : Tendsto (fun ε : ℝ => (L : ENNReal) * ENNReal.ofReal ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
    simpa only [Function.comp_def, mul_zero] using
      ((ENNReal.continuous_const_mul (by simp : (L : ENNReal) ≠ ⊤)).tendsto
        (0 : ENNReal)).comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hV

private theorem axis_variation_of_lipschitz {b : ℝ} {S : Fields}
    {L : NNReal} (hL : LipschitzOnWith L
      (fun p : ℝ × ℝ => S.phi p.1 p.2) (closedCoordTriangle 0 b))
    (a : ℝ) :
    AxisVanishingVariation (developmentWithInitialEdge b) S a := by
  constructor
  · apply tendsto_zero_of_variation_bound (L := L)
    intro ε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    have hs : {v | v ∈ Ioo (a - δ) a ∧
          (a - δ, v) ∈ developmentWithInitialEdge b} ⊆ Icc (a - δ) a := by
      intro v hv
      exact ⟨hv.1.1.le, hv.1.2.le⟩
    have hslice := slice_lipschitz_out hL (a - δ)
      {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ developmentWithInitialEdge b}
      (fun v hv => development_subset_closed hv.2)
    have hbound := slice_variation_le hslice hs
    have hδle : δ ≤ ε := hδ.2
    have hle : (L : ENNReal) * ENNReal.ofReal (a - (a - δ)) ≤
        (L : ENNReal) * ENNReal.ofReal ε := by
      gcongr
      linarith
    exact hbound.trans hle
  · apply tendsto_zero_of_variation_bound (L := L)
    intro ε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    have hs : {u | u ∈ Ioo (a - ε) (a - δ) ∧
          (u, a - δ) ∈ developmentWithInitialEdge b} ⊆
        Icc (a - ε) (a - δ) := by
      intro u hu
      exact ⟨hu.1.1.le, hu.1.2.le⟩
    have hslice := slice_lipschitz_in hL (a - δ)
      {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ developmentWithInitialEdge b}
      (fun u hu => development_subset_closed hu.2)
    have hbound := slice_variation_le hslice hs
    have hδnonneg : 0 ≤ δ := hδ.1
    have hle : (L : ENNReal) * ENNReal.ofReal ((a - δ) - (a - ε)) ≤
        (L : ENNReal) * ENNReal.ofReal ε := by
      gcongr
      linarith
    exact hbound.trans hle
  · apply tendsto_zero_of_variation_bound (L := L)
    intro ε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    have hs : {u | u ∈ Ioo a (a + δ) ∧
          (u, a + δ) ∈ developmentWithInitialEdge b} ⊆ Icc a (a + δ) := by
      intro u hu
      exact ⟨hu.1.1.le, hu.1.2.le⟩
    have hslice := slice_lipschitz_in hL (a + δ)
      {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ developmentWithInitialEdge b}
      (fun u hu => development_subset_closed hu.2)
    have hbound := slice_variation_le hslice hs
    have hδle : δ ≤ ε := hδ.2
    have hle : (L : ENNReal) * ENNReal.ofReal ((a + δ) - a) ≤
        (L : ENNReal) * ENNReal.ofReal ε := by
      gcongr
      linarith
    exact hbound.trans hle
  · apply tendsto_zero_of_variation_bound (L := L)
    intro ε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    have hs : {v | v ∈ Ioo (a + δ) (a + ε) ∧
          (a + δ, v) ∈ developmentWithInitialEdge b} ⊆
        Icc (a + δ) (a + ε) := by
      intro v hv
      exact ⟨hv.1.1.le, hv.1.2.le⟩
    have hslice := slice_lipschitz_out hL (a + δ)
      {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ developmentWithInitialEdge b}
      (fun v hv => development_subset_closed hv.2)
    have hbound := slice_variation_le hslice hs
    have hδnonneg : 0 ≤ δ := hδ.1
    have hle : (L : ENNReal) * ENNReal.ofReal ((a + ε) - (a + δ)) ≤
        (L : ENNReal) * ENNReal.ofReal ε := by
      gcongr
      linarith
    exact hbound.trans hle

private theorem phi_ac_out {b : ℝ} {S : Fields} {L : NNReal}
    (hL : LipschitzOnWith L (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 b))
    (u a c : ℝ) (hac : a ≤ c)
    (hseg : outSeg u a c ⊆ developmentWithInitialEdge b) :
    AbsolutelyContinuousOnInterval (S.phi u) a c := by
  have hs : ∀ v ∈ Icc a c, (u, v) ∈ closedCoordTriangle 0 b := by
    intro v hv
    apply development_subset_closed
    exact hseg (by simp [outSeg, hv])
  have hslice := slice_lipschitz_out hL u (Icc a c) hs
  have hslice' : LipschitzOnWith L (S.phi u) (uIcc a c) := by
    simpa only [uIcc_of_le hac] using hslice
  exact hslice'.absolutelyContinuousOnInterval

private theorem phi_ac_in {b : ℝ} {S : Fields} {L : NNReal}
    (hL : LipschitzOnWith L (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 b))
    (v a c : ℝ) (hac : a ≤ c)
    (hseg : inSeg v a c ⊆ developmentWithInitialEdge b) :
    AbsolutelyContinuousOnInterval (fun u => S.phi u v) a c := by
  have hs : ∀ u ∈ Icc a c, (u, v) ∈ closedCoordTriangle 0 b := by
    intro u hu
    apply development_subset_closed
    exact hseg (by simp [inSeg, hu])
  have hslice := slice_lipschitz_in hL v (Icc a c) hs
  have hslice' : LipschitzOnWith L (fun u => S.phi u v) (uIcc a c) := by
    simpa only [uIcc_of_le hac] using hslice
  exact hslice'.absolutelyContinuousOnInterval

private theorem axis_tendsto_of_continuousOn {b : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (closedCoordTriangle 0 b))
    {a : ℝ} (ha : (a, a) ∈ closedCoordTriangle 0 b)
    (hzero : F (a, a) = 0) :
    Tendsto (fun v => F (a, v))
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ developmentWithInitialEdge b})
      (𝓝 (0 : ℝ)) := by
  let l := 𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ developmentWithInitialEdge b}
  have hbase : l ≤ 𝓝 a := (inf_le_left : l ≤ 𝓝[>] a).trans nhdsWithin_le_nhds
  have hmember : {v | (a, v) ∈ developmentWithInitialEdge b} ∈ l :=
    le_principal_iff.mp inf_le_right
  change ∀ᶠ v in l, (a, v) ∈ developmentWithInitialEdge b at hmember
  have hmap : Tendsto (fun v : ℝ => (a, v)) l
      (𝓝[closedCoordTriangle 0 b] (a, a)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact ((continuous_const.prodMk continuous_id).tendsto a).mono_left hbase
    · exact hmember.mono (fun v hv => development_subset_closed hv)
  simpa only [Function.comp_def, hzero, l] using
    Filter.Tendsto.comp (hF.continuousWithinAt ha) hmap

private theorem axis_tendsto_of_zero_below_top {b : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (closedCoordTriangle 0 b))
    (hzero : ∀ a, 0 ≤ a → a < b → F (a, a) = 0)
    {a : ℝ} (ha : a ∈ adjacentAxis (developmentWithInitialEdge b))
    (hb : 0 < b) :
    Tendsto (fun v => F (a, v))
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ developmentWithInitialEdge b})
      (𝓝 (0 : ℝ)) := by
  have hclosure : closure (developmentWithInitialEdge b) =
      closedCoordTriangle 0 b := by
    simpa only [developmentWithInitialEdge] using closure_initialEdgeTriangle hb
  have haK : (a, a) ∈ closedCoordTriangle 0 b := by
    change (a, a) ∈ closure (developmentWithInitialEdge b) at ha
    rw [hclosure] at ha
    exact ha
  have haBounds : 0 ≤ a ∧ a ≤ b := by
    have h := haK
    simp only [closedCoordTriangle, Set.mem_ofPred_eq] at h
    exact ⟨h.1, h.2.2⟩
  by_cases hab : a < b
  · exact axis_tendsto_of_continuousOn hF haK (hzero a haBounds.1 hab)
  · have hae : a = b := le_antisymm haBounds.2 (le_of_not_gt hab)
    have hs : {v | (a, v) ∈ developmentWithInitialEdge b} = ∅ := by
      ext v
      constructor
      · intro hv
        have hlt : v < b := hv.2.2
        have hav : a < v := hv.2.1
        exact False.elim (by linarith)
      · intro hv
        cases hv
    simp [hs]

/-- A C¹ solution on a finite triangular development satisfies all six frozen
BV clauses, with variation constants uniform over the whole development. -/
theorem isBVSolution_development {b : ℝ} (hb : 0 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    IsBVSolution (developmentWithInitialEdge b) S := by
  let K := closedCoordTriangle 0 b
  have hclosure : closure (developmentWithInitialEdge b) = K := by
    simpa only [developmentWithInitialEdge, K] using closure_initialEdgeTriangle hb
  have hlam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2) K := by
    simpa only [hclosure] using H.lam_c1
  have hnu : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2) K := by
    simpa only [hclosure] using H.nu_c1
  have hphi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) K := by
    simpa only [hclosure] using H.phi_c1
  have htheta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) K := by
    simpa only [hclosure] using H.theta_c1
  have hzeta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.zeta p.1 p.2) K := by
    simpa only [hclosure] using H.zeta_c1
  obtain ⟨Lphi, hLphi⟩ :=
    slice_variation_le_of_contDiffOn (convex_closedCoordTriangle 0 b)
      (isCompact_closedCoordTriangle 0 b) hphi
  obtain ⟨Clam, hlamOut, _⟩ := uniform_slice_variation hlam
  obtain ⟨Cnu, _, hnuIn⟩ := uniform_slice_variation hnu
  obtain ⟨Cphi, hphiOut, hphiIn⟩ := uniform_slice_variation hphi
  obtain ⟨Ctheta, hthetaOut, _⟩ := uniform_slice_variation htheta
  obtain ⟨Czeta, _, hzetaIn⟩ := uniform_slice_variation hzeta
  have hnuLam : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2 + S.lam p.1 p.2)
      (closedCoordTriangle 0 b) := (hnu.add hlam).continuousOn
  have halpha : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2) K := by
    apply (htheta.add (hlam.mul hphi)).congr
    intro p hp
    simp only [Fields.theta]
    ring
  have hbeta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2) K := by
    apply (hzeta.add (hnu.mul hphi)).congr
    intro p hp
    simp only [Fields.zeta]
    ring
  have halphaBeta : ContinuousOn
      (fun p : ℝ × ℝ => S.alpha p.1 p.2 + S.beta p.1 p.2)
      (closedCoordTriangle 0 b) := (halpha.add hbeta).continuousOn
  refine {
    solution := H.solution
    nu_bounded_below := H.nu_bounded_below
    lam_bounded_below := H.lam_bounded_below
    item1 := ?_
    item2 := ?_
    item3_ac_out := ?_
    item3_ac_in := ?_
    item3_variation := ⟨Cphi, hphiOut, hphiIn⟩
    item4 := ?_
    item5 := ?_
    item6 := ?_ }
  · refine ⟨max Clam Cnu, ?_, ?_⟩
    · intro u
      exact (hlamOut u).trans (ENNReal.ofReal_mono (le_max_left _ _))
    · intro v
      exact (hnuIn v).trans (ENNReal.ofReal_mono (le_max_right _ _))
  · intro a ha
    apply axis_tendsto_of_zero_below_top hnuLam _ ha hb
    intro x hx hxb
    let B := (x + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith
    have hBb : B < b := by dsimp [B]; linarith
    have hxB : x ∈ Icc 0 B := by dsimp [B]; constructor <;> linarith
    have haxis := C1Solution.nu_eq_neg_lam_axis hB hBb H hxB
    dsimp
    linarith
  · intro u a c hac hseg
    exact phi_ac_out hLphi u a c hac hseg
  · intro v a c hac hseg
    exact phi_ac_in hLphi v a c hac hseg
  · intro a ha
    exact axis_variation_of_lipschitz hLphi a
  · refine ⟨max Ctheta Czeta, ?_, ?_⟩
    · intro u
      exact (hthetaOut u).trans (ENNReal.ofReal_mono (le_max_left _ _))
    · intro v
      exact (hzetaIn v).trans (ENNReal.ofReal_mono (le_max_right _ _))
  · intro a ha
    apply axis_tendsto_of_zero_below_top halphaBeta _ ha hb
    intro x hx hxb
    let B := (x + b) / 2
    have hB : 0 < B := by dsimp [B]; linarith
    have hBb : B < b := by dsimp [B]; linarith
    have hxB : x ∈ Icc 0 B := by dsimp [B]; constructor <;> linarith
    have haxis := C1Solution.beta_eq_neg_alpha_axis hB hBb H hxB
    dsimp
    linarith

end ChristodoulouBV.IsC1Solution

end
