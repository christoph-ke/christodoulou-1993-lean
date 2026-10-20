module

public import ChristodoulouBV.Uniqueness.AxisLocalizationUniform
public import ChristodoulouBV.Uniqueness.RegularRectangle
import ChristodoulouBV.BVSolution.InitialData

/-!
# Targetwise continuation from an agreed axis triangle

The strict past of a fixed target can be covered by one regular characteristic
rectangle after its lower face has entered the agreed triangle. The terminal
outgoing point is recovered separately by continuity.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Agreement of the three pointwise fields used in uniqueness. -/
def PrimaryAgreement (S₁ S₂ : Fields) (u v : ℝ) : Prop :=
  S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v

/-- Continuous functions equal just left of an endpoint are equal at it. -/
theorem eq_endpoint_of_continuousOn_of_eq_Ioo
    {f g : ℝ → ℝ} {w v : ℝ} (hwv : w < v)
    (hf : ContinuousOn f (Icc w v)) (hg : ContinuousOn g (Icc w v))
    (hfg : ∀ t ∈ Ioo w v, f t = g t) : f v = g v := by
  have hleft : Tendsto (fun t : ℝ => t) (𝓝[<] v) (𝓝[Icc w v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT hwv)
        (fun _ ht => ⟨ht.1.le, ht.2.le⟩)⟩
  have hev : ∀ᶠ t in 𝓝[<] v, t ∈ Ioo w v := Ioo_mem_nhdsLT hwv
  have hf' : Tendsto f (𝓝[<] v) (𝓝 (f v)) :=
    (hf.continuousWithinAt ⟨hwv.le, le_rfl⟩).tendsto.comp hleft
  have hg' : Tendsto g (𝓝[<] v) (𝓝 (g v)) :=
    (hg.continuousWithinAt ⟨hwv.le, le_rfl⟩).tendsto.comp hleft
  exact tendsto_nhds_unique (hf'.congr' (hev.mono fun t ht => hfg t ht)) hg'

/-- A residual target admits a one-member ordered rectangle cover on each
compact strict-past truncation. Its lower face is in the agreed triangle and
its left face is on the agreed cutoff slice. -/
theorem ordered_regular_cover_to_target
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b u v V : ℝ} (ha : 0 ≤ a) (hau : a < u) (hub : u < b)
    (hbV : b ≤ V) (hVv : V < v) (hp : (u, v) ∈ U₁ ∩ U₂)
    (htri : ∀ x y, (x, y) ∈ triangle a b → PrimaryAgreement S₁ S₂ x y)
    (hface : ∀ y, (a, y) ∈ U₁ ∩ U₂ → PrimaryAgreement S₁ S₂ a y) :
    ∃ v₀ : ℝ, u < v₀ ∧ v₀ < b ∧ v₀ < V ∧
      regularRectangle a u v₀ V ⊆ U₁ ∩ U₂ ∧
      {q : ℝ × ℝ | a ≤ q.1 ∧ q.1 ≤ u ∧ b ≤ q.2 ∧ q.2 ≤ V} ⊆
        regularRectangle a u v₀ V ∧
      (∀ x ∈ Icc a u, PrimaryAgreement S₁ S₂ x v₀) ∧
      (∀ y ∈ Icc v₀ V, PrimaryAgreement S₁ S₂ a y) := by
  let v₀ := (u + b) / 2
  have huv₀ : u < v₀ := by dsimp [v₀]; linarith
  have hv₀b : v₀ < b := by dsimp [v₀]; linarith
  have hv₀V : v₀ < V := lt_of_lt_of_le hv₀b hbV
  have hR : regularRectangle a u v₀ V ⊆ U₁ ∩ U₂ := by
    intro q hq
    have hqu : q.1 ∈ Icc a u := hq.1
    have hqv : q.2 ∈ Icc v₀ V := hq.2
    exact strict_past_common h₁.solution.development h₂.solution.development
      hp ha le_rfl
      ⟨hqu.1, hqu.2, lt_of_le_of_lt hqu.2 (huv₀.trans_le hqv.1),
        hqv.2.trans_lt hVv⟩
  refine ⟨v₀, huv₀, hv₀b, hv₀V, hR, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨⟨hq.1, hq.2.1⟩, ⟨hv₀b.le.trans hq.2.2.1, hq.2.2.2⟩⟩
  · intro x hx
    exact htri x v₀ ⟨hx.1, hx.2.trans_lt huv₀, hv₀b⟩
  · intro y hy
    exact hface y (hR ⟨⟨le_rfl, hau.le⟩, hy⟩)

/-- Regular uniqueness propagates from the ordered past faces to every
strict-past truncation of a residual target. -/
theorem agreement_below_target_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b u v V : ℝ} (ha : 0 ≤ a) (hau : a < u) (hub : u < b)
    (hbV : b ≤ V) (hVv : V < v) (hp : (u, v) ∈ U₁ ∩ U₂)
    (htri : ∀ x y, (x, y) ∈ triangle a b → PrimaryAgreement S₁ S₂ x y)
    (hface : ∀ y, (a, y) ∈ U₁ ∩ U₂ → PrimaryAgreement S₁ S₂ a y) :
    PrimaryAgreement S₁ S₂ u V := by
  obtain ⟨v₀, huv₀, _, hv₀V, hR, _, hbottom, hleft⟩ :=
    ordered_regular_cover_to_target h₁ h₂ ha hau hub hbV hVv hp htri hface
  have hR₁ : regularRectangle a u v₀ V ⊆ U₁ :=
    fun q hq => (hR hq).1
  have hR₂ : regularRectangle a u v₀ V ⊆ U₂ :=
    fun q hq => (hR hq).2
  obtain ⟨hcorner, hV, hU⟩ := regular_rectangle_boundary_data
    h₁ h₂ hau.le hv₀V.le hR₁ hR₂ hleft hbottom
  have hEq := regular_rectangle_unique h₁ h₂ hau hv₀V hR₁ hR₂
    hcorner.1 hcorner.2.1 hcorner.2.2 hV hU
  exact hEq u ⟨hau.le, le_rfl⟩ V ⟨hv₀V.le, le_rfl⟩

/-- Equality below a finite outgoing endpoint extends to the endpoint when
both characteristic traces are continuous there. -/
theorem agreement_at_outgoing_endpoint
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {u v w : ℝ} (huw : u < w) (hwv : w < v)
    (hp : (u, v) ∈ U₁ ∩ U₂)
    (heq : ∀ t ∈ Ioo w v, PrimaryAgreement S₁ S₂ u t) :
    PrimaryAgreement S₁ S₂ u v := by
  have hs₁ : outSeg u w v ⊆ U₁ :=
    h₁.solution.development.out_seg_subset hp.1 huw hwv.le le_rfl
  have hs₂ : outSeg u w v ⊆ U₂ :=
    h₂.solution.development.out_seg_subset hp.2 huw hwv.le le_rfl
  have hc₁ := regular_rectangle_slice_continuity h₁ (u₀ := u) (u₁ := u)
    (v₀ := w) (v₁ := v) le_rfl hwv.le (by
      intro p hpt
      rcases p with ⟨x, y⟩
      have hx : x = u := le_antisymm hpt.1.2 hpt.1.1
      subst x
      exact hs₁ (by simpa [regularRectangle, outSeg] using hpt.2))
  have hc₂ := regular_rectangle_slice_continuity h₂ (u₀ := u) (u₁ := u)
    (v₀ := w) (v₁ := v) le_rfl hwv.le (by
      intro p hpt
      rcases p with ⟨x, y⟩
      have hx : x = u := le_antisymm hpt.1.2 hpt.1.1
      subst x
      exact hs₂ (by simpa [regularRectangle, outSeg] using hpt.2))
  refine ⟨?_, ?_, ?_⟩
  · exact eq_endpoint_of_continuousOn_of_eq_Ioo hwv
      (hc₁.1 u ⟨le_rfl, le_rfl⟩).1
      (hc₂.1 u ⟨le_rfl, le_rfl⟩).1 (fun t ht => (heq t ht).1)
  · exact eq_endpoint_of_continuousOn_of_eq_Ioo hwv
      (hc₁.1 u ⟨le_rfl, le_rfl⟩).2.1
      (hc₂.1 u ⟨le_rfl, le_rfl⟩).2.1 (fun t ht => (heq t ht).2.1)
  · exact eq_endpoint_of_continuousOn_of_eq_Ioo hwv
      (hc₁.1 u ⟨le_rfl, le_rfl⟩).2.2
      (hc₂.1 u ⟨le_rfl, le_rfl⟩).2.2 (fun t ht => (heq t ht).2.2)

/-- Agreement on the axis triangle and its initial outgoing face reaches any
common target whose incoming coordinate lies before the triangle top. This
includes an included terminal outgoing endpoint. -/
theorem agreement_to_residual_target
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b u v : ℝ} (ha : 0 ≤ a) (hau : a < u) (hub : u < b)
    (hp : (u, v) ∈ U₁ ∩ U₂)
    (htri : ∀ x y, (x, y) ∈ triangle a b → PrimaryAgreement S₁ S₂ x y)
    (hface : ∀ y, (a, y) ∈ U₁ ∩ U₂ → PrimaryAgreement S₁ S₂ a y) :
    PrimaryAgreement S₁ S₂ u v := by
  rcases lt_trichotomy v b with hvb | rfl | hbv
  · exact htri u v ⟨hau.le, (h₁.solution.development.wedge hp.1).2, hvb⟩
  · let w := (u + v) / 2
    have huw : u < w := by dsimp [w]; linarith
    have hwv : w < v := by dsimp [w]; linarith
    apply agreement_at_outgoing_endpoint h₁ h₂ huw hwv hp
    intro t ht
    exact htri u t ⟨hau.le, huw.trans ht.1, ht.2⟩
  · apply agreement_at_outgoing_endpoint h₁ h₂ hub hbv hp
    intro t ht
    exact agreement_below_target_top h₁ h₂ ha hau hub ht.1.le ht.2
      hp htri hface

/-- Agreement on all earlier incoming slices passes to an included limiting
slice. Each lower `v` point is reached first by incoming continuity;
outgoing continuity then reaches the terminal point. -/
theorem agreement_on_limit_slice
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a v : ℝ} (ha : 0 < a) (hp : (a, v) ∈ U₁ ∩ U₂)
    (hprior : ∀ x y, (x, y) ∈ U₁ ∩ U₂ → x < a →
      PrimaryAgreement S₁ S₂ x y) :
    PrimaryAgreement S₁ S₂ a v := by
  have hav : a < v := (h₁.solution.development.wedge hp.1).2
  let w := (a + v) / 2
  have haw : a < w := by dsimp [w]; linarith
  have hwv : w < v := by dsimp [w]; linarith
  apply agreement_at_outgoing_endpoint h₁ h₂ haw hwv hp
  intro t ht
  have hat : a < t := haw.trans ht.1
  have htv : t < v := ht.2
  let s := a / 2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hsa : s < a := by dsimp [s]; linarith
  have hR₁ : regularRectangle s a t t ⊆ U₁ := by
    intro q hq
    rcases q with ⟨x, y⟩
    have hy : y = t := le_antisymm hq.2.2 hq.2.1
    subst y
    exact h₁.solution.development.past_mem hp.1 (hs.trans hq.1.1)
      hq.1.2 (hq.1.2.trans_lt hat) htv
  have hR₂ : regularRectangle s a t t ⊆ U₂ := by
    intro q hq
    rcases q with ⟨x, y⟩
    have hy : y = t := le_antisymm hq.2.2 hq.2.1
    subst y
    exact h₂.solution.development.past_mem hp.2 (hs.trans hq.1.1)
      hq.1.2 (hq.1.2.trans_lt hat) htv
  have hc₁ := (regular_rectangle_slice_continuity h₁ hsa.le le_rfl hR₁).2
    t ⟨le_rfl, le_rfl⟩
  have hc₂ := (regular_rectangle_slice_continuity h₂ hsa.le le_rfl hR₂).2
    t ⟨le_rfl, le_rfl⟩
  have heq : ∀ x ∈ Ioo s a, PrimaryAgreement S₁ S₂ x t := by
    intro x hx
    exact hprior x t ⟨hR₁ ⟨⟨hx.1.le, hx.2.le⟩, ⟨le_rfl, le_rfl⟩⟩,
      hR₂ ⟨⟨hx.1.le, hx.2.le⟩, ⟨le_rfl, le_rfl⟩⟩⟩ hx.2
  refine ⟨?_, ?_, ?_⟩
  · exact eq_endpoint_of_continuousOn_of_eq_Ioo
      (f := fun x => S₁.r x t) (g := fun x => S₂.r x t) hsa hc₁.1 hc₂.1
      (fun x hx => (heq x hx).1)
  · exact eq_endpoint_of_continuousOn_of_eq_Ioo
      (f := fun x => S₁.phi x t) (g := fun x => S₂.phi x t) hsa hc₁.2.1 hc₂.2.1
      (fun x hx => (heq x hx).2.1)
  · exact eq_endpoint_of_continuousOn_of_eq_Ioo
      (f := fun x => S₁.m x t) (g := fun x => S₂.m x t) hsa hc₁.2.2 hc₂.2.2
      (fun x hx => (heq x hx).2.2)

/-- A common future witness, agreed incoming past, and equal data on the
current outgoing face give agreement through a positive future slab. -/
theorem agreement_extend_from_slice
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a A V : ℝ} (ha : 0 ≤ a) (haA : a < A)
    (hp : (A, V) ∈ U₁ ∩ U₂)
    (hprior : ∀ x y, (x, y) ∈ U₁ ∩ U₂ → x < a →
      PrimaryAgreement S₁ S₂ x y)
    (hdata : ∀ y, (a, y) ∈ U₁ ∩ U₂ →
      S₁.r a y = S₂.r a y ∧ S₁.phi a y = S₂.phi a y) :
    ∃ b : ℝ, a < b ∧ ∀ x y, (x, y) ∈ U₁ ∩ U₂ → x < b →
      PrimaryAgreement S₁ S₂ x y := by
  obtain ⟨εfinal, hεfinal, hlocal⟩ :=
    fixed_pair_axis_local_agreement h₁ h₂ hp ha haA hdata
  obtain ⟨h, hh, hT, htri⟩ := hlocal εfinal hεfinal le_rfl
  have hface : ∀ y, (a, y) ∈ U₁ ∩ U₂ →
      PrimaryAgreement S₁ S₂ a y := by
    intro y hy
    obtain ⟨hr, hphi⟩ := hdata y hy
    have hay : a < y := (h₁.solution.development.wedge hy.1).2
    have hm := h₁.initial_mass_eq h₂ hy.1 hy.2 (by
      intro t hat hty
      have ht : (a, t) ∈ U₁ ∩ U₂ :=
        ⟨h₁.solution.development.outgoing_mem hy.1 hat hty,
          h₂.solution.development.outgoing_mem hy.2 hat hty⟩
      exact hdata t ht)
    exact ⟨hr, hphi, hm y ⟨hay, le_rfl⟩⟩
  refine ⟨a + h, by linarith, ?_⟩
  intro x y hxy hxb
  rcases lt_trichotomy x a with hxa | rfl | hax
  · exact hprior x y hxy hxa
  · exact hface y hxy
  · exact agreement_to_residual_target h₁ h₂ ha hax hxb hxy
      (fun u v huv => htri u v huv) hface

/-- The three primary fields agree at every common point of two BV
developments with the same initial radius and scalar field. -/
theorem global_propagation
    (U₁ U₂ : Set (ℝ × ℝ)) (S₁ S₂ : Fields)
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v) :
    ∀ p ∈ U₁ ∩ U₂,
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.m p.1 p.2 = S₂.m p.1 p.2 := by
  classical
  intro p hp
  change PrimaryAgreement S₁ S₂ p.1 p.2
  rcases p with ⟨u, v⟩
  let G : Set ℝ := {a | 0 ≤ a ∧
    ∀ x y, (x, y) ∈ U₁ ∩ U₂ → x < a → PrimaryAgreement S₁ S₂ x y}
  have hzero : (0 : ℝ) ∈ G := by
    refine ⟨le_rfl, ?_⟩
    intro x y hxy hx
    have hx0 := (h₁.solution.development.wedge hxy.1).1
    linarith
  have hGne : G.Nonempty := ⟨0, hzero⟩
  by_contra hbad
  have hbound : BddAbove G := by
    refine ⟨u, ?_⟩
    intro a ha
    by_contra hnot
    have hua : u < a := lt_of_not_ge hnot
    exact hbad (ha.2 u v hp hua)
  let c := sSup G
  have hc0 : 0 ≤ c := le_csSup hbound hzero
  have hcu : c ≤ u := csSup_le hGne (by
    intro a ha
    by_contra hnot
    have hua : u < a := lt_of_not_ge hnot
    exact hbad (ha.2 u v hp hua))
  have hprior : ∀ x y, (x, y) ∈ U₁ ∩ U₂ → x < c →
      PrimaryAgreement S₁ S₂ x y := by
    intro x y hxy hxc
    obtain ⟨a, haG, hxa⟩ := exists_lt_of_lt_csSup hGne hxc
    exact haG.2 x y hxy hxa
  have hface : ∀ y, (c, y) ∈ U₁ ∩ U₂ →
      PrimaryAgreement S₁ S₂ c y := by
    intro y hy
    by_cases hcz : c = 0
    · have hy0 : (0, y) ∈ U₁ ∩ U₂ := by simpa only [hcz] using hy
      obtain ⟨hr, hphi⟩ := hdata y hy0
      have h0y : 0 < y := (h₁.solution.development.wedge hy0.1).2
      have hm := h₁.initial_mass_eq h₂ hy0.1 hy0.2 (by
        intro t h0t hty
        have ht : (0, t) ∈ U₁ ∩ U₂ :=
          ⟨h₁.solution.development.outgoing_mem hy0.1 h0t hty,
            h₂.solution.development.outgoing_mem hy0.2 h0t hty⟩
        exact hdata t ht)
      simpa only [hcz] using (show PrimaryAgreement S₁ S₂ 0 y from
        ⟨hr, hphi, hm y ⟨h0y, le_rfl⟩⟩)
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcz)
      exact agreement_on_limit_slice h₁ h₂ hcpos hy hprior
  rcases hcu.eq_or_lt with hceq | hclt
  · have hp' : (c, v) ∈ U₁ ∩ U₂ := by simpa only [hceq] using hp
    have heq := hface v hp'
    exact hbad (by simpa only [hceq] using heq)
  · have hdata_c : ∀ y, (c, y) ∈ U₁ ∩ U₂ →
        S₁.r c y = S₂.r c y ∧ S₁.phi c y = S₂.phi c y := by
      intro y hy
      exact ⟨(hface y hy).1, (hface y hy).2.1⟩
    obtain ⟨b, hcb, hbG⟩ :=
      agreement_extend_from_slice h₁ h₂ hc0 hclt hp hprior hdata_c
    have hbmem : b ∈ G := ⟨hc0.trans hcb.le, hbG⟩
    exact (not_lt_of_ge (le_csSup hbound hbmem)) hcb

end ChristodoulouBV.Uniqueness

end
