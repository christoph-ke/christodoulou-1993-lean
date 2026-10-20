module

public import ChristodoulouBV.Existence.C1EndpointCore
public import ChristodoulouBV.Existence.E1ShiftTVScale
import Mathlib.Tactic

/-!
# Universal three-term variation at a finite endpoint

The Section 4 slice coefficient is retained through centering, scaling, and
finite cutoff exhaustion. Its value is independent of the datum and cutoff.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- On every strict finite cutoff, both three-term variation bounds use the
same universal Section 4 coefficient and the full initial datum variation. -/
theorem s6_finite_cutoff_three_term_tv
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) (haB : a < B) :
    (∀ u ∈ Ico (0 : ℝ) a,
      e1OutgoingTVFinite S u a ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) a,
      e1IncomingTVFinite S 0 v ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) := by
  let T := Uniqueness.rescaledFields S 0 a
  have Ha : IsC1Solution (developmentWithInitialEdge a) S :=
    C1Solution.isC1Solution_restrict_initialEdge H (haB.trans hBb).le
  have hr : ∀ v ∈ Ioo (0 : ℝ) a, S.r 0 v = v / 2 := by
    intro v hv
    exact (hdata v ⟨hv.1, hv.2.trans (haB.trans hBb)⟩).1
  have hboot := (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have hZ := (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).2
  have hDscale := (s6_scale ha (haB.trans hBb) H hdata).2.2
  have hDsmall : sourceD T ≤ s4Epsilon0 :=
    hDscale.trans (hD.le.trans epsilonChosen_le_s4)
  have hSlice := e1_three_term_tv_cutoff ha Ha hr hboot hDsmall hZ
  have hAlphaEq : eVariationOn (S.alpha 0) (Ioo 0 a) =
      eVariationOn alpha₀ (Ioo 0 a) := by
    apply eVariationOn.congr
    intro v hv
    exact (hdata v ⟨hv.1, hv.2.trans (haB.trans hBb)⟩).2
  have hVarLe : eVariationOn (S.alpha 0) (Ioo 0 a) ≤
      eVariationOn alpha₀ (Ioi (0 : ℝ)) := by
    rw [hAlphaEq]
    exact eVariationOn.mono _ Ioo_subset_Ioi_self
  have hDtop : eVariationOn alpha₀ (Ioi (0 : ℝ)) ≠ ∞ := by
    have hE : s4Epsilon0 ≠ ∞ := by norm_num [s4Epsilon0]
    exact ne_top_of_le_ne_top hE (hD.le.trans epsilonChosen_le_s4)
  have hRealLe : (eVariationOn (S.alpha 0) (Ioo 0 a)).toReal ≤
      (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal :=
    ENNReal.toReal_mono hDtop hVarLe
  have hKLe : ENNReal.ofReal
      (s4SliceTVK * (eVariationOn (S.alpha 0) (Ioo 0 a)).toReal) ≤
      ENNReal.ofReal
      (s4SliceTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hRealLe s4SliceTVK_pos.le
  exact ⟨fun u hu => (hSlice.1 u hu).trans hKLe,
    fun v hv => (hSlice.2 v hv).trans hKLe⟩

/-- Outgoing three-term variation of the patched field agrees with a finite
member on every strict finite cutoff, including the initial ray `u=0`. -/
theorem endpointPatch_outgoing_tv_eq_on_cutoff
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {b u a : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hu : 0 ≤ u) (_hua : u < a) (hab : a < b) :
    e1OutgoingTVFinite (endpointPatch family vStar) u a =
      e1OutgoingTVFinite (family b) u a := by
  let P := endpointPatch family vStar
  have hvalues (v : ℝ) (hv : v ∈ Ioo u a) :=
    endpointPatch_agrees hfamily hb
      (show (u, v) ∈ developmentWithInitialEdge b from
        ⟨hu, hv.1, hv.2.trans hab⟩)
  have hQ : EqOn (fun v => P.alpha u v / P.lam u v)
      (fun v => (family b).alpha u v / (family b).lam u v)
      (Ioo u a) := by
    intro v hv
    obtain ⟨_, _, _, hlam, _, halpha, _⟩ := hvalues v hv
    change (endpointPatch family vStar).alpha u v /
      (endpointPatch family vStar).lam u v = _
    rw [halpha, hlam]
  have hPhi : EqOn (P.phi u) ((family b).phi u) (Ioo u a) := by
    intro v hv
    exact (hvalues v hv).2.1
  have hLog : EqOn (fun v => Real.log (P.lam u v))
      (fun v => Real.log ((family b).lam u v)) (Ioo u a) := by
    intro v hv
    change Real.log ((endpointPatch family vStar).lam u v) = _
    rw [(hvalues v hv).2.2.2.1]
  unfold e1OutgoingTVFinite
  rw [eVariationOn.congr hQ, eVariationOn.congr hPhi,
    eVariationOn.congr hLog]

/-- Incoming three-term variation of the patch agrees with a finite member
on every incoming ray strictly below that member's cutoff. -/
theorem endpointPatch_incoming_tv_eq_on_cutoff
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {b v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (_hv : 0 < v) (hvb : v < b) :
    e1IncomingTVFinite (endpointPatch family vStar) 0 v =
      e1IncomingTVFinite (family b) 0 v := by
  let P := endpointPatch family vStar
  have hvalues (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) v) :=
    endpointPatch_agrees hfamily hb
      (show (u, v) ∈ developmentWithInitialEdge b from
        ⟨hu.1.le, hu.2, hvb⟩)
  have hQ : EqOn (fun u => P.beta u v / P.nu u v)
      (fun u => (family b).beta u v / (family b).nu u v)
      (Ioo (0 : ℝ) v) := by
    intro u hu
    obtain ⟨_, _, _, _, hnu, _, hbeta⟩ := hvalues u hu
    change (endpointPatch family vStar).beta u v /
      (endpointPatch family vStar).nu u v = _
    rw [hbeta, hnu]
  have hPhi : EqOn (fun u => P.phi u v)
      (fun u => (family b).phi u v) (Ioo (0 : ℝ) v) := by
    intro u hu
    exact (hvalues u hu).2.1
  have hLog : EqOn (fun u => Real.log (-P.nu u v))
      (fun u => Real.log (-(family b).nu u v))
      (Ioo (0 : ℝ) v) := by
    intro u hu
    change Real.log (-(endpointPatch family vStar).nu u v) = _
    rw [(hvalues u hu).2.2.2.2.1]
  unfold e1IncomingTVFinite
  rw [eVariationOn.congr hQ, eVariationOn.congr hPhi,
    eVariationOn.congr hLog]

/-- The patched endpoint field obeys both three-term variation estimates on
each strict finite cutoff, with the same universal coefficient. -/
theorem endpointPatch_three_term_tv_cutoff
    {alpha₀ : ℝ → ℝ} {vStar : ℝ}
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) vStar) :
    let P := endpointPatch family vStar
    (∀ u ∈ Ico (0 : ℝ) a,
      e1OutgoingTVFinite P u a ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) a,
      e1IncomingTVFinite P 0 v ≤
        ENNReal.ofReal (s4SliceTVK *
          (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) := by
  obtain ⟨B, haB, hBStar⟩ := exists_between ha.2
  obtain ⟨b, hBb, hbStar⟩ := exists_between hBStar
  have hB : 0 < B := ha.1.trans haB
  have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hB.trans hBb, hbStar⟩
  obtain ⟨H, hdata⟩ := hfamily b hb
  obtain ⟨hOut, hIn⟩ :=
    s6_finite_cutoff_three_term_tv hB hBb H hdata hD ha.1 haB
  constructor
  · intro u hu
    rw [endpointPatch_outgoing_tv_eq_on_cutoff hfamily hb hu.1 hu.2
      (haB.trans hBb)]
    exact hOut u hu
  · intro v hv
    rw [endpointPatch_incoming_tv_eq_on_cutoff hfamily hb hv.1
      (hv.2.trans (haB.trans hBb))]
    exact hIn v hv

/-- The endpoint patch has a universal three-term variation bound on every
outgoing ray, including `u=0`, and every incoming ray from the initial edge.
The factor three is the finite sum of the three separate monotone variation
exhaustions; it remains independent of the datum and endpoint. -/
theorem endpointPatch_three_term_tv
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (_hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧
        (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    let C := ENNReal.ofReal (s4SliceTVK *
      (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)
    (∀ u ∈ Ico (0 : ℝ) vStar,
      e1OutgoingTVFinite P u vStar ≤ C + C + C) ∧
    (∀ v ∈ Ioo (0 : ℝ) vStar,
      e1IncomingTVFinite P 0 v ≤ C + C + C) := by
  let P := endpointPatch family vStar
  let C : ℝ≥0∞ := ENNReal.ofReal (s4SliceTVK *
    (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)
  constructor
  · intro u hu
    let q : ℝ → ℝ := fun v => P.alpha u v / P.lam u v
    let p : ℝ → ℝ := P.phi u
    let l : ℝ → ℝ := fun v => Real.log (P.lam u v)
    have hCut (a : ℝ) (hua : u < a) (haStar : a < vStar) :
        e1OutgoingTVFinite P u a ≤ C := by
      have ha : a ∈ Ioo (0 : ℝ) vStar :=
        ⟨hu.1.trans_lt hua, haStar⟩
      exact (endpointPatch_three_term_tv_cutoff hD hfamily ha).1 u
        ⟨hu.1, hua⟩
    have hqCut (a : ℝ) (hua : u < a) (haStar : a < vStar) :
        eVariationOn q (Ioo u a) ≤ C := by
      have h := hCut a hua haStar
      dsimp only [e1OutgoingTVFinite, q] at h
      have h₁ : eVariationOn q (Ioo u a) ≤
          eVariationOn q (Ioo u a) + eVariationOn p (Ioo u a) :=
        le_add_of_nonneg_right bot_le
      have h₂ : eVariationOn q (Ioo u a) + eVariationOn p (Ioo u a) ≤
          eVariationOn q (Ioo u a) +
            eVariationOn p (Ioo u a) + eVariationOn l (Ioo u a) :=
        le_add_of_nonneg_right bot_le
      exact (h₁.trans h₂).trans h
    have hpCut (a : ℝ) (hua : u < a) (haStar : a < vStar) :
        eVariationOn p (Ioo u a) ≤ C := by
      have h := hCut a hua haStar
      dsimp only [e1OutgoingTVFinite, p] at h
      have h₁ : eVariationOn p (Ioo u a) ≤
          eVariationOn q (Ioo u a) + eVariationOn p (Ioo u a) :=
        le_add_of_nonneg_left bot_le
      have h₂ : eVariationOn q (Ioo u a) + eVariationOn p (Ioo u a) ≤
          eVariationOn q (Ioo u a) +
            eVariationOn p (Ioo u a) + eVariationOn l (Ioo u a) :=
        le_add_of_nonneg_right bot_le
      exact (h₁.trans h₂).trans h
    have hlCut (a : ℝ) (hua : u < a) (haStar : a < vStar) :
        eVariationOn l (Ioo u a) ≤ C := by
      have h := hCut a hua haStar
      dsimp only [e1OutgoingTVFinite, l] at h
      exact (by simp : eVariationOn l (Ioo u a) ≤
        eVariationOn q (Ioo u a) +
          eVariationOn p (Ioo u a) + eVariationOn l (Ioo u a)).trans h
    have hq := s6_variation_terminal_exhaustion_bound q hu.2 hqCut
    have hp := s6_variation_terminal_exhaustion_bound p hu.2 hpCut
    have hl := s6_variation_terminal_exhaustion_bound l hu.2 hlCut
    change eVariationOn q (Ioo u vStar) +
      eVariationOn p (Ioo u vStar) +
      eVariationOn l (Ioo u vStar) ≤ C + C + C
    exact add_le_add (add_le_add hq hp) hl
  · intro v hv
    obtain ⟨a, hva, haStar⟩ := exists_between hv.2
    have ha : a ∈ Ioo (0 : ℝ) vStar := ⟨hv.1.trans hva, haStar⟩
    have h := (endpointPatch_three_term_tv_cutoff hD hfamily ha).2 v
      ⟨hv.1, hva⟩
    exact h.trans (by simp : C ≤ C + C + C)

/-- The universal coefficient for all three endpoint slice variations. -/
noncomputable def s6EndpointTVK : ℝ := 3 * s4SliceTVK

/-- The same endpoint witness has one universal three-term variation
coefficient on every outgoing and incoming ray. -/
theorem endpointPatch_universal_tv_bound
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
    let C := ENNReal.ofReal (s6EndpointTVK *
      (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)
    (∀ u ∈ Ico (0 : ℝ) vStar,
      e1OutgoingTVFinite P u vStar ≤ C) ∧
    (∀ v ∈ Ioo (0 : ℝ) vStar,
      e1IncomingTVFinite P 0 v ≤ C) := by
  have h := endpointPatch_three_term_tv hStar hD hfamily
  have hconst :
      ENNReal.ofReal (s4SliceTVK *
        (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) +
      ENNReal.ofReal (s4SliceTVK *
        (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) +
      ENNReal.ofReal (s4SliceTVK *
        (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) =
      ENNReal.ofReal (s6EndpointTVK *
        (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) := by
    rw [s6EndpointTVK, mul_assoc,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring
  dsimp only at h ⊢
  rw [hconst] at h
  exact h

end ChristodoulouBV

end
