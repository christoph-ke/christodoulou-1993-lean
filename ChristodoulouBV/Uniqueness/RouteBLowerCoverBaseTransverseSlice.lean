module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseData
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisPacket
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous incoming coordinate jets on finite rectangles

On a compact subrectangle below the terminal edge, a C¹ field has a jointly
continuous incoming slice derivative, including both parameter endpoints.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The relative incoming slice derivative of a C¹ field is jointly
continuous on a closed rectangle. -/
theorem continuousOn_horizontal_derivWithin_of_contDiffOn_rectangle
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc u₀ u₁ ×ˢ Icc v₀ v₁)) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        derivWithin (fun t => f (t, p.2)) (Icc u₀ u₁) p.1)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁) := by
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  have hunique : UniqueDiffOn ℝ R :=
    uniqueDiffOn_convex ((convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁))
      (by
        rw [interior_prod_eq, interior_Icc, interior_Icc]
        exact (nonempty_Ioo.mpr hu).prod (nonempty_Ioo.mpr hv))
  have hJet : ContinuousOn
      (fun p => (fderivWithin ℝ f R p) (1, 0)) R :=
    (hf.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  apply hJet.congr
  intro p hp
  have hpath : HasDerivWithinAt (fun t : ℝ => (t, p.2))
      (1, 0) (Icc u₀ u₁) p.1 :=
    ((hasDerivAt_id' p.1).hasDerivWithinAt).prodMk
      ((hasDerivAt_const p.1 p.2).hasDerivWithinAt)
  have hmap : MapsTo (fun t : ℝ => (t, p.2)) (Icc u₀ u₁) R :=
    fun _ ht => ⟨ht, hp.2⟩
  have hfield := (hf.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hslice : HasDerivWithinAt (fun t => f (t, p.2))
      ((fderivWithin ℝ f R p) (1, 0)) (Icc u₀ u₁) p.1 := by
    simpa only [Function.comp_def] using
      hfield.comp_hasDerivWithinAt p.1 hpath hmap
  exact hslice.derivWithin ((uniqueDiffOn_Icc hu) p.1 hp.1)

/-- Continuity on every compact lower rectangle gives joint continuity
throughout the half-open terminal rectangle. -/
theorem continuousOn_halfOpen_rectangle_of_compact_lower
    {u₀ u₁ v₀ v₁ : ℝ} (hv : v₀ < v₁)
    {f : ℝ × ℝ → ℝ}
    (h : ∀ t ∈ Ico v₀ v₁,
      ContinuousOn f (Icc u₀ u₁ ×ˢ Icc v₀ t)) :
    ContinuousOn f (Icc u₀ u₁ ×ˢ Ico v₀ v₁) := by
  let S := Icc u₀ u₁ ×ˢ Ico v₀ v₁
  apply continuousOn_of_locally_continuousOn
  intro p hp
  let t : ℝ := (p.2 + v₁) / 2
  have hpt : p.2 < t := by dsimp [t]; linarith only [hp.2.2]
  have ht : t ∈ Ico v₀ v₁ := by
    dsimp [t]
    constructor <;> linarith only [hv, hp.2.1, hp.2.2]
  refine ⟨Set.univ ×ˢ Iio t, isOpen_univ.prod isOpen_Iio,
    ⟨trivial, hpt⟩, ?_⟩
  exact (h t ht).mono (by
    intro q hq
    exact ⟨hq.1.1, ⟨hq.1.2.1, hq.2.2.le⟩⟩)

/-- A compatible lower value trace has the old member's incoming jet at
strict interior points of every overlap rectangle. -/
theorem horizontal_derivWithin_eq_finite_triangle_jet
    {a vBar B : ℝ} (ha : 0 < a) (haBar : a < vBar)
    {f g : ℝ × ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (closedCoordTriangle 0 B))
    (hmatch : ∀ t ∈ Icc 0 a, ∀ w ∈ Ioo vBar B,
      f (t, w) = g (t, w))
    {u w : ℝ} (hu : u ∈ Ioo 0 a) (hw : w ∈ Ioo vBar B) :
    derivWithin (fun t => f (t, w)) (Icc 0 a) u =
      (fderivWithin ℝ g (closedCoordTriangle 0 B) (u, w)) (1, 0) := by
  have hEq : EqOn (fun t => f (t, w)) (fun t => g (t, w))
      (Icc 0 a) := fun t ht => hmatch t ht w hw
  have huClosed : u ∈ Icc 0 a := ⟨hu.1.le, hu.2.le⟩
  have hwithinEq := derivWithin_congr hEq (hEq huClosed)
  have hmem : (u, w) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu.1, hu.2.trans (haBar.trans hw.1), hw.2⟩
  have hdiff : DifferentiableAt ℝ g (u, w) :=
    ((hg.differentiableOn (by norm_num)).mono interior_subset
      (u, w) hmem).differentiableAt (isOpen_interior.mem_nhds hmem)
  have hB : 0 < B := (ha.trans (haBar.trans hw.1)).trans hw.2
  have hunique : UniqueDiffWithinAt ℝ (closedCoordTriangle 0 B) (u, w) :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB))
      (u, w) (interior_subset hmem)
  have hwithin : fderivWithin ℝ g (closedCoordTriangle 0 B) (u, w) =
      fderiv ℝ g (u, w) := fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun t : ℝ => (t, w)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u w)
  have hderiv : HasDerivAt (fun t => g (t, w))
      ((fderivWithin ℝ g (closedCoordTriangle 0 B) (u, w)) (1, 0)) u := by
    simpa only [hwithin, Function.comp_def] using
      hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  rw [hwithinEq, derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
  exact hderiv.deriv

/-- Each compact rectangle strictly below the terminal edge inherits C¹
regularity of `ν` and `β` from one finite member. -/
theorem OffAxisTerminalC1Packet.nu_beta_contDiffOn_lower_rectangle
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {t : ℝ} (ht : t ∈ Ico vBar vStar) :
    ContDiffOn ℝ 1 P.state.nu (Icc 0 a ×ˢ Icc vBar t) ∧
    ContDiffOn ℝ 1 (fun p => P.state.zeta p +
      P.state.nu p * P.state.phi p)
      (Icc 0 a ×ˢ Icc vBar t) := by
  let b : ℝ := (t + vStar) / 2
  have htb : t < b := by dsimp [b]; linarith only [ht.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b]
    constructor <;> linarith only [ha, haBar, ht.1, ht.2]
  let B : ℝ := (t + b) / 2
  have htB : t < B := by dsimp [B]; linarith only [htb]
  have hBb : B < b := by dsimp [B]; linarith only [htb]
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, ht.1, htb]
  let R := Icc 0 a ×ˢ Icc vBar t
  have hsub : R ⊆ closedCoordTriangle 0 B := by
    intro p hp
    change 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ B
    exact ⟨hp.1.1, (hp.1.2.trans_lt (haBar.trans_le hp.2.1)).le,
      hp.2.2.trans htB.le⟩
  have hnuEq : EqOn P.state.nu (fun p => (S b).nu p.1 p.2) R := by
    intro p hp
    exact (P.state.match_old b hb p.1 hp.1 p.2
      ⟨hp.2.1, hp.2.2.trans_lt htb⟩).2.2.2.1
  have hbetaEq : EqOn
      (fun p => P.state.zeta p + P.state.nu p * P.state.phi p)
      (fun p => (S b).beta p.1 p.2) R := by
    intro p hp
    obtain ⟨_, _, _, hn, hφ, hz, _, _, _⟩ :=
      P.state.match_old b hb p.1 hp.1 p.2
        ⟨hp.2.1, hp.2.2.trans_lt htb⟩
    change P.state.zeta p + P.state.nu p * P.state.phi p = _
    rw [hz, hn, hφ]
    simp only [Fields.zeta]
    ring
  exact ⟨((C1Solution.five_fields_contDiffOn hB hBb (hfamily b hb).1).2.1.mono
      hsub).congr hnuEq,
    ((C1Solution.beta_contDiffOn hB hBb (hfamily b hb).1).mono
      hsub).congr hbetaEq⟩

/-- The canonical relative incoming jet of `ν` below the terminal edge. -/
@[expose] noncomputable def OffAxisTerminalC1Packet.nuIncomingJetBelow
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (p : ℝ × ℝ) : ℝ :=
  derivWithin (fun u => P.state.nu (u, p.2)) (Icc 0 a) p.1

/-- The canonical relative incoming jet of `β = ζ + νφ` below the edge. -/
@[expose] noncomputable def OffAxisTerminalC1Packet.betaIncomingJetBelow
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (p : ℝ × ℝ) : ℝ :=
  derivWithin (fun u => P.state.zeta (u, p.2) +
    P.state.nu (u, p.2) * P.state.phi (u, p.2)) (Icc 0 a) p.1

/-- Both canonical incoming jets are jointly continuous on the half-open
terminal rectangle. In particular their initial values at `vBar` vary
continuously with `u` up to both endpoints. -/
theorem OffAxisTerminalC1Packet.nu_beta_incoming_jets_continuousOn_below
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ContinuousOn P.nuIncomingJetBelow (Icc 0 a ×ˢ Ico vBar vStar) ∧
    ContinuousOn P.betaIncomingJetBelow (Icc 0 a ×ˢ Ico vBar vStar) := by
  constructor
  · apply continuousOn_halfOpen_rectangle_of_compact_lower hBarStar
    intro t ht
    let s : ℝ := (t + vStar) / 2
    have hts : t < s := by dsimp [s]; linarith only [ht.2]
    have hs : s ∈ Ico vBar vStar := by
      dsimp [s]
      constructor <;> linarith only [ht.1, ht.2]
    change ContinuousOn (fun p : ℝ × ℝ =>
      derivWithin (fun u => P.state.nu (u, p.2)) (Icc 0 a) p.1) _
    exact (continuousOn_horizontal_derivWithin_of_contDiffOn_rectangle
      ha (ht.1.trans_lt hts)
      (P.nu_beta_contDiffOn_lower_rectangle ha haBar hfamily hs).1).mono
        (fun p hp => ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hts.le⟩⟩)
  · apply continuousOn_halfOpen_rectangle_of_compact_lower hBarStar
    intro t ht
    let s : ℝ := (t + vStar) / 2
    have hts : t < s := by dsimp [s]; linarith only [ht.2]
    have hs : s ∈ Ico vBar vStar := by
      dsimp [s]
      constructor <;> linarith only [ht.1, ht.2]
    change ContinuousOn (fun p : ℝ × ℝ =>
      derivWithin (fun u => P.state.zeta (u, p.2) +
        P.state.nu (u, p.2) * P.state.phi (u, p.2)) (Icc 0 a) p.1) _
    exact (continuousOn_horizontal_derivWithin_of_contDiffOn_rectangle
      ha (ht.1.trans_lt hts)
      (P.nu_beta_contDiffOn_lower_rectangle ha haBar hfamily hs).2).mono
        (fun p hp => ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hts.le⟩⟩)

end ChristodoulouBV.Uniqueness

end
