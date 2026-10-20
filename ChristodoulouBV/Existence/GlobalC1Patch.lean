module

public import ChristodoulouBV.Existence.C1Family
public import ChristodoulouBV.Frozen.GlobalDomain
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Gluing the finite C¹ developments

Read a family member beyond each point's terminal coordinate. Uniqueness
identifies all seven fields on finite developments. Continuity identifies
the five C¹ fields on their closures, including the regular axis.
-/

public section

open Set

namespace ChristodoulouBV

/-- A total patch of the finite family, evaluated at a positive cutoff
strictly beyond the terminal coordinate. -/
@[expose] noncomputable def globalC1Patch (family : ℝ → Fields) : Fields where
  r u v := (family (max v 0 + 1)).r u v
  phi u v := (family (max v 0 + 1)).phi u v
  m u v := (family (max v 0 + 1)).m u v
  lam u v := (family (max v 0 + 1)).lam u v
  nu u v := (family (max v 0 + 1)).nu u v
  alpha u v := (family (max v 0 + 1)).alpha u v
  beta u v := (family (max v 0 + 1)).beta u v

/-- The global patch agrees with every finite member in all primitive and
derived fields, including on the initial edge. -/
theorem globalC1Patch_agrees
    {alpha₀ : ℝ → ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b : ℝ, 0 < b →
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {b : ℝ} (hb : 0 < b) {u v : ℝ}
    (hp : (u, v) ∈ developmentWithInitialEdge b) :
    let P := globalC1Patch family
    P.r u v = (family b).r u v ∧
      P.phi u v = (family b).phi u v ∧
      P.m u v = (family b).m u v ∧
      P.lam u v = (family b).lam u v ∧
      P.nu u v = (family b).nu u v ∧
      P.alpha u v = (family b).alpha u v ∧
      P.beta u v = (family b).beta u v ∧
      P.theta u v = (family b).theta u v ∧
      P.zeta u v = (family b).zeta u v := by
  have hc : 0 < max v 0 + 1 := by linarith [le_max_right v 0]
  have hvc : v < max v 0 + 1 := by linarith [le_max_left v 0]
  exact c1_developments_agree (hfamily _ hc).1 (hfamily b hb).1
    (hfamily _ hc).2 (hfamily b hb).2 ⟨hp.1, hp.2.1, hvc⟩ hp

/-- Continuity extends compatibility of the five regular fields to each
closed finite triangle. No on-axis values of radius or mass are prescribed. -/
theorem globalC1Patch_five_fields_agree_on_closure
    {alpha₀ : ℝ → ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b : ℝ, 0 < b →
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closure (developmentWithInitialEdge a)) :
    let P := globalC1Patch family
    P.lam p.1 p.2 = (family b).lam p.1 p.2 ∧
      P.nu p.1 p.2 = (family b).nu p.1 p.2 ∧
      P.phi p.1 p.2 = (family b).phi p.1 p.2 ∧
      P.theta p.1 p.2 = (family b).theta p.1 p.2 ∧
      P.zeta p.1 p.2 = (family b).zeta p.1 p.2 := by
  have hpK : p ∈ closedCoordTriangle 0 a := by
    rwa [C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle ha] at hp
  let c := max p.2 0 + 1
  have hc : 0 < c := by dsimp [c]; linarith [le_max_right p.2 0]
  have hpc : p.2 < c := by dsimp [c]; linarith [le_max_left p.2 0]
  have hb : 0 < b := ha.trans hab
  let d := min b c
  have hd : 0 < d := lt_min hb hc
  have hsubB : developmentWithInitialEdge d ⊆ developmentWithInitialEdge b :=
    fun _ hq => ⟨hq.1, hq.2.1, hq.2.2.trans_le (min_le_left _ _)⟩
  have hsubC : developmentWithInitialEdge d ⊆ developmentWithInitialEdge c :=
    fun _ hq => ⟨hq.1, hq.2.1, hq.2.2.trans_le (min_le_right _ _)⟩
  have hpD : p ∈ closure (developmentWithInitialEdge d) := by
    rw [C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle hd]
    exact ⟨hpK.1, hpK.2.1, le_min (hpK.2.2.trans hab.le) hpc.le⟩
  obtain ⟨Hb, hdataB⟩ := hfamily b hb
  obtain ⟨Hc, hdataC⟩ := hfamily c hc
  have heq (q : ℝ × ℝ) (hq : q ∈ developmentWithInitialEdge d) :=
    c1_developments_agree Hc Hb hdataC hdataB (hsubC hq) (hsubB hq)
  have extend {F G : ℝ × ℝ → ℝ}
      (hF : ContinuousOn F (closure (developmentWithInitialEdge c)))
      (hG : ContinuousOn G (closure (developmentWithInitialEdge b)))
      (hEq : EqOn F G (developmentWithInitialEdge d)) : F p = G p :=
    hEq.of_subset_closure (hF.mono (closure_mono hsubC))
      (hG.mono (closure_mono hsubB)) subset_closure (Subset.refl _) hpD
  change (family c).lam p.1 p.2 = (family b).lam p.1 p.2 ∧
    (family c).nu p.1 p.2 = (family b).nu p.1 p.2 ∧
    (family c).phi p.1 p.2 = (family b).phi p.1 p.2 ∧
    (family c).theta p.1 p.2 = (family b).theta p.1 p.2 ∧
    (family c).zeta p.1 p.2 = (family b).zeta p.1 p.2
  exact ⟨extend Hc.lam_c1.continuousOn Hb.lam_c1.continuousOn
      (fun q hq => (heq q hq).2.2.2.1),
    extend Hc.nu_c1.continuousOn Hb.nu_c1.continuousOn
      (fun q hq => (heq q hq).2.2.2.2.1),
    extend Hc.phi_c1.continuousOn Hb.phi_c1.continuousOn
      (fun q hq => (heq q hq).2.1),
    extend Hc.theta_c1.continuousOn Hb.theta_c1.continuousOn
      (fun q hq => (heq q hq).2.2.2.2.2.2.2.1),
    extend Hc.zeta_c1.continuousOn Hb.zeta_c1.continuousOn
      (fun q hq => (heq q hq).2.2.2.2.2.2.2.2)⟩

/-- The same total patch is a frozen C¹ solution on every positive finite
development, with regularity on its entire closure. -/
theorem globalC1Patch_isC1Solution
    {alpha₀ : ℝ → ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b : ℝ, 0 < b →
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {a : ℝ} (ha : 0 < a) :
    IsC1Solution (developmentWithInitialEdge a) (globalC1Patch family) := by
  have hab : a < a + 1 := lt_add_one a
  have hb : 0 < a + 1 := ha.trans hab
  have H := (hfamily (a + 1) hb).1
  have hsub : developmentWithInitialEdge a ⊆ developmentWithInitialEdge (a + 1) :=
    fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.trans hab⟩
  have heq (p : ℝ × ℝ) (hp : p ∈ closure (developmentWithInitialEdge a)) :=
    globalC1Patch_five_fields_agree_on_closure hfamily ha hab hp
  have hEqU (p : ℝ × ℝ) (hp : p ∈ developmentWithInitialEdge a) :=
    globalC1Patch_agrees hfamily hb (hsub hp)
  refine {
    solution := (C1Solution.isSolution_congr_on_development
      (fun p hp => ⟨(hEqU p hp).1, (hEqU p hp).2.1,
        (hEqU p hp).2.2.1, (hEqU p hp).2.2.2.1,
        (hEqU p hp).2.2.2.2.1, (hEqU p hp).2.2.2.2.2.1,
        (hEqU p hp).2.2.2.2.2.2.1⟩)).mpr
      (C1Solution.isC1Solution_restrict_initialEdge H hab.le).solution
    nu_bounded_below := ?_
    lam_bounded_below := ?_
    lam_c1 := (H.lam_c1.mono (closure_mono hsub)).congr (fun p hp => (heq p hp).1)
    nu_c1 := (H.nu_c1.mono (closure_mono hsub)).congr (fun p hp => (heq p hp).2.1)
    phi_c1 := (H.phi_c1.mono (closure_mono hsub)).congr (fun p hp => (heq p hp).2.2.1)
    theta_c1 := (H.theta_c1.mono (closure_mono hsub)).congr
      (fun p hp => (heq p hp).2.2.2.1)
    zeta_c1 := (H.zeta_c1.mono (closure_mono hsub)).congr
      (fun p hp => (heq p hp).2.2.2.2) }
  · obtain ⟨N, hN⟩ := H.nu_bounded_below
    refine ⟨N, fun p hp => ?_⟩
    rw [(heq p (subset_closure hp)).2.1]
    exact hN p (hsub hp)
  · obtain ⟨c, hc, hC⟩ := H.lam_bounded_below
    refine ⟨c, hc, fun p hp => ?_⟩
    rw [(heq p (subset_closure hp)).1]
    exact hC p (hsub hp)

/-- The patch preserves the prescribed initial radius and scalar data
pointwise on the full positive initial ray. -/
theorem globalC1Patch_initial_data
    {alpha₀ : ℝ → ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b : ℝ, 0 < b →
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {v : ℝ} (hv : 0 < v) :
    (globalC1Patch family).r 0 v = v / 2 ∧
      (globalC1Patch family).alpha 0 v = alpha₀ v := by
  have hb : 0 < max v 0 + 1 := by linarith [le_max_right v 0]
  have hvb : v < max v 0 + 1 := by linarith [le_max_left v 0]
  exact (hfamily _ hb).2 v ⟨hv, hvb⟩

end ChristodoulouBV

end
