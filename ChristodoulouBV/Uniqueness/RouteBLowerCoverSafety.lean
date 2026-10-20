module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisPacket
public import ChristodoulouBV.C1Solution.RectangleSolution
import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import ChristodoulouBV.BVSolution.C1ToBV
import ChristodoulouBV.BVSolution.Signs
import Mathlib.Tactic.Linarith

/-!
# Terminal safety for the Route B lower cover

The canonical off-axis terminal state inherits the old family's uniform
negative incoming expansion. This supplies the sign margin required by the
off-axis rectangle solver at the top edge.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- Every strictly safe seven-state value is the center of a quantitative
safe cube for the rectangle solver. -/
theorem exists_safeRectangleBox_centered
    {z : RectangleState} (hz : IsSafeRectangleState z) :
    ∃ B : SafeRectangleBox, B.center = z := by
  rcases hz with ⟨hr, hl, hn, hgap⟩
  let δ := min (stateRadius z / 2)
    (min (stateLam z / 2)
      (min (-stateNu z / 2) (stateMassGap z / 6)))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith only [hr])
      (lt_min (by linarith only [hl])
        (lt_min (by linarith only [hn]) (by linarith only [hgap])))
  have hrδ : δ ≤ stateRadius z / 2 := min_le_left _ _
  have hlδ : δ ≤ stateLam z / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hnδ : δ ≤ -stateNu z / 2 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hgapδ : δ ≤ stateMassGap z / 6 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨{
    center := z
    radius := δ
    radius_pos := hδ
    radius_margin := by linarith only [hrδ, hr]
    lam_margin := by linarith only [hlδ, hl]
    nu_margin := by linarith only [hnδ, hn]
    gap_margin := by linarith only [hgapδ, hgap]
  }, rfl⟩

end ChristodoulouBV.C1Solution

namespace ChristodoulouBV.Uniqueness

/-- The canonical seven-state tuple of the terminal value traces. Its
outgoing scalar-radius and scalar-derivative entries are reconstructed from
`r`, `φ`, `ν`, and `ζ`. -/
@[expose] def OffAxisTerminalTraces.rectangleState
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S) (p : ℝ × ℝ) :
    C1Solution.RectangleState :=
  ((T.lam p, T.alpha p),
    (T.nu p, (T.zeta p + T.nu p * T.phi p,
      (T.m p, (T.r p, T.r p * T.phi p)))))

/-- The reconstructed seven-state field is continuous on every compact
terminal rectangle supplied by the trace data. -/
theorem OffAxisTerminalTraces.rectangleState_continuousOn
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S) :
    ContinuousOn T.rectangleState (Icc 0 a ×ˢ Icc vBar vStar) := by
  change ContinuousOn
    (fun p => ((T.lam p, T.alpha p),
      (T.nu p, (T.zeta p + T.nu p * T.phi p,
        (T.m p, (T.r p, T.r p * T.phi p)))))) _
  exact (T.lam_cont.prodMk T.alpha_cont).prodMk
    (T.nu_cont.prodMk
      ((T.zeta_cont.add (T.nu_cont.mul T.phi_cont)).prodMk
        (T.m_cont.prodMk (T.r_cont.prodMk (T.r_cont.mul T.phi_cont)))))

/-- The continuous terminal incoming expansion retains the old family's
uniform negative bound on a fixed compact lower base. -/
theorem OffAxisTerminalTraces.nu_le_neg_floor
    {a vBar vStar c : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hfloor : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < b → c ≤ (S b).lam u v)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    T.nu (u, vStar) ≤ -c := by
  have hslice : ContinuousOn (fun v => T.nu (u, v)) (Icc vBar vStar) :=
    T.nu_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu, hv⟩)
  have hmap : MapsTo (fun v => T.nu (u, v))
      (Ico vBar vStar) (Iic (-c)) := by
    intro v hv
    let b : ℝ := (v + vStar) / 2
    have hvb : v < b := by dsimp [b]; linarith only [hv.2]
    have hbStar : b < vStar := by dsimp [b]; linarith only [hv.2]
    have hb0 : 0 < b := by dsimp [b]; linarith only [ha, haBar, hv.1, hv.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hb0, hbStar⟩
    have huv : u < v := hu.2.trans_lt (haBar.trans_le hv.1)
    have hBV := (hfamily b hb).1.isBVSolution_development
      (hu.1.trans_lt (huv.trans hvb))
    have hlam : ∀ p ∈ developmentWithInitialEdge b,
        c ≤ (S b).lam p.1 p.2 := by
      intro p hp
      exact hfloor b hb p.1 p.2 hp.1 hp.2.1 hp.2.2
    have hν : (S b).nu u v ≤ -c :=
      hBV.nu_le_neg_lower hc hlam ⟨hu.1, huv, hvb⟩
    change T.nu (u, v) ≤ -c
    rw [(T.match_old b hb u hu v ⟨hv.1, hvb⟩).2.2.2.1]
    exact hν
  have hclosed : closure (Ico vBar vStar) = Icc vBar vStar :=
    closure_Ico hBarStar.ne
  have htop : vStar ∈ closure (Ico vBar vStar) := by
    rw [hclosed]
    exact ⟨hBarStar.le, le_rfl⟩
  rw [← hclosed] at hslice
  have hbound := hmap.closure_of_continuousOn hslice htop
  simpa only [isClosed_Iic.closure_eq, Set.mem_Iic] using hbound

/-- At the terminal base, the canonical seven-state tuple lies in the
open domain of the off-axis rectangle equations. -/
theorem OffAxisTerminalTraces.rectangleState_safe_at_terminal
    {a vBar vStar c : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hfloor : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < b → c ≤ (S b).lam u v)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    C1Solution.IsSafeRectangleState (T.rectangleState (u, vStar)) := by
  have hv : vStar ∈ Icc vBar vStar := ⟨hBarStar.le, le_rfl⟩
  obtain ⟨hr, hlam, hgap⟩ := T.floors u hu vStar hv
  have hrpos : 0 < T.r (u, vStar) := T.radius_pos.trans_le hr
  have hlampos : 0 < T.lam (u, vStar) := T.expansion_pos.trans_le hlam
  have hnupos : T.nu (u, vStar) < 0 :=
    (T.nu_le_neg_floor ha haBar hBarStar hc hfamily hfloor hu).trans_lt
      (by linarith only [hc])
  have hgapRatio : 0 < 1 - 2 * T.m (u, vStar) / T.r (u, vStar) :=
    T.gap_pos.trans_le hgap
  have hgapMass : 0 < T.r (u, vStar) - 2 * T.m (u, vStar) := by
    have hmul := mul_pos hgapRatio hrpos
    have heq :
        (1 - 2 * T.m (u, vStar) / T.r (u, vStar)) * T.r (u, vStar) =
          T.r (u, vStar) - 2 * T.m (u, vStar) := by
      field_simp [ne_of_gt hrpos]
    simpa only [heq] using hmul
  exact ⟨hrpos, hlampos, hnupos, hgapMass⟩

/-- Each point on the terminal lower base has a safe rectangle box centered
at its canonical seven-state value. -/
theorem OffAxisTerminalTraces.exists_safeRectangleBox_at_terminal
    {a vBar vStar c : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hfloor : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < b → c ≤ (S b).lam u v)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    ∃ B : C1Solution.SafeRectangleBox,
      B.center = T.rectangleState (u, vStar) :=
  C1Solution.exists_safeRectangleBox_centered
    (T.rectangleState_safe_at_terminal ha haBar hBarStar hc
      hfamily hfloor hu)

/-- The safe boxes along one compact terminal base can all be chosen with
the same strictly positive radius. Their centers remain the canonical trace
values, so a later finite partition only needs to control the variation of
the characteristic data. -/
theorem OffAxisTerminalTraces.exists_uniform_safeRectangleBox_radius
    {a vBar vStar c : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hfloor : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < b → c ≤ (S b).lam u v) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ Icc 0 a, ∃ B : C1Solution.SafeRectangleBox,
        B.center = T.rectangleState (u, vStar) ∧ B.radius = δ := by
  let δ := min (T.ρ / 2)
    (min (T.c / 2) (min (c / 2) (T.q * T.ρ / 6)))
  have hqρ : 0 < T.q * T.ρ := mul_pos T.gap_pos T.radius_pos
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith only [T.radius_pos])
      (lt_min (by linarith only [T.expansion_pos])
        (lt_min (by linarith only [hc]) (by linarith only [hqρ])))
  have hrδ : δ ≤ T.ρ / 2 := min_le_left _ _
  have hlδ : δ ≤ T.c / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hnδ : δ ≤ c / 2 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hgapδ : δ ≤ T.q * T.ρ / 6 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, hδ, ?_⟩
  intro u hu
  have hv : vStar ∈ Icc vBar vStar := ⟨hBarStar.le, le_rfl⟩
  obtain ⟨hr, hl, hgap⟩ := T.floors u hu vStar hv
  have hrpos : 0 < T.r (u, vStar) := T.radius_pos.trans_le hr
  have hn := T.nu_le_neg_floor ha haBar hBarStar hc hfamily hfloor hu
  have hgapMass : T.q * T.ρ ≤
      T.r (u, vStar) - 2 * T.m (u, vStar) := by
    have hmul₁ : T.q * T.ρ ≤ T.q * T.r (u, vStar) :=
      mul_le_mul_of_nonneg_left hr T.gap_pos.le
    have hmul₂ : T.q * T.r (u, vStar) ≤
        (1 - 2 * T.m (u, vStar) / T.r (u, vStar)) *
          T.r (u, vStar) :=
      mul_le_mul_of_nonneg_right hgap hrpos.le
    have heq :
        (1 - 2 * T.m (u, vStar) / T.r (u, vStar)) *
          T.r (u, vStar) =
          T.r (u, vStar) - 2 * T.m (u, vStar) := by
      field_simp [ne_of_gt hrpos]
    calc
      T.q * T.ρ ≤ T.q * T.r (u, vStar) := hmul₁
      _ ≤ (1 - 2 * T.m (u, vStar) / T.r (u, vStar)) *
          T.r (u, vStar) := hmul₂
      _ = T.r (u, vStar) - 2 * T.m (u, vStar) := heq
  refine ⟨{
    center := T.rectangleState (u, vStar)
    radius := δ
    radius_pos := hδ
    radius_margin := by
      change δ < T.r (u, vStar)
      linarith only [hrδ, hr, T.radius_pos]
    lam_margin := by
      change δ < T.lam (u, vStar)
      linarith only [hlδ, hl, T.expansion_pos]
    nu_margin := by
      change δ < -T.nu (u, vStar)
      linarith only [hnδ, hn, hc]
    gap_margin := by
      change 3 * δ < T.r (u, vStar) - 2 * T.m (u, vStar)
      linarith only [hgapδ, hgapMass, hqρ]
  }, rfl, rfl⟩

end ChristodoulouBV.Uniqueness

end
