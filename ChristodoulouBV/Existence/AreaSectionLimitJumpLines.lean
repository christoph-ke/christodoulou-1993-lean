module

public import ChristodoulouBV.Existence.AreaSectionLimitRectangle
import Mathlib.Tactic

/-!
# Common jump lines on the global carrier

A countable rational rectangle cover globalizes the common exceptional
sets. The outgoing fields include the initial edge `u=0`; incoming
continuity in `u` is asserted in the interior `0<u<v`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private abbrev SectionBox :=
  {q : Fin 4 → ℚ // 0 ≤ q 0 ∧ q 0 ≤ q 1 ∧ q 1 < q 2 ∧ q 2 ≤ q 3}

private theorem exists_section_box {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    ∃ q : SectionBox,
      (q.val 0 : ℝ) ≤ u ∧ u < (q.val 1 : ℝ) ∧
      (q.val 2 : ℝ) < v ∧ v < (q.val 3 : ℝ) := by
  obtain ⟨b, hub, hbv⟩ := exists_rat_btwn huv
  obtain ⟨l, hbl, hlv⟩ := exists_rat_btwn hbv
  obtain ⟨r, hvr⟩ := exists_rat_gt v
  let a : ℚ := 0
  have hab : a ≤ b := by
    change (0 : ℚ) ≤ b
    exact_mod_cast hu.trans hub.le
  have hblr : b < l := by exact_mod_cast hbl
  have hlr : l ≤ r := by exact_mod_cast hlv.le.trans hvr.le
  let q : SectionBox := ⟨![a, b, l, r], by
    change 0 ≤ a ∧ a ≤ b ∧ b < l ∧ l ≤ r
    exact ⟨le_rfl, hab, hblr, hlr⟩⟩
  refine ⟨q, ?_, hub, hlv, hvr⟩
  change ((0 : ℚ) : ℝ) ≤ u
  simpa only [Rat.cast_zero] using hu

private theorem exists_section_box_interior {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    ∃ q : SectionBox,
      (q.val 0 : ℝ) < u ∧ u < (q.val 1 : ℝ) ∧
      (q.val 2 : ℝ) < v ∧ v < (q.val 3 : ℝ) := by
  obtain ⟨a, ha, hau⟩ := exists_rat_btwn hu
  obtain ⟨b, hub, hbv⟩ := exists_rat_btwn huv
  obtain ⟨l, hbl, hlv⟩ := exists_rat_btwn hbv
  obtain ⟨r, hvr⟩ := exists_rat_gt v
  let q : SectionBox := ⟨![a, b, l, r], by
    change 0 ≤ a ∧ a ≤ b ∧ b < l ∧ l ≤ r
    exact ⟨by exact_mod_cast ha.le, by exact_mod_cast hau.le.trans hub.le,
      by exact_mod_cast hbl, by exact_mod_cast hlv.le.trans hvr.le⟩⟩
  exact ⟨q, hau, hub, hlv, hvr⟩

/-- One countable set of physical `v` jump lines works for both raw
outgoing fields on every outgoing section, including the initial edge. -/
theorem raw_outgoing_common_exceptional_set
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u v, 0 ≤ u → u < v → v ∉ S →
      ContinuousAt (d.rawFields.lam u) v ∧ ContinuousAt (d.rawFields.alpha u) v := by
  have hbox (q : SectionBox) : ∃ S : Set ℝ, S.Countable ∧
      ∀ v ∈ Ioo (q.val 2 : ℝ) (q.val 3 : ℝ), v ∉ S →
        ∀ u ∈ Icc (q.val 0 : ℝ) (q.val 1 : ℝ),
          ContinuousAt (d.rawFields.lam u) v ∧ ContinuousAt (d.rawFields.alpha u) v :=
    raw_outgoing_common_exceptional_set_on_rectangle h hD d
      (by exact_mod_cast q.property.1) (by exact_mod_cast q.property.2.1)
      (by exact_mod_cast q.property.2.2.1) (by exact_mod_cast q.property.2.2.2)
  choose S hSc hS using hbox
  refine ⟨⋃ q, S q, countable_iUnion hSc, ?_⟩
  intro u v hu huv hv
  obtain ⟨q, hqu, huq, hqv, hvq⟩ := exists_section_box hu huv
  exact hS q v ⟨hqv, hvq⟩ (fun hm => hv (mem_iUnion.mpr ⟨q, hm⟩))
    u ⟨hqu, huq.le⟩

/-- One countable set of physical `u` jump lines works for both raw
incoming fields on every interior incoming section. -/
theorem raw_incoming_common_exceptional_set
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ u v, 0 < u → u < v → u ∉ S →
      ContinuousAt (fun t => d.rawFields.nu t v) u ∧
        ContinuousAt (fun t => d.rawFields.beta t v) u := by
  have hbox (q : SectionBox) : ∃ S : Set ℝ, S.Countable ∧
      ∀ u ∈ Ioo (q.val 0 : ℝ) (q.val 1 : ℝ), u ∉ S →
        ∀ v ∈ Icc (q.val 2 : ℝ) (q.val 3 : ℝ),
          ContinuousAt (fun t => d.rawFields.nu t v) u ∧
            ContinuousAt (fun t => d.rawFields.beta t v) u :=
    raw_incoming_common_exceptional_set_on_rectangle h hD d
      (by exact_mod_cast q.property.1) (by exact_mod_cast q.property.2.1)
      (by exact_mod_cast q.property.2.2.1) (by exact_mod_cast q.property.2.2.2)
  choose S hSc hS using hbox
  refine ⟨⋃ q, S q, countable_iUnion hSc, ?_⟩
  intro u v hu huv hus
  obtain ⟨q, hqu, huq, hqv, hvq⟩ := exists_section_box_interior hu huv
  exact hS q u ⟨hqu, huq⟩ (fun hm => hus (mem_iUnion.mpr ⟨q, hm⟩))
    v ⟨hqv.le, hvq.le⟩

end ChristodoulouBV

end
