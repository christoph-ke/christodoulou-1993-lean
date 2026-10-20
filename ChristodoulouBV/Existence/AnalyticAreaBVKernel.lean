module
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

/-!
# Measurable variation measures of real BV sections

A sectionwise BV primitive with measurable evaluations gives a measurable
family of its variation measures. Rational partitions of the right-continuous
representative make the measurability assertion countable. This construction
discards isolated point values, as required by the variation-measure carrier convention.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem variation_eq_fin_partitions {α : Type*} [LinearOrder α]
    (f : α → ℝ) (s : Set α) :
    eVariationOn f s =
      ⨆ n : ℕ, ⨆ u : Fin (n + 1) → α,
        ⨆ (_ : Monotone u), ⨆ (_ : ∀ i, u i ∈ s),
          ∑ i : Fin n, edist (f (u i.succ)) (f (u i.castSucc)) := by
  apply le_antisymm
  · unfold eVariationOn
    refine iSup_le fun ⟨n, u, hu, hs⟩ => ?_
    let v : Fin (n + 1) → α := fun i => u i
    have hv : Monotone v := fun i j hij => hu hij
    have hvs : ∀ i, v i ∈ s := fun i => hs i
    refine le_iSup_of_le n (le_iSup_of_le v (le_iSup_of_le hv (le_iSup_of_le hvs ?_)))
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  · refine iSup_le fun n => iSup_le fun u => iSup_le fun hu => iSup_le fun hs => ?_
    let v : ℕ → α := fun i => u ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩
    have hv : Monotone v := fun i j hij => hu (min_le_min_right n hij)
    have hvs : ∀ i, v i ∈ s := fun i => hs _
    have heq : (∑ i : Fin n, edist (f (u i.succ)) (f (u i.castSucc))) =
        ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      congr 2 <;> apply congrArg u <;> apply Fin.ext <;>
        simp only [Fin.val_succ, Fin.val_castSucc,
          min_eq_left i.isLt.le, min_eq_left (Nat.succ_le_of_lt i.isLt)]
    rw [heq]
    exact eVariationOn.sum_le hv hvs

private theorem measurable_variation_countable {Y : Type*} [MeasurableSpace Y]
    {α : Type*} [LinearOrder α] [Countable α] {G : Y → α → ℝ}
    (hG : ∀ t, Measurable fun y => G y t) (s : Set α) :
    Measurable fun y => eVariationOn (G y) s := by
  simp_rw [variation_eq_fin_partitions]
  exact Measurable.iSup fun n => Measurable.iSup fun u =>
    Measurable.iSup fun _ => Measurable.iSup fun _ =>
      Finset.measurable_fun_sum _ fun i _ => (hG _).edist (hG _)

private theorem variation_Ioo_eq_rat {f : ℝ → ℝ} (hf : ∀ x, ContinuousWithinAt f (Ici x) x)
    (a b : ℝ) :
    eVariationOn f (Ioo a b) =
      eVariationOn (fun q : ℚ => f q) {q | (q : ℝ) ∈ Ioo a b} := by
  apply le_antisymm
  · rw [eVariationOn.eVariationOn_eq_strictMonoOn]
    refine iSup_le fun ⟨n, u, hu, hs⟩ => ?_
    have hq (i : ℕ) : ∃ q : ℕ → ℚ,
        (∀ m, (q m : ℝ) ∈ Ioo (u i) (u i + 1)) ∧
        Tendsto (fun m => (q m : ℝ)) atTop (𝓝 (u i)) := by
      obtain ⟨q, _, hmem, hlim⟩ :=
        Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
          (fun _ _ h => Rat.cast_le.mpr h) (lt_add_one (u i))
      exact ⟨q, hmem, hlim⟩
    choose q hqm hqt using hq
    have hlim (i : ℕ) : Tendsto (fun m => f (q i m)) atTop (𝓝 (f (u i))) := by
      apply (hf (u i)).tendsto.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨hqt i,
        Eventually.of_forall fun m => (hqm i m).1.le⟩
    have hv : Tendsto (fun m => ∑ i ∈ Finset.range n,
        edist (f (q (i + 1) m)) (f (q i m))) atTop
        (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) :=
      tendsto_finsetSum _ fun i _ => (hlim (i + 1)).edist (hlim i)
    apply le_of_tendsto hv
    have hmem : ∀ᶠ m in atTop, ∀ i ∈ Finset.Iic n,
        (q i m : ℝ) ∈ Ioo a b := by
      rw [Filter.eventually_all_finset]
      intro i hi
      exact (hqt i).eventually (isOpen_Ioo.mem_nhds (hs i (Finset.mem_Iic.mp hi)))
    have hmono : ∀ᶠ m in atTop, ∀ p ∈ (Finset.Iic n) ×ˢ (Finset.Iic n),
        p.1 < p.2 → q p.1 m < q p.2 m := by
      rw [Filter.eventually_all_finset]
      rintro ⟨i, j⟩ hp
      by_cases hij : i < j
      · have hh := hu (Finset.mem_Iic.mp (Finset.mem_product.mp hp).1)
          (Finset.mem_Iic.mp (Finset.mem_product.mp hp).2) hij
        filter_upwards [(hqt i).eventually_lt (hqt j) hh] with m hm
        exact fun _ => Rat.cast_lt.mp hm
      · exact Eventually.of_forall fun _ h => (hij h).elim
    filter_upwards [hmem, hmono] with m hm hn
    exact eVariationOn.sum_le_of_monotoneOn_Iic
      (f := fun q : ℚ => f q) (s := {q | (q : ℝ) ∈ Ioo a b})
      (u := fun i => q i m) (n := n)
      (fun i hi j hj hij => by
        rcases lt_or_eq_of_le hij with hij | rfl
        · exact (hn (i, j) (Finset.mem_product.mpr
            ⟨Finset.mem_Iic.mpr hi, Finset.mem_Iic.mpr hj⟩) hij).le
        · exact le_rfl)
      (fun i hi => hm i (Finset.mem_Iic.mpr hi))
  · exact eVariationOn.comp_le_of_monotoneOn f ((↑) : ℚ → ℝ)
      (fun _ _ _ _ h => Rat.cast_le.mpr h) (fun _ h => h)

private theorem measurable_rightLim_variation_Ioo {Y : Type*} [MeasurableSpace Y]
    {G : Y → ℝ → ℝ} (hG : ∀ x, Measurable fun y => G y x)
    (hb : ∀ y, BoundedVariationOn (G y) univ) (a b : ℝ) :
    Measurable fun y => (hb y).vectorMeasure.variation (Ioo a b) := by
  have hr (x : ℝ) : Measurable fun y => Function.rightLim (G y) x := by
    obtain ⟨q, _, hq, hqt⟩ := exists_seq_strictAnti_tendsto x
    apply measurable_of_tendsto_metrizable (fun n => hG (q n))
    apply tendsto_pi_nhds.mpr
    intro y
    exact ((hb y).tendsto_rightLim x).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hqt, Eventually.of_forall hq⟩)
  have heq (y : Y) : (hb y).vectorMeasure.variation (Ioo a b) =
      eVariationOn (fun q : ℚ => Function.rightLim (G y) q)
        {q | (q : ℝ) ∈ Ioo a b} := by
    rw [BoundedVariationOn.variation_vectorMeasure_Ioo_right]
    exact variation_Ioo_eq_rat (fun _ => (hb y).continuousWithinAt_rightLim) a b
  simp_rw [heq]
  exact measurable_variation_countable (α := ℚ)
    (G := fun y q => Function.rightLim (G y) (q : ℝ)) (fun q => hr q) _

/-- Measurable evaluations of real BV sections determine a measurable family
of their measure-theoretic variations. No right-continuity of the given
pointwise representatives is assumed. -/
theorem measurable_variation_kernel {Y : Type*} [MeasurableSpace Y]
    {G : Y → ℝ → ℝ} (hG : ∀ x, Measurable fun y => G y x)
    (hb : ∀ y, BoundedVariationOn (G y) univ) :
    Measurable fun y => (hb y).vectorMeasure.variation := by
  have hm : Monotone (fun n : ℕ => Ioo (-(n : ℝ)) n) := by
    intro m n hmn
    exact Ioo_subset_Ioo (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)
  have hu : (⋃ n : ℕ, Ioo (-(n : ℝ)) n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact mem_iUnion.mpr ⟨n, ⟨by linarith only [neg_abs_le x, hn],
      (le_abs_self x).trans_lt hn⟩⟩
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Ioo_rat)
    Real.isPiSystem_Ioo_rat
  · intro s hs
    simp only [mem_iUnion, mem_singleton_iff] at hs
    obtain ⟨a, b, _, rfl⟩ := hs
    exact measurable_rightLim_variation_Ioo hG hb a b
  · have heq (y : Y) : (hb y).vectorMeasure.variation univ =
        ⨆ n : ℕ, (hb y).vectorMeasure.variation (Ioo (-(n : ℝ)) n) := by
      rw [← hm.measure_iUnion, hu]
    simp_rw [heq]
    exact Measurable.iSup fun n => measurable_rightLim_variation_Ioo hG hb _ _

end ChristodoulouBV

end
