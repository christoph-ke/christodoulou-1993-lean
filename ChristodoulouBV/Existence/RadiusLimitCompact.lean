module

public import ChristodoulouBV.Existence.SmoothBounds
public import ChristodoulouBV.ForMathlib.Topology.ArzelaAscoliSeq
public import ChristodoulouBV.ForMathlib.BoundedVariation.Helly
public import ChristodoulouBV.BVSolution.SignAux
import Mathlib.Tactic

/-!
# Compactness on the global development

The compactness arguments for the radius limit use the initial edge as part of the domain.
Lipschitz extensions allow Arzelà–Ascoli to include the excluded axis without
placing any condition on the irrelevant total-field values on that axis.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Locally uniform convergence is retained by a strictly increasing subsequence. -/
theorem locally_uniform_comp_strictMono {X : Type*} [TopologicalSpace X]
    {f : ℕ → X → ℝ} {g : X → ℝ} (h : TendstoLocallyUniformly f g atTop)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    TendstoLocallyUniformly (fun n => f (σ n)) g atTop := by
  intro U hU x
  obtain ⟨t, ht, hevent⟩ := h U hU x
  exact ⟨t, ht, hσ.tendsto_atTop.eventually hevent⟩

/-- A bounded interval primitive controls the difference of its endpoint values. -/
theorem IntervalPrimitive.abs_sub_le {f g : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (h : IntervalPrimitive f g a b)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ M) :
    |f b - f a| ≤ M * (b - a) := by
  rw [h.2]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (f := g) (C := M)
      (a := a) (b := b)
      (fun t ht => hg t (by
        rw [uIoc_of_le hab] at ht
        exact ⟨ht.1.le, ht.2⟩))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  exact hi

/-- Uniform bounds for the two null primitive densities give a Lipschitz
bound on the entire development, including its initial edge. -/
theorem lipschitzOnWith_of_null_primitives
    {f g h : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hout : ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (f u) (g u) a b)
    (hin : ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => f u v) (fun u => h u v) a b)
    (hg : ∀ p ∈ globalDomain, |g p.1 p.2| ≤ M)
    (hh : ∀ p ∈ globalDomain, |h p.1 p.2| ≤ M) :
    LipschitzOnWith ⟨2 * M, mul_nonneg (by norm_num) hM⟩
      (fun p : ℝ × ℝ => f p.1 p.2) globalDomain := by
  have hv (u a b : ℝ) (ha : (u, a) ∈ globalDomain)
      (hb : (u, b) ∈ globalDomain) :
      |f u b - f u a| ≤ M * |b - a| := by
    wlog hab : a ≤ b generalizing a b
    · simpa only [abs_sub_comm] using this b a hb ha (le_of_not_ge hab)
    have hs : outSeg u a b ⊆ globalDomain := by
      rintro ⟨s, t⟩ ⟨rfl, ht⟩
      exact ⟨ha.1, ha.2.trans_le ht.1⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      (hout u a b hab hs).abs_sub_le hab (fun t ht => hg (u, t) (hs ⟨rfl, ht⟩))
  have hu (v a b : ℝ) (ha : (a, v) ∈ globalDomain)
      (hb : (b, v) ∈ globalDomain) :
      |f b v - f a v| ≤ M * |b - a| := by
    wlog hab : a ≤ b generalizing a b
    · simpa only [abs_sub_comm] using this b a hb ha (le_of_not_ge hab)
    have hs : inSeg v a b ⊆ globalDomain := by
      rintro ⟨s, t⟩ ⟨hs, rfl⟩
      exact ⟨ha.1.trans hs.1, hs.2.trans_lt hb.2⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      (hin v a b hab hs).abs_sub_le hab (fun t ht => hh (t, v) (hs ⟨ht, rfl⟩))
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  change |f p.1 p.2 - f q.1 q.2| ≤ (2 * M) * dist p q
  wlog hpq : p.1 ≤ q.1 generalizing p q
  · simpa only [dist_comm, abs_sub_comm] using this q hq p hp (le_of_not_ge hpq)
  have hx : (p.1, q.2) ∈ globalDomain := ⟨hp.1, hpq.trans_lt hq.2⟩
  have hfirst : |p.1 - q.1| ≤ dist p q := le_max_left _ _
  have hsecond : |p.2 - q.2| ≤ dist p q := le_max_right _ _
  calc
    |f p.1 p.2 - f q.1 q.2| ≤
        |f p.1 p.2 - f p.1 q.2| + |f p.1 q.2 - f q.1 q.2| := abs_sub_le _ _ _
    _ ≤ M * |p.2 - q.2| + M * |p.1 - q.1| :=
      add_le_add (hv p.1 q.2 p.2 hx hp) (hu q.2 q.1 p.1 hq hx)
    _ ≤ M * dist p q + M * dist p q :=
      add_le_add (mul_le_mul_of_nonneg_left hsecond hM)
        (mul_le_mul_of_nonneg_left hfirst hM)
    _ = (2 * M) * dist p q := by ring

/-- Arzelà–Ascoli for uniformly Lipschitz functions on the global domain.
The selected extensions converge on every closed coordinate triangle, with
the initial edge and axis included. -/
theorem ascoli_on_closed_triangle_exhaustion {f : ℕ → (ℝ × ℝ) → ℝ}
    {L : ℝ≥0} {B : ℝ}
    (hLip : ∀ n, LipschitzOnWith L (f n) globalDomain)
    (hbase : ∀ n, |f n (0, 1)| ≤ B) :
    ∃ (σ : ℕ → ℕ) (F : (ℝ × ℝ) → ℝ)
      (E : ℕ → (ℝ × ℝ) → ℝ),
      StrictMono σ ∧ Continuous F ∧
      (∀ n, LipschitzWith L (E n) ∧ EqOn (f n) (E n) globalDomain) ∧
      TendstoLocallyUniformly (fun n => E (σ n)) F atTop ∧
      (∀ a : ℝ, TendstoUniformlyOn (fun n => E (σ n)) F atTop
        (closedCoordTriangle 0 a)) ∧
      ∀ p ∈ globalDomain, Tendsto (fun n => f (σ n) p) atTop (𝓝 (F p)) := by
  choose E hE hEq using fun n => (hLip n).extend_real
  have hb : ∀ K : Set (ℝ × ℝ), IsCompact K →
      ∃ C : ℝ, ∀ n x, x ∈ K → |E n x| ≤ C := by
    intro K hK
    obtain ⟨R, hR⟩ := (hK.image (continuous_id.dist continuous_const)).bddAbove
    refine ⟨B + L * R, fun n x hx => ?_⟩
    have hdist : dist x (0, 1) ≤ R := hR ⟨x, hx, rfl⟩
    have hanchor : |E n (0, 1)| ≤ B := by
      rw [← hEq n (show (0, 1) ∈ globalDomain from ⟨le_rfl, zero_lt_one⟩)]
      exact hbase n
    calc
      |E n x| ≤ |E n (0, 1)| + |E n x - E n (0, 1)| := by
        simpa only [add_sub_cancel] using abs_add_le (E n (0, 1)) (E n x - E n (0, 1))
      _ ≤ B + L * dist x (0, 1) := add_le_add hanchor ((hE n).dist_le_mul x (0, 1))
      _ ≤ B + L * R := add_le_add_right (mul_le_mul_of_nonneg_left hdist L.coe_nonneg) B
  obtain ⟨σ, F, hσ, hF, hconv⟩ :=
    ArzelaAscoli.exists_strictMono_tendstoLocallyUniformly_of_lipschitzOnWith
      (fun K _ => ⟨L, fun n => (hE n).lipschitzOnWith⟩) hb
  refine ⟨σ, F, E, hσ, hF, fun n => ⟨hE n, hEq n⟩, hconv,
    fun a => tendstoLocallyUniformly_iff_forall_isCompact.mp hconv _
      (isCompact_closedCoordTriangle 0 a), ?_⟩
  intro p hp
  have h := hconv.tendstoLocallyUniformlyOn.tendsto_at hp
  exact h.congr' (Eventually.of_forall (fun n => (hEq (σ n) hp).symm))

/-- The smooth radius has a universal Lipschitz bound. -/
theorem SmoothSolutionBounds.radius_lipschitz
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) :
    LipschitzOnWith 2 (fun p : ℝ × ℝ => S.r p.1 p.2) globalDomain := by
  have hl := lipschitzOnWith_of_null_primitives (M := 1) (by norm_num)
    h.solution.solution.radius_out h.solution.solution.radius_in
  apply (by simpa only [mul_one] using hl)
  · intro p hp
    obtain ⟨hl, hu⟩ := h.amplitudes.lam p hp
    rw [abs_of_nonneg (by linarith only [hl])]
    exact hu.trans (by norm_num)
  · intro p hp
    obtain ⟨hl, hu⟩ := h.amplitudes.nu p hp
    rw [abs_of_nonpos (by linarith only [hu])]
    linarith only [hl]

/-- The smooth scalar radius has one common Lipschitz coefficient; only
the scalar offset in this coefficient depends on the datum. -/
theorem SmoothSolutionBounds.scalar_radius_lipschitz
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) :
    LipschitzOnWith ⟨2 * (4 * D.toReal + C),
        mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) h.offset_nonneg)⟩
      (fun p : ℝ × ℝ => S.r p.1 p.2 * S.phi p.1 p.2) globalDomain := by
  apply lipschitzOnWith_of_null_primitives (M := 4 * D.toReal + C)
    (add_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg) h.offset_nonneg)
    h.solution.solution.scalar_radius_out h.solution.solution.scalar_radius_in
  · intro p hp
    have ht := h.amplitudes.alpha p hp
    have hd := ENNReal.toReal_nonneg (a := D)
    linarith only [ht, hd, h.offset_nonneg]
  · intro p hp
    have ht := h.amplitudes.beta p hp
    linarith only [ht, h.offset_nonneg]

/-- The smooth mass has a Lipschitz coefficient depending only on variation. -/
theorem SmoothSolutionBounds.mass_lipschitz
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) :
    LipschitzOnWith ⟨2 * (100 * D.toReal ^ 2), by positivity⟩
      (fun p : ℝ × ℝ => S.m p.1 p.2) globalDomain :=
  lipschitzOnWith_of_null_primitives (by positivity)
    h.solution.solution.mass_out h.solution.solution.mass_in
    h.amplitudes.mass_out h.amplitudes.mass_in

/-- The global smooth geometry gives a lower radius bound on every section. -/
theorem SmoothSolutionBounds.radius_lower
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    (p.2 - p.1) / 3 ≤ S.r p.1 p.2 := by
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    IsBVSolution.radius_ge_of_lam_ge h.solution.solution.development h.solution.solution
      (fun q hq => (h.geometry q hq).1) hp

end ChristodoulouBV

end
