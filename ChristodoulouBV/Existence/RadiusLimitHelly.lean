module

public import ChristodoulouBV.Existence.RadiusLimitSelection
import Mathlib.Tactic

/-!
# Simultaneous Helly selection on rational sections

Both scalar derivatives are included in the selection, while their limit
equations are proved in the scalar limit construction. Incoming sections include the endpoint `u = 0`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- Continuity of a smooth section at the initial edge preserves the sharp
variation bound when that edge is included. -/
theorem incoming_variation_initial_edge {f : (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f (closure globalDomain)) {v : ℝ} (hv : 0 < v) :
    eVariationOn (fun u => f (u, v)) (Ico 0 v) =
      eVariationOn (fun u => f (u, v)) (Ioo 0 v) := by
  have hc : ContinuousOn (fun u => f (u, v)) (Ico 0 v) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => subset_closure ⟨hu.1, hu.2⟩)
  apply eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hv
  exact (hc 0 ⟨le_rfl, hv⟩).mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hv)

/-- The incoming expansion variation includes `u = 0` with the same
universal coefficient. -/
theorem SmoothSolutionBounds.variation_nu_initial_edge
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {v : ℝ} (hv : 0 < v) :
    eVariationOn (fun u => S.nu u v) (Ico 0 v) ≤ s4UniversalC * D ^ 2 := by
  rw [incoming_variation_initial_edge h.solution.nu_c1.continuousOn hv]
  exact (h.variation_in v hv).2

/-- The incoming scalar derivative variation also includes the initial
endpoint, retaining its scalar-offset term. -/
theorem SmoothSolutionBounds.variation_beta_initial_edge
    {a : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a D C S) {v : ℝ} (hv : 0 < v) :
    eVariationOn (fun u => S.beta u v) (Ico 0 v) ≤
      s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => S.beta p.1 p.2) (closure globalDomain) := by
    apply (h.solution.zeta_c1.continuousOn.add
      (h.solution.nu_c1.continuousOn.mul h.solution.phi_c1.continuousOn)).congr
    intro p hp
    simp only [Fields.zeta, Pi.add_apply, Pi.mul_apply]
    ring
  rw [incoming_variation_initial_edge hc hv]
  exact h.raw_variation_in v hv

/-- Helly selection for an arbitrary encodable family of section problems. -/
theorem helly_selection_encodable {ι : Type*} [Encodable ι] [Inhabited ι]
    {s : ι → Set ℝ} {f : ι → ℕ → ℝ → ℝ} {M : ℝ} {V : ℝ≥0∞}
    (hbound : ∀ i n x, x ∈ s i → |f i n x| ≤ M)
    (hvar : ∀ i n, eVariationOn (f i n) (s i) ≤ V) (hV : V < ∞) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i x, x ∈ s i → ∃ l : ℝ, Tendsto (fun n => f i (σ n) x) atTop (𝓝 l) := by
  let e (k : ℕ) : ι := (Encodable.decode k).getD default
  have hextract (k : ℕ) (σ : ℕ → ℕ) (_hσ : StrictMono σ) :
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ x ∈ s (e k), ∃ l : ℝ,
        Tendsto (fun n => f (e k) (σ (τ n)) x) atTop (𝓝 l) := by
    obtain ⟨τ, hτ, g, hg, _⟩ := BoundedVariationOn.helly_selection_of_uniform_bound
      (fun n x hx => hbound (e k) (σ n) x hx)
      (fun n => hvar (e k) (σ n)) hV
    exact ⟨τ, hτ, fun x hx => ⟨g x, hg x hx⟩⟩
  obtain ⟨σ, hσ, hg⟩ := Filter.exists_subseq_tendsto_forall hextract
  refine ⟨σ, hσ, fun i x hx => ?_⟩
  obtain ⟨k, hk⟩ := Encodable.surjective_decode_getD ι default i
  have hk' : e k = i := hk
  subst i
  exact hg k x hx

/-- One Helly subsequence handles the expansions and both scalar
derivatives on every rational section. Incoming sections contain `u = 0`.
Only the variation parameter must be finite; no normalization of the
original scalar is imposed. -/
theorem s6_lam_nu_helly {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ v ∈ Ioi (q : ℝ),
        ∃ l, Tendsto (fun n => (T (σ n)).lam q v) atTop (𝓝 l)) ∧
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ u ∈ Ico (0 : ℝ) (q : ℝ),
        ∃ l, Tendsto (fun n => (T (σ n)).nu u q) atTop (𝓝 l)) ∧
      (∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ v ∈ Ioi (q : ℝ),
        ∃ l, Tendsto (fun n => (T (σ n)).alpha q v) atTop (𝓝 l)) ∧
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ u ∈ Ico (0 : ℝ) (q : ℝ),
        ∃ l, Tendsto (fun n => (T (σ n)).beta u q) atTop (𝓝 l)) := by
  let s : (Fin 4 × ℚ) → Set ℝ := fun i =>
    if i.1.val % 2 = 0 then {x | 0 ≤ (i.2 : ℝ) ∧ (i.2 : ℝ) < x}
    else {x | 0 ≤ x ∧ x < (i.2 : ℝ)}
  let f : (Fin 4 × ℚ) → ℕ → ℝ → ℝ := fun i n x =>
    if i.1.val = 0 then (T n).lam i.2 x
    else if i.1.val = 1 then (T n).nu x i.2
    else if i.1.val = 2 then (T n).alpha i.2 x else (T n).beta x i.2
  let V : ℝ≥0∞ := s4UniversalC * D ^ 2 +
    (s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2))
  have hV : V < ∞ := by
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD)), ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
          (lt_top_iff_ne_top.mpr hD), ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
              (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD)))⟩⟩
  have hb : ∀ i n x, x ∈ s i → |f i n x| ≤ 1 + 4 * D.toReal + C := by
    rintro ⟨i, q⟩ n x hx
    fin_cases i <;> simp only [s, f, Fin.reduceFinMk] at hx ⊢
    · change 0 ≤ (q : ℝ) ∧ (q : ℝ) < x at hx
      change |(T n).lam q x| ≤ _
      have ht := (h n).amplitudes.lam (q, x) hx
      rw [abs_of_nonneg (by linarith only [ht.1])]
      linarith only [ht.2, ENNReal.toReal_nonneg (a := D), (h n).offset_nonneg]
    · change 0 ≤ x ∧ x < (q : ℝ) at hx
      change |(T n).nu x q| ≤ _
      have ht := (h n).amplitudes.nu (x, q) hx
      rw [abs_of_nonpos (by linarith only [ht.2])]
      linarith only [ht.1, ENNReal.toReal_nonneg (a := D), (h n).offset_nonneg]
    · change 0 ≤ (q : ℝ) ∧ (q : ℝ) < x at hx
      change |(T n).alpha q x| ≤ _
      have ht := (h n).amplitudes.alpha (q, x) hx
      linarith only [ht, ENNReal.toReal_nonneg (a := D), (h n).offset_nonneg]
    · change 0 ≤ x ∧ x < (q : ℝ) at hx
      change |(T n).beta x q| ≤ _
      have ht := (h n).amplitudes.beta (x, q) hx
      linarith only [ht, (h n).offset_nonneg]
  have hv : ∀ i n, eVariationOn (f i n) (s i) ≤ V := by
    rintro ⟨i, q⟩ n
    fin_cases i <;> simp only [s, f, Fin.reduceFinMk]
    · change eVariationOn ((T n).lam q) {x | 0 ≤ (q : ℝ) ∧ (q : ℝ) < x} ≤ V
      by_cases hq : 0 ≤ (q : ℝ)
      · rw [show {x : ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < x} = Ioi (q : ℝ) by
          ext x; simp only [mem_ofPred_eq, mem_Ioi, hq, true_and]]
        exact ((h n).variation_out q hq).2.trans
          (le_self_add : s4UniversalC * D ^ 2 ≤ V)
      · simp only [hq, false_and, ofPred_false,
          eVariationOn.subsingleton _ subsingleton_empty, zero_le]
    · change eVariationOn (fun u => (T n).nu u q) (Ico 0 (q : ℝ)) ≤ V
      by_cases hq : 0 < (q : ℝ)
      · exact ((h n).variation_nu_initial_edge hq).trans
          (le_self_add : s4UniversalC * D ^ 2 ≤ V)
      · rw [Ico_eq_empty_of_le (le_of_not_gt hq), eVariationOn.subsingleton _ subsingleton_empty]
        exact zero_le
    · change eVariationOn ((T n).alpha q) {x | 0 ≤ (q : ℝ) ∧ (q : ℝ) < x} ≤ V
      by_cases hq : 0 ≤ (q : ℝ)
      · rw [show {x : ℝ | 0 ≤ (q : ℝ) ∧ (q : ℝ) < x} = Ioi (q : ℝ) by
          ext x; simp only [mem_ofPred_eq, mem_Ioi, hq, true_and]]
        exact ((h n).raw_variation_out q hq).trans
          (le_add_self : s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2) ≤ V)
      · simp only [hq, false_and, ofPred_false,
          eVariationOn.subsingleton _ subsingleton_empty, zero_le]
    · change eVariationOn (fun u => (T n).beta u q) (Ico 0 (q : ℝ)) ≤ V
      by_cases hq : 0 < (q : ℝ)
      · exact ((h n).variation_beta_initial_edge hq).trans
          (le_add_self : s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2) ≤ V)
      · rw [Ico_eq_empty_of_le (le_of_not_gt hq), eVariationOn.subsingleton _ subsingleton_empty]
        exact zero_le
  obtain ⟨σ, hσ, hg⟩ := helly_selection_encodable hb hv hV
  refine ⟨σ, hσ, ?_, ?_, ?_, ?_⟩
  · intro q hq v hv
    simpa [f] using hg (0, q) v (by simpa [s] using And.intro hq hv)
  · intro q hq u hu
    simpa [f] using hg (1, q) u (by simpa [s] using hu)
  · intro q hq v hv
    simpa [f] using hg (2, q) v (by simpa [s] using And.intro hq hv)
  · intro q hq u hu
    simpa [f] using hg (3, q) u (by simpa [s] using hu)

end ChristodoulouBV

end
