module

public import ChristodoulouBV.ForMathlib.BoundedVariation.HellyMonotone
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Helly selection for real functions of bounded variation

Uniform variation and a bound at one point give a pointwise convergent subsequence on an
arbitrary subset of the real line. The limit has no larger variation.
-/

public section

open Filter Set
open scoped Topology ENNReal

namespace eVariationOn

/-- Variation is bounded by the liminf of variations under pointwise convergence on the set. -/
theorem le_liminf_of_tendsto {s : Set ℝ} {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (h : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    eVariationOn g s ≤ liminf (fun n => eVariationOn (F n) s) atTop := by
  rw [le_liminf_iff]
  intro v hv
  exact lowerSemicontinuous_aux h hv

end eVariationOn

namespace BoundedVariationOn

/-- Helly's selection theorem on an arbitrary subset of the real line. The common variation
bound must be finite; a bound of `∞` does not give sequential compactness. -/
theorem helly_selection {s : Set ℝ} {f : ℕ → ℝ → ℝ} {x₀ M : ℝ} {C : ℝ≥0∞}
    (hx₀ : x₀ ∈ s) (hpoint : ∀ n, |f n x₀| ≤ M)
    (hvar : ∀ n, eVariationOn (f n) s ≤ C) (hC : C < ∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      (∀ x ∈ s, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x))) ∧
      eVariationOn g s ≤ C := by
  have hCne : C ≠ ∞ := ne_of_lt hC
  have hV (n : ℕ) : BoundedVariationOn (f n) s :=
    (ne_of_lt ((hvar n).trans_lt hC))
  have hVreal (n : ℕ) : (eVariationOn (f n) s).toReal ≤ C.toReal :=
    ENNReal.toReal_mono hCne (hvar n)
  have hfBound (n : ℕ) (x : ℝ) (hx : x ∈ s) : |f n x| ≤ M + C.toReal := by
    have h₁ := (hV n).sub_le hx hx₀
    have h₂ := (hV n).sub_le hx₀ hx
    have h₃ := abs_le.mp (hpoint n)
    apply abs_le.mpr
    constructor <;> linarith [hVreal n]
  let w (n : ℕ) (x : ℝ) : ℝ := variationOnFromTo (f n) s x₀ x
  let p (n : ℕ) (x : ℝ) : ℝ := w n x + f n x
  let q (n : ℕ) (x : ℝ) : ℝ := w n x - f n x
  have hwBound (n : ℕ) (x : ℝ) : |w n x| ≤ C.toReal :=
    (variationOnFromTo.abs_le_eVariationOn (hV n)).trans (hVreal n)
  have hpBound (n : ℕ) (x : ℝ) (hx : x ∈ s) : |p n x| ≤ M + 2 * C.toReal := by
    calc
      |p n x| ≤ |w n x| + |f n x| := abs_add_le _ _
      _ ≤ C.toReal + (M + C.toReal) := add_le_add (hwBound n x) (hfBound n x hx)
      _ = M + 2 * C.toReal := by ring
  have hqBound (n : ℕ) (x : ℝ) (hx : x ∈ s) : |q n x| ≤ M + 2 * C.toReal := by
    have hsub : |q n x| ≤ |w n x| + |f n x| := by
      dsimp [q]
      simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (w n x) (-f n x))
    calc
      |q n x| ≤ |w n x| + |f n x| := hsub
      _ ≤ C.toReal + (M + C.toReal) := add_le_add (hwBound n x) (hfBound n x hx)
      _ = M + 2 * C.toReal := by ring
  have hpMono (n : ℕ) : MonotoneOn (p n) s := by
    intro x hx y hy hxy
    simpa only [p, w, Pi.add_apply] using
      (variationOnFromTo.add_self_monotoneOn (hV n).locallyBoundedVariationOn hx₀) hx hy hxy
  have hqMono (n : ℕ) : MonotoneOn (q n) s := by
    intro x hx y hy hxy
    simpa only [q, w, Pi.sub_apply] using
      (variationOnFromTo.sub_self_monotoneOn (hV n).locallyBoundedVariationOn hx₀) hx hy hxy
  obtain ⟨φ, hφ, P, _, hP⟩ := MonotoneOn.helly_selection hpMono hpBound
  obtain ⟨ψ, hψ, Q, _, hQ⟩ := MonotoneOn.helly_selection
    (f := fun n => q (φ n)) (fun n => hqMono (φ n))
    (fun n x hx => hqBound (φ n) x hx)
  let g : ℝ → ℝ := fun x => (P x - Q x) / 2
  have hlimit (x : ℝ) (hx : x ∈ s) :
      Tendsto (fun n => f (φ (ψ n)) x) atTop (𝓝 (g x)) := by
    have hp := (hP x hx).comp hψ.tendsto_atTop
    have hq := hQ x hx
    have h := (hp.sub hq).div_const (2 : ℝ)
    have hrepr (n : ℕ) : f (φ (ψ n)) x =
        (p (φ (ψ n)) x - q (φ (ψ n)) x) / 2 := by
      dsimp [p, q]
      ring
    simpa only [g, hrepr, Function.comp_apply] using h
  refine ⟨φ ∘ ψ, hφ.comp hψ, g, ?_, ?_⟩
  · exact fun x hx => hlimit x hx
  · by_contra hnot
    have hlt : C < eVariationOn g s := lt_of_not_ge hnot
    have hev := eVariationOn.lowerSemicontinuous_aux hlimit hlt
    obtain ⟨n, hn⟩ := hev.exists
    exact (not_lt_of_ge (hvar (φ (ψ n)))) hn

/-- Uniform pointwise boundedness is a convenient sufficient condition for Helly selection. -/
theorem helly_selection_of_uniform_bound {s : Set ℝ} {f : ℕ → ℝ → ℝ} {M : ℝ}
    {C : ℝ≥0∞} (hbound : ∀ n x, x ∈ s → |f n x| ≤ M)
    (hvar : ∀ n, eVariationOn (f n) s ≤ C) (hC : C < ∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      (∀ x ∈ s, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x))) ∧
      eVariationOn g s ≤ C := by
  by_cases hs : s.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hs
    exact helly_selection hx₀ (fun n => hbound n x₀ hx₀) hvar hC
  · have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    refine ⟨id, strictMono_id, 0, ?_, ?_⟩
    · simp [he]
    · simp [he]

/-- A single subsequence works for a countable family of bounded variation problems.
Each set, base point, pointwise bound, and finite variation bound may depend on the family index. -/
theorem helly_selection_countable {s : ℕ → Set ℝ} {f : ℕ → ℕ → ℝ → ℝ}
    {x₀ M : ℕ → ℝ} {C : ℕ → ℝ≥0∞}
    (hx₀ : ∀ k, x₀ k ∈ s k) (hpoint : ∀ k n, |f k n (x₀ k)| ≤ M k)
    (hvar : ∀ k n, eVariationOn (f k n) (s k) ≤ C k) (hC : ∀ k, C k < ∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℕ → ℝ → ℝ,
      (∀ k x, x ∈ s k → Tendsto (fun n => f k (φ n) x) atTop (𝓝 (g k x))) ∧
      ∀ k, eVariationOn (g k) (s k) ≤ C k := by
  have hextract (k : ℕ) (φ : ℕ → ℕ) (_hφ : StrictMono φ) :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ x ∈ s k, ∃ a : ℝ,
        Tendsto (fun n => f k (φ (ψ n)) x) atTop (𝓝 a) := by
    obtain ⟨ψ, hψ, g, hconv, _⟩ := helly_selection (hx₀ k)
      (fun n => hpoint k (φ n)) (fun n => hvar k (φ n)) (hC k)
    exact ⟨ψ, hψ, fun x hx => ⟨g x, hconv x hx⟩⟩
  obtain ⟨φ, hφ, hconv⟩ := Filter.exists_subseq_tendsto_forall hextract
  classical
  let g : ℕ → ℝ → ℝ := fun k x =>
    if hx : x ∈ s k then Classical.choose (hconv k x hx) else 0
  have hg (k : ℕ) (x : ℝ) (hx : x ∈ s k) :
      Tendsto (fun n => f k (φ n) x) atTop (𝓝 (g k x)) := by
    simpa only [g, dite_eq_left hx] using Classical.choose_spec (hconv k x hx)
  refine ⟨φ, hφ, g, hg, ?_⟩
  intro k
  by_contra hnot
  have hlt : C k < eVariationOn (g k) (s k) := lt_of_not_ge hnot
  have hev := eVariationOn.lowerSemicontinuous_aux (fun x hx => hg k x hx) hlt
  obtain ⟨n, hn⟩ := hev.exists
  exact (not_lt_of_ge (hvar k (φ n))) hn

/-- Helly selection with the sharper liminf bound on the variation of the limit. -/
theorem helly_selection_liminf {s : Set ℝ} {f : ℕ → ℝ → ℝ} {x₀ M : ℝ} {C : ℝ≥0∞}
    (hx₀ : x₀ ∈ s) (hpoint : ∀ n, |f n x₀| ≤ M)
    (hvar : ∀ n, eVariationOn (f n) s ≤ C) (hC : C < ∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      (∀ x ∈ s, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x))) ∧
      eVariationOn g s ≤ C ∧
      eVariationOn g s ≤ liminf (fun n => eVariationOn (f (φ n)) s) atTop := by
  obtain ⟨φ, hφ, g, hconv, hbound⟩ := helly_selection hx₀ hpoint hvar hC
  exact ⟨φ, hφ, g, hconv, hbound, eVariationOn.le_liminf_of_tendsto hconv⟩

end BoundedVariationOn

end
