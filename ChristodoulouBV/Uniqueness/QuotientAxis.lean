module

public import ChristodoulouBV.Uniqueness.QuotientNormPoints
public import ChristodoulouBV.BVSolution.AxisIntegrals

/-!
# Scalar quotient transport in the comparison triangle

The axis data and quotient equations are stated on the full comparison
triangle. Auxiliary density norms sample the fixed good incoming rays.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The quotient axis identity for two BV solutions needs only access to a
normalized full triangle. It uses each solution's own axis traces. -/
theorem beta_ratio_axis_match
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b u v : ℝ} (ha : a = 0) (hab : a < b)
    (hT : triangle a b ⊆ U₁ ∩ U₂)
    (huv : (u, v) ∈ triangle a b) :
    ∃ l : ℝ,
      Tendsto (fun t =>
        S₁.beta u t / S₁.nu u t - S₂.beta u t / S₂.nu u t)
        (𝓝[>] u) (𝓝 l) ∧
      Tendsto (fun t =>
        S₁.alpha u t / S₁.lam u t - S₂.alpha u t / S₂.lam u t)
        (𝓝[>] u) (𝓝 l) := by
  have hsingle {U : Set (ℝ × ℝ)} {S : Fields}
      (h : IsBVSolution U S) (haccess : triangle a b ⊆ U) :
      ∃ P : ℝ,
        Tendsto (fun t => S.beta u t / S.nu u t)
          (𝓝[>] u) (𝓝 P) ∧
        Tendsto (fun t => S.alpha u t / S.lam u t)
          (𝓝[>] u) (𝓝 P) := by
    let w := (a + b) / 2
    have haw : a < w := by dsimp [w]; linarith [hab]
    have hwb : w < b := by dsimp [w]; linarith [hab]
    have href : (0, w) ∈ U := by
      simpa only [ha] using haccess
        ((mem_triangle).2 ⟨le_rfl, haw, hwb⟩)
    have hpair : triangle a b ⊆ U ∩ U := by
      intro p hp
      exact ⟨haccess hp, haccess hp⟩
    obtain ⟨c, C, hc, _, htraces⟩ :=
      h.preloc_axis_traces h ⟨href, href⟩ rfl
    obtain ⟨L, P, hL, _, _, hLam, hNu, _, hAlpha, hBeta, _, _⟩ :=
      htraces a b u v hpair huv S (Or.inl rfl)
    have hLne : L ≠ 0 := ne_of_gt (hc.trans_le hL)
    have hNegNe : -L ≠ 0 := neg_ne_zero.mpr hLne
    have hβ : Tendsto (fun t => S.beta u t / S.nu u t)
        (𝓝[>] u) (𝓝 P) := by
      have hh := hBeta.div hNu hNegNe
      have hval : -(L * P) / -L = P := by field_simp [hLne]
      have hfun : (S.beta u / S.nu u) =
          (fun t => S.beta u t / S.nu u t) := by
        funext t
        exact Pi.div_apply (S.beta u) (S.nu u) t
      rw [hfun, hval] at hh
      exact hh
    have hα : Tendsto (fun t => S.alpha u t / S.lam u t)
        (𝓝[>] u) (𝓝 P) := by
      have hh := hAlpha.div hLam hLne
      have hval : L * P / L = P := by field_simp [hLne]
      have hfun : (S.alpha u / S.lam u) =
          (fun t => S.alpha u t / S.lam u t) := by
        funext t
        exact Pi.div_apply (S.alpha u) (S.lam u) t
      rw [hfun, hval] at hh
      exact hh
    exact ⟨P, hβ, hα⟩
  obtain ⟨P₁, hβ₁, hα₁⟩ := hsingle h₁ (fun p hp => (hT hp).1)
  obtain ⟨P₂, hβ₂, hα₂⟩ := hsingle h₂ (fun p hp => (hT hp).2)
  exact ⟨P₁ - P₂, hβ₁.sub hβ₂, hα₁.sub hα₂⟩

/-- At an accessible axis point the incoming scalar quotient and outgoing
scalar quotient of each solution have the same one-sided limit. This is the
axis datum for the difference of the two `β/ν` quotients. -/
theorem ComparisonData.beta_ratio_axis_match (D : ComparisonData)
    (ha : D.a = 0) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    Tendsto (fun t =>
      (D.S₁.beta u t / D.S₁.nu u t - D.S₂.beta u t / D.S₂.nu u t) -
      (D.S₁.alpha u t / D.S₁.lam u t - D.S₂.alpha u t / D.S₂.lam u t))
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  let w := (D.a + D.b) / 2
  have haw : D.a < w := by dsimp [w]; linarith [D.hab]
  have hwb : w < D.b := by dsimp [w]; linarith [D.hab]
  have hwT : (D.a, w) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, haw, hwb⟩
  have hw := D.hT hwT
  have hdata := (D.hdata w ⟨haw, hwb⟩).2
  obtain ⟨c, C, hc, _, htraces⟩ :=
    D.h₁.preloc_axis_traces D.h₂ (by simpa only [ha] using hw) (by simpa only [ha] using hdata)
  have hsingle (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      Tendsto (fun t => S.beta u t / S.nu u t - S.alpha u t / S.lam u t)
        (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    obtain ⟨L, P, hL, _, _, hLam, hNu, _, hAlpha, hBeta, _, _⟩ :=
      htraces D.a D.b u v D.hT huv S hS
    have hLpos : 0 < L := hc.trans_le hL
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hNegNe : -L ≠ 0 := neg_ne_zero.mpr hLne
    have hβ : Tendsto (fun t => S.beta u t / S.nu u t)
        (𝓝[>] u) (𝓝 P) := by
      have hh := hBeta.div hNu hNegNe
      have hval : -(L * P) / -L = P := by field_simp [hLne]
      have hfun : (S.beta u / S.nu u) =
          (fun t => S.beta u t / S.nu u t) := by
        funext t
        exact Pi.div_apply (S.beta u) (S.nu u) t
      rw [hfun, hval] at hh
      exact hh
    have hα : Tendsto (fun t => S.alpha u t / S.lam u t)
        (𝓝[>] u) (𝓝 P) := by
      have hh := hAlpha.div hLam hLne
      have hval : L * P / L = P := by field_simp [hLne]
      have hfun : (S.alpha u / S.lam u) =
          (fun t => S.alpha u t / S.lam u t) := by
        funext t
        exact Pi.div_apply (S.alpha u) (S.lam u) t
      rw [hfun, hval] at hh
      exact hh
    simpa only [sub_self] using hβ.sub hα
  have h₁ := hsingle D.S₁ (Or.inl rfl)
  have h₂ := hsingle D.S₂ (Or.inr rfl)
  have heq : (fun t =>
      (D.S₁.beta u t / D.S₁.nu u t - D.S₂.beta u t / D.S₂.nu u t) -
      (D.S₁.alpha u t / D.S₁.lam u t - D.S₂.alpha u t / D.S₂.lam u t)) =
      (fun t =>
        (D.S₁.beta u t / D.S₁.nu u t - D.S₁.alpha u t / D.S₁.lam u t) -
        (D.S₂.beta u t / D.S₂.nu u t - D.S₂.alpha u t / D.S₂.lam u t)) := by
    funext t
    ring
  rw [heq]
  simpa only [sub_self] using h₁.sub h₂

/-- The one-sided outgoing quotient difference at the axis is bounded by the
good-ray `A` norm. The `β/ν` trace is the same limit by the axis matching
identity, and no exceptional value of `α` is asserted. -/
theorem ComparisonData.beta_ratio_axis_le_A (D : ComparisonData)
    (ha : D.a = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ((∀ x y, (x, y) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ ε₀) →
      ∀ V, D.a < V → V < D.b →
        ∀ u ∈ Ico D.a V,
          ∃ l : ℝ,
            Tendsto (fun t =>
              D.S₁.beta u t / D.S₁.nu u t -
                D.S₂.beta u t / D.S₂.nu u t)
              (𝓝[>] u) (𝓝 l) ∧
            |l| ≤ D.A V) := by
  obtain ⟨ε₀, hε₀, hnorm⟩ := D.quotient_differences_le_norms ha
  refine ⟨ε₀, hε₀, ?_⟩
  intro hsmall V haV hVb u hu
  have hpt : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by
    dsimp [w]
    constructor <;> linarith [D.hab]
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT ((mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩)
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨c, C, hc, _, htraces⟩ :=
    D.h₁.preloc_axis_traces D.h₂ href hdata
  have hsingle (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      ∃ P : ℝ,
        Tendsto (fun t => S.alpha u t / S.lam u t)
          (𝓝[>] u) (𝓝 P) := by
    obtain ⟨L, P, hL, _, _, hLam, _, _, hAlpha, _, _, _⟩ :=
      htraces D.a D.b u V D.hT hpt S hS
    have hLne : L ≠ 0 := ne_of_gt (hc.trans_le hL)
    have hh := hAlpha.div hLam hLne
    have hfun : (S.alpha u / S.lam u) =
        (fun t => S.alpha u t / S.lam u t) := by
      funext t
      exact Pi.div_apply (S.alpha u) (S.lam u) t
    rw [hfun] at hh
    have hval : L * P / L = P := by field_simp [hLne]
    rw [hval] at hh
    exact ⟨P, hh⟩
  obtain ⟨P₁, hP₁⟩ := hsingle D.S₁ (Or.inl rfl)
  obtain ⟨P₂, hP₂⟩ := hsingle D.S₂ (Or.inr rfl)
  let l := P₁ - P₂
  have hα : Tendsto (fun t =>
      D.S₁.alpha u t / D.S₁.lam u t -
        D.S₂.alpha u t / D.S₂.lam u t)
      (𝓝[>] u) (𝓝 l) := hP₁.sub hP₂
  have hGcl : u ∈ closure (D.goodV ∩ Ioo u V) := by
    have hs : Ioo u V ⊆ closure (D.goodV ∩ Ioo u V) := by
      simpa only [inter_comm] using
        (D.goodV_properties).2.1.open_subset_closure_inter isOpen_Ioo
    have hs' := closure_mono hs
    rw [closure_closure, closure_Ioo (ne_of_lt hu.2)] at hs'
    exact hs' ⟨le_rfl, hu.2.le⟩
  have hne : (𝓝[D.goodV ∩ Ioo u V] u).NeBot :=
    mem_closure_iff_clusterPt.mp hGcl
  have hfilter : 𝓝[D.goodV ∩ Ioo u V] u ≤ 𝓝[>] u := by
    apply nhdsWithin_mono
    intro x hx
    exact hx.2.1
  have hlim : Tendsto
      (fun t => |D.S₁.alpha u t / D.S₁.lam u t -
        D.S₂.alpha u t / D.S₂.lam u t|)
      (𝓝[D.goodV ∩ Ioo u V] u) (𝓝 |l|) :=
    hα.abs.mono_left hfilter
  have hbound : |l| ≤ D.A V := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hnorm hsmall V haV hVb u t
      ((mem_triangle).2 ⟨hu.1, ht.2.1, ht.2.2⟩)).1 ht.1
  have hmatch := D.beta_ratio_axis_match ha hpt
  have hβ : Tendsto (fun t =>
      D.S₁.beta u t / D.S₁.nu u t -
        D.S₂.beta u t / D.S₂.nu u t)
      (𝓝[>] u) (𝓝 l) := by
    have hh := hmatch.add hα
    simpa only [zero_add, sub_add_cancel] using hh
  exact ⟨l, hβ, hbound⟩

end ChristodoulouBV.Uniqueness

end
