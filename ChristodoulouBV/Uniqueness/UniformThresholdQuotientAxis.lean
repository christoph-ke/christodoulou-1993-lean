module

public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientPoints
public import ChristodoulouBV.Uniqueness.QuotientAxis

/-!
# Package-uniform axis quotient trace
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Package-uniform version of the original quotient estimate. -/
theorem UniformThresholdBounds.beta_ratio_axis_le_A
    (P : UniformThresholdBounds) :
    ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
      P.Holds D.S₁ D.S₂ →
      ((∀ x y, (x, y) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ P.gapThreshold ∧
          (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ P.gapThreshold) →
      ∀ V, D.a < V → V < D.b →
        ∀ u ∈ Ico D.a V,
          ∃ l : ℝ,
            Tendsto (fun t =>
              D.S₁.beta u t / D.S₁.nu u t -
                D.S₂.beta u t / D.S₂.nu u t)
              (𝓝[>] u) (𝓝 l) ∧
            |l| ≤ D.A V) := by
  have hnorm := P.quotient_differences_le_norms
  intro D ha hb hP hsmall V haV hVb u hu
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
    exact (hnorm D ha hb hP hsmall V haV hVb u t
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
