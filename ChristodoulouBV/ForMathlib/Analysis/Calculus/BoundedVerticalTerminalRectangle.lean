module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.BoundedDerivativeEndpoint
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Joint continuity of a terminal rectangle trace

A field continuous on each closed lower rectangle remains jointly continuous
after adjoining the top edge when its vertical modulus is uniform in the
horizontal coordinate. The proof approximates the field uniformly by
clipping the vertical coordinate below the top.
-/

public section

open Set

/-- A uniform vertical Lipschitz bound upgrades continuity below the top
edge to joint continuity on the closed rectangle, including its corners. -/
theorem continuousOn_closed_rectangle_of_vertical_lipschitz
    {u₀ u₁ v₀ v₁ M : ℝ} {F : ℝ × ℝ → ℝ}
    (_hu : u₀ ≤ u₁) (hv : v₀ < v₁) (hM : 0 ≤ M)
    (hlower : ∀ t ∈ Ico v₀ v₁,
      ContinuousOn F (Icc u₀ u₁ ×ˢ Icc v₀ t))
    (hvertical : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      ∀ w ∈ Icc v₀ v₁, |F (u, v) - F (u, w)| ≤ M * |v - w|) :
    ContinuousOn F (Icc u₀ u₁ ×ˢ Icc v₀ v₁) := by
  let K : Set (ℝ × ℝ) := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  have hM1 : 0 < M + 1 := by linarith
  have hleft : max v₀ (v₁ - ε / (M + 1)) < v₁ := by
    apply max_lt hv
    exact sub_lt_self v₁ (div_pos hε hM1)
  obtain ⟨t, htLeft, htRight⟩ := exists_between hleft
  have ht : t ∈ Ico v₀ v₁ := ⟨(le_max_left _ _).trans htLeft.le, htRight⟩
  let G : ℝ × ℝ → ℝ := fun p => F (p.1, min p.2 t)
  have hclip : Continuous (fun p : ℝ × ℝ => (p.1, min p.2 t)) :=
    continuous_fst.prodMk (continuous_snd.min continuous_const)
  have hG : ContinuousOn G K := by
    apply (hlower t ht).comp hclip.continuousOn
    intro p hp
    exact ⟨hp.1, ⟨le_min hp.2.1 ht.1, min_le_right _ _⟩⟩
  refine ⟨G, hG, ?_⟩
  intro p hp
  apply hεU
  change |F p - G p| < ε
  have hmin : min p.2 t ∈ Icc v₀ v₁ :=
    ⟨le_min hp.2.1 ht.1, (min_le_right _ _).trans htRight.le⟩
  have hbound := hvertical p.1 hp.1 p.2 hp.2 (min p.2 t) hmin
  have hdiff0 : 0 ≤ p.2 - min p.2 t := sub_nonneg.mpr (min_le_left _ _)
  have hdiff : p.2 - min p.2 t ≤ v₁ - t := by
    rcases le_total p.2 t with hpt | htp
    · rw [min_eq_left hpt]
      linarith
    · rw [min_eq_right htp]
      linarith [hp.2.2]
  have hsmall : (M + 1) * (v₁ - t) < ε := by
    have hlt : v₁ - t < ε / (M + 1) := by
      have h := (le_max_right v₀ (v₁ - ε / (M + 1))).trans_lt htLeft
      linarith
    calc
      (M + 1) * (v₁ - t) < (M + 1) * (ε / (M + 1)) :=
        mul_lt_mul_of_pos_left hlt hM1
      _ = ε := by field_simp
  have hMle : M * (v₁ - t) ≤ (M + 1) * (v₁ - t) := by
    have : 0 ≤ v₁ - t := sub_nonneg.mpr htRight.le
    nlinarith
  calc
    |F p - G p| ≤ M * |p.2 - min p.2 t| := hbound
    _ = M * (p.2 - min p.2 t) := by rw [abs_of_nonneg hdiff0]
    _ ≤ M * (v₁ - t) := mul_le_mul_of_nonneg_left hdiff hM
    _ ≤ (M + 1) * (v₁ - t) := hMle
    _ < ε := hsmall

/-- A uniform vertical derivative bound on lower rectangles gives a jointly
continuous extension to their common top edge. -/
theorem exists_continuousOn_closed_rectangle_of_vertical_deriv_bound
    {u₀ u₁ v₀ v₁ M : ℝ} {f : ℝ × ℝ → ℝ}
    (hu : u₀ ≤ u₁) (hv : v₀ < v₁) (hM : 0 ≤ M)
    (hlower : ∀ t ∈ Ico v₀ v₁,
      ContinuousOn f (Icc u₀ u₁ ×ˢ Icc v₀ t))
    (hdiff : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ioo v₀ v₁,
      DifferentiableAt ℝ (fun w => f (u, w)) v)
    (hbound : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ioo v₀ v₁,
      |deriv (fun w => f (u, w)) v| ≤ M) :
    ∃ F : ℝ × ℝ → ℝ,
      ContinuousOn F (Icc u₀ u₁ ×ˢ Icc v₀ v₁) ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ico v₀ v₁, F (u, v) = f (u, v) := by
  have hExt (u : ℝ) (hu' : u ∈ Icc u₀ u₁) :
      ∃ g : ℝ → ℝ, LipschitzWith ⟨M, hM⟩ g ∧
        EqOn (fun v => f (u, v)) g (Ico v₀ v₁) := by
    have hLip : LipschitzOnWith ⟨M, hM⟩ (fun v => f (u, v))
        (Ico v₀ v₁) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hmax : max x y < v₁ := max_lt hx.2 hy.2
      obtain ⟨t, htMax, htStar⟩ := exists_between hmax
      have hv₀t : v₀ < t := lt_of_le_of_lt (hx.1.trans (le_max_left x y)) htMax
      have ht : t ∈ Ico v₀ v₁ := ⟨hv₀t.le, htStar⟩
      have hslice : ContinuousOn (fun v => f (u, v)) (Icc v₀ t) :=
        (hlower t ht).comp (continuous_const.prodMk continuous_id).continuousOn
          (fun v hv' => ⟨hu', hv'⟩)
      have hinner : ∀ v ∈ Ioo v₀ t,
          DifferentiableAt ℝ (fun w => f (u, w)) v := by
        intro v hv'
        exact hdiff u hu' v ⟨hv'.1, hv'.2.trans htStar⟩
      have hinnerBound : ∀ v ∈ Ioo v₀ t,
          |deriv (fun w => f (u, w)) v| ≤ M := by
        intro v hv'
        exact hbound u hu' v ⟨hv'.1, hv'.2.trans htStar⟩
      have hLipIcc := lipschitzOnWith_Icc_of_continuousOn_deriv_bound_Ioo
        hv₀t hM hslice hinner hinnerBound
      exact hLipIcc.dist_le_mul x ⟨hx.1, (le_max_left _ _).trans htMax.le⟩
        y ⟨hy.1, (le_max_right _ _).trans htMax.le⟩
    exact hLip.extend_real
  let g : ℝ → ℝ → ℝ := fun u =>
    if h : u ∈ Icc u₀ u₁ then Classical.choose (hExt u h) else fun _ => 0
  let F : ℝ × ℝ → ℝ := fun p => g p.1 p.2
  have hgLip (u : ℝ) (hu' : u ∈ Icc u₀ u₁) :
      LipschitzWith ⟨M, hM⟩ (g u) := by
    simpa only [g, dite_eq_left hu'] using (Classical.choose_spec (hExt u hu')).1
  have hgEq (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (hv' : v ∈ Ico v₀ v₁) : F (u, v) = f (u, v) := by
    have heq := (Classical.choose_spec (hExt u hu')).2 hv'
    simpa only [F, g, dite_eq_left hu'] using heq.symm
  have hFLower (t : ℝ) (ht : t ∈ Ico v₀ v₁) :
      ContinuousOn F (Icc u₀ u₁ ×ˢ Icc v₀ t) := by
    apply (hlower t ht).congr
    intro p hp
    exact hgEq p.1 hp.1 p.2 ⟨hp.2.1, hp.2.2.trans_lt ht.2⟩
  have hFVertical (u : ℝ) (hu' : u ∈ Icc u₀ u₁)
      (v : ℝ) (_hv' : v ∈ Icc v₀ v₁)
      (w : ℝ) (_hw' : w ∈ Icc v₀ v₁) :
      |F (u, v) - F (u, w)| ≤ M * |v - w| := by
    have h := (hgLip u hu').dist_le_mul v w
    change |g u v - g u w| ≤ M * |v - w| at h
    exact h
  exact ⟨F, continuousOn_closed_rectangle_of_vertical_lipschitz hu hv hM
    hFLower hFVertical, hgEq⟩

end
