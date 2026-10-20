module

public import ChristodoulouBV.ForMathlib.Gronwall.TwoVariable

/-!
# Two-conull-set Volterra comparison

The two characteristic past faces can each have an exceptional null set.
Masking both coordinate sets lets the established all-point Volterra theorem apply
without assigning equality to exceptional density representatives.
-/

public section

open Set MeasureTheory intervalIntegral

namespace ChristodoulouBV.Uniqueness

/-- A nonnegative bounded Volterra comparison vanishes on the product of
its two conull sets of good characteristic parameters. -/
theorem eq_zero_of_le_two_variable_volterra_ae_both
    {a a' b b' C B : ℝ} {F : ℝ → ℝ → ℝ}
    {P Q : Set ℝ}
    (haa' : a ≤ a') (hbb' : b ≤ b') (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hP : ∀ᵐ v : ℝ ∂volume, v ∈ P)
    (hQ : ∀ᵐ u : ℝ ∂volume, u ∈ Q)
    (hF0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F u v)
    (hFB : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F u v ≤ B)
    (hFu : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F s v) volume a u)
    (hFv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F u t) volume b v)
    (hineq : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      u ∈ Q → v ∈ P →
      F u v ≤ C * (∫ s in a..u, F s v) +
        C * (∫ t in b..v, F u t)) :
    ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      u ∈ Q → v ∈ P → F u v = 0 := by
  classical
  let F' : ℝ → ℝ → ℝ :=
    fun u v => if u ∈ Q ∧ v ∈ P then F u v else 0
  have hF'0 : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', 0 ≤ F' u v := by
    intro u hu v hv
    dsimp [F']
    split_ifs
    · exact hF0 u hu v hv
    · exact le_rfl
  have hF'B : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b', F' u v ≤ B := by
    intro u hu v hv
    dsimp [F']
    split_ifs
    · exact hFB u hu v hv
    · exact hB
  have hF'u : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun s => F' s v) volume a u := by
    intro u hu v hv
    by_cases hvP : v ∈ P
    · apply (hFu u hu v hv).congr_ae
      apply ae_restrict_of_ae
      filter_upwards [hQ] with s hs
      simp only [F', ite_eq_left (show s ∈ Q ∧ v ∈ P from ⟨hs, hvP⟩)]
    · have hzero : (fun s => F' s v) = fun _ => 0 := by
        funext s
        simp only [F', ite_eq_right (show ¬ (s ∈ Q ∧ v ∈ P) from
          fun h => hvP h.2)]
      rw [hzero]
      exact intervalIntegrable_const
  have hF'v : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      IntervalIntegrable (fun t => F' u t) volume b v := by
    intro u hu v hv
    by_cases huQ : u ∈ Q
    · apply (hFv u hu v hv).congr_ae
      apply ae_restrict_of_ae
      filter_upwards [hP] with t ht
      simp only [F', ite_eq_left (show u ∈ Q ∧ t ∈ P from ⟨huQ, ht⟩)]
    · have hzero : (fun t => F' u t) = fun _ => 0 := by
        funext t
        simp only [F', ite_eq_right (show ¬ (u ∈ Q ∧ t ∈ P) from
          fun h => huQ h.1)]
      rw [hzero]
      exact intervalIntegrable_const
  have hvertical (u v : ℝ) (huQ : u ∈ Q) :
      (∫ t in b..v, F' u t) = ∫ t in b..v, F u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hP] with t ht _
    simp only [F', ite_eq_left (show u ∈ Q ∧ t ∈ P from ⟨huQ, ht⟩)]
  have hhorizontal (u v : ℝ) (hvP : v ∈ P) :
      (∫ s in a..u, F' s v) = ∫ s in a..u, F s v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hQ] with s hs _
    simp only [F', ite_eq_left (show s ∈ Q ∧ v ∈ P from ⟨hs, hvP⟩)]
  have hineq' : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      F' u v ≤ C * (∫ s in a..u, F' s v) +
        C * (∫ t in b..v, F' u t) := by
    intro u hu v hv
    by_cases huQ : u ∈ Q
    · by_cases hvP : v ∈ P
      · simpa only [F', ite_eq_left
          (show u ∈ Q ∧ v ∈ P from ⟨huQ, hvP⟩),
          hhorizontal u v hvP, hvertical u v huQ] using
          hineq u hu v hv huQ hvP
      · have hIu : 0 ≤ ∫ s in a..u, F' s v := by
          apply intervalIntegral.integral_nonneg hu.1
          intro s hs
          exact hF'0 s ⟨hs.1, hs.2.trans hu.2⟩ v hv
        have hIv : 0 ≤ ∫ t in b..v, F' u t := by
          apply intervalIntegral.integral_nonneg hv.1
          intro t ht
          exact hF'0 u hu t ⟨ht.1, ht.2.trans hv.2⟩
        have hbad : F' u v = 0 := by
          simp only [F', ite_eq_right
            (show ¬ (u ∈ Q ∧ v ∈ P) from fun h => hvP h.2)]
        rw [hbad]
        exact add_nonneg (mul_nonneg hC hIu) (mul_nonneg hC hIv)
    · have hIu : 0 ≤ ∫ s in a..u, F' s v := by
        apply intervalIntegral.integral_nonneg hu.1
        intro s hs
        exact hF'0 s ⟨hs.1, hs.2.trans hu.2⟩ v hv
      have hIv : 0 ≤ ∫ t in b..v, F' u t := by
        apply intervalIntegral.integral_nonneg hv.1
        intro t ht
        exact hF'0 u hu t ⟨ht.1, ht.2.trans hv.2⟩
      have hbad : F' u v = 0 := by
        simp only [F', ite_eq_right
          (show ¬ (u ∈ Q ∧ v ∈ P) from fun h => huQ h.1)]
      rw [hbad]
      exact add_nonneg (mul_nonneg hC hIu) (mul_nonneg hC hIv)
  have hzero := eq_zero_of_le_two_variable_volterra haa' hbb' hC hB
    hF'0 hF'B hF'u hF'v hineq'
  intro u hu v hv huQ hvP
  simpa only [F', ite_eq_left
    (show u ∈ Q ∧ v ∈ P from ⟨huQ, hvP⟩)] using hzero u hu v hv

end ChristodoulouBV.Uniqueness

end
