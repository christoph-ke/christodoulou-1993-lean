module

public import ChristodoulouBV.ForMathlib.BoundedVariation.Mollify
public import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives
public import ChristodoulouBV.ForMathlib.BoundedVariation.Helly
import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Approximation of BV initial data

The initial datum in Theorem 6.2 is specified pointwise, with no convention at
jumps.  The zero-variation and right-continuous cases are recorded here as
preliminary interfaces for the arbitrary-representative construction.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

private noncomputable def smoothStep (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a))

private theorem smoothStep_contDiff (a b : ℝ) :
    ContDiff ℝ 1 (smoothStep a b) := by
  unfold smoothStep
  fun_prop

private theorem smoothStep_zero_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    smoothStep a b x = 0 := by
  unfold smoothStep
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le

private theorem smoothStep_one_of_ge {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    smoothStep a b x = 1 := by
  unfold smoothStep
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div₀ (sub_pos.mpr hab)).2
  linarith

private theorem smoothStep_monotone {a b : ℝ} (hab : a < b) :
    Monotone (smoothStep a b) := by
  apply Real.smoothTransition.monotone.comp
  intro x y hxy
  dsimp [smoothStep]
  exact (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)

private theorem smoothStep_variation_le_one {a b : ℝ} (hab : a < b) :
    eVariationOn (smoothStep a b) Set.univ ≤ 1 := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, iSup_le_iff]
  rintro ⟨x, y⟩ hxy
  rw [((smoothStep_monotone hab).monotoneOn Set.univ).eVariationOn_eq (Set.mem_univ x)
    (Set.mem_univ y)]
  have hnonneg : 0 ≤ smoothStep a b x := Real.smoothTransition.nonneg _
  have hle : smoothStep a b y ≤ 1 := Real.smoothTransition.le_one _
  simpa only [ENNReal.ofReal_one] using
    (ENNReal.ofReal_le_ofReal (show smoothStep a b y - smoothStep a b x ≤ 1 by linarith))

private theorem smoothStep_increment_variation_le {a b : ℝ} (hab : a < b)
    (c : ℝ) :
    eVariationOn (fun x => c * smoothStep a b x) Set.univ ≤ ENNReal.ofReal |c| := by
  have hc : 0 ≤ |c| := abs_nonneg c
  have hdist (x : ℝ) (_ : x ∈ Set.univ) (y : ℝ) (_ : y ∈ Set.univ) :
      dist (c * smoothStep a b x) (c * smoothStep a b y) ≤
        |c| * dist (smoothStep a b x) (smoothStep a b y) := by
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
  calc
    eVariationOn (fun x => c * smoothStep a b x) Set.univ ≤
        ENNReal.ofReal |c| * eVariationOn (smoothStep a b) Set.univ :=
      eVariationOn.le_of_dist_le hc hdist
    _ ≤ ENNReal.ofReal |c| * 1 := by
      gcongr
      exact smoothStep_variation_le_one hab
    _ = ENNReal.ofReal |c| := mul_one _

private theorem exists_smooth_interpolant_finite (f : ℝ → ℝ) (s : Finset ℝ) :
    ∃ g : ℝ → ℝ,
      ContDiff ℝ 1 g ∧
      (∀ x ∈ s, g x = f x) ∧
      eVariationOn g Set.univ ≤ eVariationOn f (↑s : Set ℝ) ∧
      (s = ∅ ∨ ∃ t : ℝ, t ∈ s ∧ (∀ x ∈ s, x ≤ t) ∧
        ∀ x : ℝ, t ≤ x → g x = f t) ∧
      (∀ x p q : ℝ, p ∈ s → q ∈ s → p ≤ x → x ≤ q →
        ∃ p' ∈ s, ∃ q' ∈ s, p ≤ p' ∧ p' ≤ x ∧
          x ≤ q' ∧ q' ≤ q ∧
          g x ∈ Set.uIcc (f p') (f q')) := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
      refine ⟨fun _ => f 0, contDiff_const, ?_, ?_, Or.inl rfl, ?_⟩
      · simp
      · have hzero : eVariationOn (fun _ : ℝ => f 0) Set.univ = 0 := by
          apply (eVariationOn.eq_zero_iff _).2
          intro x hx y hy
          exact edist_self _
        simp [hzero]
      · intro x p q hp
        simp at hp
  | insert a s hmax ih =>
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst s
        refine ⟨fun _ => f a, contDiff_const, ?_, ?_, Or.inr ?_, ?_⟩
        · intro x hx
          have : x = a := by simpa using hx
          simp [this]
        · simp [eVariationOn.eq_zero_iff]
        · exact ⟨a, by simp, by simp, by simp⟩
        · intro x p q hp hq hpx hxq
          have hpa : p = a := by simpa using hp
          have hqa : q = a := by simpa using hq
          subst p
          subst q
          refine ⟨a, by simp, a, by simp, le_rfl, hpx, hxq, le_rfl, ?_⟩
          simp
      · obtain ⟨g, hgdiff, hgmatch, hgvar, hright, hlocal⟩ := ih
        rcases hright with hnil | ⟨t, ht, htmax, hgright⟩
        · exact False.elim (hs.ne_empty hnil)
        have hta : t < a := hmax t ht
        let G : ℝ → ℝ := fun x => g x + (f a - f t) * smoothStep t a x
        have hGdiff : ContDiff ℝ 1 G := by
          dsimp [G]
          exact hgdiff.add (contDiff_const.mul (smoothStep_contDiff t a))
        have hGmatch (x : ℝ) (hx : x ∈ insert a s) : G x = f x := by
          rcases Finset.mem_insert.mp hx with hxa | hxs
          · rw [hxa]
            change g a + (f a - f t) * smoothStep t a a = f a
            rw [smoothStep_one_of_ge hta le_rfl]
            rw [hgright a hta.le]
            ring
          · have hxt : x ≤ t := htmax x hxs
            simp only [G, smoothStep_zero_of_le hta hxt, mul_zero, add_zero]
            exact hgmatch x hxs
        have hGright (x : ℝ) (hax : a ≤ x) : G x = f a := by
          simp only [G, hgright x (hta.le.trans hax),
            smoothStep_one_of_ge hta hax, mul_one]
          ring
        have hGvar : eVariationOn G Set.univ ≤
            eVariationOn f (↑(insert a s) : Set ℝ) := by
          calc
            eVariationOn G Set.univ ≤ eVariationOn g Set.univ +
                eVariationOn (fun x => (f a - f t) * smoothStep t a x) Set.univ := by
              have hG : G = g + (fun x => (f a - f t) * smoothStep t a x) := by
                funext x
                simp only [G, Pi.add_apply]
              rw [hG]
              exact eVariationOn.add_le g
                (fun x => (f a - f t) * smoothStep t a x) Set.univ
            _ ≤ eVariationOn f (↑s : Set ℝ) + ENNReal.ofReal |f a - f t| :=
              add_le_add hgvar (smoothStep_increment_variation_le hta _)
            _ = eVariationOn f (↑(insert a s) : Set ℝ) := by
              have hgreat : IsGreatest (↑s : Set ℝ) t :=
                ⟨ht, fun x hx => htmax x hx⟩
              have hleast : IsLeast ({a} : Set ℝ) a := by simp [IsLeast]
              have h := eVariationOn.union' f hgreat hleast hta.le
              have hsingleton : eVariationOn f ({a} : Set ℝ) = 0 := by simp
              rw [hsingleton, add_zero] at h
              simpa only [edist_dist, Real.dist_eq, abs_sub_comm,
                Finset.coe_insert, Set.union_singleton] using h.symm
        refine ⟨G, hGdiff, hGmatch, hGvar, Or.inr ?_, ?_⟩
        · exact ⟨a, Finset.mem_insert_self _ _, fun x hx =>
            (Finset.mem_insert.mp hx).elim (fun he => he.le)
              (fun hxs => (htmax x hxs).trans hta.le), hGright⟩
        · intro x p q hp hq hpx hxq
          by_cases hxt : x ≤ t
          · have hps : p ∈ s := by
              rcases Finset.mem_insert.mp hp with hpa | hps
              · subst p
                exact False.elim ((not_lt_of_ge hxt) (hta.trans_le hpx))
              · exact hps
            obtain ⟨q₀, hq₀s, hxq₀, hq₀q⟩ :
                ∃ q₀ ∈ s, x ≤ q₀ ∧ q₀ ≤ q := by
              rcases Finset.mem_insert.mp hq with hqa | hqs
              · subst q
                exact ⟨t, ht, hxt, hta.le⟩
              · exact ⟨q, hqs, hxq, le_rfl⟩
            obtain ⟨p', hp's, q', hq's, hpp', hp'x, hxq', hq'q₀, hbetween⟩ :=
              hlocal x p q₀ hps hq₀s hpx hxq₀
            refine ⟨p', Finset.mem_insert_of_mem hp's, q',
              Finset.mem_insert_of_mem hq's, hpp', hp'x, hxq',
              hq'q₀.trans hq₀q, ?_⟩
            simpa only [G, smoothStep_zero_of_le hta hxt, mul_zero, add_zero] using hbetween
          · have htx : t < x := lt_of_not_ge hxt
            have hqa : q = a := by
              rcases Finset.mem_insert.mp hq with hqa | hqs
              · exact hqa
              · exact False.elim ((not_lt_of_ge (htmax q hqs)) (htx.trans_le hxq))
            subst q
            rcases Finset.mem_insert.mp hp with hpa | hps
            · subst p
              have hxa : x = a := le_antisymm hxq hpx
              subst x
              exact ⟨a, Finset.mem_insert_self _ _, a, Finset.mem_insert_self _ _,
                le_rfl, le_rfl, le_rfl, le_rfl, by simp [hGmatch]⟩
            have hw0 : 0 ≤ smoothStep t a x := Real.smoothTransition.nonneg _
            have hw1 : smoothStep t a x ≤ 1 := Real.smoothTransition.le_one _
            have hbetween : G x ∈ Set.uIcc (f t) (f a) := by
              rw [show G x = f t + (f a - f t) * smoothStep t a x by
                simp only [G, hgright x htx.le]]
              rw [Set.mem_uIcc]
              rcases le_total (f t) (f a) with hfa | hfa
              · left
                constructor
                · nlinarith [mul_nonneg (sub_nonneg.mpr hfa) hw0]
                · nlinarith [mul_le_mul_of_nonneg_left hw1 (sub_nonneg.mpr hfa)]
              · right
                constructor
                · nlinarith [mul_le_mul_of_nonpos_left hw1 (sub_nonpos.mpr hfa)]
                · nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfa) hw0]
            exact ⟨t, Finset.mem_insert_of_mem ht, a, Finset.mem_insert_self _ _,
              htmax p hps, htx.le, hxq, le_rfl, hbetween⟩

private theorem countable_discontinuities_Ioi {f : ℝ → ℝ}
    (hf : eVariationOn f (Ioi (0 : ℝ)) < ⊤) :
    Set.Countable {x : ℝ | 0 < x ∧ ¬ ContinuousAt f x} := by
  have hBV : BoundedVariationOn f (Ioi (0 : ℝ)) := ne_of_lt hf
  obtain ⟨p, q, hp, hq, hfp, _⟩ :=
    hBV.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  have hpc := hp.countable_not_continuousWithinAt
  have hqc := hq.countable_not_continuousWithinAt
  apply (hpc.union hqc).mono
  intro x hx
  by_contra hnot
  have hpx : ContinuousWithinAt p (Ioi (0 : ℝ)) x := by
    by_contra h
    exact hnot (Or.inl ⟨hx.1, h⟩)
  have hqx : ContinuousWithinAt q (Ioi (0 : ℝ)) x := by
    by_contra h
    exact hnot (Or.inr ⟨hx.1, h⟩)
  have hfx : ContinuousWithinAt f (Ioi (0 : ℝ)) x := by
    rw [hfp]
    exact hpx.sub hqx
  exact hx.2 (hfx.continuousAt (isOpen_Ioi.mem_nhds hx.1))

/-- A datum of zero variation on the positive ray is constant there. -/
theorem eq_on_Ioi_of_eVariationOn_eq_zero {f : ℝ → ℝ}
    (hzero : eVariationOn f (Ioi (0 : ℝ)) = 0) :
    ∀ x y : ℝ, 0 < x → 0 < y → f x = f y := by
  intro x y hx hy
  have hdist := (eVariationOn.eq_zero_iff f).mp hzero x hx y hy
  exact edist_eq_zero.mp hdist

/-- A zero-variation datum has a smooth constant approximating sequence with
the same prescribed value at every positive point. -/
theorem exists_smooth_approx_of_eVariationOn_eq_zero (f : ℝ → ℝ)
    (hzero : eVariationOn f (Ioi (0 : ℝ)) = 0) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (g n) (Ici 0)) ∧
      (∀ v, 0 < v → Tendsto (fun n => g n v) atTop (𝓝 (f v))) ∧
      (∀ n, eVariationOn (g n) (Ioi (0 : ℝ)) = 0) := by
  refine ⟨fun _ _ => f 1, ?_, ?_, ?_⟩
  · intro n
    exact contDiff_const.contDiffOn
  · intro v hv
    have hval : f 1 = f v :=
      eq_on_Ioi_of_eVariationOn_eq_zero hzero 1 v (by norm_num) hv
    simpa only [hval] using (tendsto_const_nhds (x := f v) (f := atTop))
  · intro n
    apply (eVariationOn.eq_zero_iff _).2
    intro x hx y hy
    exact edist_self _

/-- The established one-sided mollifier gives the requested conclusion when the
datum is right continuous, including at the endpoint of the ray. -/
theorem exists_smooth_approx_of_right_continuous (f : ℝ → ℝ)
    (hfin : eVariationOn f (Ioi (0 : ℝ)) < ⊤)
    (hrc : ∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt f (Ici v) v) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (g n) (Ici 0)) ∧
      (∀ v, 0 < v → Tendsto (fun n => g n v) atTop (𝓝 (f v))) ∧
      (∀ n, eVariationOn (g n) (Ioi (0 : ℝ)) ≤
        eVariationOn f (Ioi (0 : ℝ))) := by
  have hV : eVariationOn f (Ici (0 : ℝ)) =
      eVariationOn f (Ioi (0 : ℝ)) :=
    eVariationOn.Ici_eq_Ioi_of_continuousWithinAt (hrc 0 le_rfl)
  have hf : BoundedVariationOn f (Ici (0 : ℝ)) := by
    change eVariationOn f (Ici (0 : ℝ)) ≠ ⊤
    rw [hV]
    exact ne_of_lt hfin
  obtain ⟨g, hgdiff, hgvar, hgpoint⟩ :=
    BoundedVariationOn.exists_contDiff_sequence_of_continuousWithinAt_Ici hf hrc
  refine ⟨g, (fun n => ((hgdiff n).of_le (by norm_num)).contDiffOn), ?_, ?_⟩
  · intro v hv
    exact hgpoint v hv.le
  · intro n
    calc
      eVariationOn (g n) (Ioi (0 : ℝ)) ≤
          eVariationOn (g n) (Ici (0 : ℝ)) :=
        eVariationOn.mono _ Ioi_subset_Ici_self
      _ ≤ eVariationOn f (Ici (0 : ℝ)) := hgvar n
      _ = eVariationOn f (Ioi (0 : ℝ)) := hV

/-- Once arbitrary-value pointwise approximation and the sharp upper bound are
constructed, convergence of the variations follows from lower semicontinuity. -/
theorem tendsto_eVariationOn_of_pointwise_of_le (f : ℝ → ℝ)
    (g : ℕ → ℝ → ℝ)
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => g n v) atTop (𝓝 (f v)))
    (hvar : ∀ n, eVariationOn (g n) (Ioi (0 : ℝ)) ≤
      eVariationOn f (Ioi (0 : ℝ))) :
    Tendsto (fun n => eVariationOn (g n) (Ioi (0 : ℝ))) atTop
      (𝓝 (eVariationOn f (Ioi (0 : ℝ)))) := by
  apply tendsto_of_le_liminf_of_limsup_le (h := by isBoundedDefault)
    (h' := by isBoundedDefault)
  · exact eVariationOn.le_liminf_of_tendsto (fun v hv => hpoint v hv)
  · calc
      limsup (fun n => eVariationOn (g n) (Ioi (0 : ℝ))) atTop ≤
          limsup (fun _ : ℕ => eVariationOn f (Ioi (0 : ℝ))) atTop :=
        limsup_le_limsup (Filter.Eventually.of_forall hvar)
      _ = eVariationOn f (Ioi (0 : ℝ)) := by simp only [limsup_const]

/-- A fixed positive reference trace and a uniform variation bound control all
values of a smooth approximating family, including its zero-side value. This
is the datum-dependent amplitude needed for per-approximant scalar shifts. -/
theorem exists_uniform_bound_of_smooth_approx_at_reference
    (f : ℝ → ℝ) (g : ℕ → ℝ → ℝ) (vref : ℝ) (hvref : 0 < vref)
    (hD : eVariationOn f (Ioi (0 : ℝ)) < ⊤)
    (hgdiff : ∀ n, ContDiffOn ℝ 1 (g n) (Ici 0))
    (hpoint : Tendsto (fun n => g n vref) atTop (𝓝 (f vref)))
    (hvar : ∀ n, eVariationOn (g n) (Ioi (0 : ℝ)) ≤
      eVariationOn f (Ioi (0 : ℝ))) :
    ∃ C : ℝ, ∀ n x, 0 ≤ x → |g n x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ :=
    (Metric.isBounded_range_of_tendsto (fun n => g n vref) hpoint).exists_norm_le
  refine ⟨C₀ + (eVariationOn f (Ioi (0 : ℝ))).toReal, ?_⟩
  intro n x hx
  have hcont : ContinuousWithinAt (g n) (Ici (0 : ℝ)) 0 :=
    (hgdiff n).continuousOn 0 le_rfl
  have hV : eVariationOn (g n) (Ici (0 : ℝ)) =
      eVariationOn (g n) (Ioi (0 : ℝ)) :=
    eVariationOn.Ici_eq_Ioi_of_continuousWithinAt hcont
  have hVn : BoundedVariationOn (g n) (Ici (0 : ℝ)) := by
    change eVariationOn (g n) (Ici (0 : ℝ)) ≠ ⊤
    rw [hV]
    exact ne_of_lt ((hvar n).trans_lt hD)
  have hd := hVn.dist_le hx hvref.le
  have hVreal : (eVariationOn (g n) (Ici (0 : ℝ))).toReal ≤
      (eVariationOn f (Ioi (0 : ℝ))).toReal := by
    rw [hV]
    exact ENNReal.toReal_mono (ne_of_lt hD) (hvar n)
  have href : |g n vref| ≤ C₀ := by
    simpa only [Real.norm_eq_abs] using hC₀ (g n vref) ⟨n, rfl⟩
  calc
    |g n x| = ‖g n x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖g n vref‖ + ‖g n x - g n vref‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ C₀ + (eVariationOn f (Ioi (0 : ℝ))).toReal := by
      simpa only [Real.norm_eq_abs, dist_eq_norm] using
        add_le_add href (hd.trans hVreal)

/-- The scalar shifts `cₙ = -2 α₀,ₙ(0+)` used to center each smooth datum
have a common datum-dependent bound. Smoothness identifies `0+` with `0`. -/
theorem exists_uniform_bound_scalar_centers
    (f : ℝ → ℝ) (g : ℕ → ℝ → ℝ) (vref : ℝ) (hvref : 0 < vref)
    (hD : eVariationOn f (Ioi (0 : ℝ)) < ⊤)
    (hgdiff : ∀ n, ContDiffOn ℝ 1 (g n) (Ici 0))
    (hpoint : Tendsto (fun n => g n vref) atTop (𝓝 (f vref)))
    (hvar : ∀ n, eVariationOn (g n) (Ioi (0 : ℝ)) ≤
      eVariationOn f (Ioi (0 : ℝ))) :
    ∃ C : ℝ, ∀ n, |(-2) * g n 0| ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_bound_of_smooth_approx_at_reference f g vref hvref
      hD hgdiff hpoint hvar
  refine ⟨2 * C, fun n => ?_⟩
  have hzero := hC n 0 le_rfl
  simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
    (mul_le_mul_of_nonneg_left hzero (by norm_num : (0 : ℝ) ≤ 2))

/-- Every finite-variation datum on the positive ray admits smooth approximants
which retain its literal value at every positive point, including all jump
points. Their variations never exceed the datum's variation and converge to it. -/
theorem exists_smooth_approx_arbitrary_values (alpha₀ : ℝ → ℝ)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ⊤) :
    ∃ alphaₙ : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (alphaₙ n) (Ici 0)) ∧
      (∀ v, 0 < v → Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤
        eVariationOn alpha₀ (Ioi (0 : ℝ))) ∧
      Tendsto (fun n => eVariationOn (alphaₙ n) (Ioi (0 : ℝ))) atTop
        (𝓝 (eVariationOn alpha₀ (Ioi (0 : ℝ)))) := by
  classical
  let J : Set ℝ := {x | 0 < x ∧ ¬ ContinuousAt alpha₀ x}
  let Q : Set ℝ := Ioi (0 : ℝ) ∩ Set.range (fun q : ℚ => (q : ℝ))
  let S : Set ℝ := J ∪ Q
  have hJ : J.Countable := countable_discontinuities_Ioi hD
  have hQ : Q.Countable := (Set.countable_range (fun q : ℚ => (q : ℝ))).mono
    Set.inter_subset_right
  have hS : S.Countable := hJ.union hQ
  have hSpos : S ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hx.1
  have hSne : S.Nonempty := by
    refine ⟨1, Or.inr ⟨by norm_num, ?_⟩⟩
    exact ⟨1, by norm_num⟩
  obtain ⟨e, he⟩ := hS.exists_eq_range hSne
  let s (n : ℕ) : Finset ℝ := (Finset.range (n + 1)).image e
  have hspos (n : ℕ) : (↑(s n) : Set ℝ) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hSpos (he ▸ Set.mem_range_self i)
  have hmem (x : ℝ) (hx : x ∈ S) : ∀ᶠ n : ℕ in atTop, x ∈ s n := by
    obtain ⟨i, rfl⟩ := he ▸ hx
    filter_upwards [eventually_ge_atTop i] with n hn
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩
  let alphaₙ (n : ℕ) : ℝ → ℝ :=
    Classical.choose (exists_smooth_interpolant_finite alpha₀ (s n))
  have hdata (n : ℕ) :=
    Classical.choose_spec (exists_smooth_interpolant_finite alpha₀ (s n))
  have hdiff (n : ℕ) : ContDiffOn ℝ 1 (alphaₙ n) (Ici 0) :=
    (hdata n).1.contDiffOn
  have hvar (n : ℕ) : eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤
      eVariationOn alpha₀ (Ioi (0 : ℝ)) := by
    calc
      eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤
          eVariationOn (alphaₙ n) Set.univ :=
        eVariationOn.mono _ (Set.subset_univ _)
      _ ≤ eVariationOn alpha₀ (↑(s n) : Set ℝ) := (hdata n).2.2.1
      _ ≤ eVariationOn alpha₀ (Ioi (0 : ℝ)) :=
        eVariationOn.mono _ (hspos n)
  have hpoint (v : ℝ) (hv : 0 < v) :
      Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v)) := by
    by_cases hvJ : v ∈ J
    · apply tendsto_nhds_of_eventually_eq
      filter_upwards [hmem v (Or.inl hvJ)] with n hn
      exact (hdata n).2.1 v hn
    have hvcont : ContinuousAt alpha₀ v := by
      by_contra h
      exact hvJ ⟨hv, h⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hvcont) ε hε
    have hpinterval : max 0 (v - δ) < v := max_lt hv (sub_lt_self v hδpos)
    obtain ⟨p, hpl, hpv⟩ := exists_rat_btwn hpinterval
    obtain ⟨q, hvq, hqu⟩ := exists_rat_btwn (lt_add_of_pos_right v hδpos)
    have hpQ : (p : ℝ) ∈ Q := ⟨lt_of_le_of_lt (le_max_left _ _) hpl,
      ⟨p, rfl⟩⟩
    have hqQ : (q : ℝ) ∈ Q := ⟨hv.trans hvq, ⟨q, rfl⟩⟩
    apply Filter.eventually_atTop.1
    filter_upwards [hmem (p : ℝ) (Or.inr hpQ), hmem (q : ℝ) (Or.inr hqQ)]
      with n hpn hqn
    obtain ⟨p', hp's, q', hq's, hpp', hp'v, hvq', hq'q, hbetween⟩ :=
      (hdata n).2.2.2.2 v p q hpn hqn hpv.le hvq.le
    have hp'dist : dist p' v < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hp'v)]
      have hlow : v - δ < p' := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hpl) hpp'
      linarith
    have hq'dist : dist q' v < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hvq')]
      linarith
    have hfp : dist (alpha₀ p') (alpha₀ v) < ε := hδ hp'dist
    have hfq : dist (alpha₀ q') (alpha₀ v) < ε := hδ hq'dist
    rw [Real.dist_eq] at hfp hfq ⊢
    have hpabs := abs_lt.mp hfp
    have hqabs := abs_lt.mp hfq
    have hlow : alpha₀ v - ε < min (alpha₀ p') (alpha₀ q') :=
      lt_min (by linarith) (by linarith)
    have hhigh : max (alpha₀ p') (alpha₀ q') < alpha₀ v + ε :=
      max_lt (by linarith) (by linarith)
    apply abs_lt.mpr
    constructor <;> linarith [hbetween.1, hbetween.2]
  refine ⟨alphaₙ, hdiff, hpoint, hvar, ?_⟩
  exact tendsto_eVariationOn_of_pointwise_of_le alpha₀ alphaₙ hpoint hvar

end ChristodoulouBV

end
