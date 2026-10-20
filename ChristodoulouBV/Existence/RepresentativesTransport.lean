module

public import ChristodoulouBV.Existence.RepresentativesCore
import Mathlib.Tactic

/-!
# Transport on the replaced outgoing lines

The raw outgoing fields are continuous in u by their incoming primitives.
Taking a right-u limit in the two outgoing mixed primitives therefore
changes only ν and β. Dominated convergence retains the endpoint equations
even on the exceptional whole outgoing lines.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem incoming_primitive_right_continuous {f g : ℝ → ℝ → ℝ}
    (hprim : ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => f u v) (fun u => g u v) a b)
    {u v : ℝ} (hp : (u, v) ∈ globalDomain) :
    ContinuousWithinAt (fun x => f x v) (Ici u) u := by
  let b := (u + v) / 2
  have hub : u < b := by dsimp [b]; linarith only [hp.2]
  have hbv : b < v := by dsimp [b]; linarith only [hp.2]
  have hac : AbsolutelyContinuousOnInterval (fun x => f x v) u b := by
    refine IsBVSolution.primitive_ac (g := fun x => g x v) hub.le ?_
    intro t ht
    apply hprim v u t ht.1
    rintro ⟨x, y⟩ ⟨hx, rfl⟩
    exact ⟨hp.1.trans hx.1, (hx.2.trans ht.2).trans_lt hbv⟩
  have hc := hac.continuousOn u (by simp only [uIcc_of_le hub.le, mem_Icc]; exact ⟨le_rfl, hub.le⟩)
  rw [uIcc_of_le hub.le] at hc
  apply hc.mono_of_mem_nhdsWithin
  simpa only [← Ici_inter_Iic] using
    inter_mem_nhdsWithin (Ici u) (Iic_mem_nhds hub)

/-- Both raw outgoing fields are right continuous in the transverse
incoming direction, including at u = 0. -/
theorem raw_outgoing_fields_right_u_continuous
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    ContinuousWithinAt (fun u => d.lam u p.2) (Ici p.1) p.1 ∧
      ContinuousWithinAt (fun u => d.alpha u p.2) (Ici p.1) p.1 :=
  ⟨incoming_primitive_right_continuous (raw_expansion_primitive_limit h d).1 hp,
    incoming_primitive_right_continuous (raw_alpha_beta_transport_limit h d).1 hp⟩

/-- The raw mixed density has the exact right-u limit obtained by
changing ν alone. No right-v change of λ or α is made. -/
theorem incoming_radius_coeff_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun u => IsBVSolution.radiusCoeff d.rawFields u p.2) (𝓝[>] p.1)
      (𝓝 (IsBVSolution.radiusCoeff d.incomingRightFields p.1 p.2)) := by
  have hr : Tendsto (fun u => d.radius (u, p.2)) (𝓝[>] p.1)
      (𝓝 (d.radius p)) :=
    (d.radius_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
      |>.tendsto.mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun u => d.mass (u, p.2)) (𝓝[>] p.1) (𝓝 (d.mass p)) :=
    (d.mass_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
      |>.tendsto.mono_left nhdsWithin_le_nhds
  have hl := (raw_outgoing_fields_right_u_continuous h d hp).1.mono Ioi_subset_Ici_self
  have hn := (nu_right_rep h hD d p hp).1
  have hμ := ((tendsto_const_nhds (x := (2 : ℝ))).mul hm).div hr (d.radius_pos h hp).ne'
  have hq : 0 < 1 - 2 * d.mass p / d.radius p :=
    lt_of_lt_of_le (by norm_num) (d.mass_geometry h p hp).1
  exact ((hμ.mul hl).mul hn).div ((tendsto_const_nhds.sub hμ).mul hr)
    (mul_pos hq (d.radius_pos h hp)).ne'

private theorem scalar_right_u_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun u => d.rawFields.phi u p.2) (𝓝[>] p.1) (𝓝 (d.rawFields.phi p.1 p.2)) := by
  have ht : Tendsto (fun u : ℝ => (u, p.2)) (𝓝[>] p.1) (𝓝 p) :=
    (tendsto_id.prodMk_nhds tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  have htU : Tendsto (fun u : ℝ => (u, p.2)) (𝓝[>] p.1) (𝓝[globalDomain] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hp.2] with u hu
    exact ⟨hp.1.trans hu.1.le, hu.2⟩
  exact (d.scalar_continuousOn h p hp).tendsto.comp htU

private theorem outgoing_primitive_right_u
    {f g F G : ℝ → ℝ → ℝ} {K : ℝ}
    (hprim : ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (f u) (g u) a b)
    (hbound : ∀ p ∈ globalDomain, ∀ δ > 0, δ ≤ p.2 - p.1 → |g p.1 p.2| ≤ K / δ)
    (hf : ∀ p ∈ globalDomain,
      Tendsto (fun u => f u p.2) (𝓝[>] p.1) (𝓝 (F p.1 p.2)))
    (hg : ∀ p ∈ globalDomain,
      Tendsto (fun u => g u p.2) (𝓝[>] p.1) (𝓝 (G p.1 p.2)))
    {u a b : ℝ} (hab : a ≤ b) (hs : outSeg u a b ⊆ globalDomain) :
    IntervalPrimitive (F u) (G u) a b := by
  have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  let δ := (a - u) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hp.2)
  let s := fun n => u + δ * transportStep n
  have hstep (n : ℕ) : transportStep n ≤ 1 := by
    unfold transportStep
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hsn (n : ℕ) : u < s n ∧ s n ≤ u + δ := by
    refine ⟨lt_add_of_pos_right _ (mul_pos hδ (transport_step_pos n)), ?_⟩
    have hm := mul_le_mul_of_nonneg_left (hstep n) hδ.le
    dsimp only [s]
    linarith only [hm]
  have hslim : Tendsto s atTop (𝓝[>] u) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul transport_step_tendsto),
      Eventually.of_forall (fun n => (hsn n).1)⟩
  have hsU (n : ℕ) : outSeg (s n) a b ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨hp.1.trans (hsn n).1.le, by
      have hh := (hsn n).2
      dsimp [δ] at hh
      linarith only [hh, hp.2, hy.1]⟩
  apply interval_primitive_limit_ae hab (fun n => hprim (s n) a b hab (hsU n))
    (M := K / δ)
  · intro n t ht
    apply hbound (s n, t) (hsU n ⟨rfl, ht⟩) δ hδ
    have hh := (hsn n).2
    dsimp [δ] at hh ⊢
    linarith only [hh, ht.1]
  · exact (hf (u, a) hp).comp hslim
  · exact (hf (u, b) (hs ⟨rfl, ⟨hab, le_rfl⟩⟩)).comp hslim
  · exact Eventually.of_forall (fun t ht =>
      (hg (u, t) (hs ⟨rfl, ht⟩)).comp hslim)

/-- The outgoing ν and β primitives survive the whole-line changes,
including their endpoint values on every exceptional outgoing line. -/
theorem incoming_right_fields_outgoing_transport
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.incomingRightFields.nu u)
        (IsBVSolution.radiusCoeff d.incomingRightFields u) a b) ∧
    ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (d.incomingRightFields.beta u)
        (fun v => IsBVSolution.radiusCoeff d.incomingRightFields u v *
          d.incomingRightFields.phi u v) a b := by
  constructor
  · intro u a b hab hs
    exact outgoing_primitive_right_u (raw_expansion_primitive_limit h d).2
      (fun p hp δ hδ hgap => d.raw_radius_coeff_bound h hp hδ hgap)
      (fun p hp => (nu_right_rep h hD d p hp).1)
      (fun _ hp => incoming_radius_coeff_tendsto h hD d hp) hab hs
  · intro u a b hab hs
    apply outgoing_primitive_right_u (raw_alpha_beta_transport_limit h d).2
      (K := 9 * (6 * D.toReal + C)) ?_
      (fun p hp => (beta_right_rep h hD d p hp).1)
      (fun _ hp => (incoming_radius_coeff_tendsto h hD d hp).mul
        (scalar_right_u_tendsto h d hp)) hab hs
    intro p hp δ hδ hgap
    rw [abs_mul]
    calc
      _ ≤ (9 / δ) * (6 * D.toReal + C) :=
        mul_le_mul (d.raw_radius_coeff_bound h hp hδ hgap)
          (d.scalar_amplitude h hp) (abs_nonneg _)
          (div_nonneg (by norm_num) hδ.le)
      _ = _ := by ring

end ChristodoulouBV

end
