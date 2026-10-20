module

public import ChristodoulouBV.Existence.TransportLimitRaw
import Mathlib.Tactic

/-!
# Simultaneous right traces of the selected fields

A positive translation of both coordinates preserves the distance from
the axis. Transverse primitive estimates show that these translations of
the raw limits converge pointwise to the canonical radius and scalar representatives.
This is a spatial limit; the smooth subsequence is never changed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The positive spatial step used to approach the canonical right traces. -/
@[expose] noncomputable def transportStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Every spatial step is strictly positive. -/
theorem transport_step_pos (n : ℕ) : 0 < transportStep n := by
  unfold transportStep
  positivity

/-- The spatial steps tend to zero. -/
theorem transport_step_tendsto : Tendsto transportStep atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Translate all seven fields by the same positive spatial step. -/
@[expose] noncomputable def transportShiftFields (S : Fields) (n : ℕ) : Fields where
  r u v := S.r (u + transportStep n) (v + transportStep n)
  phi u v := S.phi (u + transportStep n) (v + transportStep n)
  m u v := S.m (u + transportStep n) (v + transportStep n)
  lam u v := S.lam (u + transportStep n) (v + transportStep n)
  nu u v := S.nu (u + transportStep n) (v + transportStep n)
  alpha u v := S.alpha (u + transportStep n) (v + transportStep n)
  beta u v := S.beta (u + transportStep n) (v + transportStep n)

/-- The simultaneous right translation stays in the same global carrier. -/
theorem transport_shift_mem {p : ℝ × ℝ} (hp : p ∈ globalDomain) (n : ℕ) :
    (p.1 + transportStep n, p.2 + transportStep n) ∈ globalDomain :=
  ⟨add_nonneg hp.1 (transport_step_pos n).le, by linarith only [hp.2]⟩

private theorem transportStep_add_tendsto_right (x : ℝ) :
    Tendsto (fun n => x + transportStep n) atTop (𝓝[>] x) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨by simpa only [add_zero] using tendsto_const_nhds.add transport_step_tendsto,
    Eventually.of_forall (fun n => lt_add_of_pos_right x (transport_step_pos n))⟩

private theorem tendsto_of_transport_bound {f g : ℕ → ℝ} {L K : ℝ}
    (hg : Tendsto g atTop (𝓝 L))
    (hb : ∀ᶠ n in atTop, |g n - f n| ≤ K * transportStep n) :
    Tendsto f atTop (𝓝 L) := by
  apply hg.congr_dist
  rw [show (fun n => dist (g n) (f n)) = (fun n => |g n - f n|) from rfl]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hb
  simpa only [mul_zero] using tendsto_const_nhds.mul transport_step_tendsto

private theorem diagonal_outgoing_trace {f g : ℝ → ℝ → ℝ} {u v K : ℝ}
    (hp : (u, v) ∈ globalDomain)
    (hprim : ∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      IntervalPrimitive (fun u => f u v) (fun u => g u v) a b)
    (hb : ∀ p ∈ globalDomain, ∀ δ > 0, δ ≤ p.2 - p.1 → |g p.1 p.2| ≤ K / δ)
    (ht : Tendsto (f u) (𝓝[>] v) (𝓝 ((f u).rightLim v))) :
    Tendsto (fun n => f (u + transportStep n) (v + transportStep n)) atTop
      (𝓝 ((f u).rightLim v)) := by
  apply tendsto_of_transport_bound (K := K / (v - u))
    (ht.comp (transportStep_add_tendsto_right v))
  apply Eventually.of_forall
  intro n
  let e := transportStep n
  have he : 0 ≤ e := (transport_step_pos n).le
  have hs : inSeg (v + e) u (u + e) ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨hx, rfl⟩
    exact ⟨hp.1.trans hx.1, by linarith only [hx.2, hp.2]⟩
  have hh := (hprim (v + e) u (u + e) (le_add_of_nonneg_right he) hs).abs_sub_le
    (le_add_of_nonneg_right he) (fun t ht => hb (t, v + e) (hs ⟨ht, rfl⟩)
      (v - u) (sub_pos.mpr hp.2) (by linarith only [ht.2]))
  change |f u (v + e) - f (u + e) (v + e)| ≤ (K / (v - u)) * e
  rw [abs_sub_comm]
  simpa only [add_sub_cancel_left] using hh

private theorem diagonal_incoming_trace {f g : ℝ → ℝ → ℝ} {u v K : ℝ}
    (hp : (u, v) ∈ globalDomain)
    (hprim : ∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      IntervalPrimitive (f u) (g u) a b)
    (hb : ∀ p ∈ globalDomain, ∀ δ > 0, δ ≤ p.2 - p.1 → |g p.1 p.2| ≤ K / δ)
    (ht : Tendsto (fun x => f x v) (𝓝[>] u) (𝓝 ((fun x => f x v).rightLim u))) :
    Tendsto (fun n => f (u + transportStep n) (v + transportStep n)) atTop
      (𝓝 ((fun x => f x v).rightLim u)) := by
  apply tendsto_of_transport_bound (K := K / ((v - u) / 2))
    (ht.comp (transportStep_add_tendsto_right u))
  filter_upwards [transport_step_tendsto.eventually (gt_mem_nhds
    (half_pos (sub_pos.mpr hp.2)))] with n hn
  let e := transportStep n
  have he : 0 ≤ e := (transport_step_pos n).le
  have hs : outSeg (u + e) v (v + e) ⊆ globalDomain := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨add_nonneg hp.1 he, by dsimp [e] at *; linarith only [hy.1, hn, hp.2]⟩
  have hh := (hprim (u + e) v (v + e) (le_add_of_nonneg_right he) hs).abs_sub_le
    (le_add_of_nonneg_right he) (fun t ht => hb (u + e, t) (hs ⟨rfl, ht⟩)
      ((v - u) / 2) (half_pos (sub_pos.mpr hp.2)) (by
        dsimp [e] at *
        linarith only [ht.1, hn]))
  change |f (u + e) v - f (u + e) (v + e)| ≤ (K / ((v - u) / 2)) * e
  rw [abs_sub_comm]
  simpa only [add_sub_cancel_left] using hh

/-- All seven simultaneously translated raw fields converge pointwise to
exactly the canonical scalar field record, including points on the initial edge. -/
theorem transport_shift_fields_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun n => (transportShiftFields d.rawFields n).r p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.r p.1 p.2)) ∧
    Tendsto (fun n => (transportShiftFields d.rawFields n).phi p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.phi p.1 p.2)) ∧
    Tendsto (fun n => (transportShiftFields d.rawFields n).m p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.m p.1 p.2)) ∧
    Tendsto (fun n => (transportShiftFields d.rawFields n).lam p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.lam p.1 p.2)) ∧
    Tendsto (fun n => (transportShiftFields d.rawFields n).nu p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.nu p.1 p.2)) ∧
    Tendsto (fun n => (transportShiftFields d.rawFields n).alpha p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.alpha p.1 p.2)) ∧
    Tendsto (fun n => (transportShiftFields d.rawFields n).beta p.1 p.2) atTop
      (𝓝 (d.scalarRightFields.beta p.1 p.2)) := by
  have hpseq : Tendsto (fun n => (p.1 + transportStep n, p.2 + transportStep n))
      atTop (𝓝 p) := by
    have hu : Tendsto (fun n => p.1 + transportStep n) atTop (𝓝 p.1) := by
      simpa only [add_zero] using tendsto_const_nhds.add transport_step_tendsto
    have hv : Tendsto (fun n => p.2 + transportStep n) atTop (𝓝 p.2) := by
      simpa only [add_zero] using tendsto_const_nhds.add transport_step_tendsto
    exact hu.prodMk_nhds hv
  have hpwithin := tendsto_nhdsWithin_iff.mpr
    ⟨hpseq, Eventually.of_forall (transport_shift_mem hp)⟩
  have hr := d.radius_continuous.continuousAt.tendsto.comp hpseq
  have hm := d.mass_continuous.continuousAt.tendsto.comp hpseq
  have hφ := ((d.scalar_continuousOn h) p hp).tendsto.comp hpwithin
  have hV : s4UniversalC * D ^ 2 < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr s4UniversalC_ne_top)
      (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hD))
  have hW := lt_top_iff_ne_top.mpr (scalarVariationBound_ne_top hD C)
  obtain ⟨hlvar, hnvar, _⟩ := expansions_limit h d
  obtain ⟨_, hαvar, hβvar, _⟩ := alpha_beta_limit h d
  have hlBV : BoundedVariationOn (d.lam p.1) (Ioi p.1) :=
    ne_of_lt ((hlvar p.1 hp.1).trans_lt hV)
  have hnBV : BoundedVariationOn (fun u => d.nu u p.2) (Ico 0 p.2) :=
    ne_of_lt ((hnvar p.2 (hp.1.trans_lt hp.2)).trans_lt hV)
  have hαBV : BoundedVariationOn (d.alpha p.1) (Ioi p.1) :=
    ne_of_lt ((hαvar p.1 hp.1).trans_lt hW)
  have hβBV : BoundedVariationOn (fun u => d.beta u p.2) (Ico 0 p.2) :=
    ne_of_lt ((hβvar p.2 (hp.1.trans_lt hp.2)).trans_lt hW)
  have hinter : Ioi p.1 ∩ Ioi p.2 = Ioi p.2 :=
    inter_eq_right.mpr (Ioi_subset_Ioi hp.2.le)
  have hlt : Tendsto (d.lam p.1) (𝓝[>] p.2) (𝓝 (d.rightLam p.1 p.2)) := by
    apply tendsto_rightLim_of_tendsto
    simpa only [hinter] using hlBV.exists_tendsto_right p.2
  have hαt : Tendsto (d.alpha p.1) (𝓝[>] p.2) (𝓝 (d.rightAlpha p.1 p.2)) := by
    apply tendsto_rightLim_of_tendsto
    simpa only [hinter] using hαBV.exists_tendsto_right p.2
  have hnt := tendsto_rightLim_of_tendsto (hnBV.exists_tendsto_right_Ico hp)
  have hβt := tendsto_rightLim_of_tendsto (hβBV.exists_tendsto_right_Ico hp)
  have hb (q : ℝ × ℝ) (hq : q ∈ globalDomain) (δ : ℝ) (hδ : 0 < δ)
      (hgap : δ ≤ q.2 - q.1) : |IsBVSolution.radiusCoeff d.rawFields q.1 q.2| ≤ 9 / δ :=
    d.raw_radius_coeff_bound h hq hδ hgap
  have hbφ (q : ℝ × ℝ) (hq : q ∈ globalDomain) (δ : ℝ) (hδ : 0 < δ)
      (hgap : δ ≤ q.2 - q.1) :
      |IsBVSolution.radiusCoeff d.rawFields q.1 q.2 * d.rawFields.phi q.1 q.2| ≤
        (9 * (6 * D.toReal + C)) / δ := by
    rw [abs_mul]
    calc
      _ ≤ (9 / δ) * (6 * D.toReal + C) :=
        mul_le_mul (hb q hq δ hδ hgap) (d.scalar_amplitude h hq) (abs_nonneg _)
          (div_nonneg (by norm_num) hδ.le)
      _ = _ := by ring
  obtain ⟨hlprim, hnprim⟩ := raw_expansion_primitive_limit h d
  obtain ⟨hαprim, hβprim⟩ := raw_alpha_beta_transport_limit h d
  exact ⟨hr, hφ, hm, diagonal_outgoing_trace hp hlprim hb hlt,
    diagonal_incoming_trace hp hnprim hb hnt,
    diagonal_outgoing_trace hp hαprim hbφ hαt,
    diagonal_incoming_trace hp hβprim hbφ hβt⟩

end ChristodoulouBV

end
