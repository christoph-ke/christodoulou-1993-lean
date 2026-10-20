module

public import ChristodoulouBV.Existence.GlobalC1Patch
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Exhaustion of the global development

Every closed null segment and every finite point of the closed wedge is
contained in a finite chart. The primitive equations and regularity therefore
pass from one total field's finite developments to the global domain.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

/-- The global development is closed under the frozen causal past. -/
theorem s6_globalDomain_isDomainOfDevelopment : IsDomainOfDevelopment globalDomain := by
  refine ⟨Subset.refl _, ?_⟩
  intro p _ q hq
  exact ⟨hq.1.1, hq.2.1⟩

/-- The closure of the initial-edge-inclusive global development is the
closed nonnegative wedge, including its origin and the entire diagonal. -/
theorem s6_closure_globalDomain :
    closure globalDomain = {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact fun _ hp => ⟨hp.1, hp.2.le⟩
    · exact (isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd)
  · intro p hp
    let b := max p.2 0 + 1
    have hb : 0 < b := by dsimp [b]; linarith [le_max_right p.2 0]
    have hpb : p.2 < b := by dsimp [b]; linarith [le_max_left p.2 0]
    have hpcl : p ∈ closure (developmentWithInitialEdge b) := by
      rw [C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle hb]
      exact ⟨hp.1, hp.2, hpb.le⟩
    have hsub : developmentWithInitialEdge b ⊆ globalDomain :=
      fun _ hq => ⟨hq.1, hq.2.1⟩
    exact closure_mono hsub hpcl

private theorem outgoing_segment_in_finite {u a b : ℝ}
    (hab : a ≤ b) (hseg : outSeg u a b ⊆ globalDomain) :
    ∃ c : ℝ, 0 < c ∧ outSeg u a b ⊆ developmentWithInitialEdge c := by
  have hp := hseg (show (u, b) ∈ outSeg u a b from ⟨rfl, hab, le_rfl⟩)
  refine ⟨b + 1, by linarith [hp.1, hp.2], ?_⟩
  intro p hq
  exact ⟨(hseg hq).1, (hseg hq).2, hq.2.2.trans_lt (lt_add_one b)⟩

private theorem incoming_segment_in_finite {v a b : ℝ}
    (hab : a ≤ b) (hseg : inSeg v a b ⊆ globalDomain) :
    ∃ c : ℝ, 0 < c ∧ inSeg v a b ⊆ developmentWithInitialEdge c := by
  have hp := hseg (show (a, v) ∈ inSeg v a b from ⟨⟨le_rfl, hab⟩, rfl⟩)
  refine ⟨v + 1, by linarith [hp.1, hp.2], ?_⟩
  intro p hq
  exact ⟨(hseg hq).1, (hseg hq).2, by rw [hq.2]; exact lt_add_one v⟩

/-- A single total field solving the reduced equations on every finite
development solves them on the global development, including its axis limits. -/
theorem isSolution_global_of_finite {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsSolution (developmentWithInitialEdge b) S) :
    IsSolution globalDomain S := by
  have haxis (a : ℝ) (ha : a ∈ adjacentAxis globalDomain) :
      Tendsto (S.r a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ globalDomain}) (𝓝 0) ∧
      Tendsto (S.m a) (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ globalDomain}) (𝓝 0) := by
    have ha0 : 0 ≤ a := by
      have hcl : (a, a) ∈ closure globalDomain := ha
      rw [s6_closure_globalDomain] at hcl
      exact hcl.1
    have hb : 0 < a + 1 := by linarith
    have hp : (a, a + 1 / 2) ∈ developmentWithInitialEdge (a + 1) :=
      ⟨ha0, by linarith, by linarith⟩
    have H := hfinite (a + 1) hb
    have haC := H.development.axis_mem hp
    have hr := H.radius_axis a haC
    have hm := H.mass_axis a haC
    rw [H.development.axis_filter_eq hp] at hr hm
    rw [s6_globalDomain_isDomainOfDevelopment.axis_filter_eq
      (show (a, a + 1 / 2) ∈ globalDomain from ⟨ha0, by linarith⟩)]
    exact ⟨hr, hm⟩
  refine {
    development := s6_globalDomain_isDomainOfDevelopment
    radius_out := ?_
    radius_in := ?_
    scalar_radius_out := ?_
    scalar_radius_in := ?_
    mass_out := ?_
    mass_in := ?_
    lam_in := ?_
    nu_out := ?_
    alpha_in := ?_
    beta_out := ?_
    radius_axis := fun a ha => (haxis a ha).1
    mass_axis := fun a ha => (haxis a ha).2
    radius_pos := ?_
    lam_pos := ?_
    conformal := ?_ }
  · intro u a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := outgoing_segment_in_finite hab hseg
    exact (hfinite c hc).radius_out u a b hab hsegc
  · intro v a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := incoming_segment_in_finite hab hseg
    exact (hfinite c hc).radius_in v a b hab hsegc
  · intro u a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := outgoing_segment_in_finite hab hseg
    exact (hfinite c hc).scalar_radius_out u a b hab hsegc
  · intro v a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := incoming_segment_in_finite hab hseg
    exact (hfinite c hc).scalar_radius_in v a b hab hsegc
  · intro u a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := outgoing_segment_in_finite hab hseg
    exact (hfinite c hc).mass_out u a b hab hsegc
  · intro v a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := incoming_segment_in_finite hab hseg
    exact (hfinite c hc).mass_in v a b hab hsegc
  · intro v a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := incoming_segment_in_finite hab hseg
    exact (hfinite c hc).lam_in v a b hab hsegc
  · intro u a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := outgoing_segment_in_finite hab hseg
    exact (hfinite c hc).nu_out u a b hab hsegc
  · intro v a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := incoming_segment_in_finite hab hseg
    exact (hfinite c hc).alpha_in v a b hab hsegc
  · intro u a b hab hseg
    obtain ⟨c, hc, hsegc⟩ := outgoing_segment_in_finite hab hseg
    exact (hfinite c hc).beta_out u a b hab hsegc
  all_goals
    intro p hp
    have hb : 0 < p.2 + 1 := by linarith [hp.1, hp.2]
    have hpb : p ∈ developmentWithInitialEdge (p.2 + 1) :=
      ⟨hp.1, hp.2, lt_add_one p.2⟩
  · exact (hfinite _ hb).radius_pos p hpb
  · exact (hfinite _ hb).lam_pos p hpb
  · exact (hfinite _ hb).conformal p hpb

/-- C¹ regularity on every closed finite development gives C¹ regularity
on the entire closed global wedge by locality within that wedge. -/
theorem s6_contDiffOn_global_closure_of_finite {f : ℝ × ℝ → ℝ}
    (hfinite : ∀ b : ℝ, 0 < b →
      ContDiffOn ℝ 1 f (closure (developmentWithInitialEdge b))) :
    ContDiffOn ℝ 1 f (closure globalDomain) := by
  intro p hp
  have hpw : 0 ≤ p.1 ∧ p.1 ≤ p.2 := by
    rwa [s6_closure_globalDomain] at hp
  let b := p.2 + 1
  have hb : 0 < b := by dsimp [b]; linarith [hpw.1, hpw.2]
  have hpb : p.2 < b := lt_add_one p.2
  have hpcl : p ∈ closure (developmentWithInitialEdge b) := by
    rw [C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle hb]
    exact ⟨hpw.1, hpw.2, hpb.le⟩
  apply (hfinite b hb p hpcl).mono_of_mem_nhdsWithin
  have hnear : {q : ℝ × ℝ | q.2 < b} ∈ 𝓝 p :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hpb
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnear] with q hq hqb
  rw [s6_closure_globalDomain] at hq
  rw [C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle hb]
  exact ⟨hq.1, hq.2, hqb.le⟩

/-- Uniform expansion bounds and finite C¹ charts give the exact frozen
global C¹ class for the same total field. -/
theorem isC1Solution_global_of_finite {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hnu : ∃ N : ℝ, ∀ p ∈ globalDomain, -S.nu p.1 p.2 ≤ N)
    (hlam : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ globalDomain, c ≤ S.lam p.1 p.2) :
    IsC1Solution globalDomain S := by
  exact {
    solution := isSolution_global_of_finite (fun b hb => (hfinite b hb).solution)
    nu_bounded_below := hnu
    lam_bounded_below := hlam
    lam_c1 := s6_contDiffOn_global_closure_of_finite (fun b hb => (hfinite b hb).lam_c1)
    nu_c1 := s6_contDiffOn_global_closure_of_finite (fun b hb => (hfinite b hb).nu_c1)
    phi_c1 := s6_contDiffOn_global_closure_of_finite (fun b hb => (hfinite b hb).phi_c1)
    theta_c1 := s6_contDiffOn_global_closure_of_finite (fun b hb => (hfinite b hb).theta_c1)
    zeta_c1 := s6_contDiffOn_global_closure_of_finite (fun b hb => (hfinite b hb).zeta_c1) }

/-- A finite C¹ family with exact common data
and uniform bootstrap geometry yields one global C¹ field, retaining all
finite C¹ charts and the initial traces. Compatibility follows from uniqueness of the finite C¹ developments. -/
theorem s6_global_glue
    {alpha₀ : ℝ → ℝ} {family : ℝ → Fields}
    (hfamily : ∀ b : ℝ, 0 < b →
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    (hgeometry : ∀ b : ℝ, 0 < b → ∀ p ∈ developmentWithInitialEdge b,
      (1 / 3 : ℝ) ≤ (family b).lam p.1 p.2 ∧
      -(2 / 3 : ℝ) ≤ (family b).nu p.1 p.2 ∧
      2 * (family b).m p.1 p.2 / (family b).r p.1 p.2 ≤ (1 / 3 : ℝ)) :
    let T := globalC1Patch family
    IsC1Solution globalDomain T ∧
      (∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) T) ∧
      (∀ v : ℝ, 0 < v → T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) := by
  have hfinite := fun b (hb : 0 < b) => globalC1Patch_isC1Solution hfamily hb
  have hbounds (p : ℝ × ℝ) (hp : p ∈ globalDomain) :
      (1 / 3 : ℝ) ≤ (globalC1Patch family).lam p.1 p.2 ∧
      -(2 / 3 : ℝ) ≤ (globalC1Patch family).nu p.1 p.2 := by
    have hb : 0 < p.2 + 1 := by linarith [hp.1, hp.2]
    have hpb : p ∈ developmentWithInitialEdge (p.2 + 1) :=
      ⟨hp.1, hp.2, lt_add_one p.2⟩
    have heq := globalC1Patch_agrees hfamily hb hpb
    rw [heq.2.2.2.1, heq.2.2.2.2.1]
    exact ⟨(hgeometry _ hb p hpb).1, (hgeometry _ hb p hpb).2.1⟩
  refine ⟨isC1Solution_global_of_finite hfinite ?_ ?_, hfinite,
    fun _ hv => globalC1Patch_initial_data hfamily hv⟩
  · exact ⟨2 / 3, fun p hp => by linarith only [(hbounds p hp).2]⟩
  · exact ⟨1 / 3, by norm_num, fun p hp => (hbounds p hp).1⟩

end ChristodoulouBV

end
