module

public import ChristodoulouBV.Frozen.IsC1Solution
import Mathlib.Topology.Algebra.Order.Field

/-!
# The domain underlying the adjacent strip

The old development, lower cover, and new strip form a single past-closed
domain. The characteristic calculations at positive incoming coordinate take
place in its open off-axis part.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The actual enlarged domain used in the strip argument. Its `u = 0` edge
is retained for the frozen solution's initial data. -/
def extensionWorkingDomain (u₁ top : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < top ∧ p.1 < u₁}

/-- The enlarged domain is closed under the printed causal past. -/
theorem extensionWorkingDomain_isDomainOfDevelopment (u₁ top : ℝ) :
    IsDomainOfDevelopment (extensionWorkingDomain u₁ top) := by
  constructor
  · intro p hp
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp q hq
    exact ⟨hq.1.1, hq.2.1, lt_trans hq.2.2 hp.2.2.1,
      lt_of_le_of_lt hq.1.2 hp.2.2.2⟩

/-- Every point with positive incoming coordinate is interior to the
enlarged domain. This is the locality condition used for classical jets. -/
theorem extensionWorkingDomain_mem_interior {u₁ top u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : v < top) (hu₁ : u < u₁) :
    (u, v) ∈ interior (extensionWorkingDomain u₁ top) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hOpen : IsOpen {p : ℝ × ℝ |
      0 < p.1 ∧ p.1 < p.2 ∧ p.2 < top ∧ p.1 < u₁} := by
    have h₁ : IsOpen {p : ℝ × ℝ | 0 < p.1} :=
      isOpen_lt (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℝ)))
        continuous_fst
    have h₂ : IsOpen {p : ℝ × ℝ | p.1 < p.2} :=
      isOpen_lt continuous_fst continuous_snd
    have h₃ : IsOpen {p : ℝ × ℝ | p.2 < top} :=
      isOpen_lt continuous_snd
        (continuous_const : Continuous (fun _ : ℝ × ℝ => top))
    have h₄ : IsOpen {p : ℝ × ℝ | p.1 < u₁} :=
      isOpen_lt continuous_fst
        (continuous_const : Continuous (fun _ : ℝ × ℝ => u₁))
    simpa only [Set.ofPred_and, Set.inter_assoc] using
      ((h₁.inter h₂).inter h₃).inter h₄
  exact Filter.mem_of_superset (hOpen.mem_nhds ⟨hu, huv, hv, hu₁⟩)
    (fun p hp => ⟨hp.1.le, hp.2⟩)

/-- Every actual incoming segment in the strip lies in the working domain,
including its lower endpoint on the incoming edge. -/
theorem incoming_strip_segment_subset_workingDomain
    {u₀ u₁ vStar η u v : ℝ}
    (hu₀ : 0 ≤ u₀) (_hu₀u : u₀ ≤ u) (huu₁ : u < u₁)
    (hu₁Star : u₁ ≤ vStar) (hv : v ∈ Ico vStar (vStar + η)) :
    ∀ s ∈ Icc u₀ u, (s, v) ∈ extensionWorkingDomain u₁ (vStar + η) := by
  intro s hs
  exact ⟨hu₀.trans hs.1, (hs.2.trans_lt huu₁).trans_le
    (hu₁Star.trans hv.1), hv.2, hs.2.trans_lt huu₁⟩

/-- The complete outgoing ray from the axis to a strip point stays in the
working domain. Its part below `vStar` is therefore available to (5.16). -/
theorem outgoing_ray_subset_workingDomain
    {u₁ top u v : ℝ} (hu : 0 ≤ u) (hu₁ : u < u₁)
    (_huv : u < v) (hv : v < top) :
    ∀ t ∈ Ioc u v, (u, t) ∈ extensionWorkingDomain u₁ top := by
  intro t ht
  exact ⟨hu, ht.1, ht.2.trans_lt hv, hu₁⟩

/-- On any C¹ development, `α = θ + λφ` is C¹ on the domain's closure.
The derivation uses only the frozen C¹ fields and no triangular geometry. -/
theorem alpha_contDiffOn_closure {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsC1Solution U S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2) (closure U) := by
  have h := H.theta_c1.add (H.lam_c1.mul H.phi_c1)
  apply h.congr
  intro p hp
  simp only [Fields.theta]
  ring

/-- The global C¹ lower expansion bound extends from the development to its
closure. -/
theorem lam_pos_closure {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsC1Solution U S) {p : ℝ × ℝ} (hp : p ∈ closure U) :
    0 < S.lam p.1 p.2 := by
  obtain ⟨c, hc, hcl⟩ := H.lam_bounded_below
  have hmap : MapsTo (fun q : ℝ × ℝ => S.lam q.1 q.2) U (Ici c) :=
    fun q hq => hcl q hq
  have hbound := hmap.closure_of_continuousOn H.lam_c1.continuousOn hp
  exact hc.trans_le (by
    simpa only [isClosed_Ici.closure_eq, mem_Ici] using hbound)

/-- The quotient `α/λ` is C¹ on the closure of any C¹ development. Its
denominator stays positive there by the global lower bound and continuity. -/
theorem alpha_div_lam_contDiffOn_closure {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsC1Solution U S) :
    ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.alpha p.1 p.2 / S.lam p.1 p.2) (closure U) := by
  have hne : ∀ p ∈ closure U, S.lam p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (lam_pos_closure H hp)
  exact (alpha_contDiffOn_closure H).div H.lam_c1 hne

end ChristodoulouBV.Uniqueness

end
