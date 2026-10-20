module

public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.Linarith

/-!
# A Gronwall estimate from a continuous initial trace

The differential equation is only known for strictly positive incoming
coordinates. Continuity at the initial edge permits an interior starting
point whose value is within one unit of the edge bound.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- An interior differential inequality and a continuous initial trace
give a bound depending only on the initial trace and interval length. -/
theorem abs_le_gronwall_from_initial_continuity
    {a b P C F : ℝ} {f f' : ℝ → ℝ}
    (hab : a < b) (hP : 0 ≤ P) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hf : ContinuousOn f (Icc a b))
    (ha : |f a| ≤ P)
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt f (f' s) s)
    (hbound : ∀ s ∈ Ioo a b, |f' s| ≤ C * |f s| + F) :
    |f b| ≤ gronwallBound (P + 1) C F (b - a) := by
  have hcont : ContinuousWithinAt (fun s => |f s|) (Ioo a b) a :=
    (continuous_abs.comp_continuousOn hf a ⟨le_rfl, hab.le⟩).mono
      (fun _ hs => ⟨hs.1.le, hs.2.le⟩)
  have hlt : |f a| < P + 1 := by linarith
  have hnear : ∀ᶠ s in 𝓝[Ioo a b] a, |f s| < P + 1 :=
    hcont.tendsto.eventually (gt_mem_nhds hlt)
  have hbot : NeBot (𝓝[Ioo a b] a) := left_nhdsWithin_Ioo_neBot hab
  obtain ⟨s, hsbound, hs⟩ := @Filter.Eventually.exists ℝ _ _ hbot
    (hnear.and self_mem_nhdsWithin)
  have hsI : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hfsmall : ContinuousOn f (Icc s b) :=
    hf.mono (fun t ht => ⟨hs.1.le.trans ht.1, ht.2⟩)
  have hright : ∀ t ∈ Ico s b,
      HasDerivWithinAt f (f' t) (Ici t) t := by
    intro t ht
    exact (hderiv t ⟨hs.1.trans_le ht.1, ht.2⟩).hasDerivWithinAt
  have hbd : ∀ t ∈ Ico s b, ‖f' t‖ ≤ C * ‖f t‖ + F := by
    intro t ht
    simpa only [Real.norm_eq_abs] using
      hbound t ⟨hs.1.trans_le ht.1, ht.2⟩
  have hpoint := norm_le_gronwallBound_of_norm_deriv_right_le hfsmall
    hright (by simpa only [Real.norm_eq_abs] using hsbound.le) hbd
    b ⟨hs.2.le, le_refl b⟩
  have hmono := gronwallBound_mono (by linarith : 0 ≤ P + 1) hF hC
  have hlength : b - s ≤ b - a := by linarith [hs.1]
  have hpoint' : |f b| ≤ gronwallBound (P + 1) C F (b - s) := by
    simpa only [Real.norm_eq_abs] using hpoint
  exact hpoint'.trans (hmono hlength)

end ChristodoulouBV.Uniqueness

end
