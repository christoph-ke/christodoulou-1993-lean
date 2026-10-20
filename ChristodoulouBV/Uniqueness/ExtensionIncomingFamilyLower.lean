module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingQuotientC1
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import ChristodoulouBV.BVSolution.InitialData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A uniform lower bound for the incoming expansion quotient

The flux bound controls the logarithmic incoming decay of the positive
quotient. The initial gauge gives a fixed lower value at `u = 0`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The expansion quotient stays uniformly positive on the
off-axis family strip before the missing outgoing endpoint. -/
theorem exists_quotient_floor_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 < u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₁ → vBar ≤ v → v < b →
          c ≤ (S b).lam u v /
            (1 - 2 * (S b).m u v / (S b).r u v) := by
  obtain ⟨C, hC, hflux⟩ :=
    exists_flux_bound_before_star hu₁ hu₁v hvBarStar hα hfamily
  let c : ℝ := (1 / 2) * Real.exp (-(C * u₁))
  have hc : 0 < c := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨c, hc, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  let H := (hfamily b hb).1
  have hu₁v' : u₁ < v := hu₁v.trans_le hvBarv
  let κ : ℝ → ℝ := fun s =>
    (S b).lam s v / (1 - 2 * (S b).m s v / (S b).r s v)
  let G : ℝ → ℝ := fun s =>
    (S b).zeta s v ^ 2 / ((S b).r s v * (-(S b).nu s v))
  have hκcont : ContinuousOn κ (Icc (0 : ℝ) u₁) :=
    incoming_quotient_continuousOn_of_c1 H hu₁.le hu₁v' hvb
  have hκpos : ∀ s ∈ Icc (0 : ℝ) u₁, 0 < κ s := by
    intro s hs
    have hp : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hs.1, hs.2.trans_lt hu₁v', hvb⟩
    exact div_pos (H.solution.lam_pos (s, v) hp)
      (H.mass_gap_pos_of_c1 hp)
  have hG : ∀ s ∈ Ioo (0 : ℝ) u₁, G s ≤ C := by
    intro s hs
    exact hflux b hb s v hs.1 hs.2.le hvBarv hvb
  have hκderiv : ∀ s ∈ Ioo (0 : ℝ) u₁,
      HasDerivAt κ (-(G s * κ s)) s := by
    intro s hs
    exact incoming_quotient_hasDerivAt_u_of_c1 H
      hs.1 (hs.2.trans hu₁v') hvb
  have hpoint := incoming_quotient_lower_of_flux_bound hu₁.le
    hκcont hκpos hG hκderiv u ⟨hu, huu₁⟩
  have hv : v ∈ Ioo (0 : ℝ) b :=
    ⟨hu₁.trans (hu₁v'.trans_le (le_refl v)), hvb⟩
  have hlam0 : (S b).lam 0 v = 1 / 2 :=
    initial_lam_eq_of_gauge H
      (fun w hw => ((hfamily b hb).2 w hw).1) hv
  have hp0 : (0, v) ∈ developmentWithInitialEdge b :=
    ⟨le_refl 0, hv.1, hv.2⟩
  have hq0 : 0 < 1 - 2 * (S b).m 0 v / (S b).r 0 v :=
    H.mass_gap_pos_of_c1 hp0
  have hmu0 : 0 ≤ 2 * (S b).m 0 v / (S b).r 0 v :=
    H.mass_ratio_nonneg_of_c1 hp0
  have hκ0 : (1 / 2 : ℝ) ≤ κ 0 := by
    dsimp [κ]
    rw [hlam0]
    apply (le_div_iff₀ hq0).2
    nlinarith only [hmu0]
  have hexp : Real.exp (-(C * u₁)) ≤ Real.exp (-(C * u)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hC, huu₁]
  calc
    c = (1 / 2) * Real.exp (-(C * u₁)) := rfl
    _ ≤ (1 / 2) * Real.exp (-(C * u)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ κ 0 * Real.exp (-(C * (u - 0))) := by
      simpa only [sub_zero] using
        mul_le_mul_of_nonneg_right hκ0 (Real.exp_nonneg _)
    _ ≤ κ u := hpoint
    _ = (S b).lam u v /
      (1 - 2 * (S b).m u v / (S b).r u v) := rfl

end ChristodoulouBV.Uniqueness

end
