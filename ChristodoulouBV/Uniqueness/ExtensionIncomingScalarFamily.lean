module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEstimate
public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarBase
public import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform scalar amplitudes on the off-axis family strip

The two characteristic transport equations and the bounds for radius,
expansion, and edge data control both scalar amplitudes before the missing
outgoing endpoint.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

private theorem abs_mul_div_le_of_bounds
    {x y r ρ D : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r)
    (hD : 0 ≤ D) (hx : |x| ≤ D) :
    |x * y / r| ≤ (D / ρ) * |y| := by
  have hrpos : 0 < r := hρ.trans_le hr
  rw [abs_div, abs_mul, abs_of_pos hrpos]
  apply (div_le_iff₀ hrpos).2
  calc
    |x| * |y| ≤ D * |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = (D / ρ * |y|) * ρ := by field_simp
    _ ≤ (D / ρ * |y|) * r :=
      mul_le_mul_of_nonneg_left hr
        (mul_nonneg (div_nonneg hD hρ.le) (abs_nonneg y))

/-- The invariant fields `θ` and `ζ` have one bound on every closed off-axis
strip inside a family member, independent of that member's cutoff. -/
theorem exists_scalar_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 < u₁) (hu₁v : u₁ < vBar) (hvBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₁ → vBar ≤ v → v < b →
          |(S b).theta u v| ≤ M ∧ |(S b).zeta u v| ≤ M := by
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_radius_floor_before_star hu₁.le hu₁v hvBarStar hfamily
  obtain ⟨N, hN, hnu⟩ :=
    exists_nu_bound_closed_before_star hu₁ hu₁v hvBarStar hα hfamily
  obtain ⟨A, hA, hθinitial⟩ :=
    exists_initial_scalar_bound_before_star (hu₁.trans hu₁v |>.trans hvBarStar)
      hα hfamily
  obtain ⟨Z, hZ, hζinitial⟩ :=
    exists_zeta_bound_at_vBar_before_star hu₁.le hu₁v hvBarStar hfamily
  let D : ℝ := 1 / 2 + N
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := D / ρ
  have hC : 0 ≤ C := div_nonneg hD hρ.le
  let k : ℝ := 4 * C + 1
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let M : ℝ := 2 * (2 * A + Z) *
    (Real.exp (k * u₁) * Real.exp (k * (vStar - vBar)))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  let H := (hfamily b hb).1
  have hBarb : vBar < b := hvBarv.trans_lt hvb
  have hrect (p : ℝ × ℝ)
      (hp : p ∈ Icc (0 : ℝ) u₁ ×ˢ Icc vBar v) :
      p ∈ closure (developmentWithInitialEdge b) := by
    apply subset_closure
    exact ⟨hp.1.1, hp.1.2.trans_lt (hu₁v.trans_le hp.2.1),
      hp.2.2.trans_lt hvb⟩
  have hθcont : ContinuousOn (fun p : ℝ × ℝ => (S b).theta p.1 p.2)
      (Icc (0 : ℝ) u₁ ×ˢ Icc vBar v) :=
    H.theta_c1.continuousOn.mono hrect
  have hζcont : ContinuousOn (fun p : ℝ × ℝ => (S b).zeta p.1 p.2)
      (Icc (0 : ℝ) u₁ ×ˢ Icc vBar v) :=
    H.zeta_c1.continuousOn.mono hrect
  have hθedge : ∀ w ∈ Icc vBar v, |(S b).theta 0 w| ≤ 2 * A := by
    intro w hw
    exact (hθinitial b hb w ⟨hu₁.trans (hu₁v.trans_le hw.1),
      hw.2.trans_lt hvb⟩).2
  have hζedge : ∀ s ∈ Icc (0 : ℝ) u₁,
      |(S b).zeta s vBar| ≤ Z := by
    intro s hs
    exact hζinitial b hb s hs hBarb
  have hθderiv : ∀ s ∈ Ioo (0 : ℝ) u₁, ∀ w ∈ Icc vBar v,
      DifferentiableAt ℝ (fun t => (S b).theta t w) s ∧
      |deriv (fun t => (S b).theta t w) s| ≤
        C * (|(S b).theta s w| + |(S b).zeta s w|) := by
    intro s hs w hw
    have hp : (s, w) ∈ openDevelopment 0 b := by
      refine ⟨⟨hs.1, ?_⟩, ⟨?_, hw.2.trans_lt hvb⟩⟩
      · exact hs.2.trans (hu₁v.trans_le hw.1) |>.trans (hw.2.trans_lt hvb)
      · exact hs.2.trans (hu₁v.trans_le hw.1)
    have hd := theta_hasDerivAt_u_of_c1 H hp
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    have hlam : 0 < (S b).lam s w :=
      H.solution.lam_pos (s, w) ⟨hs.1.le, hp.2.1, hp.2.2⟩
    have hhalf : (S b).lam s w ≤ 1 / 2 :=
      lam_le_half_of_initial_gauge H
        (fun t ht => ((hfamily b hb).2 t ht).1)
        hs.1.le hp.2.1 hp.2.2
    have hfield : |(S b).lam s w| ≤ D := by
      rw [abs_of_pos hlam]
      dsimp [D]
      linarith only [hhalf, hN]
    have hbound := abs_mul_div_le_of_bounds hρ
      (hr b hb s w hs.1.le hs.2.le hw.1 (hw.2.trans_lt hvb)) hD hfield
      (y := (S b).zeta s w)
    have hz : |(S b).zeta s w| ≤
        |(S b).theta s w| + |(S b).zeta s w| := by
      linarith only [abs_nonneg ((S b).theta s w)]
    have hmul := mul_le_mul_of_nonneg_left hz hC
    simpa only [abs_neg, C] using hbound.trans hmul
  have hζderiv : ∀ s ∈ Icc (0 : ℝ) u₁, ∀ w ∈ Ioo vBar v,
      DifferentiableAt ℝ ((S b).zeta s) w ∧
      |deriv ((S b).zeta s) w| ≤
        C * (|(S b).theta s w| + |(S b).zeta s w|) := by
    intro s hs w hw
    have hwB : w < b := hw.2.trans_le (le_of_lt hvb)
    have hd : HasDerivAt ((S b).zeta s)
        (-( (S b).nu s w * (S b).theta s w / (S b).r s w)) w := by
      by_cases hs0 : s = 0
      · subst s
        exact zeta_hasDerivAt_v_initial_of_c1 H
          ⟨hu₁.trans (hu₁v.trans hw.1), hwB⟩
      · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        have hsw : s < w := hs.2.trans_lt (hu₁v.trans hw.1)
        exact zeta_hasDerivAt_v_of_c1 H
          ⟨⟨hspos, hsw.trans hwB⟩, ⟨hsw, hwB⟩⟩
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    have hfield : |(S b).nu s w| ≤ D :=
      (hnu b hb s w hs.1 hs.2 hw.1.le hwB).trans (by dsimp [D]; linarith)
    have hbound := abs_mul_div_le_of_bounds hρ
      (hr b hb s w hs.1 hs.2 hw.1.le hwB) hD hfield
      (y := (S b).theta s w)
    have hθ : |(S b).theta s w| ≤
        |(S b).theta s w| + |(S b).zeta s w| := by
      linarith only [abs_nonneg ((S b).zeta s w)]
    have hmul := mul_le_mul_of_nonneg_left hθ hC
    simpa only [abs_neg, C] using hbound.trans hmul
  have hpoint := scalar_transport_rectangle_bound (a := 0) (b := u₁)
    (c := vBar) (d := v) (C := C) (A := 2 * A) (Z := Z)
    hu₁.le hvBarv hC (by positivity) hZ hθcont hζcont hθedge hζedge
    hθderiv hζderiv u ⟨hu, huu₁⟩ v ⟨hvBarv, le_refl v⟩
  have hexpu : Real.exp (k * u) ≤ Real.exp (k * u₁) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huu₁ hk)
  have hexpv : Real.exp (k * (v - vBar)) ≤
      Real.exp (k * (vStar - vBar)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [hvb.trans hb.2]) hk
  have hsum : |(S b).theta u v| + |(S b).zeta u v| ≤ M := by
    calc
      _ ≤ 2 * (2 * A + Z) *
          (Real.exp (k * (u - 0)) * Real.exp (k * (v - vBar))) := hpoint
      _ ≤ M := by
        dsimp [M]
        have hAZ : 0 ≤ 2 * (2 * A + Z) := by positivity
        have hprod := mul_le_mul hexpu hexpv (Real.exp_nonneg _) (Real.exp_nonneg _)
        simpa only [sub_zero] using mul_le_mul_of_nonneg_left hprod hAZ
  exact ⟨le_trans (by linarith only [abs_nonneg ((S b).zeta u v)]) hsum,
    le_trans (by linarith only [abs_nonneg ((S b).theta u v)]) hsum⟩

end ChristodoulouBV.Uniqueness

end
