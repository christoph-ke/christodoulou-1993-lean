module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyUniformFloor
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformLambdaV
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceAllPrime
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceAllMass
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.IntervalC1Extension
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalarIncoming
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.BoundedDerivativeEndpoint
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyInitial
import ChristodoulouBV.Uniqueness.ExtensionOldAbsorption
import ChristodoulouBV.Uniqueness.ExtensionStripAxis
import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Uniform expansion derivative on compact Route B edges

Every interior point of the compact edge has a neighborhood represented by
one finite old solution. The uniform old-family derivative estimate therefore
passes to the compact edge and, by continuity, to both endpoints.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Locally inside the compact incoming edge, its expansion and scalar
quotient are represented by the same finite member of the old family. -/
theorem OffAxisTerminalC1Packet.eventually_eq_old_edge
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    {v : ℝ} (hv : v ∈ Ioo a vStar) :
    ∃ b ∈ Ioo (0 : ℝ) vStar, v < b ∧
      P.g =ᶠ[𝓝 v] (S b).lam a ∧
      P.hEdge =ᶠ[𝓝 v]
        (fun w => (S b).alpha a w / (S b).lam a w) := by
  by_cases hvt : v < P.t
  · refine ⟨P.b₀, P.b₀_mem, hvt.trans P.t_lt_b₀, ?_, ?_⟩
    · filter_upwards [Ioo_mem_nhds hv.1 hvt] with w hw
      exact (P.old_match w ⟨hw.1.le, hw.2.le⟩).1
    · filter_upwards [Ioo_mem_nhds hv.1 hvt] with w hw
      exact (P.old_match w ⟨hw.1.le, hw.2.le⟩).2.1
  · have htv : P.t ≤ v := le_of_not_gt hvt
    have hBarv : vBar < v := P.vBar_lt_t.trans_le htv
    let b : ℝ := (v + vStar) / 2
    have hvb : v < b := by dsimp [b]; linarith only [hv.2]
    have hbStar : b < vStar := by dsimp [b]; linarith only [hv.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar :=
      ⟨ha.trans (hv.1.trans hvb), hbStar⟩
    have haI : a ∈ Icc (0 : ℝ) a := ⟨ha.le, le_rfl⟩
    refine ⟨b, hb, hvb, ?_, ?_⟩
    · filter_upwards [Ioo_mem_nhds hBarv hvb] with w hw
      have hwTop : w ∈ Icc vBar vStar :=
        ⟨hw.1.le, hw.2.trans hbStar |>.le⟩
      exact (P.top_match w hwTop).1.trans
        (P.state.match_old b hb a haI w ⟨hw.1.le, hw.2⟩).2.2.1
    · filter_upwards [Ioo_mem_nhds hBarv hvb] with w hw
      have hwTop : w ∈ Icc vBar vStar :=
        ⟨hw.1.le, hw.2.trans hbStar |>.le⟩
      exact (P.top_match w hwTop).2.1.trans
        (P.state.match_old b hb a haI w ⟨hw.1.le, hw.2⟩).2.2.2.2.2.2.2.2

/-- One old-family `λᵥ` bound controls the derivative of the canonical C¹
continuation of every compact edge, including both endpoints. -/
theorem OffAxisTerminalC1Packet.extended_g_deriv_abs_le_of_old_bound
    {a vBar vStar C : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hbound : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u w : ℝ, 0 ≤ u → u < w → w < b →
        |deriv ((S b).lam u) w| ≤ C) :
    ∀ v ∈ Icc a vStar,
      |deriv (intervalC1Extension P.g a vStar) v| ≤ C := by
  have haStar : a < vStar := haBar.trans hBarStar
  let G := intervalC1Extension P.g a vStar
  have hG : ContDiff ℝ 1 G := intervalC1Extension_c1 haStar P.g_c1
  have hinterior : ∀ v ∈ Ioo a vStar, |deriv G v| ≤ C := by
    intro v hv
    obtain ⟨b, hb, hvb, hg, _⟩ :=
      P.eventually_eq_old_edge ha hv
    have hlocal : G =ᶠ[𝓝 v] P.g := by
      filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
      exact intervalC1Extension_eq ⟨hw.1.le, hw.2.le⟩
    rw [(hlocal.trans hg).deriv_eq]
    exact hbound b hb a v ha.le hv.1 hvb
  have hclosure : closure (Ioo a vStar) = Icc a vStar :=
    closure_Ioo haStar.ne
  have hderiv_cont : ContinuousOn (fun v => deriv G v) (Icc a vStar) :=
    (contDiff_one_iff_deriv.mp hG).2.continuousOn
  have habs_cont : ContinuousOn (fun v => |deriv G v|) (Icc a vStar) :=
    hderiv_cont.abs
  intro v hv
  have h := le_on_closure hinterior
    (by rw [hclosure]; exact habs_cont)
    (by rw [hclosure]; exact continuousOn_const)
    (by rw [hclosure]; exact hv)
  exact h

/-- The frozen family premises give one outgoing derivative bound for the
canonical C¹ continuation of every compact Route B expansion edge. -/
theorem exists_uniform_routeB_extended_g_deriv_bound
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {a vBar : ℝ} (_ha : 0 < a) (_haBar : a < vBar)
        (_hBarStar : vBar < vStar)
        (P : OffAxisTerminalC1Packet a vBar vStar S),
        ∀ v ∈ Icc a vStar,
          |deriv (intervalC1Extension P.g a vStar) v| ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_lambda_v_bound_before_star hu₀ hα hfamily hε htail
  exact ⟨C, hC, fun ha haBar hBarStar P =>
    P.extended_g_deriv_abs_le_of_old_bound ha haBar hBarStar hbound⟩

/-- A uniform old-family outgoing quotient derivative bound passes to the
canonical C¹ continuation of every compact Route B scalar edge. -/
theorem OffAxisTerminalC1Packet.extended_h_deriv_abs_le_of_old_bound
    {a vBar vStar C : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hbound : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u w : ℝ, 0 < u → u < w → w < b →
        |deriv (fun t => (S b).alpha u t / (S b).lam u t) w| ≤ C) :
    ∀ v ∈ Icc a vStar,
      |deriv (intervalC1Extension P.hEdge a vStar) v| ≤ C := by
  have haStar : a < vStar := haBar.trans hBarStar
  let H := intervalC1Extension P.hEdge a vStar
  have hH : ContDiff ℝ 1 H := intervalC1Extension_c1 haStar P.h_c1
  have hinterior : ∀ v ∈ Ioo a vStar, |deriv H v| ≤ C := by
    intro v hv
    obtain ⟨b, hb, hvb, _, hh⟩ :=
      P.eventually_eq_old_edge ha hv
    have hlocal : H =ᶠ[𝓝 v] P.hEdge := by
      filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
      exact intervalC1Extension_eq ⟨hw.1.le, hw.2.le⟩
    rw [(hlocal.trans hh).deriv_eq]
    exact hbound b hb a v ha hv.1 hvb
  have hclosure : closure (Ioo a vStar) = Icc a vStar :=
    closure_Ioo haStar.ne
  have hderiv_cont : ContinuousOn (fun v => deriv H v) (Icc a vStar) :=
    (contDiff_one_iff_deriv.mp hH).2.continuousOn
  have habs_cont : ContinuousOn (fun v => |deriv H v|) (Icc a vStar) :=
    hderiv_cont.abs
  intro v hv
  exact le_on_closure hinterior
    (by rw [hclosure]; exact habs_cont)
    (by rw [hclosure]; exact continuousOn_const)
    (by rw [hclosure]; exact hv)

/-- One unweighted `α′` estimate and the initial expansion gauge bound the
outgoing derivative of `α/λ` throughout the strict old union. -/
theorem exists_uniform_quotient_deriv_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u w : ℝ, 0 < u → u < w → w < b →
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) w| ≤ C := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  obtain ⟨B, hB, hprime⟩ :=
    exists_uniform_alphaPrime_bound_on_old_union_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε htail hIncoming
  have hC : 0 ≤ B / 2 := div_nonneg hB (by norm_num)
  refine ⟨B / 2, hC, ?_⟩
  intro b hb u w hu huw hwb
  let H := (hfamily b hb).1
  have hlam : 0 < (S b).lam u w :=
    H.solution.lam_pos (u, w) ⟨hu.le, huw, hwb⟩
  have hlamHalf : (S b).lam u w ≤ 1 / 2 :=
    lam_le_half_of_initial_gauge H
      (fun v hv => ((hfamily b hb).2 v hv).1) hu.le huw hwb
  have hpoint := hprime b hb u w hu huw hwb
  have hidentity :
      |deriv (fun t => (S b).alpha u t / (S b).lam u t) w| =
        |deriv (fun t => (S b).alpha u t / (S b).lam u t) w /
          (S b).lam u w| * (S b).lam u w := by
    rw [abs_div, abs_of_pos hlam]
    field_simp [ne_of_gt hlam]
  rw [hidentity]
  calc
    _ ≤ B * (S b).lam u w :=
      mul_le_mul_of_nonneg_right hpoint hlam.le
    _ ≤ B / 2 := by nlinarith only [hlamHalf, hB]

/-- The frozen premises provide a cutoff-independent bound on the derivative
of every canonical C¹ scalar edge continuation. -/
theorem exists_uniform_routeB_extended_h_deriv_bound
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {a vBar : ℝ} (_ha : 0 < a) (_haBar : a < vBar)
        (_hBarStar : vBar < vStar)
        (P : OffAxisTerminalC1Packet a vBar vStar S),
        ∀ v ∈ Icc a vStar,
          |deriv (intervalC1Extension P.hEdge a vStar) v| ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_quotient_deriv_bound_before_star hu₀ hα hfamily hε htail
  exact ⟨C, hC, fun ha haBar hBarStar P =>
    P.extended_h_deriv_abs_le_of_old_bound ha haBar hBarStar hbound⟩

/-- The initial scalar datum and the uniform incoming scalar derivative
bound give one bound for `φ` throughout the strict old union. -/
theorem exists_uniform_phi_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
          |(S b).phi u v| ≤ M := by
  obtain ⟨A, hA, hinitAlpha⟩ :=
    exists_initial_scalar_bound_before_star (hu₀.1.trans hu₀.2) hα hfamily
  obtain ⟨C, hC, hphiDeriv⟩ :=
    exists_uniform_scalar_incoming_derivative_bound_before_star
      hu₀ hα hfamily hε htail
  have hStar : 0 < vStar := hu₀.1.trans hu₀.2
  have hinitPhi (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) vStar)
      (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) b) :
      |(S b).phi 0 v| ≤ 2 * A := by
    let H := (hfamily b hb).1
    have hp : (0, v) ∈ developmentWithInitialEdge b :=
      ⟨le_refl 0, hv.1, hv.2⟩
    have hφ := phi_eq_outgoing_alpha_integral_of_c1_domain H hp
    have hr := ((hfamily b hb).2 v hv).1
    have hψ : (v / 2) * (S b).phi 0 v =
        ∫ w in (0 : ℝ)..v, (S b).alpha 0 w := by
      rw [hφ, hr]
      field_simp [ne_of_gt hv.1]
    have hInt : |∫ w in (0 : ℝ)..v, (S b).alpha 0 w| ≤ A * v := by
      have hbnd : ∀ w ∈ Set.uIoc (0 : ℝ) v,
          ‖(S b).alpha 0 w‖ ≤ A := by
        intro w hw
        have hw' : w ∈ Ioc (0 : ℝ) v := by
          simpa only [uIoc_of_le hv.1.le] using hw
        exact_mod_cast (hinitAlpha b hb w ⟨hw'.1, hw'.2.trans_lt hv.2⟩).1
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      simpa only [Real.norm_eq_abs, abs_of_pos hv.1, sub_zero] using hh
    have habs := congrArg abs hψ
    rw [abs_mul, abs_of_pos (half_pos hv.1)] at habs
    have hmul : v * |(S b).phi 0 v| ≤ v * (2 * A) := by
      nlinarith only [hInt, habs]
    nlinarith only [hmul, hv.1]
  let M : ℝ := 2 * A + C * vStar
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro b hb u v hu huv hvb
  have hv : v ∈ Ioo (0 : ℝ) b := ⟨hu.trans_lt huv, hvb⟩
  by_cases huZero : u = 0
  · subst u
    exact (hinitPhi b hb v hv).trans (by
      dsimp [M]
      nlinarith only [mul_nonneg hC hStar.le])
  have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm huZero)
  let H := (hfamily b hb).1
  have hcont : ContinuousOn (fun s => (S b).phi s v) (Icc 0 u) :=
    H.phi_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (by
        intro s hs
        exact subset_closure ⟨hs.1, hs.2.trans_lt huv, hvb⟩)
  have hdiff : ∀ s ∈ Ioo (0 : ℝ) u,
      DifferentiableAt ℝ (fun t => (S b).phi t v) s := by
    intro s hs
    exact (phi_hasDerivAt_u_of_c1 H
      (show (s, v) ∈ openDevelopment 0 b from
        ⟨⟨hs.1, (hs.2.trans huv).trans hvb⟩,
          ⟨hs.2.trans huv, hvb⟩⟩)).differentiableAt
  have hbound : ∀ s ∈ Ioo (0 : ℝ) u,
      |deriv (fun t => (S b).phi t v) s| ≤ C := by
    intro s hs
    exact hphiDeriv b hb s v hs.1 (hs.2.trans huv) hvb
  have hLip := lipschitzOnWith_Icc_of_continuousOn_deriv_bound_Ioo
    huPos hC hcont hdiff hbound
  have hdist := hLip.dist_le_mul u
    (show u ∈ Icc (0 : ℝ) u from ⟨hu, le_rfl⟩)
    0 (show (0 : ℝ) ∈ Icc (0 : ℝ) u from ⟨le_rfl, hu⟩)
  change dist ((S b).phi u v) ((S b).phi 0 v) ≤ C * dist u 0 at hdist
  have hdiffBound : |(S b).phi u v - (S b).phi 0 v| ≤ C * u := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hu] using hdist
  have huStar : u ≤ vStar :=
    (huv.le.trans hvb.le).trans hb.2.le
  calc
    |(S b).phi u v| ≤
        |(S b).phi u v - (S b).phi 0 v| + |(S b).phi 0 v| := by
      simpa only [sub_add_cancel] using
        (abs_add_le ((S b).phi u v - (S b).phi 0 v) ((S b).phi 0 v))
    _ ≤ C * u + 2 * A := add_le_add hdiffBound (hinitPhi b hb v hv)
    _ ≤ M := by dsimp [M]; nlinarith only [huStar, hC]

/-- The scalar decomposition `α/λ = θ/λ + φ` supplies a uniform value bound
for the characteristic scalar edge throughout the old union. -/
theorem exists_uniform_quotient_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |(S b).alpha u v / (S b).lam u v| ≤ H := by
  obtain ⟨M, hM, hphi⟩ :=
    exists_uniform_phi_bound_before_star hu₀ hα hfamily hε htail
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  obtain ⟨B, hB, _, htheta, _, _⟩ :=
    exists_uniform_scalar_and_cubic_mass_bounds_on_old_union_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε htail hIncoming
  let H : ℝ := B * vStar / 4 + M
  have hStar : 0 ≤ vStar := (hu₀.1.trans hu₀.2).le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨H, hH, ?_⟩
  intro b hb u v hu huv hvb
  let D := (hfamily b hb).1
  have hlam : 0 < (S b).lam u v :=
    D.solution.lam_pos (u, v) ⟨hu.le, huv, hvb⟩
  have hr : (S b).r u v ≤ v / 2 := by
    have hr' := radius_antitone_on_incoming_of_c1 D
      (le_refl 0) hu.le huv hvb
    rw [((hfamily b hb).2 v ⟨hu.trans huv, hvb⟩).1] at hr'
    exact hr'
  have hθ : |(S b).theta u v / (S b).lam u v| ≤ B * vStar / 4 := by
    have hBhalf : 0 ≤ B / 2 := div_nonneg hB (by norm_num)
    calc
      |(S b).theta u v / (S b).lam u v| ≤
          B / 2 * (S b).r u v := htheta b hb u v hu huv hvb
      _ ≤ B / 2 * (v / 2) :=
          mul_le_mul_of_nonneg_left hr hBhalf
      _ ≤ B / 2 * (vStar / 2) := by
          apply mul_le_mul_of_nonneg_left _ hBhalf
          linarith only [hvb, hb.2]
      _ = B * vStar / 4 := by ring
  have heq : (S b).alpha u v / (S b).lam u v =
      (S b).theta u v / (S b).lam u v + (S b).phi u v := by
    dsimp [Fields.theta]
    field_simp [ne_of_gt hlam]
    ring
  rw [heq]
  calc
    |(S b).theta u v / (S b).lam u v + (S b).phi u v| ≤
        |(S b).theta u v / (S b).lam u v| + |(S b).phi u v| :=
          abs_add_le _ _
    _ ≤ B * vStar / 4 + M := add_le_add hθ (hphi b hb u v hu.le huv hvb)
    _ = H := rfl

/-- A uniform strict old-union bound on `α/λ` passes to the entire compact
scalar edge, including its axis and terminal endpoints. -/
theorem OffAxisTerminalC1Packet.h_abs_le_of_old_bound
    {a vBar vStar H : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hbound : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 < u → u < v → v < b →
        |(S b).alpha u v / (S b).lam u v| ≤ H) :
    ∀ v ∈ Icc a vStar, |P.hEdge v| ≤ H := by
  have haStar : a < vStar := haBar.trans hBarStar
  have hinterior : ∀ v ∈ Ioo a vStar, |P.hEdge v| ≤ H := by
    intro v hv
    by_cases hvt : v ≤ P.t
    · rw [(P.old_match v ⟨hv.1.le, hvt⟩).2.1]
      exact hbound P.b₀ P.b₀_mem a v ha hv.1
        (hvt.trans_lt P.t_lt_b₀)
    · have hBarv : vBar ≤ v :=
        (P.vBar_lt_t.trans (lt_of_not_ge hvt)).le
      let b : ℝ := (v + vStar) / 2
      have hvb : v < b := by dsimp [b]; linarith only [hv.2]
      have hbStar : b < vStar := by dsimp [b]; linarith only [hv.2]
      have hb : b ∈ Ioo (0 : ℝ) vStar :=
        ⟨ha.trans (hv.1.trans hvb), hbStar⟩
      have haI : a ∈ Icc (0 : ℝ) a := ⟨ha.le, le_rfl⟩
      rw [(P.top_match v ⟨hBarv, hv.2.le⟩).2.1,
        (P.state.match_old b hb a haI v ⟨hBarv, hvb⟩).2.2.2.2.2.2.2.2]
      exact hbound b hb a v ha hv.1 hvb
  have hclosure : closure (Ioo a vStar) = Icc a vStar :=
    closure_Ioo haStar.ne
  have hcont : ContinuousOn (fun v => |P.hEdge v|) (Icc a vStar) :=
    P.h_c1.continuousOn.abs
  intro v hv
  exact le_on_closure hinterior
    (by rw [hclosure]; exact hcont)
    (by rw [hclosure]; exact continuousOn_const)
    (by rw [hclosure]; exact hv)

/-- One scalar-edge value bound works for every incoming cutoff and every
compact Route B edge construction from the frozen family. -/
theorem exists_uniform_routeB_h_value_bound
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ {a vBar : ℝ} (_ha : 0 < a) (_haBar : a < vBar)
        (_hBarStar : vBar < vStar)
        (P : OffAxisTerminalC1Packet a vBar vStar S),
        ∀ v ∈ Icc a vStar, |P.hEdge v| ≤ H := by
  obtain ⟨H, hH, hbound⟩ :=
    exists_uniform_quotient_bound_before_star hu₀ hα hfamily hε htail
  exact ⟨H, hH, fun ha haBar hBarStar P =>
    P.h_abs_le_of_old_bound ha haBar hBarStar hbound⟩

/-- A single physical edge norm controls every cutoff-dependent construction.
The functions used here are the canonical globally C¹ continuations of the
construction's old edge, so the endpoint derivative bounds have their intended
one-sided values. -/
theorem exists_uniform_routeB_extended_edge_bounds
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ c Clam H : ℝ, 0 < c ∧ 0 ≤ Clam ∧ 0 ≤ H ∧
      ∀ {a vBar : ℝ} (_ha : 0 < a) (_haBar : a < vBar)
        (_hBarStar : vBar < vStar)
        (P : OffAxisTerminalC1Packet a vBar vStar S),
        ∀ v ∈ Icc a vStar,
          c ≤ intervalC1Extension P.g a vStar v ∧
          |deriv (intervalC1Extension P.g a vStar) v| ≤ Clam ∧
          |intervalC1Extension P.hEdge a vStar v| ≤ H ∧
          |deriv (intervalC1Extension P.hEdge a vStar) v| ≤ H := by
  obtain ⟨c, hc, hfloor⟩ :=
    exists_uniform_routeB_edge_floor hu₀ hα hfamily hε htail
  obtain ⟨Clam, hClam, hgderiv⟩ :=
    exists_uniform_routeB_extended_g_deriv_bound hu₀ hα hfamily hε htail
  obtain ⟨Hval, hHval, hhval⟩ :=
    exists_uniform_routeB_h_value_bound hu₀ hα hfamily hε htail
  obtain ⟨Hderiv, hHderiv, hhderiv⟩ :=
    exists_uniform_routeB_extended_h_deriv_bound hu₀ hα hfamily hε htail
  let H := max Hval Hderiv
  have hH : 0 ≤ H := hHval.trans (le_max_left _ _)
  refine ⟨c, Clam, H, hc, hClam, hH, ?_⟩
  intro a vBar ha haBar hBarStar P v hv
  have hvOld : intervalC1Extension P.g a vStar v = P.g v :=
    intervalC1Extension_eq hv
  have hvScalar : intervalC1Extension P.hEdge a vStar v = P.hEdge v :=
    intervalC1Extension_eq hv
  refine ⟨?_, hgderiv ha haBar hBarStar P v hv, ?_, ?_⟩
  · rw [hvOld]
    exact hfloor ha haBar hBarStar P v hv
  · rw [hvScalar]
    exact (hhval ha haBar hBarStar P v hv).trans (le_max_left _ _)
  · exact (hhderiv ha haBar hBarStar P v hv).trans (le_max_right _ _)

end ChristodoulouBV.Uniqueness

end
