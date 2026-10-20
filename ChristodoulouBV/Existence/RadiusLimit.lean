module

public import ChristodoulouBV.Existence.RadiusLimitRepresentatives
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Radius limit and the common subsequence for global BV existence

Arzelà–Ascoli compactness, simultaneous Helly selection, and the radius
primitive identities give a limit on the global domain. All subsequent
existence constructions use
`(radiusLimitData h hD).subsequence`; the scalar radius, mass, α, and β
have already been selected along this same map.

Raw Helly values converge pointwise everywhere. `rightLam` and `rightNu`
are their canonical right representatives, with right continuity, section
variation bounds, all-point geometry, and the two radius primitives proved
in `RadiusLimitRepresentatives`. At jumps the convergence to these
representatives is sectionwise almost everywhere, as stated there.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The fixed countable closed-triangle exhaustion used for all limits. -/
@[expose] def radiusLimitTriangle (n : ℕ) : Set (ℝ × ℝ) :=
  closedCoordTriangle 0 ((n : ℝ) + 1)

/-- The exhaustion is compact and increasing, covers the initial-edge
inclusive global domain, and contains every nonnegative axis point. -/
theorem radius_limit_triangle_exhaustion :
    (∀ n, IsCompact (radiusLimitTriangle n)) ∧ Monotone radiusLimitTriangle ∧
      (∀ p ∈ globalDomain, ∃ n, p ∈ radiusLimitTriangle n) ∧
      ∀ x : ℝ, 0 ≤ x → ∃ n, (x, x) ∈ radiusLimitTriangle n := by
  refine ⟨fun n => isCompact_closedCoordTriangle 0 _, ?_, ?_, ?_⟩
  · intro m n hmn p hp
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact ⟨hp.1, hp.2.1, hp.2.2.trans (add_le_add_left hmn' 1)⟩
  · intro p hp
    obtain ⟨n, hn⟩ := exists_nat_gt p.2
    exact ⟨n, hp.1, hp.2.le, hn.le.trans (le_add_of_nonneg_right zero_le_one)⟩
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, hx, le_rfl, hn.le.trans (le_add_of_nonneg_right zero_le_one)⟩

/-- The shared existence selection. Subsequent constructions use its `subsequence` without
any new extraction; all seven limits have already been selected. -/
@[expose] noncomputable def radiusLimitData
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞) :
    RadiusLimitData T := Classical.choice (s6_global_domain_limit h hD)

/-- The quantitative radius floor passes to the limit at every point. -/
theorem RadiusLimitData.radius_lower
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    (p.2 - p.1) / 3 ≤ d.radius p :=
  ge_of_tendsto (d.radius_limit.tendsto_at hp)
    (Eventually.of_forall (fun n => (h (d.subsequence n)).radius_lower hp))

/-- The limiting radius is strictly positive throughout the global development. -/
theorem RadiusLimitData.radius_pos
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) : 0 < d.radius p :=
  (div_pos (sub_pos.mpr hp.2) (by norm_num)).trans_le (d.radius_lower h hp)

/-- The radius converges locally uniformly on the whole global development,
uniformly on each closed triangle after its zero-axis extension, and
retains both the axis trace and the exact initial gauge. The index map is
the same one exported for all subsequent limit constructions. -/
theorem radius_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞) :
    let d := radiusLimitData h hD
    StrictMono d.subsequence ∧ Continuous d.radius ∧
      TendstoLocallyUniformlyOn
        (fun n (p : ℝ × ℝ) => (T (d.subsequence n)).r p.1 p.2) d.radius atTop globalDomain ∧
      (∀ b : ℝ, TendstoUniformlyOn (fun n => radiusWithAxis (T (d.subsequence n)))
        d.radius atTop (closedCoordTriangle 0 b)) ∧
      (∀ x : ℝ, 0 ≤ x → d.radius (x, x) = 0) ∧
      (∀ v : ℝ, 0 < v → d.radius (0, v) = v / 2) ∧
      ∀ p ∈ globalDomain, (p.2 - p.1) / 3 ≤ d.radius p := by
  let d := radiusLimitData h hD
  exact ⟨d.strictMono, d.radius_continuous, d.radius_limit,
    d.radius_uniform_on_closed_triangle h, fun _ hx => d.radius_axis h hx,
    fun _ hv => d.initial_radius h hv, fun _ hp => d.radius_lower h hp⟩

/-- The seven raw limits packaged as fields on the common carrier. The
scalar is the quotient of the selected scalar radius and positive radius. -/
@[expose] noncomputable def RadiusLimitData.rawFields {T : ℕ → Fields}
    (d : RadiusLimitData T) : Fields where
  r := fun u v => d.radius (u, v)
  phi := fun u v => d.scalarRadius (u, v) / d.radius (u, v)
  m := fun u v => d.mass (u, v)
  lam := d.lam
  nu := d.nu
  alpha := d.alpha
  beta := d.beta

/-- The same fields with the canonical right-v λ and right-u ν representatives.
The scalar derivative representatives are retained for the scalar limit and final representative constructions. -/
@[expose] noncomputable def RadiusLimitData.rightFields {T : ℕ → Fields}
    (d : RadiusLimitData T) : Fields :=
  { d.rawFields with lam := d.rightLam, nu := d.rightNu }

/-- The two mass-ratio geometry inequalities survive the already selected
mass and radius limits. Their constants are universal. -/
theorem RadiusLimitData.mass_geometry
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      (2 / 3 : ℝ) ≤ 1 - 2 * d.mass p / d.radius p ∧
      1 - 2 * d.mass p / d.radius p ≤ 1 := by
  intro p hp
  have hr := d.radius_limit.tendsto_at hp
  have hm := d.mass_limit.tendsto_at hp
  have hq : Tendsto
      (fun n => 1 - 2 * (T (d.subsequence n)).m p.1 p.2 / (T (d.subsequence n)).r p.1 p.2)
      atTop (𝓝 (1 - 2 * d.mass p / d.radius p)) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.mul hm).div hr (d.radius_pos h hp).ne')
  exact ⟨ge_of_tendsto hq (Eventually.of_forall
      (fun n => ((h (d.subsequence n)).geometry p hp).2.2.2.2.1)),
    le_of_tendsto hq (Eventually.of_forall
      (fun n => ((h (d.subsequence n)).geometry p hp).2.2.2.2.2))⟩

/-- All six geometry inequalities hold at every point for the same
right-representative fields, including on the initial edge. -/
theorem radius_limit_geometry
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      (1 / 3 : ℝ) ≤ d.rightFields.lam p.1 p.2 ∧ d.rightFields.lam p.1 p.2 ≤ 1 / 2 ∧
      (1 / 3 : ℝ) ≤ -d.rightFields.nu p.1 p.2 ∧ -d.rightFields.nu p.1 p.2 ≤ 2 / 3 ∧
      (2 / 3 : ℝ) ≤ 1 - 2 * d.rightFields.m p.1 p.2 / d.rightFields.r p.1 p.2 ∧
      1 - 2 * d.rightFields.m p.1 p.2 / d.rightFields.r p.1 p.2 ≤ 1 := by
  intro p hp
  obtain ⟨hl0, hl1, hn0, hn1⟩ := right_expansions_geometry h hD d p hp
  obtain ⟨hq0, hq1⟩ := d.mass_geometry h p hp
  exact ⟨hl0, hl1, hn0, hn1, hq0, hq1⟩

end ChristodoulouBV

end
