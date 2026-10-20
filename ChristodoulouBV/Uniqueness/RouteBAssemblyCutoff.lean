module

public import ChristodoulouBV.C1Solution.AxisUniformEndpointNormalization
import Mathlib.Tactic.Linarith

/-!
# Selecting the Route B incoming cutoff

A positive uniform axis lifetime allows the incoming line to be chosen after
the lifetime is fixed. The finite lower-cover height may then be chosen below
half the lifetime, leaving room for the prescribed axis endpoint.
-/

public section

open Set ChristodoulouBV.AxisPicard

namespace ChristodoulouBV.Uniqueness

/-- For any positive lifetime, choose an incoming cutoff beyond `u₀` with
less than half the lifetime remaining before the terminal outgoing line. -/
theorem exists_routeB_cutoff_near_terminal
    {u₀ vStar T : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hT : 0 < T) :
    ∃ a vBar : ℝ,
      u₀ < a ∧ a < vBar ∧ vBar < vStar ∧
      vStar - a < T / 2 := by
  let x : ℝ := max u₀ (vStar - T / 2)
  let a : ℝ := (x + vStar) / 2
  let vBar : ℝ := (a + vStar) / 2
  have hxStar : x < vStar := max_lt hu₀.2 (by linarith only [hT])
  have hu₀x : u₀ ≤ x := le_max_left _ _
  have hTx : vStar - T / 2 ≤ x := le_max_right _ _
  refine ⟨a, vBar, ?_, ?_, ?_, ?_⟩
  · dsimp [a]
    linarith only [hu₀x, hxStar]
  · dsimp [vBar]
    dsimp [a]
    linarith only [hxStar]
  · dsimp [vBar, a]
    linarith only [hxStar]
  · dsimp [a]
    linarith only [hTx, hxStar]

/-- A lower-cover height below half the uniform lifetime places its top
strictly inside the prescribed axis interval. -/
theorem routeB_lower_top_lt_axis_lifetime
    {a vStar η T : ℝ} (hgap : vStar - a < T / 2)
    (hη : η < T / 2) : vStar + η < a + T := by
  linarith only [hgap, hη]

/-- The endpoint selected by the lower cover lies above the old terminal
line and within the available prescribed axis lifetime. -/
theorem routeB_lower_top_endpoint
    {a vStar η T : ℝ} (haStar : a < vStar)
    (hgap : vStar - a < T / 2)
    (hη : 0 < η) (hηT : η < T / 2) :
    a < vStar + η ∧ vStar < vStar + η ∧
      vStar + η - a ≤ T ∧
      min (a + T) (vStar + η) = vStar + η := by
  have htop := routeB_lower_top_lt_axis_lifetime hgap hηT
  refine ⟨by linarith only [haStar, hη], by linarith only [hη],
    by linarith only [htop], ?_⟩
  exact min_eq_right htop.le

/-- The preceding choice applies to the quantitative prescribed-endpoint
lifetime for any fixed physical edge bounds. -/
theorem exists_routeB_cutoff_for_uniform_axis_lifetime
    {u₀ vStar : ℝ} (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (c Clam H : ℝ) :
    ∃ a vBar : ℝ,
      u₀ < a ∧ a < vBar ∧ vBar < vStar ∧
      vStar - a < uniformAxisLifetime c Clam H / 2 :=
  exists_routeB_cutoff_near_terminal hu₀
    (uniformAxisLifetime_pos c Clam H)

end ChristodoulouBV.Uniqueness

end
