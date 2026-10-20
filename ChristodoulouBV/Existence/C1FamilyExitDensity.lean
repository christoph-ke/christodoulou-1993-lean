module

public import ChristodoulouBV.C1Solution.ExtractionRemovable
public import ChristodoulouBV.Existence.C1FamilyBootstrap
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Continuous null densities for finite C¹ developments

The two singular-looking source integrands have continuous extensions
through the regular axis. These extensions are the analytic input for
continuity of the first-exit null-size functional.
-/

public section

open Set

namespace ChristodoulouBV

/-- Continuous outgoing null density on a compact triangle. -/
@[expose] noncomputable def s6OutgoingDensity (B : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  |C1Solution.normalizedTheta B S p| /
    C1Solution.canonicalNormalizedRadius S p

/-- Continuous incoming null density on a compact triangle. -/
@[expose] noncomputable def s6IncomingDensity (B : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  |C1Solution.normalizedZeta B S p| /
    C1Solution.canonicalNormalizedRadius S p

/-- The outgoing density extends continuously through the axis and agrees
with the source quotient on the open finite development. -/
theorem s6_outgoing_density_continuous_and_eq {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (s6OutgoingDensity B S) (closedCoordTriangle 0 B) ∧
    ∀ u v : ℝ, 0 ≤ u → u < v → v < B →
      |S.theta u v| / S.r u v = s6OutgoingDensity B S (u, v) := by
  obtain ⟨hRcont, c, hc, hRlow⟩ :=
    C1Solution.canonicalNormalizedRadius_continuousOn_and_lower_bound
      hB hBb H
  have hRne : ∀ p ∈ closedCoordTriangle 0 B,
      C1Solution.canonicalNormalizedRadius S p ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hRlow p hp))
  constructor
  · exact (C1Solution.normalizedTheta_continuousOn hB hBb H).abs.div
      hRcont hRne
  · intro u v hu huv hvB
    have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
      ⟨hu, huv.le, hvB.le⟩
    have hpD : (u, v) ∈ developmentWithInitialEdge b :=
      ⟨hu, huv, hvB.trans hBb⟩
    have hθ := C1Solution.theta_eq_gap_mul_normalizedTheta hB hBb H hpK
    have hr := C1Solution.canonicalRadius_eq_radius hB hBb H
      hu huv hvB.le
    have hnorm := C1Solution.canonicalRadius_eq_gap_mul_normalized S u v
    have hgap : v - u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
    have hR : C1Solution.canonicalNormalizedRadius S (u, v) ≠ 0 :=
      hRne (u, v) hpK
    have hRpos : 0 < C1Solution.canonicalNormalizedRadius S (u, v) :=
      hc.trans_le (hRlow (u, v) hpK)
    rw [← hr, hnorm, hθ]
    simp only [s6OutgoingDensity, abs_mul,
      abs_of_pos (sub_pos.mpr huv)]
    field_simp [hgap, hR]

/-- The incoming density extends continuously through the axis and agrees
with the source quotient on the open finite development. -/
theorem s6_incoming_density_continuous_and_eq {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (s6IncomingDensity B S) (closedCoordTriangle 0 B) ∧
    ∀ u v : ℝ, 0 ≤ u → u < v → v < B →
      |S.zeta u v| / S.r u v = s6IncomingDensity B S (u, v) := by
  obtain ⟨hRcont, c, hc, hRlow⟩ :=
    C1Solution.canonicalNormalizedRadius_continuousOn_and_lower_bound
      hB hBb H
  have hRne : ∀ p ∈ closedCoordTriangle 0 B,
      C1Solution.canonicalNormalizedRadius S p ≠ 0 :=
    fun p hp => ne_of_gt (hc.trans_le (hRlow p hp))
  constructor
  · exact (C1Solution.normalizedZeta_continuousOn hB hBb H).abs.div
      hRcont hRne
  · intro u v hu huv hvB
    have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
      ⟨hu, huv.le, hvB.le⟩
    have hζ := C1Solution.zeta_eq_gap_mul_normalizedZeta hB hBb H hpK
    have hr := C1Solution.canonicalRadius_eq_radius hB hBb H
      hu huv hvB.le
    have hnorm := C1Solution.canonicalRadius_eq_gap_mul_normalized S u v
    have hgap : v - u ≠ 0 := ne_of_gt (sub_pos.mpr huv)
    have hR : C1Solution.canonicalNormalizedRadius S (u, v) ≠ 0 :=
      hRne (u, v) hpK
    rw [← hr, hnorm, hζ]
    simp only [s6IncomingDensity, abs_mul,
      abs_of_pos (sub_pos.mpr huv)]
    field_simp [hgap, hR]

/-- Both source null integrands on a rescaled unit triangle are the
continuous compact-triangle densities with one scale factor. -/
theorem s6_rescaled_null_density_eq {b B a : ℝ}
    (hB : 0 < B) (hBb : B < b) (ha : 0 < a) (haB : a < B)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v < 1) :
    |(Uniqueness.rescaledFields S 0 a).theta u v| /
        (Uniqueness.rescaledFields S 0 a).r u v =
      a * s6OutgoingDensity B S (a * u, a * v) ∧
    |(Uniqueness.rescaledFields S 0 a).zeta u v| /
        (Uniqueness.rescaledFields S 0 a).r u v =
      a * s6IncomingDensity B S (a * u, a * v) := by
  have hu' : 0 ≤ a * u := mul_nonneg ha.le hu
  have huv' : a * u < a * v := mul_lt_mul_of_pos_left huv ha
  have hv' : a * v < B := by
    calc
      a * v < a * 1 := mul_lt_mul_of_pos_left hv ha
      _ = a := by ring
      _ < B := haB
  have hrpos : 0 < S.r (a * u) (a * v) :=
    H.solution.radius_pos (a * u, a * v)
      ⟨hu', huv', hv'.trans hBb⟩
  have hout := (s6_outgoing_density_continuous_and_eq hB hBb H).2
    (a * u) (a * v) hu' huv' hv'
  have hin := (s6_incoming_density_continuous_and_eq hB hBb H).2
    (a * u) (a * v) hu' huv' hv'
  constructor
  · simp only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, Fields.theta] at hout ⊢
    rw [← hout]
    field_simp [ha.ne', hrpos.ne']
  · simp only [Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, Fields.zeta] at hin ⊢
    rw [← hin]
    field_simp [ha.ne', hrpos.ne']

end ChristodoulouBV

end
