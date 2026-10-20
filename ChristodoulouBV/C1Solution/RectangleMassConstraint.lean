module

public import ChristodoulouBV.C1Solution.RectangleConstraints
import Mathlib.Tactic

/-!
# Calculus for the incoming mass constraint

The outgoing mass density and the proposed incoming mass density have a
common differentiated defect. This pointwise calculation is valid for
relative derivatives at every edge and corner of an off-axis rectangle.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The derivative calculation for the incoming mass defect. The hypotheses
are the differentiated radius, scalar, and mass transport equations at one
point, with the mixed mass partial supplied separately. -/
theorem mass_defect_hasDerivWithinAt
    {s : Set ℝ} {v : ℝ}
    {m r lam nu theta zeta d : ℝ → ℝ}
    (hr : r v ≠ 0) (hlam : lam v ≠ 0) (hnu : nu v ≠ 0)
    (hgap : r v - 2 * m v ≠ 0)
    (hm : HasDerivWithinAt m
      ((1 - 2 * m v / r v) * theta v ^ 2 / (2 * lam v)) s v)
    (hrv : HasDerivWithinAt r (lam v) s v)
    (hnuv : HasDerivWithinAt nu
      (2 * m v * lam v * nu v / (r v * (r v - 2 * m v))) s v)
    (hzetav : HasDerivWithinAt zeta (-nu v * theta v / r v) s v)
    (hdv : HasDerivWithinAt d
      ((-2 * d v / r v + 2 * m v * nu v / r v ^ 2) * theta v ^ 2 /
          (2 * lam v) +
        (1 - 2 * m v / r v) * (2 * theta v * (-lam v * zeta v / r v)) /
          (2 * lam v) -
        (1 - 2 * m v / r v) * theta v ^ 2 *
          (2 * m v * lam v * nu v / (r v * (r v - 2 * m v))) /
          (2 * lam v ^ 2)) s v) :
    HasDerivWithinAt
      (fun t => d t - (1 - 2 * m t / r t) * zeta t ^ 2 / (2 * nu t))
      (-theta v ^ 2 / (r v * lam v) *
        (d v - (1 - 2 * m v / r v) * zeta v ^ 2 / (2 * nu v))) s v := by
  let A : ℝ → ℝ := fun t => 1 - 2 * m t / r t
  let N : ℝ → ℝ := fun t => A t * zeta t ^ 2 / (2 * nu t)
  have hAv : HasDerivWithinAt A
      (-2 * ((1 - 2 * m v / r v) * theta v ^ 2 / (2 * lam v)) / r v +
        2 * m v * lam v / r v ^ 2) s v := by
    have h := (hasDerivWithinAt_const (s := s) (x := v) (c := (1 : ℝ))).sub
      ((hm.const_mul 2).div hrv hr)
    convert h using 1
    field_simp
    ring
  have hNv : HasDerivWithinAt N
      ((-2 * ((1 - 2 * m v / r v) * theta v ^ 2 / (2 * lam v)) / r v +
          2 * m v * lam v / r v ^ 2) * zeta v ^ 2 / (2 * nu v) +
        (1 - 2 * m v / r v) * (2 * zeta v * (-nu v * theta v / r v)) /
          (2 * nu v) -
        (1 - 2 * m v / r v) * zeta v ^ 2 *
          (2 * m v * lam v * nu v / (r v * (r v - 2 * m v))) /
          (2 * nu v ^ 2)) s v := by
    have h := ((hAv.mul (hzetav.pow 2)).div (hnuv.const_mul 2)
      (mul_ne_zero two_ne_zero hnu))
    convert h using 1
    dsimp [A]
    field_simp
  have hE := hdv.sub hNv
  convert hE using 1
  exact (mass_defect_vertical_algebra (m v) (r v) (lam v) (nu v)
    (theta v) (zeta v) (d v) hr hlam hnu hgap).symm

/-- The horizontal derivative of the outgoing mass density, computed from
the incoming radius, expansion, and scalar equations. -/
theorem outgoing_mass_density_hasDerivWithinAt_horizontal
    {s : Set ℝ} {u : ℝ}
    {m r lam nu theta zeta d : ℝ → ℝ}
    (hr : r u ≠ 0) (hlam : lam u ≠ 0)
    (hmu : HasDerivWithinAt m (d u) s u)
    (hru : HasDerivWithinAt r (nu u) s u)
    (hlamu : HasDerivWithinAt lam
      (2 * m u * lam u * nu u / (r u * (r u - 2 * m u))) s u)
    (hthetau : HasDerivWithinAt theta (-lam u * zeta u / r u) s u) :
    HasDerivWithinAt
      (fun t => (1 - 2 * m t / r t) * theta t ^ 2 / (2 * lam t))
      ((-2 * d u / r u + 2 * m u * nu u / r u ^ 2) * theta u ^ 2 /
          (2 * lam u) +
        (1 - 2 * m u / r u) * (2 * theta u * (-lam u * zeta u / r u)) /
          (2 * lam u) -
        (1 - 2 * m u / r u) * theta u ^ 2 *
          (2 * m u * lam u * nu u / (r u * (r u - 2 * m u))) /
          (2 * lam u ^ 2)) s u := by
  let A : ℝ → ℝ := fun t => 1 - 2 * m t / r t
  have hAu : HasDerivWithinAt A
      (-2 * d u / r u + 2 * m u * nu u / r u ^ 2) s u := by
    have h := (hasDerivWithinAt_const (s := s) (x := u) (c := (1 : ℝ))).sub
      ((hmu.const_mul 2).div hru hr)
    convert h using 1
    field_simp
    ring
  have h := ((hAu.mul (hthetau.pow 2)).div (hlamu.const_mul 2)
    (mul_ne_zero two_ne_zero hlam))
  convert h using 1
  dsimp [A]
  field_simp

/-- Incoming mass propagation for continuous scalar rectangle fields. The
transport hypotheses are the off-axis first-order field equations; the
horizontal mass jet is identified with `d`. The mixed mass partial is derived
from the outgoing density rather than assumed. -/
theorem incoming_mass_constraint_of_rectangle_equations
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    {m r lam nu theta zeta d : ℝ → ℝ → ℝ}
    (hmcont : ContinuousOn (fun p : ℝ × ℝ => m p.1 p.2)
      (Set.Icc a₀ a₁ ×ˢ Set.Icc b₀ b₁))
    (hdcont : ContinuousOn (fun p : ℝ × ℝ => d p.1 p.2)
      (Set.Icc a₀ a₁ ×ˢ Set.Icc b₀ b₁))
    (hPcont : ContinuousOn
      (fun p : ℝ × ℝ => (1 - 2 * m p.1 p.2 / r p.1 p.2) *
        theta p.1 p.2 ^ 2 / (2 * lam p.1 p.2))
      (Set.Icc a₀ a₁ ×ˢ Set.Icc b₀ b₁))
    (hHcont : ContinuousOn
      (fun p : ℝ × ℝ =>
        (-2 * d p.1 p.2 / r p.1 p.2 +
            2 * m p.1 p.2 * nu p.1 p.2 / r p.1 p.2 ^ 2) *
            theta p.1 p.2 ^ 2 / (2 * lam p.1 p.2) +
          (1 - 2 * m p.1 p.2 / r p.1 p.2) *
            (2 * theta p.1 p.2 *
              (-lam p.1 p.2 * zeta p.1 p.2 / r p.1 p.2)) /
              (2 * lam p.1 p.2) -
          (1 - 2 * m p.1 p.2 / r p.1 p.2) * theta p.1 p.2 ^ 2 *
            (2 * m p.1 p.2 * lam p.1 p.2 * nu p.1 p.2 /
              (r p.1 p.2 * (r p.1 p.2 - 2 * m p.1 p.2))) /
              (2 * lam p.1 p.2 ^ 2))
      (Set.Icc a₀ a₁ ×ˢ Set.Icc b₀ b₁))
    (hsafe : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      r u v ≠ 0 ∧ lam u v ≠ 0 ∧ nu u v ≠ 0 ∧
      r u v - 2 * m u v ≠ 0)
    (hmu : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (fun s => m s v) (d u v) (Set.Icc a₀ a₁) u)
    (hru : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (fun s => r s v) (nu u v) (Set.Icc a₀ a₁) u)
    (hlamu : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (fun s => lam s v)
        (2 * m u v * lam u v * nu u v /
          (r u v * (r u v - 2 * m u v))) (Set.Icc a₀ a₁) u)
    (hthetau : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (fun s => theta s v)
        (-lam u v * zeta u v / r u v) (Set.Icc a₀ a₁) u)
    (hmv : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (m u)
        ((1 - 2 * m u v / r u v) * theta u v ^ 2 / (2 * lam u v))
        (Set.Icc b₀ b₁) v)
    (hrv : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (r u) (lam u v) (Set.Icc b₀ b₁) v)
    (hnuv : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (nu u)
        (2 * m u v * lam u v * nu u v /
          (r u v * (r u v - 2 * m u v))) (Set.Icc b₀ b₁) v)
    (hzetav : ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt (zeta u) (-nu u v * theta u v / r u v)
        (Set.Icc b₀ b₁) v)
    (hecont : ∀ u ∈ Set.Icc a₀ a₁,
      ContinuousOn (fun v => d u v -
        (1 - 2 * m u v / r u v) * zeta u v ^ 2 / (2 * nu u v))
        (Set.Icc b₀ b₁))
    (hccont : ∀ u ∈ Set.Icc a₀ a₁,
      ContinuousOn (fun v => -theta u v ^ 2 / (r u v * lam u v))
        (Set.Icc b₀ b₁))
    (hbottom : ∀ u ∈ Set.Icc a₀ a₁,
      d u b₀ = (1 - 2 * m u b₀ / r u b₀) * zeta u b₀ ^ 2 /
        (2 * nu u b₀)) :
    ∀ u ∈ Set.Icc a₀ a₁, ∀ v ∈ Set.Icc b₀ b₁,
      d u v = (1 - 2 * m u v / r u v) * zeta u v ^ 2 /
        (2 * nu u v) := by
  let P : ℝ → ℝ → ℝ := fun u v =>
    (1 - 2 * m u v / r u v) * theta u v ^ 2 / (2 * lam u v)
  let H : ℝ → ℝ → ℝ := fun u v =>
    (-2 * d u v / r u v + 2 * m u v * nu u v / r u v ^ 2) *
        theta u v ^ 2 / (2 * lam u v) +
      (1 - 2 * m u v / r u v) *
        (2 * theta u v * (-lam u v * zeta u v / r u v)) /
        (2 * lam u v) -
      (1 - 2 * m u v / r u v) * theta u v ^ 2 *
        (2 * m u v * lam u v * nu u v /
          (r u v * (r u v - 2 * m u v))) / (2 * lam u v ^ 2)
  have hPu (u : ℝ) (hu : u ∈ Set.Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Set.Icc b₀ b₁) :
      HasDerivWithinAt (fun s => P s v) (H u v) (Set.Icc a₀ a₁) u :=
    outgoing_mass_density_hasDerivWithinAt_horizontal
      (m := fun s => m s v) (r := fun s => r s v)
      (lam := fun s => lam s v) (nu := fun s => nu s v)
      (theta := fun s => theta s v) (zeta := fun s => zeta s v)
      (d := fun s => d s v)
      (hsafe u hu v hv).1 (hsafe u hu v hv).2.1
      (hmu u hu v hv) (hru u hu v hv)
      (hlamu u hu v hv) (hthetau u hu v hv)
  have hdv :=
    (hasDerivWithinAt_horizontal_partial_of_vertical_partial haa hbb
      hmcont hdcont hPcont hHcont hmu hmv hPu).2.2
  intro u hu v hv
  have hODE : ∀ t ∈ Set.Icc b₀ b₁,
      HasDerivWithinAt
        (fun w => d u w -
          (1 - 2 * m u w / r u w) * zeta u w ^ 2 / (2 * nu u w))
        ((-theta u t ^ 2 / (r u t * lam u t)) *
          (d u t - (1 - 2 * m u t / r u t) * zeta u t ^ 2 /
            (2 * nu u t))) (Set.Icc b₀ b₁) t := by
    intro t ht
    obtain ⟨hr, hl, hn, hg⟩ := hsafe u hu t ht
    exact mass_defect_hasDerivWithinAt hr hl hn hg
      (hmv u hu t ht) (hrv u hu t ht) (hnuv u hu t ht)
      (hzetav u hu t ht) (hdv u hu t ht)
  have hzero := eq_zero_of_linear_vertical_equation hbb.le
    (hecont u hu) (hccont u hu) hODE (sub_eq_zero.mpr (hbottom u hu))
  exact sub_eq_zero.mp (hzero v hv)

end ChristodoulouBV.C1Solution

end
