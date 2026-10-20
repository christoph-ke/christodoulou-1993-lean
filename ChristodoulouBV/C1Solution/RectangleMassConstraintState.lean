module

public import ChristodoulouBV.C1Solution.RectangleMassConstraint
public import ChristodoulouBV.C1Solution.RectangleJetSeams
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Incoming mass constraint for the seven-state rectangle solution

The scalar propagation theorem is applied to the actual coordinate jets of a
relative `C¹` rectangle solution. The radius and scalar-radius constraints
provide the two incoming derivatives needed for the cancellation.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The mass coordinate of a relative `C¹` outgoing state is relative `C¹`
on the same rectangle. -/
theorem contDiffOn_stateMass_of_outgoing
    {a₀ a₁ b₀ b₁ : ℝ}
    {Y : ℝ × ℝ → OutgoingState}
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁)) :
    ContDiffOn ℝ 1
      (fun p => stateMass ((0, 0), Y p))
      (Goursat.rectangle a₀ a₁ b₀ b₁) := by
  let massProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ)))))
  change ContDiffOn ℝ 1 (fun p => massProj (Y p)) _
  exact massProj.contDiff.comp_contDiffOn hY

/-- The scalar quotient derivative in a null coordinate, expressed through
its transport numerator. -/
theorem scalar_quotient_hasDerivWithinAt
    {s : Set ℝ} {t : ℝ} {r psi : ℝ → ℝ}
    {dr dpsi : ℝ} (hr : r t ≠ 0)
    (hrderiv : HasDerivWithinAt r dr s t)
    (hpsideriv : HasDerivWithinAt psi dpsi s t) :
    HasDerivWithinAt (fun w => psi w / r w)
      ((dpsi - dr * (psi t / r t)) / r t) s t := by
  have h := hpsideriv.div hrderiv hr
  convert h using 1
  field_simp

/-- The incoming scalar numerator has the derivative forced by the
characteristic equations and the quotient rule. -/
theorem theta_hasDerivWithinAt_of_transport
    {s : Set ℝ} {t : ℝ}
    {lam alpha r psi : ℝ → ℝ} {nu beta K : ℝ}
    (hr : r t ≠ 0)
    (hlam : HasDerivWithinAt lam K s t)
    (halpha : HasDerivWithinAt alpha (K * (psi t / r t)) s t)
    (hrderiv : HasDerivWithinAt r nu s t)
    (hpsideriv : HasDerivWithinAt psi beta s t) :
    HasDerivWithinAt
      (fun w => alpha w - lam w * (psi w / r w))
      (-lam t * (beta - nu * (psi t / r t)) / r t) s t := by
  have hphi := scalar_quotient_hasDerivWithinAt hr hrderiv hpsideriv
  have h := halpha.sub (hlam.mul hphi)
  convert h using 1
  ring

/-- The outgoing scalar numerator has the symmetric derivative forced by
the characteristic equations and the quotient rule. -/
theorem zeta_hasDerivWithinAt_of_transport
    {s : Set ℝ} {t : ℝ}
    {nu beta r psi : ℝ → ℝ} {lam alpha K : ℝ}
    (hr : r t ≠ 0)
    (hnu : HasDerivWithinAt nu K s t)
    (hbeta : HasDerivWithinAt beta (K * (psi t / r t)) s t)
    (hrderiv : HasDerivWithinAt r lam s t)
    (hpsideriv : HasDerivWithinAt psi alpha s t) :
    HasDerivWithinAt
      (fun w => beta w - nu w * (psi w / r w))
      (-nu t * (alpha - lam * (psi t / r t)) / r t) s t := by
  have hphi := scalar_quotient_hasDerivWithinAt hr hrderiv hpsideriv
  have h := hbeta.sub (hnu.mul hphi)
  convert h using 1
  ring

/-- The scalar transport derivatives needed by mass propagation follow from
the seven-state Goursat jets and the two reconstructed incoming equations. -/
theorem rectangle_mass_transport_derivatives
    {a₀ a₁ b₀ b₁ : ℝ}
    (B : SafeRectangleBox)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (hball : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      (X p, Y p) ∈ B.carrier)
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    (hru : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt
        (fun s => stateRadius (X (s, v), Y (s, v)))
        (stateNu (X (u, v), Y (u, v))) (Icc a₀ a₁) u)
    (hpsiu : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt
        (fun s => statePsi (X (s, v), Y (s, v)))
        (stateBeta (X (u, v), Y (u, v))) (Icc a₀ a₁) u)
    {u v : ℝ} (hu : u ∈ Icc a₀ a₁) (hv : v ∈ Icc b₀ b₁) :
    HasDerivWithinAt
      (fun s => stateLam (X (s, v), Y (s, v)))
      (stateGrav (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
    HasDerivWithinAt
      (fun s => stateTheta (X (s, v), Y (s, v)))
      (-stateLam (X (u, v), Y (u, v)) *
        stateZeta (X (u, v), Y (u, v)) /
        stateRadius (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
    HasDerivWithinAt
      (fun t => stateMass (X (u, t), Y (u, t)))
      (stateMassGap (X (u, v), Y (u, v)) /
        stateRadius (X (u, v), Y (u, v)) *
        stateTheta (X (u, v), Y (u, v)) ^ 2 /
        (2 * stateLam (X (u, v), Y (u, v)))) (Icc b₀ b₁) v ∧
    HasDerivWithinAt
      (fun t => stateRadius (X (u, t), Y (u, t)))
      (stateLam (X (u, v), Y (u, v))) (Icc b₀ b₁) v ∧
    HasDerivWithinAt
      (fun t => stateNu (X (u, t), Y (u, t)))
      (stateGrav (X (u, v), Y (u, v))) (Icc b₀ b₁) v ∧
    HasDerivWithinAt
      (fun t => stateZeta (X (u, t), Y (u, t)))
      (-stateNu (X (u, v), Y (u, v)) *
        stateTheta (X (u, v), Y (u, v)) /
        stateRadius (X (u, v), Y (u, v))) (Icc b₀ b₁) v := by
  let z := (X (u, v), Y (u, v))
  have hr : stateRadius z ≠ 0 := ne_of_gt (B.safe
    (hball (u, v) (Goursat.pair_mem_rectangle hu hv))).1
  have hXu := (hjet u hu v hv).1
  have hYv := (hjet u hu v hv).2
  have hlamu : HasDerivWithinAt
      (fun s => stateLam (X (s, v), Y (s, v)))
      (stateGrav z) (Icc a₀ a₁) u := by
    convert hXu.fst using 1; rfl
  have halphau : HasDerivWithinAt
      (fun s => stateAlpha (X (s, v), Y (s, v)))
      (stateGrav z * statePhi z) (Icc a₀ a₁) u := by
    convert hXu.snd using 1; rfl
  have hnuv : HasDerivWithinAt
      (fun t => stateNu (X (u, t), Y (u, t)))
      (stateGrav z) (Icc b₀ b₁) v := by
    convert hYv.fst using 1; rfl
  have hbetav : HasDerivWithinAt
      (fun t => stateBeta (X (u, t), Y (u, t)))
      (stateGrav z * statePhi z) (Icc b₀ b₁) v := by
    convert hYv.snd.fst using 1; rfl
  have hmv : HasDerivWithinAt
      (fun t => stateMass (X (u, t), Y (u, t)))
      (stateMassGap z / stateRadius z * stateTheta z ^ 2 /
        (2 * stateLam z)) (Icc b₀ b₁) v := by
    convert hYv.snd.snd.fst using 1; rfl
  have hrv : HasDerivWithinAt
      (fun t => stateRadius (X (u, t), Y (u, t)))
      (stateLam z) (Icc b₀ b₁) v := by
    convert hYv.snd.snd.snd.fst using 1; rfl
  have hpsiv : HasDerivWithinAt
      (fun t => statePsi (X (u, t), Y (u, t)))
      (stateAlpha z) (Icc b₀ b₁) v := by
    convert hYv.snd.snd.snd.snd using 1; rfl
  have hthetau := theta_hasDerivWithinAt_of_transport
    (lam := fun s => stateLam (X (s, v), Y (s, v)))
    (alpha := fun s => stateAlpha (X (s, v), Y (s, v)))
    (r := fun s => stateRadius (X (s, v), Y (s, v)))
    (psi := fun s => statePsi (X (s, v), Y (s, v)))
    hr hlamu halphau (hru u hu v hv) (hpsiu u hu v hv)
  have hzetav := zeta_hasDerivWithinAt_of_transport
    (nu := fun t => stateNu (X (u, t), Y (u, t)))
    (beta := fun t => stateBeta (X (u, t), Y (u, t)))
    (r := fun t => stateRadius (X (u, t), Y (u, t)))
    (psi := fun t => statePsi (X (u, t), Y (u, t)))
    hr hnuv hbetav hrv hpsiv
  exact ⟨hlamu, hthetau, hmv, hrv, hnuv, hzetav⟩

/-- The incoming mass equation propagates on a safe relative `C¹` rectangle
once the radius and scalar-radius incoming equations and the lower mass data
hold. The mixed mass derivative is supplied by the closed-rectangle
interchange theorem. -/
theorem rectangle_mass_incoming_constraint
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (B : SafeRectangleBox)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (hX : ContDiffOn ℝ 1 X (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hball : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      (X p, Y p) ∈ B.carrier)
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    (hru : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt
        (fun s => stateRadius (X (s, v), Y (s, v)))
        (stateNu (X (u, v), Y (u, v))) (Icc a₀ a₁) u)
    (hpsiu : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt
        (fun s => statePsi (X (s, v), Y (s, v)))
        (stateBeta (X (u, v), Y (u, v))) (Icc a₀ a₁) u)
    (hbottom : ∀ u ∈ Icc a₀ a₁,
      (fderivWithin ℝ
        (fun p => stateMass (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) =
      (1 - 2 * stateMass (X (u, b₀), Y (u, b₀)) /
        stateRadius (X (u, b₀), Y (u, b₀))) *
        stateZeta (X (u, b₀), Y (u, b₀)) ^ 2 /
        (2 * stateNu (X (u, b₀), Y (u, b₀)))) :
    ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => stateMass (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
      (1 - 2 * stateMass (X (u, v), Y (u, v)) /
        stateRadius (X (u, v), Y (u, v))) *
        stateZeta (X (u, v), Y (u, v)) ^ 2 /
        (2 * stateNu (X (u, v), Y (u, v))) := by
  let R := Goursat.rectangle a₀ a₁ b₀ b₁
  let Z : ℝ × ℝ → RectangleState := fun p => (X p, Y p)
  let m : ℝ → ℝ → ℝ := fun u v => stateMass (Z (u, v))
  let r : ℝ → ℝ → ℝ := fun u v => stateRadius (Z (u, v))
  let lam : ℝ → ℝ → ℝ := fun u v => stateLam (Z (u, v))
  let nu : ℝ → ℝ → ℝ := fun u v => stateNu (Z (u, v))
  let alpha : ℝ → ℝ → ℝ := fun u v => stateAlpha (Z (u, v))
  let beta : ℝ → ℝ → ℝ := fun u v => stateBeta (Z (u, v))
  let psi : ℝ → ℝ → ℝ := fun u v => statePsi (Z (u, v))
  let theta : ℝ → ℝ → ℝ := fun u v => stateTheta (Z (u, v))
  let zeta : ℝ → ℝ → ℝ := fun u v => stateZeta (Z (u, v))
  let d : ℝ → ℝ → ℝ := fun u v =>
    (fderivWithin ℝ (fun p => stateMass (Z p)) R (u, v)) (1, 0)
  have hmC1 : ContDiffOn ℝ 1 (fun p => stateMass (Z p)) R := by
    convert contDiffOn_stateMass_of_outgoing hY using 1
    funext p
    rfl
  have hmderiv := horizontal_partial_of_contDiffOn_rectangle haa hbb
    (by simpa only [R, Goursat.rectangle] using hmC1)
  have hXcont : ContinuousOn X R := hX.continuousOn
  have hYcont : ContinuousOn Y R := hY.continuousOn
  have hmcont : ContinuousOn (fun p => m p.1 p.2) R := by
    exact hmC1.continuousOn
  have hrcont : ContinuousOn (fun p => r p.1 p.2) R := by
    change ContinuousOn (fun p => (Y p).2.2.2.1) R
    exact hYcont.snd.snd.snd.fst
  have hlamcont : ContinuousOn (fun p => lam p.1 p.2) R := by
    change ContinuousOn (fun p => (X p).1) R
    exact hXcont.fst
  have hnucont : ContinuousOn (fun p => nu p.1 p.2) R := by
    change ContinuousOn (fun p => (Y p).1) R
    exact hYcont.fst
  have halphacont : ContinuousOn (fun p => alpha p.1 p.2) R := by
    change ContinuousOn (fun p => (X p).2) R
    exact hXcont.snd
  have hbetacont : ContinuousOn (fun p => beta p.1 p.2) R := by
    change ContinuousOn (fun p => (Y p).2.1) R
    exact hYcont.snd.fst
  have hpsicont : ContinuousOn (fun p => psi p.1 p.2) R := by
    change ContinuousOn (fun p => (Y p).2.2.2.2) R
    exact hYcont.snd.snd.snd.snd
  have hdcont : ContinuousOn (fun p => d p.1 p.2) R := by
    exact hmderiv.1
  have hsafe (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      r u v ≠ 0 ∧ lam u v ≠ 0 ∧ nu u v ≠ 0 ∧
        r u v - 2 * m u v ≠ 0 := by
    obtain ⟨hr, hl, hn, hg⟩ := B.safe
      (hball (u, v) (Goursat.pair_mem_rectangle hu hv))
    exact ⟨ne_of_gt hr, ne_of_gt hl, ne_of_lt hn, ne_of_gt hg⟩
  have hrne : ∀ p ∈ R, r p.1 p.2 ≠ 0 := by
    intro p hp
    exact (hsafe p.1 hp.1 p.2 hp.2).1
  have hlamne : ∀ p ∈ R, 2 * lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact mul_ne_zero two_ne_zero (hsafe p.1 hp.1 p.2 hp.2).2.1
  have hnune : ∀ p ∈ R, 2 * nu p.1 p.2 ≠ 0 := by
    intro p hp
    exact mul_ne_zero two_ne_zero (hsafe p.1 hp.1 p.2 hp.2).2.2.1
  have hgapne : ∀ p ∈ R, r p.1 p.2 *
      (r p.1 p.2 - 2 * m p.1 p.2) ≠ 0 := by
    intro p hp
    exact mul_ne_zero (hrne p hp) (hsafe p.1 hp.1 p.2 hp.2).2.2.2
  have hphicont : ContinuousOn
      (fun p => psi p.1 p.2 / r p.1 p.2) R :=
    hpsicont.div hrcont hrne
  have hthetacont : ContinuousOn (fun p => theta p.1 p.2) R := by
    exact halphacont.sub (hlamcont.mul hphicont)
  have hzetacont : ContinuousOn (fun p => zeta p.1 p.2) R := by
    exact hbetacont.sub (hnucont.mul hphicont)
  have hAcont : ContinuousOn
      (fun p => 1 - 2 * m p.1 p.2 / r p.1 p.2) R :=
    continuousOn_const.sub ((continuousOn_const.mul hmcont).div hrcont hrne)
  have hKcont : ContinuousOn
      (fun p => 2 * m p.1 p.2 * lam p.1 p.2 * nu p.1 p.2 /
        (r p.1 p.2 * (r p.1 p.2 - 2 * m p.1 p.2))) R :=
    (((continuousOn_const.mul hmcont).mul hlamcont).mul hnucont).div
      (hrcont.mul (hrcont.sub (continuousOn_const.mul hmcont))) hgapne
  have hPcont : ContinuousOn
      (fun p => (1 - 2 * m p.1 p.2 / r p.1 p.2) *
        theta p.1 p.2 ^ 2 / (2 * lam p.1 p.2)) R :=
    (hAcont.mul (hthetacont.pow 2)).div
      (continuousOn_const.mul hlamcont) hlamne
  have hHcont : ContinuousOn
      (fun p =>
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
              (2 * lam p.1 p.2 ^ 2)) R := by
    have hD : ContinuousOn
        (fun p => -2 * d p.1 p.2 / r p.1 p.2 +
          2 * m p.1 p.2 * nu p.1 p.2 / r p.1 p.2 ^ 2) R :=
      ((continuousOn_const.mul hdcont).div hrcont hrne).add
        (((continuousOn_const.mul hmcont).mul hnucont).div
          (hrcont.pow 2) (fun p hp => pow_ne_zero 2 (hrne p hp)))
    have hT : ContinuousOn
        (fun p => 2 * theta p.1 p.2 *
          (-lam p.1 p.2 * zeta p.1 p.2 / r p.1 p.2)) R :=
      (continuousOn_const.mul hthetacont).mul
        ((hlamcont.neg.mul hzetacont).div hrcont hrne)
    exact ((hD.mul (hthetacont.pow 2)).div
        (continuousOn_const.mul hlamcont) hlamne).add
      ((hAcont.mul hT).div (continuousOn_const.mul hlamcont) hlamne) |>.sub
      (((hAcont.mul (hthetacont.pow 2)).mul hKcont).div
        (continuousOn_const.mul (hlamcont.pow 2))
        (fun p hp => mul_ne_zero two_ne_zero
          (pow_ne_zero 2 (hsafe p.1 hp.1 p.2 hp.2).2.1)))
  have hecont (u : ℝ) (hu : u ∈ Icc a₀ a₁) :
      ContinuousOn (fun v => d u v -
        (1 - 2 * m u v / r u v) * zeta u v ^ 2 / (2 * nu u v))
        (Icc b₀ b₁) := by
    have hE : ContinuousOn (fun p => d p.1 p.2 -
        (1 - 2 * m p.1 p.2 / r p.1 p.2) *
          zeta p.1 p.2 ^ 2 / (2 * nu p.1 p.2)) R :=
      hdcont.sub ((hAcont.mul (hzetacont.pow 2)).div
        (continuousOn_const.mul hnucont) hnune)
    exact hE.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => Goursat.pair_mem_rectangle hu hv)
  have hccont (u : ℝ) (hu : u ∈ Icc a₀ a₁) :
      ContinuousOn (fun v => -theta u v ^ 2 / (r u v * lam u v))
        (Icc b₀ b₁) := by
    have hpath : ContinuousOn (fun v : ℝ => (u, v)) (Icc b₀ b₁) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc b₀ b₁) R := by
      intro v hv
      exact Goursat.pair_mem_rectangle hu hv
    have hθ : ContinuousOn (theta u) (Icc b₀ b₁) :=
      hthetacont.comp hpath hmap
    have hr : ContinuousOn (r u) (Icc b₀ b₁) :=
      hrcont.comp hpath hmap
    have hlamslice : ContinuousOn (lam u) (Icc b₀ b₁) :=
      hlamcont.comp hpath hmap
    exact ((hθ.pow 2).neg).div (hr.mul hlamslice)
      (fun v hv => mul_ne_zero (hsafe u hu v hv).1
        (hsafe u hu v hv).2.1)
  have htrans (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :=
    rectangle_mass_transport_derivatives B X Y hball hjet hru hpsiu hu hv
  apply incoming_mass_constraint_of_rectangle_equations haa hbb
    (m := m) (r := r) (lam := lam) (nu := nu)
    (theta := theta) (zeta := zeta) (d := d)
    (by simpa only [R, Goursat.rectangle] using hmcont)
    (by simpa only [R, Goursat.rectangle] using hdcont)
    (by simpa only [R, Goursat.rectangle] using hPcont)
    (by simpa only [R, Goursat.rectangle] using hHcont)
    hsafe
  · intro u hu v hv
    exact hmderiv.2 u hu v hv
  · exact hru
  · intro u hu v hv
    convert (htrans u hu v hv).1 using 1
    rfl
  · intro u hu v hv
    exact (htrans u hu v hv).2.1
  · intro u hu v hv
    convert (htrans u hu v hv).2.2.1 using 1
    change (1 - 2 * m u v / r u v) * theta u v ^ 2 /
      (2 * lam u v) =
      ((r u v - 2 * m u v) / r u v) * theta u v ^ 2 /
        (2 * lam u v)
    field_simp [(hsafe u hu v hv).1]
  · intro u hu v hv
    exact (htrans u hu v hv).2.2.2.1
  · intro u hu v hv
    convert (htrans u hu v hv).2.2.2.2.1 using 1
    rfl
  · intro u hu v hv
    exact (htrans u hu v hv).2.2.2.2.2
  · exact hecont
  · exact hccont
  · exact hbottom

/-- The three incoming constraints follow from the corrected tangential
lower-edge data: radius and scalar-radius derivatives are supplied by the
prescribed outgoing trace, while the mass derivative is propagated by its
homogeneous defect equation. -/
theorem rectangle_incoming_constraints_of_lower_edge
    {a₀ a₁ b₀ b₁ : ℝ} (haa : a₀ < a₁) (hbb : b₀ < b₁)
    (B : SafeRectangleBox)
    (X : ℝ × ℝ → IncomingState) (Y : ℝ × ℝ → OutgoingState)
    (y₀ y₀' : ℝ → OutgoingState)
    (hX : ContDiffOn ℝ 1 X (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hY : ContDiffOn ℝ 1 Y (Goursat.rectangle a₀ a₁ b₀ b₁))
    (hball : ∀ p ∈ Goursat.rectangle a₀ a₁ b₀ b₁,
      (X p, Y p) ∈ B.carrier)
    (hjet : ∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      HasDerivWithinAt (fun s => X (s, v))
        (rectangleF (X (u, v), Y (u, v))) (Icc a₀ a₁) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (rectangleG (X (u, v), Y (u, v))) (Icc b₀ b₁) v)
    (hYedge : ∀ u ∈ Icc a₀ a₁, Y (u, b₀) = y₀ u)
    (hdy₀ : ∀ u ∈ Icc a₀ a₁,
      HasDerivWithinAt y₀ (y₀' u) (Icc a₀ a₁) u)
    (hrdata : ∀ u ∈ Icc a₀ a₁, (y₀' u).2.2.2.1 = (y₀ u).1)
    (hpsidata : ∀ u ∈ Icc a₀ a₁, (y₀' u).2.2.2.2 = (y₀ u).2.1)
    (hmdata : ∀ u ∈ Icc a₀ a₁,
      (fderivWithin ℝ (fun p => stateMass (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, b₀)) (1, 0) =
      (1 - 2 * stateMass (X (u, b₀), Y (u, b₀)) /
        stateRadius (X (u, b₀), Y (u, b₀))) *
        stateZeta (X (u, b₀), Y (u, b₀)) ^ 2 /
        (2 * stateNu (X (u, b₀), Y (u, b₀)))) :
    (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => stateRadius (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
        stateNu (X (u, v), Y (u, v))) ∧
    (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => statePsi (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
        stateBeta (X (u, v), Y (u, v))) ∧
    (∀ u ∈ Icc a₀ a₁, ∀ v ∈ Icc b₀ b₁,
      (fderivWithin ℝ (fun p => stateMass (X p, Y p))
        (Goursat.rectangle a₀ a₁ b₀ b₁) (u, v)) (1, 0) =
      (1 - 2 * stateMass (X (u, v), Y (u, v)) /
        stateRadius (X (u, v), Y (u, v))) *
        stateZeta (X (u, v), Y (u, v)) ^ 2 /
        (2 * stateNu (X (u, v), Y (u, v)))) := by
  obtain ⟨hrin, hpsiin⟩ :=
    rectangle_radius_scalar_radius_constraints_of_lower_edge haa hbb B
      X Y y₀ y₀' hX hY hball hjet hYedge hdy₀ hrdata hpsidata
  let rProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  let psiProj : OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  have hrC1 : ContDiffOn ℝ 1
      (fun p => stateRadius (X p, Y p))
      (Goursat.rectangle a₀ a₁ b₀ b₁) := by
    change ContDiffOn ℝ 1 (fun p => rProj (Y p)) _
    exact rProj.contDiff.comp_contDiffOn hY
  have hpsiC1 : ContDiffOn ℝ 1
      (fun p => statePsi (X p, Y p))
      (Goursat.rectangle a₀ a₁ b₀ b₁) := by
    change ContDiffOn ℝ 1 (fun p => psiProj (Y p)) _
    exact psiProj.contDiff.comp_contDiffOn hY
  have hrjet := (horizontal_partial_of_contDiffOn_rectangle haa hbb
    (by simpa only [Goursat.rectangle] using hrC1)).2
  have hpsijet := (horizontal_partial_of_contDiffOn_rectangle haa hbb
    (by simpa only [Goursat.rectangle] using hpsiC1)).2
  have hru (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt
        (fun s => stateRadius (X (s, v), Y (s, v)))
        (stateNu (X (u, v), Y (u, v))) (Icc a₀ a₁) u := by
    have hreq := hrin u hu v hv
    simp only [Goursat.rectangle] at hreq
    have h := hrjet u hu v hv
    rw [hreq] at h
    exact h
  have hpsiu (u : ℝ) (hu : u ∈ Icc a₀ a₁)
      (v : ℝ) (hv : v ∈ Icc b₀ b₁) :
      HasDerivWithinAt
        (fun s => statePsi (X (s, v), Y (s, v)))
        (stateBeta (X (u, v), Y (u, v))) (Icc a₀ a₁) u := by
    have hpsieq := hpsiin u hu v hv
    simp only [Goursat.rectangle] at hpsieq
    have h := hpsijet u hu v hv
    rw [hpsieq] at h
    exact h
  exact ⟨hrin, hpsiin,
    rectangle_mass_incoming_constraint haa hbb B X Y hX hY hball hjet
      hru hpsiu hmdata⟩

end ChristodoulouBV.C1Solution

end
