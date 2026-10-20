module

public import ChristodoulouBV.Existence.RepresentativesBounds

/-!
# A universal TV coefficient for the final quantitative witness

Pointwise lower semicontinuity passes the smooth three-term bounds to
the limit along the shared existence subsequence. The representative change
keeps outgoing TV unchanged and does not increase incoming TV when choosing right-u
representatives. Here their common bound is written with one real
coefficient inside `ENNReal.ofReal`, as required by the three-term variation estimates.
-/

public section

open scoped ENNReal

namespace ChristodoulouBV

/-- The universal three-term TV coefficient for the final BV witness.
The factor three is the componentwise lower-semicontinuity loss. -/
@[expose] noncomputable def e1WitnessTVK : ℝ := 3 * s6EndpointTVK

/-- The quantitative witness coefficient is strictly positive, independently of
the initial datum, its scalar offset, and the characteristic ray. -/
theorem e1WitnessTVK_pos : 0 < e1WitnessTVK :=
  mul_pos (by norm_num) s6EndpointTVK_pos

/-- Both complete three-term TV bounds hold for the final incoming
representatives with the same universal real coefficient. The outgoing
bound includes `u = 0`; the incoming ray is exactly `Ioo 0 v`. -/
theorem e1_witness_three_term_tv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u, 0 ≤ u → e1OutgoingTV d.incomingRightFields u ≤
      ENNReal.ofReal (e1WitnessTVK * D.toReal)) ∧
    ∀ v, 0 < v → e1IncomingTV d.incomingRightFields v ≤
      ENNReal.ofReal (e1WitnessTVK * D.toReal) := by
  have hK : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) =
      ENNReal.ofReal (e1WitnessTVK * D.toReal) := by
    have he := ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)
      (q := s6EndpointTVK * D.toReal)
    simpa only [e1WitnessTVK, mul_assoc, ENNReal.ofReal_ofNat] using he.symm
  obtain ⟨hout, hin⟩ := incoming_right_fields_three_term_tv h hD d
  exact ⟨fun u hu => (hout u hu).trans_eq hK, fun v hv => (hin v hv).trans_eq hK⟩

end ChristodoulouBV

end
