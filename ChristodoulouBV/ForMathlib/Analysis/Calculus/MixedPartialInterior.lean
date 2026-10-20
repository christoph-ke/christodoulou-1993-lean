module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial

/-!
# Interior mixed partial from continuous first jets

This is a local rectangular form of the mixed-partial fundamental theorem.
It requires a continuous outgoing derivative of the incoming equation, but
no a priori second derivative of the original state.
-/

public section

open Set

/-- If `Fᵤ = K` and `Kᵥ` is continuous, then the continuous first jet `Fᵥ`
has incoming derivative `Kᵥ` at every interior point of the rectangle. -/
theorem hasDerivAt_vertical_partial_of_horizontal_equation
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁)
    {F Fv K Kv : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hFv : ContinuousOn (fun p : ℝ × ℝ => Fv p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hK : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hKv : ContinuousOn (fun p : ℝ × ℝ => Kv p.1 p.2)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hFv_deriv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivAt (F u) (Fv u v) v)
    (hK_deriv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivAt (fun t => F t v) (K u v) u)
    (hKv_deriv : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc v₀ v₁,
      HasDerivAt (fun t => K u t) (Kv u v) v)
    {u v : ℝ} (huv : u ∈ Ioo u₀ u₁) (hvv : v ∈ Ioo v₀ v₁) :
    HasDerivAt (fun t => Fv t v) (Kv u v) u := by
  have hswap : Continuous (fun p : ℝ × ℝ => (p.2, p.1)) :=
    continuous_snd.prodMk continuous_fst
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.2, p.1))
      (Icc v₀ v₁ ×ˢ Icc u₀ u₁)
      (Icc u₀ u₁ ×ˢ Icc v₀ v₁) :=
    fun _ hp => ⟨hp.2, hp.1⟩
  have hmain := hasDerivWithinAt_horizontal_partial_of_vertical_partial
    hv hu
    (f := fun v u => F u v)
    (fu := fun v u => Fv u v)
    (G := fun v u => K u v)
    (Gu := fun v u => Kv u v)
    (hF.comp hswap.continuousOn hmap)
    (hFv.comp hswap.continuousOn hmap)
    (hK.comp hswap.continuousOn hmap)
    (hKv.comp hswap.continuousOn hmap)
    (by
      intro v hv' u hu'
      exact (hFv_deriv u hu' v hv').hasDerivWithinAt)
    (by
      intro v hv' u hu'
      exact (hK_deriv u hu' v hv').hasDerivWithinAt)
    (by
      intro v hv' u hu'
      exact (hKv_deriv u hu' v hv').hasDerivWithinAt)
  exact (hmain.2.2 v ⟨hvv.1.le, hvv.2.le⟩ u
    ⟨huv.1.le, huv.2.le⟩).hasDerivAt
      (Icc_mem_nhds huv.1 huv.2)

end
