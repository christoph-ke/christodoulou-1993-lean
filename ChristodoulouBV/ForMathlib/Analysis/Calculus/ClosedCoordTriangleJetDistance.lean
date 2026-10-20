module

public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Uniform sum distances of first jets on coordinate triangles

The distance of a scalar first jet is the sum of the uniform norms of its
value and two coordinate derivatives. A finite maximum gives the corresponding
distance for several fields.
-/

public section

open Set

variable {α : Type*} [TopologicalSpace α]

/-- The uniform absolute-value bound of a real function on a set. -/
@[expose] noncomputable def uniformAbsOn (K : Set α) (f : α → ℝ) : ℝ :=
  sSup ((fun x => |f x|) '' K)

/-- Evaluation is bounded by the uniform absolute-value bound on a compact set. -/
theorem abs_le_uniformAbsOn {K : Set α} {f : α → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) {x : α} (hx : x ∈ K) :
    |f x| ≤ uniformAbsOn K f := by
  exact le_csSup (hK.bddAbove_image hf.abs) (mem_image_of_mem _ hx)

/-- The uniform absolute-value bound is nonnegative on a nonempty compact set. -/
theorem uniformAbsOn_nonneg {K : Set α} {f : α → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : ContinuousOn f K) :
    0 ≤ uniformAbsOn K f := by
  obtain ⟨x, hx⟩ := hne
  exact (abs_nonneg (f x)).trans (abs_le_uniformAbsOn hK hf hx)

/-- The sum of the three uniform coordinate seminorms of the difference of
two scalar first jets on a set. -/
@[expose] noncomputable def coordinateJetDistanceOn (K : Set (ℝ × ℝ))
    (f₁ f₂ : ℝ × ℝ → ℝ)
    (G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) : ℝ :=
  uniformAbsOn K (f₁ - f₂) +
    uniformAbsOn K (fun p => G₁ p (1, 0) - G₂ p (1, 0)) +
    uniformAbsOn K (fun p => G₁ p (0, 1) - G₂ p (0, 1))

private theorem continuousOn_clm_apply_sub {K : Set (ℝ × ℝ)}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG₁ : ContinuousOn G₁ K) (hG₂ : ContinuousOn G₂ K)
    (q : ℝ × ℝ) :
    ContinuousOn (fun p => G₁ p q - G₂ p q) K :=
  (hG₁.clm_apply continuousOn_const).sub
    (hG₂.clm_apply continuousOn_const)

/-- A first-jet sum distance is nonnegative for continuous jets on a nonempty
compact set. -/
theorem coordinateJetDistanceOn_nonneg
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    {f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf₁ : ContinuousOn f₁ K) (hf₂ : ContinuousOn f₂ K)
    (hG₁ : ContinuousOn G₁ K) (hG₂ : ContinuousOn G₂ K) :
    0 ≤ coordinateJetDistanceOn K f₁ f₂ G₁ G₂ := by
  have h₀ := uniformAbsOn_nonneg hK hne (hf₁.sub hf₂)
  have h₁ := uniformAbsOn_nonneg hK hne
    (continuousOn_clm_apply_sub hG₁ hG₂ (1, 0))
  have h₂ := uniformAbsOn_nonneg hK hne
    (continuousOn_clm_apply_sub hG₁ hG₂ (0, 1))
  dsimp only [coordinateJetDistanceOn]
  linarith

/-- Every value difference is bounded by the sum distance of its first jets. -/
theorem abs_value_sub_le_coordinateJetDistanceOn
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    {f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf₁ : ContinuousOn f₁ K) (hf₂ : ContinuousOn f₂ K)
    (hG₁ : ContinuousOn G₁ K) (hG₂ : ContinuousOn G₂ K)
    {p : ℝ × ℝ} (hp : p ∈ K) :
    |f₁ p - f₂ p| ≤ coordinateJetDistanceOn K f₁ f₂ G₁ G₂ := by
  have h₀ := abs_le_uniformAbsOn hK (hf₁.sub hf₂) hp
  have h₁ : 0 ≤ uniformAbsOn K (fun z => G₁ z (1, 0) - G₂ z (1, 0)) :=
    uniformAbsOn_nonneg hK hne (continuousOn_clm_apply_sub hG₁ hG₂ (1, 0))
  have h₂ : 0 ≤ uniformAbsOn K (fun z => G₁ z (0, 1) - G₂ z (0, 1)) :=
    uniformAbsOn_nonneg hK hne (continuousOn_clm_apply_sub hG₁ hG₂ (0, 1))
  change |f₁ p - f₂ p| ≤ uniformAbsOn K (f₁ - f₂) at h₀
  dsimp only [coordinateJetDistanceOn]
  linarith

/-- Every horizontal derivative difference is bounded by the sum distance. -/
theorem abs_horizontal_sub_le_coordinateJetDistanceOn
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    {f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf₁ : ContinuousOn f₁ K) (hf₂ : ContinuousOn f₂ K)
    (hG₁ : ContinuousOn G₁ K) (hG₂ : ContinuousOn G₂ K)
    {p : ℝ × ℝ} (hp : p ∈ K) :
    |G₁ p (1, 0) - G₂ p (1, 0)| ≤
      coordinateJetDistanceOn K f₁ f₂ G₁ G₂ := by
  have h₀ : 0 ≤ uniformAbsOn K (f₁ - f₂) :=
    uniformAbsOn_nonneg hK hne (hf₁.sub hf₂)
  have h₁ : |G₁ p (1, 0) - G₂ p (1, 0)| ≤
      uniformAbsOn K (fun z => G₁ z (1, 0) - G₂ z (1, 0)) :=
    abs_le_uniformAbsOn hK (continuousOn_clm_apply_sub hG₁ hG₂ (1, 0)) hp
  have h₂ : 0 ≤ uniformAbsOn K (fun z => G₁ z (0, 1) - G₂ z (0, 1)) :=
    uniformAbsOn_nonneg hK hne (continuousOn_clm_apply_sub hG₁ hG₂ (0, 1))
  dsimp only [coordinateJetDistanceOn]
  linarith

/-- Every vertical derivative difference is bounded by the sum distance. -/
theorem abs_vertical_sub_le_coordinateJetDistanceOn
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    {f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hf₁ : ContinuousOn f₁ K) (hf₂ : ContinuousOn f₂ K)
    (hG₁ : ContinuousOn G₁ K) (hG₂ : ContinuousOn G₂ K)
    {p : ℝ × ℝ} (hp : p ∈ K) :
    |G₁ p (0, 1) - G₂ p (0, 1)| ≤
      coordinateJetDistanceOn K f₁ f₂ G₁ G₂ := by
  have h₀ : 0 ≤ uniformAbsOn K (f₁ - f₂) :=
    uniformAbsOn_nonneg hK hne (hf₁.sub hf₂)
  have h₁ : 0 ≤ uniformAbsOn K (fun z => G₁ z (1, 0) - G₂ z (1, 0)) :=
    uniformAbsOn_nonneg hK hne (continuousOn_clm_apply_sub hG₁ hG₂ (1, 0))
  have h₂ : |G₁ p (0, 1) - G₂ p (0, 1)| ≤
      uniformAbsOn K (fun z => G₁ z (0, 1) - G₂ z (0, 1)) :=
    abs_le_uniformAbsOn hK (continuousOn_clm_apply_sub hG₁ hG₂ (0, 1)) hp
  dsimp only [coordinateJetDistanceOn]
  linarith

/-- The maximum of three first-jet sum distances. -/
@[expose] noncomputable def threeJetDistanceOn (K : Set (ℝ × ℝ))
    (f₁ f₂ g₁ g₂ h₁ h₂ : ℝ × ℝ → ℝ)
    (F₁ F₂ G₁ G₂ H₁ H₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) : ℝ :=
  max (coordinateJetDistanceOn K f₁ f₂ F₁ F₂)
    (max (coordinateJetDistanceOn K g₁ g₂ G₁ G₂)
      (coordinateJetDistanceOn K h₁ h₂ H₁ H₂))

/-- The first field's sum distance is bounded by the three-field maximum. -/
theorem coordinateJetDistanceOn_first_le_threeJetDistanceOn
    (K : Set (ℝ × ℝ))
    (f₁ f₂ g₁ g₂ h₁ h₂ : ℝ × ℝ → ℝ)
    (F₁ F₂ G₁ G₂ H₁ H₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) :
    coordinateJetDistanceOn K f₁ f₂ F₁ F₂ ≤
      threeJetDistanceOn K f₁ f₂ g₁ g₂ h₁ h₂ F₁ F₂ G₁ G₂ H₁ H₂ :=
  le_max_left _ _

/-- The second field's sum distance is bounded by the three-field maximum. -/
theorem coordinateJetDistanceOn_second_le_threeJetDistanceOn
    (K : Set (ℝ × ℝ))
    (f₁ f₂ g₁ g₂ h₁ h₂ : ℝ × ℝ → ℝ)
    (F₁ F₂ G₁ G₂ H₁ H₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) :
    coordinateJetDistanceOn K g₁ g₂ G₁ G₂ ≤
      threeJetDistanceOn K f₁ f₂ g₁ g₂ h₁ h₂ F₁ F₂ G₁ G₂ H₁ H₂ :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- The third field's sum distance is bounded by the three-field maximum. -/
theorem coordinateJetDistanceOn_third_le_threeJetDistanceOn
    (K : Set (ℝ × ℝ))
    (f₁ f₂ g₁ g₂ h₁ h₂ : ℝ × ℝ → ℝ)
    (F₁ F₂ G₁ G₂ H₁ H₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ) :
    coordinateJetDistanceOn K h₁ h₂ H₁ H₂ ≤
      threeJetDistanceOn K f₁ f₂ g₁ g₂ h₁ h₂ F₁ F₂ G₁ G₂ H₁ H₂ :=
  (le_max_right _ _).trans (le_max_right _ _)

end
