module

public import ChristodoulouBV.ForMathlib.ODE.GoursatC1Theorem
import all ChristodoulouBV.ForMathlib.ODE.Goursat

/-!
# Explicit bounds for transverse Goursat jets

The bounds are consequences of the linear Volterra equations and the
Banach-valued Gronwall estimate. They apply pointwise on a closed rectangle.
-/

public section

open Set intervalIntegral

namespace Goursat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- A continuous horizontal Volterra field has the explicit exponential
bound at every point of a closed rectangle. -/
theorem norm_le_add_mul_exp_of_horizontal_volterra
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (P : C(rectangle u₀ u₁ v₀ v₁, E))
    (A : C(rectangle u₀ u₁ v₀ v₁, E →L[ℝ] E))
    (H : C(rectangle u₀ u₁ v₀ v₁, E))
    (d : ℝ → E) (P₀ B κ : ℝ)
    (hP₀ : ∀ v ∈ Icc v₀ v₁, ‖d v‖ ≤ P₀)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hH : ∀ p, ‖H p‖ ≤ B)
    (hA : ∀ p, ‖A p‖ ≤ κ)
    (heq : ∀ p : rectangle u₀ u₁ v₀ v₁,
      P p = d p.1.2 + ∫ s in u₀..p.1.1,
        A (clippedPoint hu hv (s, p.1.2))
          (P (clippedPoint hu hv (s, p.1.2))) +
        H (clippedPoint hu hv (s, p.1.2)))
    (p : rectangle u₀ u₁ v₀ v₁) :
    ‖P p‖ ≤ (P₀ + B * (p.1.1 - u₀)) *
      Real.exp (κ * (p.1.1 - u₀)) := by
  have hpI : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
    simpa only [rectangle, mem_prod] using p.2
  let z : ℝ → E := fun s => P (clippedPoint hu hv (s, p.1.2))
  let a : ℝ → E →L[ℝ] E := fun s => A (clippedPoint hu hv (s, p.1.2))
  let j : ℝ → E := fun s => H (clippedPoint hu hv (s, p.1.2))
  have hz : Continuous z :=
    P.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_id.prodMk continuous_const))
  have ha : Continuous a :=
    A.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_id.prodMk continuous_const))
  have hj : Continuous j :=
    H.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_id.prodMk continuous_const))
  have hzeq : ∀ s ∈ Icc u₀ u₁,
      z s = d p.1.2 + ∫ t in u₀..s, a t (z t) + j t := by
    intro s hs
    have hq : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hs hpI.2
    have hc := clippedPoint_eq_self hu hv ⟨(s, p.1.2), hq⟩
    simpa only [z, a, j, hc] using
      (heq ⟨(s, p.1.2), hq⟩)
  have hbound := intervalIntegral.norm_le_add_mul_exp_of_linear_volterra
    hu z j a (d p.1.2) P₀ B κ hz.continuousOn hj.continuousOn
    ha.continuousOn (hP₀ p.1.2 hpI.2) hB hκ
    (fun s hs => hH (clippedPoint hu hv (s, p.1.2)))
    (fun s hs => hA (clippedPoint hu hv (s, p.1.2)))
    hzeq hpI.1
  simpa only [z, clippedPoint_eq_self hu hv p] using hbound

/-- A continuous vertical Volterra field has the corresponding explicit
exponential bound on a closed rectangle. -/
theorem norm_le_add_mul_exp_of_vertical_volterra
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (Q : C(rectangle u₀ u₁ v₀ v₁, E))
    (A : C(rectangle u₀ u₁ v₀ v₁, E →L[ℝ] E))
    (H : C(rectangle u₀ u₁ v₀ v₁, E))
    (d : ℝ → E) (Q₀ B κ : ℝ)
    (hQ₀ : ∀ u ∈ Icc u₀ u₁, ‖d u‖ ≤ Q₀)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hH : ∀ p, ‖H p‖ ≤ B)
    (hA : ∀ p, ‖A p‖ ≤ κ)
    (heq : ∀ p : rectangle u₀ u₁ v₀ v₁,
      Q p = d p.1.1 + ∫ t in v₀..p.1.2,
        A (clippedPoint hu hv (p.1.1, t))
          (Q (clippedPoint hu hv (p.1.1, t))) +
        H (clippedPoint hu hv (p.1.1, t)))
    (p : rectangle u₀ u₁ v₀ v₁) :
    ‖Q p‖ ≤ (Q₀ + B * (p.1.2 - v₀)) *
      Real.exp (κ * (p.1.2 - v₀)) := by
  have hpI : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
    simpa only [rectangle, mem_prod] using p.2
  let z : ℝ → E := fun t => Q (clippedPoint hu hv (p.1.1, t))
  let a : ℝ → E →L[ℝ] E := fun t => A (clippedPoint hu hv (p.1.1, t))
  let j : ℝ → E := fun t => H (clippedPoint hu hv (p.1.1, t))
  have hz : Continuous z :=
    Q.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_const.prodMk continuous_id))
  have ha : Continuous a :=
    A.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_const.prodMk continuous_id))
  have hj : Continuous j :=
    H.continuous.comp ((continuous_clippedPoint hu hv).comp
      (continuous_const.prodMk continuous_id))
  have hzeq : ∀ t ∈ Icc v₀ v₁,
      z t = d p.1.1 + ∫ s in v₀..t, a s (z s) + j s := by
    intro t ht
    have hq : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hpI.1 ht
    have hc := clippedPoint_eq_self hu hv ⟨(p.1.1, t), hq⟩
    simpa only [z, a, j, hc] using
      (heq ⟨(p.1.1, t), hq⟩)
  have hbound := intervalIntegral.norm_le_add_mul_exp_of_linear_volterra
    hv z j a (d p.1.1) Q₀ B κ hz.continuousOn hj.continuousOn
    ha.continuousOn (hQ₀ p.1.1 hpI.1) hB hκ
    (fun t ht => hH (clippedPoint hu hv (p.1.1, t)))
    (fun t ht => hA (clippedPoint hu hv (p.1.1, t)))
    hzeq hpI.2
  simpa only [z, clippedPoint_eq_self hu hv p] using hbound

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- The transverse Goursat jets satisfy the explicit exponential bounds.
The source estimates state precisely the directional bounds needed for the
inhomogeneous terms of the two linearized equations. -/
theorem norm_transverse_le_exp_of_goursat_jets
    (u₀ u₁ v₀ v₁ : ℝ) (hu : u₀ ≤ u₁) (hv : v₀ ≤ v₁)
    (X : ℝ × ℝ → E) (Y : ℝ × ℝ → F)
    (hX : Continuous X) (hY : Continuous Y)
    (c : E × F) (ρ : ℝ)
    (fX : ℝ × ℝ → E × F → E) (fY : ℝ × ℝ → E × F → F)
    (DF : ((ℝ × ℝ) × (E × F)) → ((ℝ × ℝ) × (E × F)) →L[ℝ] E)
    (DG : ((ℝ × ℝ) × (E × F)) → ((ℝ × ℝ) × (E × F)) →L[ℝ] F)
    (hfX : ContinuousOn fX.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hfY : ContinuousOn fY.uncurry
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hDF : ContinuousOn DF
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hDG : ContinuousOn DG
      (rectangle u₀ u₁ v₀ v₁ ×ˢ {z | dist z c ≤ ρ}))
    (hball : ∀ p ∈ rectangle u₀ u₁ v₀ v₁,
      dist (X p, Y p) c ≤ ρ)
    (M H PX₀ QY₀ : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (κ : NNReal)
    (hMX : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fX p z‖ ≤ M)
    (hMY : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ‖fY p z‖ ≤ M)
    (hDFX : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ x : E,
      ‖DF (p, z) ((0, 0), (x, 0))‖ ≤ (κ : ℝ) * ‖x‖)
    (hDGY : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ y : F,
      ‖DG (p, z) ((0, 0), (0, y))‖ ≤ (κ : ℝ) * ‖y‖)
    (hDFsource : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ y : F,
      ‖DF (p, z) ((0, 1), (0, y))‖ ≤ H + (κ : ℝ) * ‖y‖)
    (hDGsource : ∀ p ∈ rectangle u₀ u₁ v₀ v₁, ∀ z,
      dist z c ≤ ρ → ∀ x : E,
      ‖DG (p, z) ((1, 0), (x, 0))‖ ≤ H + (κ : ℝ) * ‖x‖)
    (x₀' : ℝ → E) (y₀' : ℝ → F)
    (hPX₀ : ∀ v ∈ Icc v₀ v₁, ‖x₀' v‖ ≤ PX₀)
    (hQY₀ : ∀ u ∈ Icc u₀ u₁, ‖y₀' u‖ ≤ QY₀)
    (P : C(rectangle u₀ u₁ v₀ v₁, E))
    (Q : C(rectangle u₀ u₁ v₀ v₁, F))
    (hPeq : ∀ p : rectangle u₀ u₁ v₀ v₁,
      P p = x₀' p.1.2 + ∫ s in u₀..p.1.1,
        DF ((s, p.1.2), (X (s, p.1.2), Y (s, p.1.2)))
          ((0, 1), (P (clippedPoint hu hv (s, p.1.2)),
            fY (s, p.1.2) (X (s, p.1.2), Y (s, p.1.2)))))
    (hQeq : ∀ p : rectangle u₀ u₁ v₀ v₁,
      Q p = y₀' p.1.1 + ∫ t in v₀..p.1.2,
        DG ((p.1.1, t), (X (p.1.1, t), Y (p.1.1, t)))
          ((1, 0), (fX (p.1.1, t) (X (p.1.1, t), Y (p.1.1, t)),
            Q (clippedPoint hu hv (p.1.1, t))))) :
    (∀ p : rectangle u₀ u₁ v₀ v₁,
      ‖P p‖ ≤ (PX₀ + (H + (κ : ℝ) * M) * (p.1.1 - u₀)) *
        Real.exp ((κ : ℝ) * (p.1.1 - u₀))) ∧
    (∀ p : rectangle u₀ u₁ v₀ v₁,
      ‖Q p‖ ≤ (QY₀ + (H + (κ : ℝ) * M) * (p.1.2 - v₀)) *
        Real.exp ((κ : ℝ) * (p.1.2 - v₀))) := by
  let Z : C(rectangle u₀ u₁ v₀ v₁, E × F) :=
    ⟨fun p => (X p.1, Y p.1), (hX.prodMk hY).comp continuous_subtype_val⟩
  have hZball : ∀ p, dist (Z p) c ≤ ρ := fun p => hball p.1 p.2
  let D : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] E) :=
    ⟨fun p => DF (p.1, Z p),
      hDF.comp_continuous (continuous_subtype_val.prodMk Z.continuous)
        (fun p => ⟨p.2, hZball p⟩)⟩
  let G : C(rectangle u₀ u₁ v₀ v₁,
      ((ℝ × ℝ) × (E × F)) →L[ℝ] F) :=
    ⟨fun p => DG (p.1, Z p),
      hDG.comp_continuous (continuous_subtype_val.prodMk Z.continuous)
        (fun p => ⟨p.2, hZball p⟩)⟩
  let R : C(rectangle u₀ u₁ v₀ v₁, F) :=
    ⟨fun p => fY p.1 (Z p),
      hfY.comp_continuous (continuous_subtype_val.prodMk Z.continuous)
        (fun p => ⟨p.2, hZball p⟩)⟩
  let S : C(rectangle u₀ u₁ v₀ v₁, E) :=
    ⟨fun p => fX p.1 (Z p),
      hfX.comp_continuous (continuous_subtype_val.prodMk Z.continuous)
        (fun p => ⟨p.2, hZball p⟩)⟩
  have hA : ∀ p, ‖firstLinearCoefficient D p‖ ≤ (κ : ℝ) := by
    intro p
    exact norm_firstLinearCoefficient_le D κ κ.coe_nonneg
      (fun p x => hDFX p.1 p.2 (Z p) (hZball p) x) p
  have hB : ∀ p, ‖secondLinearCoefficient G p‖ ≤ (κ : ℝ) := by
    intro p
    exact norm_secondLinearCoefficient_le G κ κ.coe_nonneg
      (fun p y => hDGY p.1 p.2 (Z p) (hZball p) y) p
  have hR : ∀ p, ‖firstLinearSource D R p‖ ≤ H + (κ : ℝ) * M := by
    intro p
    calc
      ‖firstLinearSource D R p‖ ≤ H + (κ : ℝ) * ‖R p‖ :=
        hDFsource p.1 p.2 (Z p) (hZball p) (R p)
      _ ≤ H + (κ : ℝ) * M := by
        gcongr
        exact hMY p.1 p.2 (Z p) (hZball p)
  have hS : ∀ p, ‖secondLinearSource G S p‖ ≤ H + (κ : ℝ) * M := by
    intro p
    calc
      ‖secondLinearSource G S p‖ ≤ H + (κ : ℝ) * ‖S p‖ :=
        hDGsource p.1 p.2 (Z p) (hZball p) (S p)
      _ ≤ H + (κ : ℝ) * M := by
        gcongr
        exact hMX p.1 p.2 (Z p) (hZball p)
  have hPeq' : ∀ p : rectangle u₀ u₁ v₀ v₁,
      P p = x₀' p.1.2 + ∫ s in u₀..p.1.1,
        firstLinearCoefficient D (clippedPoint hu hv (s, p.1.2))
          (P (clippedPoint hu hv (s, p.1.2))) +
        firstLinearSource D R (clippedPoint hu hv (s, p.1.2)) := by
    intro p
    rw [hPeq p]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hpI : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2
    have hsI : s ∈ Icc u₀ u₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hu⟩ hpI.1 hs
    have hpt : (s, p.1.2) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hsI hpI.2
    have hc := clippedPoint_eq_self hu hv ⟨_, hpt⟩
    dsimp only [D, Z, firstLinearCoefficient, firstLinearSource,
      ContinuousMap.coe_mk]
    rw [hc]
    have hRval : R ⟨_, hpt⟩ =
        fY (s, p.1.2) (X (s, p.1.2), Y (s, p.1.2)) := rfl
    rw [hRval]
    exact (first_linearized_split
      (DF ((s, p.1.2), (X (s, p.1.2), Y (s, p.1.2))))
      (P ⟨_, hpt⟩)
      (fY (s, p.1.2) (X (s, p.1.2), Y (s, p.1.2))))
  have hQeq' : ∀ p : rectangle u₀ u₁ v₀ v₁,
      Q p = y₀' p.1.1 + ∫ t in v₀..p.1.2,
        secondLinearCoefficient G (clippedPoint hu hv (p.1.1, t))
          (Q (clippedPoint hu hv (p.1.1, t))) +
        secondLinearSource G S (clippedPoint hu hv (p.1.1, t)) := by
    intro p
    rw [hQeq p]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have hpI : p.1.1 ∈ Icc u₀ u₁ ∧ p.1.2 ∈ Icc v₀ v₁ := by
      simpa only [rectangle, mem_prod] using p.2
    have htI : t ∈ Icc v₀ v₁ :=
      Set.uIcc_subset_Icc ⟨le_rfl, hv⟩ hpI.2 ht
    have hpt : (p.1.1, t) ∈ rectangle u₀ u₁ v₀ v₁ :=
      pair_mem_rectangle hpI.1 htI
    have hc := clippedPoint_eq_self hu hv ⟨_, hpt⟩
    dsimp only [G, Z, secondLinearCoefficient, secondLinearSource,
      ContinuousMap.coe_mk]
    rw [hc]
    have hSval : S ⟨_, hpt⟩ =
        fX (p.1.1, t) (X (p.1.1, t), Y (p.1.1, t)) := rfl
    rw [hSval]
    exact (second_linearized_split
      (DG ((p.1.1, t), (X (p.1.1, t), Y (p.1.1, t))))
      (fX (p.1.1, t) (X (p.1.1, t), Y (p.1.1, t))) (Q ⟨_, hpt⟩))
  constructor
  · intro p
    exact norm_le_add_mul_exp_of_horizontal_volterra hu hv
      P (firstLinearCoefficient D) (firstLinearSource D R)
      x₀' PX₀ (H + (κ : ℝ) * M) κ hPX₀
      (add_nonneg hH (mul_nonneg κ.coe_nonneg hM)) κ.coe_nonneg
      hR hA hPeq' p
  · intro p
    exact norm_le_add_mul_exp_of_vertical_volterra hu hv
      Q (secondLinearCoefficient G) (secondLinearSource G S)
      y₀' QY₀ (H + (κ : ℝ) * M) κ hQY₀
      (add_nonneg hH (mul_nonneg κ.coe_nonneg hM)) κ.coe_nonneg
      hS hB hQeq' p


end Goursat

end
