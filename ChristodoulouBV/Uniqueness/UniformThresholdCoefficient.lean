module

public import ChristodoulouBV.Uniqueness.UniformThresholdGap

/-!
# Coefficient closure from a shared numerical package

The constants here are selected before the normalized comparison data.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- One package dependent constant bounds every coefficient occurring in the
normalized comparison once its scalar variation is below the package's
preliminary threshold. -/
theorem UniformThresholdBounds.coefficient_bounds_normalized
    (P : UniformThresholdBounds) :
    ∃ C₁ : ℝ, 4 ≤ C₁ ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
        ∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            1 / C₁ ≤ S.lam u v ∧ S.lam u v ≤ C₁ ∧
            1 / C₁ ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₁ ∧
            |S.phi u v| ≤ C₁ ∧ |S.theta u v| ≤ C₁ ∧
            |S.zeta u v| ≤ C₁ ∧
            1 / C₁ ≤ S.r u v / (v - u) ∧
            S.r u v / (v - u) ≤ C₁ ∧
            1 / 2 ≤ 1 - IsBVSolution.mu S u v ∧
            (1 - IsBVSolution.mu S u v)⁻¹ ≤ C₁ ∧
            |S.theta u v / S.lam u v| ≤ C₁ ∧
            |S.zeta u v / S.nu u v| ≤ C₁ ∧
            |S.alpha u v / S.lam u v| ≤ C₁ ∧
            |S.beta u v / S.nu u v| ≤ C₁ ∧
            |S.lam u v / (1 - IsBVSolution.mu S u v)| ≤ C₁ ∧
            |S.nu u v / (1 - IsBVSolution.mu S u v)| ≤ C₁ ∧
            |S.lam u v / S.nu u v| ≤ C₁ ∧
            |S.nu u v / S.lam u v| ≤ C₁ ∧
            ∀ T : Fields, (T = D.S₁ ∨ T = D.S₂) →
              |S.lam u v / T.nu u v| ≤ C₁ ∧
              |S.nu u v / T.lam u v| ≤ C₁ ∧
              S.r u v / T.r u v ≤ C₁ := by
  let C₀ := 1 + P.C + 1 / P.c + 1 / P.radiusLower + max P.radiusUpper 0
  have hcinv : 0 ≤ 1 / P.c := one_div_nonneg.mpr P.c_pos.le
  have hdinv : 0 ≤ 1 / P.radiusLower :=
    one_div_nonneg.mpr P.radiusLower_pos.le
  have hK : 0 ≤ max P.radiusUpper 0 := le_max_right _ _
  have hC₀ : 1 ≤ C₀ := by dsimp [C₀]; linarith [P.C_nonneg]
  have hC₀pos : 0 < C₀ := by linarith
  have hC : P.C ≤ C₀ := by dsimp [C₀]; linarith
  have hci : 1 / P.c ≤ C₀ := by dsimp [C₀]; linarith [P.C_nonneg]
  have hdi : 1 / P.radiusLower ≤ C₀ := by
    dsimp [C₀]; linarith [P.C_nonneg]
  have hri : P.radiusUpper ≤ C₀ := by
    dsimp [C₀]
    linarith [le_max_left P.radiusUpper 0, P.C_nonneg]
  have hcLo : 1 / C₀ ≤ P.c := by
    have hh := (div_le_iff₀ P.c_pos).1 hci
    apply (div_le_iff₀ hC₀pos).2
    nlinarith
  have hdLo : 1 / C₀ ≤ P.radiusLower := by
    have hh := (div_le_iff₀ P.radiusLower_pos).1 hdi
    apply (div_le_iff₀ hC₀pos).2
    nlinarith
  let M := C₀ ^ 2
  let C₁ := 2 * (C₀ + M + 1)
  have hM : 0 ≤ M := sq_nonneg C₀
  have hC₁ : 4 ≤ C₁ := by dsimp [C₁]; nlinarith
  have hC₁pos : 0 < C₁ := by linarith
  have hC₀₁ : C₀ ≤ C₁ := by dsimp [C₁]; linarith
  have hM₁ : M ≤ C₁ := by dsimp [C₁]; linarith
  have hcLo₁ : 1 / C₁ ≤ P.c := by
    have hh := (div_le_iff₀ P.c_pos).1 (hci.trans hC₀₁)
    apply (div_le_iff₀ hC₁pos).2
    nlinarith
  have hdLo₁ : 1 / C₁ ≤ P.radiusLower := by
    have hh := (div_le_iff₀ P.radiusLower_pos).1 (hdi.trans hC₀₁)
    apply (div_le_iff₀ hC₁pos).2
    nlinarith
  refine ⟨C₁, hC₁, ?_⟩
  intro D ha hb hP hsmall u v huv S hS
  have hpt : (u, v) ∈ triangle 0 1 := by simpa only [ha, hb] using huv
  obtain ⟨hlamLo, hlamHi, hnuLo, hnuHi, hphi, htheta, hzeta,
    hradLo, hradHi⟩ := hP u v hpt S hS
  have hbase :
      1 / C₀ ≤ S.lam u v ∧ S.lam u v ≤ C₀ ∧
      1 / C₀ ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₀ ∧
      |S.phi u v| ≤ C₀ ∧ |S.theta u v| ≤ C₀ ∧
      |S.zeta u v| ≤ C₀ :=
    ⟨hcLo.trans hlamLo, hlamHi.trans hC,
      hcLo.trans hnuLo, hnuHi.trans hC,
      hphi.trans hC, htheta.trans hC, hzeta.trans hC⟩
  have hgap := P.gap_ge_half D ha hb hP le_rfl hsmall u v huv S hS
  have hratio := IsBVSolution.field_ratio_bounds
    (by positivity : 0 < 1 / C₀) (by positivity : 0 ≤ C₀)
    hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2.1
    hbase.2.2.2.2.1 hbase.2.2.2.2.2.1 hbase.2.2.2.2.2.2 hgap
  have hBexpr : 2 * (C₀ + C₀ / (1 / C₀) + 1) = C₁ := by
    dsimp [C₁, M]
    field_simp [ne_of_gt hC₀pos]
  rw [hBexpr] at hratio
  have hdist : 0 < v - u := sub_pos.mpr huv.2.1
  have hrlo : 1 / C₁ ≤ S.r u v / (v - u) :=
    hdLo₁.trans ((le_div_iff₀ hdist).2 hradLo)
  have hrhi : S.r u v / (v - u) ≤ C₁ :=
    (div_le_iff₀ hdist).2
      (hradHi.trans (mul_le_mul_of_nonneg_right (hri.trans hC₀₁) hdist.le))
  have hlamNu : |S.lam u v / S.nu u v| ≤ C₁ := by
    have hpos : 0 < |S.nu u v| :=
      (one_div_pos.mpr hC₀pos).trans_le hbase.2.2.1
    rw [abs_div]
    have hh : |S.lam u v| ≤ C₀ := by
      rw [abs_of_pos ((one_div_pos.mpr hC₀pos).trans_le hbase.1)]
      exact hbase.2.1
    have hsq : |S.lam u v| / |S.nu u v| ≤ M := by
      apply (div_le_iff₀ hpos).2
      have hbound := mul_le_mul_of_nonneg_left hbase.2.2.1 hM
      have heq : M * (1 / C₀) = C₀ := by
        dsimp [M]
        field_simp [hC₀pos.ne']
      nlinarith only [hh, hbound, heq]
    exact hsq.trans hM₁
  have hnuLam : |S.nu u v / S.lam u v| ≤ C₁ := by
    have hpos : 0 < S.lam u v :=
      (one_div_pos.mpr hC₀pos).trans_le hbase.1
    rw [abs_div, abs_of_pos hpos]
    have hsq : |S.nu u v| / S.lam u v ≤ M := by
      apply (div_le_iff₀ hpos).2
      have hbound := mul_le_mul_of_nonneg_left hbase.1 hM
      have heq : M * (1 / C₀) = C₀ := by
        dsimp [M]
        field_simp [hC₀pos.ne']
      nlinarith only [hbase.2.2.2.1, hbound, heq]
    exact hsq.trans hM₁
  have hcross : ∀ T : Fields, (T = D.S₁ ∨ T = D.S₂) →
      |S.lam u v / T.nu u v| ≤ C₁ ∧
      |S.nu u v / T.lam u v| ≤ C₁ ∧
      S.r u v / T.r u v ≤ C₁ := by
    intro T hTfield
    obtain ⟨htlamLo, _, htnuLo, _, _, _, _, htradLo, _⟩ :=
      hP u v hpt T hTfield
    have htlam : 1 / C₀ ≤ T.lam u v := hcLo.trans htlamLo
    have htnu : 1 / C₀ ≤ |T.nu u v| := hcLo.trans htnuLo
    have htnuPos : 0 < |T.nu u v| := (one_div_pos.mpr hC₀pos).trans_le htnu
    have htlamPos : 0 < T.lam u v := (one_div_pos.mpr hC₀pos).trans_le htlam
    have hcrossLam : |S.lam u v / T.nu u v| ≤ C₁ := by
      rw [abs_div]
      have hsq : |S.lam u v| / |T.nu u v| ≤ M := by
        apply (div_le_iff₀ htnuPos).2
        have hh := mul_le_mul_of_nonneg_left htnu hM
        have heq : M * (1 / C₀) = C₀ := by
          dsimp [M]; field_simp [hC₀pos.ne']
        have hs : |S.lam u v| ≤ C₀ := by
          rw [abs_of_pos ((one_div_pos.mpr hC₀pos).trans_le hbase.1)]
          exact hbase.2.1
        nlinarith only [hh, heq, hs]
      exact hsq.trans hM₁
    have hcrossNu : |S.nu u v / T.lam u v| ≤ C₁ := by
      rw [abs_div, abs_of_pos htlamPos]
      have hsq : |S.nu u v| / T.lam u v ≤ M := by
        apply (div_le_iff₀ htlamPos).2
        have hh := mul_le_mul_of_nonneg_left htlam hM
        have heq : M * (1 / C₀) = C₀ := by
          dsimp [M]; field_simp [hC₀pos.ne']
        nlinarith only [hh, heq, hbase.2.2.2.1]
      exact hsq.trans hM₁
    have hrTpos : 0 < T.r u v := by
      have hh := mul_pos P.radiusLower_pos hdist
      exact hh.trans_le htradLo
    have hcrossR : S.r u v / T.r u v ≤ C₁ := by
      apply (div_le_iff₀ hrTpos).2
      have hradM : P.radiusUpper ≤ M * P.radiusLower := by
        have hh := mul_le_mul_of_nonneg_left hdLo hM
        have heq : M * (1 / C₀) = C₀ := by
          dsimp [M]; field_simp [hC₀pos.ne']
        nlinarith only [hri, hh, heq]
      calc
        S.r u v ≤ P.radiusUpper * (v - u) := hradHi
        _ ≤ (M * P.radiusLower) * (v - u) :=
          mul_le_mul_of_nonneg_right hradM hdist.le
        _ = M * (P.radiusLower * (v - u)) := by ring
        _ ≤ M * T.r u v := mul_le_mul_of_nonneg_left htradLo hM
        _ ≤ C₁ * T.r u v := mul_le_mul_of_nonneg_right hM₁ hrTpos.le
    exact ⟨hcrossLam, hcrossNu, hcrossR⟩
  exact ⟨hcLo₁.trans hlamLo, hlamHi.trans (hC.trans hC₀₁),
    hcLo₁.trans hnuLo, hnuHi.trans (hC.trans hC₀₁),
    hphi.trans (hC.trans hC₀₁), htheta.trans (hC.trans hC₀₁),
    hzeta.trans (hC.trans hC₀₁), hrlo, hrhi, hgap,
    hratio.2.2.2.2.2.2, hratio.1, hratio.2.1,
    hratio.2.2.1, hratio.2.2.2.1, hratio.2.2.2.2.1,
    hratio.2.2.2.2.2.1, hlamNu, hnuLam, hcross⟩

end ChristodoulouBV.Uniqueness

end
