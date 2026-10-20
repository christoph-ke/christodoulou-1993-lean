module

public import ChristodoulouBV.BVSolution.CoefficientClosure
public import ChristodoulouBV.BVSolution.InitialData
import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives

/-!
# Representative-stable comparison data

The common initial good set is fixed before a compact comparison top is
chosen. Auxiliary-field norms sample only incoming rays based in that set.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Initial values at which both outgoing primitive densities agree. Outside
the initial interval the implication is vacuous; this makes the set conull in
the ambient real line. -/
def goodInitialVSet (S₁ S₂ : Fields) (a b : ℝ) : Set ℝ :=
  {v | v ∈ Ioo a b →
    S₁.lam a v = S₂.lam a v ∧ S₁.alpha a v = S₂.alpha a v}

/-- The common initial set is conull, and initial masses agree pointwise. -/
theorem good_initial_v_set
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b : ℝ} (_hab : a < b)
    (hT : triangle a b ⊆ U₁ ∩ U₂)
    (hdata : ∀ v ∈ Ioo a b,
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    (∀ᵐ v ∂volume, v ∈ goodInitialVSet S₁ S₂ a b) ∧
    Dense (goodInitialVSet S₁ S₂ a b) ∧
    (∀ v ∈ Ioo a b, S₁.m a v = S₂.m a v) := by
  have hq : ∀ q : ℚ, ∀ᵐ v ∂volume,
      a < (q : ℝ) → (q : ℝ) < b → v ∈ Ioc a (q : ℝ) →
        S₁.lam a v = S₂.lam a v ∧ S₁.alpha a v = S₂.alpha a v := by
    intro q
    by_cases haq : a < (q : ℝ)
    · by_cases hqb : (q : ℝ) < b
      · have hpt := hT (initial_edge_of_triangle haq hqb)
        filter_upwards [h₁.initial_lam_alpha_ae h₂ hpt.1 hpt.2
          (fun v hav hvq => hdata v ⟨hav, hvq.trans_lt hqb⟩)]
          with v hv _ _ hmem
        exact hv hmem
      · exact Filter.Eventually.of_forall (fun _ _ h => (hqb h).elim)
    · exact Filter.Eventually.of_forall (fun _ h => (haq h).elim)
  have hae : ∀ᵐ v ∂volume, v ∈ goodInitialVSet S₁ S₂ a b := by
    filter_upwards [eventually_countable_forall.mpr hq] with v hv hvab
    obtain ⟨q, hvq, hqb⟩ := exists_rat_btwn hvab.2
    exact hv q (hvab.1.trans hvq) hqb ⟨hvab.1, hvq.le⟩
  refine ⟨hae, volume.dense_of_ae hae, ?_⟩
  intro v hv
  obtain ⟨q, hvq, hqb⟩ := exists_rat_btwn hv.2
  have hpt := hT (initial_edge_of_triangle (hv.1.trans hvq) hqb)
  exact h₁.initial_mass_eq h₂ hpt.1 hpt.2
    (fun t hat htq => hdata t ⟨hat, htq.trans_lt hqb⟩)
    v ⟨hv.1, hvq.le⟩

/-- The initial good set contains a point in each open subinterval of the
initial characteristic. -/
theorem good_initial_v_set_exists_between
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {a b x y : ℝ} (hab : a < b) (hxy : x < y)
    (hax : a ≤ x) (hyb : y ≤ b)
    (hT : triangle a b ⊆ U₁ ∩ U₂)
    (hdata : ∀ v ∈ Ioo a b,
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∃ v ∈ Ioo x y, v ∈ Ioo a b ∧ v ∈ goodInitialVSet S₁ S₂ a b := by
  have hd := (good_initial_v_set h₁ h₂ hab hT hdata).2.1
  obtain ⟨v, hvG, hvI⟩ := hd.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hxy)
  exact ⟨v, hvI, ⟨hax.trans_lt hvI.1, hvI.2.trans_le hyb⟩, hvG⟩

/-- A continuous field bound on the dense good rays extends to all outgoing
points in the open interval. The field here denotes a continuous primitive,
not an arbitrary representative of a BV density. -/
theorem goodV_continuous_extension
    {G : Set ℝ} (hG : Dense G) {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b)) {C : ℝ}
    (hbound : ∀ v ∈ Ioo a b, v ∈ G → |f v| ≤ C) :
    ∀ v ∈ Ioo a b, |f v| ≤ C := by
  intro v hv
  have hopen : IsOpen (Ioo a b) := isOpen_Ioo
  have hcl : v ∈ closure (G ∩ Ioo a b) :=
    (by simpa only [inter_comm] using hG.open_subset_closure_inter hopen hv)
  have : (𝓝[G ∩ Ioo a b] v).NeBot :=
    mem_closure_iff_clusterPt.mp hcl
  have htend : Tendsto (fun x => |f x|) (𝓝[G ∩ Ioo a b] v) (𝓝 |f v|) :=
    ((hf v hv).mono (inter_subset_right)).abs
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hbound x hx.2 hx.1

/-- A one-sided inequality for a continuous primitive also extends from a
dense good set to every point of the open outgoing interval. -/
theorem goodV_continuous_le
    {G : Set ℝ} (hG : Dense G) {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b)) {C : ℝ}
    (hbound : ∀ v ∈ Ioo a b, v ∈ G → f v ≤ C) :
    ∀ v ∈ Ioo a b, f v ≤ C := by
  intro v hv
  have hcl : v ∈ closure (G ∩ Ioo a b) := by
    simpa only [inter_comm] using
      hG.open_subset_closure_inter isOpen_Ioo hv
  have : (𝓝[G ∩ Ioo a b] v).NeBot :=
    mem_closure_iff_clusterPt.mp hcl
  have htend : Tendsto f (𝓝[G ∩ Ioo a b] v) (𝓝 (f v)) :=
    (hf v hv).mono inter_subset_right
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hbound x hx.2 hx.1

/-- The two BV solutions and their common primary initial data on a full
augmented comparison triangle. No representative convention is included. -/
structure ComparisonData where
  U₁ : Set (ℝ × ℝ)
  U₂ : Set (ℝ × ℝ)
  S₁ : Fields
  S₂ : Fields
  a : ℝ
  b : ℝ
  hab : a < b
  h₁ : IsBVSolution U₁ S₁
  h₂ : IsBVSolution U₂ S₂
  hT : triangle a b ⊆ U₁ ∩ U₂
  hdata : ∀ v ∈ Ioo a b,
    S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v

/-- The common conull set attached to comparison data. -/
def ComparisonData.goodV (D : ComparisonData) : Set ℝ :=
  goodInitialVSet D.S₁ D.S₂ D.a D.b

/-- The good initial rays are dense; their initial mass values agree. -/
theorem ComparisonData.goodV_properties (D : ComparisonData) :
    (∀ᵐ v ∂volume, v ∈ D.goodV) ∧ Dense D.goodV ∧
    (∀ v ∈ Ioo D.a D.b, D.S₁.m D.a v = D.S₂.m D.a v) := by
  exact good_initial_v_set D.h₁ D.h₂ D.hab D.hT D.hdata

/-- A real supremum of a nonnegative comparison observable over points whose
incoming coordinate belongs to the fixed good set. Zero is included so this
definition is meaningful even on an empty compact cutoff. -/
noncomputable def ComparisonData.goodVNorm (D : ComparisonData)
    (V : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  sSup (insert 0 {x : ℝ | ∃ u v,
    (u, v) ∈ triangle D.a V ∧ v ∈ D.goodV ∧ x = |f u v|})

/-- An upper bound on every sampled value bounds the good-ray supremum. -/
theorem ComparisonData.goodVNorm_le (D : ComparisonData)
    {V M : ℝ} {f : ℝ → ℝ → ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u v, (u, v) ∈ triangle D.a V → v ∈ D.goodV →
      |f u v| ≤ M) :
    D.goodVNorm V f ≤ M := by
  unfold ComparisonData.goodVNorm
  apply csSup_le ⟨0, mem_insert 0 _⟩
  intro x hx
  rcases hx with rfl | ⟨u, v, huv, hvG, rfl⟩
  · exact hM
  · exact hbound u v huv hvG

/-- Each good-ray value lies below its finite good-ray supremum. -/
theorem ComparisonData.le_goodVNorm (D : ComparisonData)
    {V M : ℝ} {f : ℝ → ℝ → ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u v, (u, v) ∈ triangle D.a V → v ∈ D.goodV →
      |f u v| ≤ M)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV) :
    |f u v| ≤ D.goodVNorm V f := by
  unfold ComparisonData.goodVNorm
  have hb : BddAbove (insert 0 {x : ℝ | ∃ u v,
      (u, v) ∈ triangle D.a V ∧ v ∈ D.goodV ∧ x = |f u v|}) := by
    refine ⟨M, ?_⟩
    intro x hx
    rcases hx with rfl | ⟨u', v', huv', hvG', rfl⟩
    · exact hM
    · exact hbound u' v' huv' hvG'
  apply le_csSup hb
  exact mem_insert_of_mem 0 ⟨u, v, huv, hvG, rfl⟩

/-- A finite good-ray norm is nonnegative because its supremum set contains
zero. -/
theorem ComparisonData.goodVNorm_nonneg (D : ComparisonData)
    {V M : ℝ} {f : ℝ → ℝ → ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u v, (u, v) ∈ triangle D.a V → v ∈ D.goodV →
      |f u v| ≤ M) :
    0 ≤ D.goodVNorm V f := by
  unfold ComparisonData.goodVNorm
  have hb : BddAbove (insert 0 {x : ℝ | ∃ u v,
      (u, v) ∈ triangle D.a V ∧ v ∈ D.goodV ∧ x = |f u v|}) := by
    refine ⟨M, ?_⟩
    intro x hx
    rcases hx with rfl | ⟨u, v, huv, hvG, rfl⟩
    · exact hM
    · exact hbound u v huv hvG
  exact le_csSup hb (mem_insert 0 _)

/-- The four source comparison observables use the same fixed good-v set. -/
noncomputable def ComparisonData.L (D : ComparisonData) (V : ℝ) : ℝ :=
  D.goodVNorm V (fun u v => D.S₁.lam u v - D.S₂.lam u v)

/-- Incoming expansion difference on good incoming rays. -/
noncomputable def ComparisonData.N (D : ComparisonData) (V : ℝ) : ℝ :=
  D.goodVNorm V (fun u v => D.S₁.nu u v - D.S₂.nu u v)

/-- Outgoing scalar quotient difference on good incoming rays. -/
noncomputable def ComparisonData.A (D : ComparisonData) (V : ℝ) : ℝ :=
  D.goodVNorm V
    (fun u v => D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v)

/-- Incoming scalar quotient difference on good incoming rays. -/
noncomputable def ComparisonData.B (D : ComparisonData) (V : ℝ) : ℝ :=
  D.goodVNorm V
    (fun u v => D.S₁.beta u v / D.S₁.nu u v -
      D.S₂.beta u v / D.S₂.nu u v)

/-- The outgoing weighted mass comparison on a compact top, as an extended
nonnegative integral. Its finiteness is a separate axis Hardy obligation. -/
noncomputable def ComparisonData.Gamma (D : ComparisonData)
    (V : ℝ) : ENNReal :=
  ⨆ u ∈ Ico D.a V, ∫⁻ v in Ioc u V,
    ENNReal.ofReal (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2)

/-- The incoming weighted mass comparison on a compact top, retaining the
open terminal axis as an improper endpoint. -/
noncomputable def ComparisonData.GammaStar (D : ComparisonData)
    (V : ℝ) : ENNReal :=
  ⨆ v ∈ Ioo D.a V, ∫⁻ u in Ico D.a v,
    ENNReal.ofReal (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2)

private theorem abs_sub_le_two_of_bounds {x y C : ℝ}
    (hx : |x| ≤ C) (hy : |y| ≤ C) : |x - y| ≤ 2 * C := by
  calc
    |x - y| ≤ |x| + |y| := abs_sub x y
    _ ≤ C + C := add_le_add hx hy
    _ = 2 * C := by ring

/-- The fixed preliminary coefficient choice bounds all four good-ray norms,
uniformly as a compact top approaches the open top of the normalized
triangle. The order of choices is `C₀`, `ε₀`, then `C₁`; a final contraction
threshold is chosen only after this result. -/
theorem ComparisonData.finite_goodV_norms (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V, D.a < V → V < D.b →
          D.L V ≤ 2 * C₁ ∧ D.N V ≤ 2 * C₁ ∧
          D.A V ≤ 2 * C₁ ∧ D.B V ≤ 2 * C₁) := by
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) = D.S₂.phi 0 (1 / 2 : ℝ) := by
    have hh := (D.hdata (1 / 2 : ℝ) (by rw [ha, hb]; constructor <;> norm_num)).2
    simpa only [ha] using hh
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, hcoeff⟩ :=
    D.h₁.coefficient_bounds D.h₂ href hdatum
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, ?_⟩
  intro hsmall V haV hVb
  have hfield (u v : ℝ) (huv : (u, v) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D.a D.b D.hT hsmall u v
      ((mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩) S hS
  have htwo : 0 ≤ 2 * C₁ := by linarith
  have hbounds (u v : ℝ) (huv : (u, v) ∈ triangle D.a V)
      (hvG : v ∈ D.goodV) :
      |D.S₁.lam u v - D.S₂.lam u v| ≤ 2 * C₁ ∧
      |D.S₁.nu u v - D.S₂.nu u v| ≤ 2 * C₁ ∧
      |D.S₁.alpha u v / D.S₁.lam u v -
        D.S₂.alpha u v / D.S₂.lam u v| ≤ 2 * C₁ ∧
      |D.S₁.beta u v / D.S₁.nu u v -
        D.S₂.beta u v / D.S₂.nu u v| ≤ 2 * C₁ := by
    have hf₁ := hfield u v huv D.S₁ (Or.inl rfl)
    have hf₂ := hfield u v huv D.S₂ (Or.inr rfl)
    have hp : (u, v) ∈ D.U₁ ∩ D.U₂ :=
      D.hT ((mem_triangle).2
        ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩)
    rcases hf₁ with ⟨_, hlam₁, _, hnu₁, _, _, _, _, _, _, _, _, _, halpha₁,
      hbeta₁, _, _, _, _, _⟩
    rcases hf₂ with ⟨_, hlam₂, _, hnu₂, _, _, _, _, _, _, _, _, _, halpha₂,
      hbeta₂, _, _, _, _, _⟩
    have hlamAbs₁ : |D.S₁.lam u v| ≤ C₁ := by
      rw [abs_of_pos (D.h₁.solution.lam_pos (u,v) hp.1)]
      exact hlam₁
    have hlamAbs₂ : |D.S₂.lam u v| ≤ C₁ := by
      rw [abs_of_pos (D.h₂.solution.lam_pos (u,v) hp.2)]
      exact hlam₂
    exact ⟨abs_sub_le_two_of_bounds hlamAbs₁ hlamAbs₂,
      abs_sub_le_two_of_bounds hnu₁ hnu₂,
      abs_sub_le_two_of_bounds halpha₁ halpha₂,
      abs_sub_le_two_of_bounds hbeta₁ hbeta₂⟩
  exact ⟨D.goodVNorm_le htwo (fun u v huv hvG => (hbounds u v huv hvG).1),
    D.goodVNorm_le htwo (fun u v huv hvG => (hbounds u v huv hvG).2.1),
    D.goodVNorm_le htwo (fun u v huv hvG => (hbounds u v huv hvG).2.2.1),
    D.goodVNorm_le htwo (fun u v huv hvG => (hbounds u v huv hvG).2.2.2)⟩

end ChristodoulouBV.Uniqueness

end
