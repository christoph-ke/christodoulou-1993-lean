module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Sequences

/-!
# Sequential Arzelà–Ascoli on locally compact spaces

An equicontinuous family of real functions that is bounded on compact sets has a
locally uniformly convergent subsequence. The proof uses compactness in the
compact-open topology and its metrizability for a σ-compact domain.
-/

public section

open Set Filter Topology
open scoped NNReal

namespace ArzelaAscoli

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] {f : ℕ → X → ℝ}

/-- Compactwise equicontinuity and compactwise bounds give a locally uniformly
convergent subsequence of real functions. -/
theorem exists_strictMono_tendstoLocallyUniformly
    (heq : ∀ K : Set X, IsCompact K → EquicontinuousOn f K)
    (hb : ∀ K : Set X, IsCompact K →
      ∃ B : ℝ, ∀ n x, x ∈ K → |f n x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : X → ℝ), StrictMono φ ∧ Continuous g ∧
      TendstoLocallyUniformly (fun n ↦ f (φ n)) g atTop := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have heq_all : Equicontinuous f := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem_nhds x
    have hx : x ∈ K n := mem_of_mem_nhds hn
    simpa only [EquicontinuousWithinAt, EquicontinuousAt,
      nhdsWithin_eq_nhds.mpr hn] using heq (K n) (K.isCompact n) x hx
  let F : ℕ → C(X, ℝ) := fun n ↦ ⟨f n, heq_all.continuous n⟩
  have hclosed : IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact : C(X, ℝ) →
        UniformOnFun X ℝ {K : Set X | IsCompact K}) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous
      CompactlyCoherentSpace.isCoherentWith
  have hcompact : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {K : Set X | IsCompact K}) (F := fun h : C(X, ℝ) ↦ (h : X → ℝ))
      (fun _ h ↦ h) hclosed
    · intro K hK x hx U hU
      filter_upwards [heq K hK x hx U hU] with y hy i
      obtain ⟨n, hn⟩ := i.property
      change ((i : C(X, ℝ)) x, (i : C(X, ℝ)) y) ∈ U
      rw [← hn]
      exact hy n
    · intro K hK x hx
      obtain ⟨B, hB⟩ := hb K hK
      refine ⟨Set.Icc (-B) B, isCompact_Icc, ?_⟩
      intro h hh
      obtain ⟨n, rfl⟩ := hh
      have h := hB n x hx
      simp only [ContinuousMap.coe_mk, F] at *
      exact abs_le.mp h
  obtain ⟨G, -, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq (x := F) (fun n ↦ subset_closure ⟨n, rfl⟩)
  exact ⟨φ, G, hφ, G.continuous,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim⟩

/-- The subsequence from compactwise Arzelà–Ascoli converges uniformly on
every compact subset. -/
theorem exists_strictMono_tendstoUniformlyOn_compact
    (heq : ∀ K : Set X, IsCompact K → EquicontinuousOn f K)
    (hb : ∀ K : Set X, IsCompact K →
      ∃ B : ℝ, ∀ n x, x ∈ K → |f n x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : X → ℝ), StrictMono φ ∧ Continuous g ∧
      ∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun n ↦ f (φ n)) g atTop K := by
  obtain ⟨φ, g, hφ, hg, hlim⟩ :=
    exists_strictMono_tendstoLocallyUniformly heq hb
  exact ⟨φ, g, hφ, hg, tendstoLocallyUniformly_iff_forall_isCompact.mp hlim⟩

/-- A compactwise uniformly Lipschitz family with compactwise bounds has a
locally uniformly convergent subsequence. -/
theorem exists_strictMono_tendstoLocallyUniformly_of_lipschitzOnWith
    {M : Type*} [PseudoMetricSpace M] [LocallyCompactSpace M]
    [SigmaCompactSpace M] {fM : ℕ → M → ℝ}
    (hLip : ∀ K : Set M, IsCompact K →
      ∃ L : ℝ≥0, ∀ n, LipschitzOnWith L (fM n) K)
    (hb : ∀ K : Set M, IsCompact K →
      ∃ B : ℝ, ∀ n x, x ∈ K → |fM n x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : M → ℝ), StrictMono φ ∧ Continuous g ∧
      TendstoLocallyUniformly (fun n ↦ fM (φ n)) g atTop := by
  apply exists_strictMono_tendstoLocallyUniformly (hb := hb)
  intro K hK
  obtain ⟨L, hL⟩ := hLip K hK
  exact (LipschitzOnWith.uniformEquicontinuousOn fM L hL).equicontinuousOn

/-- The same conclusion from real-valued compactwise Lipschitz estimates
written as absolute-value inequalities. -/
theorem exists_strictMono_tendstoLocallyUniformly_of_abs_sub_le
    {M : Type*} [PseudoMetricSpace M] [LocallyCompactSpace M]
    [SigmaCompactSpace M] {fM : ℕ → M → ℝ}
    (hLip : ∀ K : Set M, IsCompact K →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ n, ∀ x ∈ K, ∀ y ∈ K,
        |fM n x - fM n y| ≤ L * dist x y)
    (hb : ∀ K : Set M, IsCompact K →
      ∃ B : ℝ, ∀ n x, x ∈ K → |fM n x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : M → ℝ), StrictMono φ ∧ Continuous g ∧
      TendstoLocallyUniformly (fun n ↦ fM (φ n)) g atTop := by
  apply exists_strictMono_tendstoLocallyUniformly_of_lipschitzOnWith (hb := hb)
  intro K hK
  obtain ⟨L, hL, hbound⟩ := hLip K hK
  refine ⟨⟨L, hL⟩, fun n ↦ LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  change |fM n x - fM n y| ≤ L * dist x y
  exact hbound n x hx y hy

variable {Y : Type*} [TopologicalSpace Y] {U : Set Y}
  [LocallyCompactSpace U] [SigmaCompactSpace U] {fU : ℕ → Y → ℝ}

/-- Sequential Arzelà–Ascoli on a locally compact, σ-compact subset, with the
limit expressed as a function on the ambient space. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn
    (heq : ∀ K : Set U, IsCompact K →
      EquicontinuousOn (fun n (x : U) ↦ fU n x) K)
    (hb : ∀ K : Set U, IsCompact K →
      ∃ B : ℝ, ∀ n (x : U), x ∈ K → |fU n x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : Y → ℝ), StrictMono φ ∧ ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n ↦ fU (φ n)) g atTop U := by
  obtain ⟨φ, g, hφ, hg, hlim⟩ :=
    exists_strictMono_tendstoLocallyUniformly (X := U) (f := fun n (x : U) ↦ fU n x)
      heq hb
  classical
  let G : Y → ℝ := fun y ↦ if h : y ∈ U then g ⟨y, h⟩ else 0
  have hG : ∀ x : U, G x = g x := by
    intro x
    simp [G]
  refine ⟨φ, G, hφ, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hfun : U.domRestrict G = g := funext hG
    rw [hfun]
    exact hg
  · rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have hfun : G ∘ ((↑) : U → Y) = g := funext hG
    rw [hfun]
    exact hlim

/-- Sequential Arzelà–Ascoli on an open subset of a locally compact,
second-countable space. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_isOpen
    {Z : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z]
    [SecondCountableTopology Z] {V : Set Z} (hV : IsOpen V)
    {fV : ℕ → Z → ℝ}
    (heq : ∀ K : Set V, IsCompact K →
      EquicontinuousOn (fun n (x : V) ↦ fV n x) K)
    (hb : ∀ K : Set V, IsCompact K →
      ∃ B : ℝ, ∀ n (x : V), x ∈ K → |fV n x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (g : Z → ℝ), StrictMono φ ∧ ContinuousOn g V ∧
      TendstoLocallyUniformlyOn (fun n ↦ fV (φ n)) g atTop V := by
  exact (letI : LocallyCompactSpace V := hV.locallyCompactSpace
    exists_strictMono_tendstoLocallyUniformlyOn heq hb)

end ArzelaAscoli

end
