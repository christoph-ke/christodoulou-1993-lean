module

public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Selection for bounded monotone real functions

A countable order-separating subset and one additional extraction at the possible jumps give
pointwise convergence on an arbitrary subset of the real line.
-/

public section

open Filter Set TopologicalSpace
open scoped Topology

namespace Set

/-- Every subset of the real line has a countable subset meeting each nontrivial closed
order interval with endpoints in the set. -/
theorem exists_countable_order_separating (s : Set ℝ) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ s ∧
      ∀ x ∈ s, ∀ y ∈ s, x < y → ∃ z ∈ D, x ≤ z ∧ z ≤ y := by
  obtain ⟨d, hd, hds, hsd⟩ := TopologicalSpace.exists_countable_dense_subset s
  let I : Set ℝ := {x | x ∈ s ∧ 𝓝[s ∩ Ioi x] x = ⊥}
  have hI : I.Countable := countable_setOfPred_isolated_right_within
  refine ⟨d ∪ I, hd.union hI, union_subset hds (fun x hx => hx.1), ?_⟩
  intro x hx y hy hxy
  by_cases hix : x ∈ I
  · exact ⟨x, Or.inr hix, le_rfl, hxy.le⟩
  have hne : (𝓝[s ∩ Ioi x] x).NeBot := by
    rw [neBot_iff]
    intro hbot
    exact hix ⟨hx, hbot⟩
  have hmem : s ∩ Ioi x ∩ Iio y ∈ 𝓝[s ∩ Ioi x] x :=
    inter_mem_nhdsWithin _ (Iio_mem_nhds hxy)
  obtain ⟨z, hz⟩ := hne.nonempty_of_mem hmem
  have hzcl : z ∈ closure d := hsd hz.1.1
  obtain ⟨w, hw, hwd⟩ := (mem_closure_iff.mp hzcl) (Ioo x y) isOpen_Ioo ⟨hz.1.2, hz.2⟩
  exact ⟨w, Or.inl hwd, hw.1.le, hw.2.le⟩

end Set

namespace Filter

/-- A uniformly bounded family of real sequences admits one subsequence converging at every
point of a countable index set. -/
theorem exists_subseq_tendsto_on_countable {α : Type*} {D : Set α}
    (hD : D.Countable) {u : ℕ → α → ℝ} {M : ℝ}
    (hu : ∀ n x, x ∈ D → |u n x| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ x ∈ D, ∃ a : ℝ,
      Tendsto (fun n => u (φ n) x) atTop (𝓝 a) := by
  let hCount : Countable D := hD.to_subtype
  let v : ℕ → D → Set.Icc (-M) M := fun n x => ⟨u n x, abs_le.mp (hu n x x.property)⟩
  obtain ⟨w, φ, hφ, hw⟩ := CompactSpace.tendsto_subseq v
  refine ⟨φ, hφ, ?_⟩
  intro x hx
  refine ⟨w ⟨x, hx⟩, ?_⟩
  exact (continuous_subtype_val.tendsto (w ⟨x, hx⟩)).comp
    ((tendsto_pi_nhds).mp hw ⟨x, hx⟩)

end Filter

namespace MonotoneOn

/-- Helly selection for a uniformly bounded sequence of monotone real functions on an arbitrary
subset of the real line. Values outside the set are unconstrained. -/
theorem helly_selection {s : Set ℝ} {f : ℕ → ℝ → ℝ} {M : ℝ}
    (hf : ∀ n, MonotoneOn (f n) s)
    (hb : ∀ n x, x ∈ s → |f n x| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      MonotoneOn g s ∧ ∀ x ∈ s, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨D, hD, hDs, hsep⟩ := Set.exists_countable_order_separating s
  obtain ⟨φ, hφ, hDconv⟩ := Filter.exists_subseq_tendsto_on_countable hD
    (fun n x hx => hb n x (hDs hx))
  let F : ℕ → ℝ → ℝ := fun n x => f (φ n) x
  let lo : ℝ → ℝ := fun x => liminf (fun n => F n x) atTop
  let hi : ℝ → ℝ := fun x => limsup (fun n => F n x) atTop
  have hUpper (x : ℝ) (hx : x ∈ s) :
      (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) (fun n => F n x) :=
    isBoundedUnder_of ⟨M, fun n => (abs_le.mp (hb (φ n) x hx)).2⟩
  have hLower (x : ℝ) (hx : x ∈ s) :
      (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) (fun n => F n x) :=
    isBoundedUnder_of ⟨-M, fun n => (abs_le.mp (hb (φ n) x hx)).1⟩
  have hcross (x y : ℝ) (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) : hi x ≤ lo y := by
    obtain ⟨z, hzD, hxz, hzy⟩ := hsep x hx y hy hxy
    obtain ⟨a, ha⟩ := hDconv z hzD
    have hxle : hi x ≤ hi z :=
      limsup_le_limsup (Eventually.of_forall (fun n => hf (φ n) hx (hDs hzD) hxz))
        (hLower x hx).isCoboundedUnder_le (hUpper z (hDs hzD))
    have hzle : lo z ≤ lo y :=
      liminf_le_liminf (Eventually.of_forall (fun n => hf (φ n) (hDs hzD) hy hzy))
        (hLower z (hDs hzD)) (hUpper y hy).isCoboundedUnder_ge
    exact hxle.trans ((ha.limsup_eq).trans_le ((ha.liminf_eq).symm.le.trans hzle))
  have hbad : {x | x ∈ s ∧ lo x < hi x}.Countable := by
    apply (countable_image_lt_image_Ioi_within s lo).mono
    rintro x ⟨hx, hlt⟩
    exact ⟨hx, hi x, hlt, fun y hy hxy => hcross x y hx hy hxy⟩
  obtain ⟨ψ, hψ, hbadConv⟩ := Filter.exists_subseq_tendsto_on_countable hbad
    (fun n x hx => hb (φ n) x hx.1)
  have hconv : ∀ x ∈ s, ∃ a : ℝ, Tendsto (fun n => F (ψ n) x) atTop (𝓝 a) := by
    intro x hx
    by_cases hlt : lo x < hi x
    · exact hbadConv x ⟨hx, hlt⟩
    · have hle : lo x ≤ hi x := liminf_le_limsup (hUpper x hx) (hLower x hx)
      have heq : lo x = hi x := le_antisymm hle (le_of_not_gt hlt)
      refine ⟨lo x, ?_⟩
      exact (tendsto_of_liminf_eq_limsup rfl heq.symm (hUpper x hx) (hLower x hx)).comp
        hψ.tendsto_atTop
  classical
  let g : ℝ → ℝ := fun x => if hx : x ∈ s then Classical.choose (hconv x hx) else 0
  have hg (x : ℝ) (hx : x ∈ s) :
      Tendsto (fun n => F (ψ n) x) atTop (𝓝 (g x)) := by
    simp only [g, dite_eq_left hx]
    exact Classical.choose_spec (hconv x hx)
  have hgm : MonotoneOn g s := by
    intro x hx y hy hxy
    exact le_of_tendsto_of_tendsto (hg x hx) (hg y hy)
      (Eventually.of_forall (fun n => hf (φ (ψ n)) hx hy hxy))
  exact ⟨φ ∘ ψ, hφ.comp hψ, g, hgm, fun x hx => hg x hx⟩

end MonotoneOn

namespace Filter

/-- Diagonal extraction for countably many pointwise convergence problems. Each extraction is
allowed to start from an arbitrary strictly increasing subsequence. -/
theorem exists_subseq_tendsto_forall {α β : Type*} [TopologicalSpace β]
    {u : ℕ → ℕ → α → β} {s : ℕ → Set α}
    (hextract : ∀ k (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ x ∈ s k, ∃ a : β,
        Tendsto (fun n => u k (φ (ψ n)) x) atTop (𝓝 a)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k x, x ∈ s k → ∃ a : β,
      Tendsto (fun n => u k (φ n) x) atTop (𝓝 a) := by
  classical
  let Subseq := {φ : ℕ → ℕ // StrictMono φ}
  let next (k : ℕ) (a : Subseq) : ℕ → ℕ :=
    Classical.choose (hextract k a.val a.property)
  have hnext (k : ℕ) (a : Subseq) : StrictMono (next k a) ∧
      ∀ x ∈ s k, ∃ b : β,
        Tendsto (fun n => u k (a.val ((next k a) n)) x) atTop (𝓝 b) :=
    Classical.choose_spec (hextract k a.val a.property)
  let step (k : ℕ) (a : Subseq) : Subseq :=
    ⟨a.val ∘ next k a, a.property.comp (hnext k a).1⟩
  let stage : ℕ → Subseq := Nat.rec ⟨id, strictMono_id⟩ step
  have hstage_succ (k : ℕ) : (stage (k + 1)).val = (stage k).val ∘ next k (stage k) := rfl
  have hfactor (m n : ℕ) (hmn : m ≤ n) :
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ (stage n).val = (stage m).val ∘ τ := by
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, by funext i; rfl⟩
    | succ n hmn ih =>
      obtain ⟨τ, hτ, heq⟩ := ih
      refine ⟨τ ∘ next n (stage n), hτ.comp (hnext n (stage n)).1, ?_⟩
      calc
        (stage (n + 1)).val = (stage n).val ∘ next n (stage n) := hstage_succ n
        _ = ((stage m).val ∘ τ) ∘ next n (stage n) := by rw [heq]
        _ = (stage m).val ∘ (τ ∘ next n (stage n)) := by funext i; rfl
  let φ : ℕ → ℕ := fun n => (stage n).val n
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n => by
    calc
      (stage n).val n < (stage n).val (n + 1) := (stage n).property (Nat.lt_succ_self n)
      _ ≤ (stage (n + 1)).val (n + 1) := by
        rw [hstage_succ]
        exact (stage n).property.monotone ((hnext n (stage n)).1.id_le _)
  refine ⟨φ, hφ, ?_⟩
  intro k x hx
  obtain ⟨a, ha⟩ := (hnext k (stage k)).2 x hx
  have hstage : Tendsto (fun n => u k ((stage (k + 1)).val n) x) atTop (𝓝 a) := by
    simpa only [hstage_succ, Function.comp_apply] using ha
  let m := k + 1
  let η (n : ℕ) : ℕ := if h : m ≤ n then (Classical.choose (hfactor m n h)) n else n
  have hηlower (n : ℕ) : n ≤ η n := by
    dsimp [η]
    split
    · exact (Classical.choose_spec (hfactor m n ‹m ≤ n›)).1.id_le n
    · exact le_rfl
  have hη : Tendsto η atTop atTop :=
    tendsto_atTop.mpr fun b => (eventually_ge_atTop b).mono fun n hn => hn.trans (hηlower n)
  have heq : (fun n => u k (φ n) x) =ᶠ[atTop]
      (fun n => u k ((stage m).val (η n)) x) := by
    filter_upwards [eventually_ge_atTop m] with n hn
    have hfac := (Classical.choose_spec (hfactor m n hn)).2
    congr 1
    change (stage n).val n = (stage m).val (η n)
    rw [hfac]
    simp only [Function.comp_apply, η, dite_eq_left hn]
  exact ⟨a, (hstage.comp hη).congr' heq.symm⟩

end Filter

end
