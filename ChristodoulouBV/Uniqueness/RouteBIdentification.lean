module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisPacket
import ChristodoulouBV.Uniqueness.ExtensionFamily
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Matching the old family to the compact Route B axis edge

The compact edge is built from one old member near the axis and the terminal
traces away from it. Compatibility identifies both pieces with any old member
defined at the point.
-/

public section

open Set
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The compact expansion and scalar amplitude agree with any finite old
member on the strict incoming edge. -/
theorem OffAxisTerminalC1Packet.edge_expansion_scalar_eq_old
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {b v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hav : a < v) (hvb : v < b) :
    P.g v = (S b).lam a v ∧
      P.hEdge v = (S b).alpha a v / (S b).lam a v := by
  by_cases hvt : v ≤ P.t
  · have hvOld : v ∈ Icc a P.t := ⟨hav.le, hvt⟩
    have hcompat := family_fields_eq_on_common_development hfamily
      P.b₀_mem hb (p := (a, v))
      (show (a, v) ∈ developmentWithInitialEdge P.b₀ ∩
          developmentWithInitialEdge b from
        ⟨⟨ha.le, hav, hvt.trans_lt P.t_lt_b₀⟩,
          ⟨ha.le, hav, hvb⟩⟩)
    obtain ⟨hg, hh, _⟩ := P.old_match v hvOld
    exact ⟨hg.trans hcompat.2.2.2.1,
      hh.trans (by rw [hcompat.2.2.2.2.2.1,
        hcompat.2.2.2.1])⟩
  · have htv : P.t < v := lt_of_not_ge hvt
    have hvTop : v ∈ Icc vBar vStar :=
      ⟨(P.vBar_lt_t.trans htv).le, hvb.le.trans hb.2.le⟩
    have hmatch := P.state.match_old b hb a ⟨ha.le, le_rfl⟩ v
      ⟨hvTop.1, hvb⟩
    obtain ⟨hg, hh, _⟩ := P.top_match v hvTop
    exact ⟨hg.trans hmatch.2.2.1,
      hh.trans hmatch.2.2.2.2.2.2.2.2⟩

/-- The compact radius and scalar-radius primitives equal those of each
finite old member up to its strict outgoing cutoff. The diagonal values
are canonical, so this statement makes no claim about raw old `r` or `m`
there. -/
theorem OffAxisTerminalC1Packet.edge_primitives_eq_old
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {b v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hav : a ≤ v) (hvb : v < b) :
    P.rEdge v = C1Solution.canonicalRadius (S b) (a, v) ∧
      (∫ s in a..v, P.g s * P.hEdge s) =
        C1Solution.canonicalScalarRadius (S b) (a, v) := by
  have hgv : (∫ s in a..v, P.g s) =
      C1Solution.canonicalRadius (S b) (a, v) := by
    change (∫ s in a..v, P.g s) =
      ∫ s in a..v, (S b).lam a s
    apply intervalIntegral.integral_congr_Ioo_of_le hav
    intro s hs
    exact (P.edge_expansion_scalar_eq_old ha hfamily hb hs.1
      (hs.2.trans hvb)).1
  constructor
  · exact (P.radius_primitive v ⟨hav, hvb.le.trans hb.2.le⟩).trans hgv
  · change (∫ s in a..v, P.g s * P.hEdge s) =
      ∫ s in a..v, (S b).alpha a s
    apply intervalIntegral.integral_congr_Ioo_of_le hav
    intro s hs
    have hmatch := P.edge_expansion_scalar_eq_old ha hfamily hb hs.1
      (hs.2.trans hvb)
    have hlam : (S b).lam a s ≠ 0 :=
      ne_of_gt ((hfamily b hb).1.solution.lam_pos (a, s)
        ⟨ha.le, hs.1, hs.2.trans hvb⟩)
    change P.g s * P.hEdge s = (S b).alpha a s
    rw [hmatch.1, hmatch.2]
    field_simp [hlam]

/-- On the strict old edge, the compact primitives are the old physical
radius and scalar-radius product. This uses only values inside the frozen
development and does not identify its raw diagonal radius. -/
theorem OffAxisTerminalC1Packet.edge_radius_scalar_product_eq_old
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {b v : ℝ} (hb : b ∈ Ioo (0 : ℝ) vStar)
    (hav : a < v) (hvb : v < b) :
    P.rEdge v = (S b).r a v ∧
      (∫ s in a..v, P.g s * P.hEdge s) =
        (S b).r a v * (S b).phi a v := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [ha, hav, hvb]
  have hBb : B < b := by dsimp [B]; linarith only [hvb]
  have hvB : v ≤ B := by dsimp [B]; linarith only [hvb]
  have hprim := P.edge_primitives_eq_old ha hfamily hb hav.le hvb
  exact ⟨hprim.1.trans
      (C1Solution.canonicalRadius_eq_radius hB hBb (hfamily b hb).1
        ha.le hav hvB),
    hprim.2.trans
      (C1Solution.canonicalScalarRadius_eq_radius_mul_phi hB hBb
        (hfamily b hb).1 ha.le hav hvB)⟩

end ChristodoulouBV.Uniqueness

end
