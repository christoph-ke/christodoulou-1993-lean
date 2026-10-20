module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassicalAmplitudes

/-!
# The twelve classical equations on each lower tile

The primitive, transport, mass, and amplitude jet packages assemble into
the complete classical reduced system on every closed safe tile.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- A constrained safe tile satisfies all twelve classical equations as
relative first jets on its closed rectangle. -/
theorem LowerCoverTile.classical_jet_on
    {a vStar L u₀ u₁ H b : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ ≤ a) :
    RouteBClassicalJetOn b
      (Goursat.rectangle u₀ u₁ vStar (vStar + H))
      (rectangleStateFields fun p => (T.incoming p, T.outgoing p)) := by
  have hp := T.radius_psi_classical_jets (b := b) hu hH hu₀ hu₁
  have ht := T.transport_classical_jets (b := b) hu hH hu₀ hu₁
  have ha := T.amplitude_classical_jets (b := b) hu hH hu₀ hu₁
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
    ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    ha.1, ha.2, ht.2.2.2.2.1, ht.2.2.2.2.2⟩

end ChristodoulouBV.Uniqueness

end
