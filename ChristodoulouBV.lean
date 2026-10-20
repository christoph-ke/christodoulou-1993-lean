module

-- Theorem 3.1 (p. 1148), uniqueness and extension halves
public import ChristodoulouBV.Frozen.Theorem3_1Unique
public import ChristodoulouBV.Frozen.Theorem3_1Extend
-- Theorem 5.1 (p. 1172), extension principle
public import ChristodoulouBV.Frozen.Theorem5_1
-- Theorems 6.1 and 6.2 (pp. 1179, 1183), existence part
public import ChristodoulouBV.Frozen.Theorem6_1_6_2Exists
-- Declarations cited in ERRATA.md
public import ChristodoulouBV.Existence.Lemma62Counterexamples
public import ChristodoulouBV.Uniqueness.ExpansionIncomingCoeffSmall
public import ChristodoulouBV.Uniqueness.ExtensionStripIncrement
public import ChristodoulouBV.Uniqueness.ExtensionOldAbsorptionStar
public import ChristodoulouBV.Uniqueness.RouteBGluingFinal
public import ChristodoulouBV.C1Solution.AxisLocalExistenceCompactEdge
public import ChristodoulouBV.C1Solution.AxisUniformEndpointCompact

/-!
# Christodoulou (1993), Lean formalization

Root module. It imports the four sealed main theorems (`ChristodoulouBV.Frozen.*`), whose import closure is the
library, and the modules containing the declarations cited in `ERRATA.md`.
-/
