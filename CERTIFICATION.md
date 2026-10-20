# Certification of the frozen declarations

This release certifies four Lean theorem statements relative to 16 frozen definitions of the reduced Einstein–scalar field system. The definitions and statements were approved on 2026-10-17 before the proofs were completed. The theorem seals were independently audited on 2026-10-17, 2026-10-18, and 2026-10-19. All four exports depend only on `propext`, `Classical.choice`, and `Quot.sound`. The [README](README.md) describes their mathematical content; the [interpretive rulings](docs/AUTHOR-RULINGS.md) specify the approved departures from the printed statements.

## Frozen files and checksums

The table lists all 20 files in `ChristodoulouBV/Frozen/`, their designated exports, kinds, paper locations, and SHA-256 digests of the complete sealed file bytes, including comments and final newlines. A structure is counted as a definition. Page numbers refer to Communications on Pure and Applied Mathematics **46** (1993), 1131–1220. The initial-edge domains are approved adaptations of the printed developments, as explained in ruling D8.

For release preparation on 2026-10-20, `sha256sum` was run on all 20 files. All files were also compared byte for byte with the sealed originals. The 16 definition hashes matched their approved whole-file digests and all 64 occurrences of definition-checksum entries in the four theorem records. All four frozen theorem prefixes and suffixes matched their approved digests. **No mismatch was found.** The full sealed-file digests below also agree with [scripts/frozen-files.sha256](scripts/frozen-files.sha256).

The frozen files intentionally retain their original docstrings, including internal manifest identifiers and paths to documents in the nonpublic development repository. Those annotations are historical references, not dependencies supplied by this release. They were left unchanged to preserve byte identity with the sealed state. Comments outside the frozen files have been cleaned for public release.

| Frozen file | Designated Lean export | Kind | Paper location | SHA-256 |
| --- | --- | --- | --- | --- |
| [AdjacentAxis.lean](ChristodoulouBV/Frozen/AdjacentAxis.lean) | `ChristodoulouBV.adjacentAxis` | definition | pp. 1146–1147, axis convention | `c0fb53896b3365b9eecb5a0c7c1fac9be036cde0bdfedfeb372ddb59299e7b03` |
| [AxisVanishingVariation.lean](ChristodoulouBV/Frozen/AxisVanishingVariation.lean) | `ChristodoulouBV.AxisVanishingVariation` | definition | p. 1146, BV item 4 | `1376612cf3d5d604b724e41ac0a51d9bc6882095ce67210a0828f1025acfbff8` |
| [CausalPast.lean](ChristodoulouBV/Frozen/CausalPast.lean) | `ChristodoulouBV.causalPast` | definition | p. 1146, causal past | `ee675c1dffd011e9dceee748d4514621d3734390094fe8e2a2bf3d24c8ab007f` |
| [DevelopmentWithInitialEdge.lean](ChristodoulouBV/Frozen/DevelopmentWithInitialEdge.lean) | `ChristodoulouBV.developmentWithInitialEdge` | definition | pp. 1148, 1157, 1172; D8 | `4e45df1454bcaf0005b91fe1e3da08e4a38f7b96a3d8f1dfb930cc873e585200` |
| [DomainOfDevelopment.lean](ChristodoulouBV/Frozen/DomainOfDevelopment.lean) | `ChristodoulouBV.IsDomainOfDevelopment` | definition | p. 1146, domain of development | `da61c34144108ff081099719bdccdc083a0200271ad2c07e9223b17dc1810ed5` |
| [Fields.lean](ChristodoulouBV/Frozen/Fields.lean) | `ChristodoulouBV.Fields` | definition | pp. 1133–1138, (1.5), (1.11)–(1.18) | `fc29d74bc9f650ddbcb96c23df974ad15599127efd2adbd92afb0bddb68f7b12` |
| [FieldsTheta.lean](ChristodoulouBV/Frozen/FieldsTheta.lean) | `ChristodoulouBV.Fields.theta` | definition | p. 1137, (1.13), (1.17) | `1e81c06e56ae9b9ade70dd248ae8c00dec9b2b350eece568fdcdc0b2d5716474` |
| [FieldsZeta.lean](ChristodoulouBV/Frozen/FieldsZeta.lean) | `ChristodoulouBV.Fields.zeta` | definition | p. 1137, (1.13), (1.17) | `8aa70909364604be8db69ecb0ddf6c5f461e768e725df8b6d3246c940be053fb` |
| [GlobalDomain.lean](ChristodoulouBV/Frozen/GlobalDomain.lean) | `ChristodoulouBV.globalDomain` | definition | pp. 1148, 1179, 1183; D8 | `e40ad42243e3ff14d78851b6adf07539f1e19e8db8f7a7fe776fafed7c138363` |
| [InSeg.lean](ChristodoulouBV/Frozen/InSeg.lean) | `ChristodoulouBV.inSeg` | definition | p. 1137, (1.12) | `aa349807be9da19e3a476849b500c2044cbeb1a7d19e896e53a6dde2d0fbc9e5` |
| [IntervalPrimitive.lean](ChristodoulouBV/Frozen/IntervalPrimitive.lean) | `ChristodoulouBV.IntervalPrimitive` | definition | pp. 1185–1187, integral identities | `466e95219dfe410b5b3889353193f34ac1c94864d283c14df8a468ffbb28b5bf` |
| [IsBVSolution.lean](ChristodoulouBV/Frozen/IsBVSolution.lean) | `ChristodoulouBV.IsBVSolution` | definition | pp. 1146–1147, BV definition | `a5141dc59ec0a5dd595197b339febadb1489c72631354b2e223bcb116262a0ab` |
| [IsC1Solution.lean](ChristodoulouBV/Frozen/IsC1Solution.lean) | `ChristodoulouBV.IsC1Solution` | definition | p. 1157, C¹ definition | `ebc7676ff8368f5b3ef36ca544e297acc0df389a54cf01f75d3957e53a1394ee` |
| [IsSolution.lean](ChristodoulouBV/Frozen/IsSolution.lean) | `ChristodoulouBV.IsSolution` | definition | pp. 1133–1138, 1146, 1185–1187; D4 | `932129cbdcc8857c7f10918d4fa99ee76c53c71f525c716a44e390823adf8ed8` |
| [OpenDevelopment.lean](ChristodoulouBV/Frozen/OpenDevelopment.lean) | `ChristodoulouBV.openDevelopment` | definition | p. 1148, open development | `36375521583f7975b8bac4c1d63823b1459b5eca94cbeba353664cee9c53b19b` |
| [OutSeg.lean](ChristodoulouBV/Frozen/OutSeg.lean) | `ChristodoulouBV.outSeg` | definition | p. 1137, (1.12) | `e3044e5b2722028dfd5ac5a99e8542b33ed6900355a177cf034a226a1770005c` |
| [Theorem3_1Extend.lean](ChristodoulouBV/Frozen/Theorem3_1Extend.lean) | `ChristodoulouBV.theorem3_1_extend` | theorem | p. 1148, Theorem 3.1, extension | `7493a646f8517443c22707c29a53674c3613ec412702ee3b2af1eec4557462ca` |
| [Theorem3_1Unique.lean](ChristodoulouBV/Frozen/Theorem3_1Unique.lean) | `ChristodoulouBV.theorem3_1_unique` | theorem | p. 1148, Theorem 3.1, uniqueness | `516c465d1add3eb3166729206077156f7fef5ecd5c3840965e678c0c7e0dfaf5` |
| [Theorem5_1.lean](ChristodoulouBV/Frozen/Theorem5_1.lean) | `ChristodoulouBV.theorem5_1` | theorem | pp. 1172, 1176, 1179, Theorem 5.1 | `950fab09c8b843ce9d8d0e14bcbc7421c6506897cd779b5368a8becec0b5516f` |
| [Theorem6_1_6_2Exists.lean](ChristodoulouBV/Frozen/Theorem6_1_6_2Exists.lean) | `ChristodoulouBV.theorem6_1_6_2_exists` | theorem | pp. 1179, 1183, Theorems 6.1/6.2, existence only | `845258dcf93eb7f4ed29c297f5988b4f247136ec57ca123d891bd3239e255627` |

The complete-file hashes can be checked from the repository root with:

```sh
sha256sum -c scripts/frozen-files.sha256
```

## Seal discipline

The 16 definition files were frozen in their entirety. In each theorem file, the imports, declaration name, binders, hypotheses, conclusion, and surrounding text were frozen before proof completion. Only the marked proof region was replaced when sealing. Its body is exactly one of:

```lean
by exact ChristodoulouBV.Provider.theorem3_1_unique
by exact ChristodoulouBV.Provider.theorem3_1_extend
by exact ChristodoulouBV.Provider.theorem5_1
by exact ChristodoulouBV.Provider.theorem6_1_6_2_exists
```

Each line belongs to its corresponding theorem file. The provider supplies the proof through the declarations and results below it. The two Theorem 3.1 providers infer their domain and field parameters and use the existing solution and initial-data hypotheses. No extra logical hypothesis is added by this arrangement. The other two providers prove the closed existential statements.

Before freezing, independent reviews compared the Lean declarations and their expanded definition clauses with the paper. At sealing, independent audits checked the frozen text and elaborated types, exact provider applications, actual uses of intermediate results, and transitive axiom dependencies. The release checksum file now protects the complete sealed files, including the proof lines.

## Audit history

The historical audit verdicts below concern the approved formulations, including their explicit scope restrictions. They do not certify omitted conclusions or erase the findings of the statement reviews.

**Statement reviews, 2026-10-17, before freezing.** Three independent reviews covered the definitions and all four theorem statements. They checked the printed source, endpoints and carriers, every logical input, quantifier order, axis limits, uniform BV bounds, C¹ regularity on closures, and examples establishing non-vacuity. The initial verdicts included **FAIL** and **PASS WITH NOTES**. Revisions removed separate mass-ratio and conformal-factor definitions, corrected the base sign premise, represented Theorem 5.1 by a family with a universal constant, and combined the two existence branches under one threshold. The targeted final statement review accepted the sign-premise revision and theorem-region format, while still identifying interpretive choices and proof obligations. The approved rulings fixed those choices later that day. The statements were frozen at that point; their proofs were still incomplete. The later passing seal audits checked the exact approved reduced-system formulations.

| Frozen theorem | Statement review before freeze | Pre-seal or seal audit, verdict and date | Main proof checks |
| --- | --- | --- | --- |
| `ChristodoulouBV.theorem3_1_unique` | 2026-10-17: reviewed against p. 1148; the reduced coincidence conclusion required an explicit ruling, and inherited solution-predicate issues required revision or a scope decision. | Seal-candidate audit **PASS**, 2026-10-17; sealed the same day. | Approved bytes and elaborated type; only the two BV hypotheses and common initial data; uniform contraction threshold selected before scaling; axis localization from BV item 4; regular-rectangle continuation and included endpoints; standard axiom closure. |
| `ChristodoulouBV.theorem3_1_extend` | 2026-10-17: reviewed as the union-extension part of p. 1148, subject to the same reduced coincidence and solution-class rulings. | Seal-candidate audit **PASS**, 2026-10-18; sealed the same day. | Exact existential type; use of sealed uniqueness on overlaps; representative choices and mixed terminal traces; all reduced equations and BV conditions for one union witness; restriction equalities in precisely $r,\phi,m$; direct compilation of the changed dependency chain and standard axiom closure. |
| `ChristodoulouBV.theorem5_1` | 2026-10-17: reviewed against pp. 1172 and 1176; universal threshold, family-wide eventual bound, and absence of an agreement clause were made explicit. Compatibility and continuation remained proof obligations. | Initial seal audit **FAIL**, 2026-10-18, solely for four local elaboration-budget overrides. After their removal, independent re-audit **PASS**, 2026-10-18; sealed status confirmed. | No frozen statement or provider change during that repair; explicit use of the mass-ratio bound and $(5-2\sqrt6)/3$; uniform bounds before cutoffs, joined derivatives and seam signs, local construction and gluing; exact-type application, build, directive scan, and standard axiom closure. |
| `ChristodoulouBV.theorem6_1_6_2_exists` | 2026-10-17: reviewed against pp. 1179 and 1183; shared threshold and arbitrary BV data retained; missing image-area conclusions identified and explicitly deferred under D9. | Independent pre-seal audit **PASS**, 2026-10-19; author-approved seal and independent post-seal audit **PASS**, 2026-10-19. | Exact closed type; shared constant before both data quantifiers; internally constructed smooth approximants and limit fields; exact trace at every positive initial point without right continuity; all four BV item-4 limits for the same final witness; use of sealed Theorems 3.1 and 5.1; build, directive scans, and standard axiom closure. |

The existence audits also checked the adopted Lemma 6.2 lower-integral argument, the distinction between pointwise section variation and analytic variation measures, and the endpoint and sign corrections used by the proof. Measurability for the concrete functionals was established separately. The lower-integral inequality was not used to infer the false printed L¹ conclusion. The [errata](ERRATA.md) describe these mathematical corrections and the Lean counterexamples.

## Axiom audit and reproducibility

The release pins `leanprover/lean4:v4.35.0-rc3` and Mathlib `7d6757bc18680044fc0ff6efc8ee20494b408556`. Run:

```sh
lake env lean scripts/AxiomAudit.lean
```

For **each** of `ChristodoulouBV.theorem3_1_unique`, `ChristodoulouBV.theorem3_1_extend`, `ChristodoulouBV.theorem5_1`, and `ChristodoulouBV.theorem6_1_6_2_exists`, the expected dependency list is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard propositional extensionality, classical choice, and quotient soundness axioms. The audit is transitive through the proof dependencies. There is no admitted proof or project-specific axiom in these four theorem closures. The seal audits checked this independently, and the post-seal existence audit rechecked all four exports together.

With the dependencies available, `scripts/check.sh` runs the build, compares the axiom output, verifies the frozen-file checksums, and checks the library modules. The [README build instructions](README.md#build-and-audit) include the Mathlib cache command for a fresh checkout. This is a standalone package with its own `.lake/packages` directory.

## Limits of certification

The certified theorem statements are the frozen Lean statements, with the approved reduced-system definitions. In particular:

- Theorem 3.1 asserts equality and union preservation of $r,\phi,m$, without pointwise equality of the auxiliary fields or a conformal factor.
- Theorem 5.1 assumes a family and concludes existence with the prescribed initial data, without an agreement clause with that family.
- Theorems 6.1 and 6.2 are certified only for their joint existence fragment. Under D9, the four printed multiplicity-counted image-area finiteness conclusions in each theorem are deferred. Analytic area estimates proved internally do not certify those image-area statements.
- Sections 2, 7, and 8 are outside scope. A derivation of the reduced system from the four-dimensional Einstein equations is also outside the certified statements.

Kernel checking verifies proofs of these precise statements. Their relationship to the paper depends on the explicit definitions, approved interpretations, and source comparisons summarized here; it is not a certification of every statement or argument in the paper.
