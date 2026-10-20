# Christodoulou 1993 in Lean 4

A Lean 4 formalization of selected results from D. Christodoulou, *Bounded variation solutions of the spherically symmetric Einstein-scalar field equations*, Communications on Pure and Applied Mathematics **46** (1993), 1131–1220. The library proves the uniqueness and union-extension parts of Theorem 3.1, the C¹ continuation criterion of Theorem 5.1, and the joint small-data existence part of Theorems 6.1 and 6.2 for the reduced system in double-null coordinates. The statements use the definitions and explicit interpretive choices described below; the finite image-area conclusions of Theorems 6.1 and 6.2 are deferred.

Formalized by the Einstein–Scalar Field Collaboration, with assistance from Claude Code and OpenAI Codex.

## Formalized statements

The four public theorem declarations are in `ChristodoulouBV/Frozen/`. The following descriptions follow their Lean statements. A solution means the integrated reduced-system predicate defined in this repository, with the BV or C¹ conditions indicated below.

**Theorem 3.1, uniqueness (p. 1148).** If two BV solutions on domains of development $U_1,U_2$ have the same initial radius $r$ and scalar field $\phi$ at every common point $(0,v)$, then their $r,\phi,m$ agree at every point of $U_1\cap U_2$.

Lean: `ChristodoulouBV.theorem3_1_unique` in [Theorem3_1Unique.lean](ChristodoulouBV/Frozen/Theorem3_1Unique.lean).

**Theorem 3.1, extension (p. 1148).** Under the same hypotheses, there is a BV solution on $U_1\cup U_2$ whose $r,\phi,m$ agree with those of each original solution on its domain.

Lean: `ChristodoulouBV.theorem3_1_extend` in [Theorem3_1Extend.lean](ChristodoulouBV/Frozen/Theorem3_1Extend.lean).

The paper's single theorem is thus split into two declarations. Its coincidence conclusion is represented by equality of $r,\phi,m$. The frozen statements do not assert pointwise equality of $\lambda,\nu,\alpha,\beta$ or of a conformal factor: at BV regularity the auxiliary fields are determined only up to representatives on null sets along characteristic lines.

**Theorem 5.1, C¹ continuation (p. 1172).** Write

$$
D_b=\lbrace (u,v):0\le u\lt v\lt b\rbrace ,\qquad
O_{a,b}=\lbrace (u,v):a\lt u\lt v\lt b\rbrace .
$$

There is a universal $\varepsilon_1\gt 0$ with the following property. Let $\alpha_0:\mathbb R\to\mathbb R$ be C¹ on $[0,\infty)$ and let $v_{\ast}\gt 0$. Suppose a family $S(v_0)$ supplies a C¹ solution on $D_{v_0}$ for each $0\lt v_0\lt v_{\ast}$, with $r(0,v)=v/2$ and $\alpha(0,v)=\alpha_0(v)$ for $0\lt v\lt v_0$. If there are $0\lt u_0\lt v_{\ast}$ and $\eta\lt\varepsilon_1$ such that

$$
\frac{2m_{S(v_0)}(u,v)}{r_{S(v_0)}(u,v)}\le\eta
\quad\text{for every }0\lt v_0\lt v_{\ast},\quad
(u,v)\in O_{u_0,v_{\ast}}\cap D_{v_0},
$$

then there are $v_1\gt v_{\ast}$ and a C¹ solution on $D_{v_1}$ with those same initial radius and $\alpha$ data for every $0\lt v\lt v_1$.

Lean: `ChristodoulouBV.theorem5_1` in [Theorem5_1.lean](ChristodoulouBV/Frozen/Theorem5_1.lean).

The hypotheses are a family, without an additional compatibility premise. The paper's limiting supremum is encoded as the displayed eventual bound over all family members. The frozen conclusion asserts existence with the prescribed data; it has no agreement clause with the original family. The proof chooses $\varepsilon_1=(5-2\sqrt6)/3$, the value used on p. 1176.

**Theorems 6.1 and 6.2, joint existence (pp. 1179 and 1183).** There is one $\varepsilon_{\ast}\gt 0$ such that, for any $\alpha_0:\mathbb R\to\mathbb R$ with pointwise total variation $\operatorname{TV}_{(0,\infty)}(\alpha_0)\lt\varepsilon_{\ast}$:

- if $\alpha_0$ is C¹ on $[0,\infty)$, there is a global C¹ solution;
- for arbitrary such $\alpha_0$, there is a global BV solution.

Both solutions are on $\lbrace (u,v):0\le u\lt v\rbrace $ and satisfy $r(0,v)=v/2$ and $\alpha(0,v)=\alpha_0(v)$ at every $v\gt 0$. The BV branch has no right-continuity hypothesis, and its trace is an equality of the given point values, rather than an almost-everywhere equality. The two existence claims share the same constant, as in the paper. The proof uses $\varepsilon_{\ast}=10^{-80}$, defined by `ChristodoulouBV.epsilonChosen` in [C1Bootstrap.lean](ChristodoulouBV/Existence/C1Bootstrap.lean); the frozen statement only asserts a positive shared constant.

Lean: `ChristodoulouBV.theorem6_1_6_2_exists` in [Theorem6_1_6_2Exists.lean](ChristodoulouBV/Frozen/Theorem6_1_6_2Exists.lean).

This is the existence fragment. The four multiplicity-counted image-area conclusions in each of the two printed theorems are omitted under ruling D9.

## Definitions and scope

The names in this table are in the `ChristodoulouBV` namespace. All are frozen definitions; the links give their complete clauses.

| Lean name | Meaning |
| --- | --- |
| [`Fields`](ChristodoulouBV/Frozen/Fields.lean) | Seven total real functions $r,\phi,m,\lambda,\nu,\alpha,\beta$ of $(u,v)$; solution predicates constrain their values on the domain. |
| [`Fields.theta`](ChristodoulouBV/Frozen/FieldsTheta.lean), [`Fields.zeta`](ChristodoulouBV/Frozen/FieldsZeta.lean) | Derived amplitudes $\theta=\alpha-\lambda\phi$, $\zeta=\beta-\nu\phi$. The mass ratio $2m/r$ is written inline in the frozen equations. |
| [`IsSolution`](ChristodoulouBV/Frozen/IsSolution.lean) | Domain of development; ten integrated equations from (1.12), (1.14), (1.15), (1.17), (1.18) on every contained closed null segment; outgoing axis limits $r,m\to0$; $r,\lambda\gt0$; a positive pointwise conformal witness satisfying (1.5). |
| [`IsBVSolution`](ChristodoulouBV/Frozen/IsBVSolution.lean) | `IsSolution`, a uniform lower bound for $\nu$, a uniform positive lower bound for $\lambda$, and the six BV conditions of pp. 1146–1147, with global uniform constants and no right-continuity convention. |
| [`IsC1Solution`](ChristodoulouBV/Frozen/IsC1Solution.lean) | `IsSolution`, the same expansion bounds, and C¹ regularity of $\lambda,\nu,\phi,\theta,\zeta$ on the closure of the domain. |
| [`globalDomain`](ChristodoulouBV/Frozen/GlobalDomain.lean) | $\lbrace (u,v):0\le u\lt v\rbrace $. |
| [`openDevelopment`](ChristodoulouBV/Frozen/OpenDevelopment.lean) | $O_{a,b}=\lbrace (u,v):a\lt u\lt v\lt b\rbrace $. |
| [`developmentWithInitialEdge`](ChristodoulouBV/Frozen/DevelopmentWithInitialEdge.lean) | $D_b=\lbrace (u,v):0\le u\lt v\lt b\rbrace $. |
| [`causalPast`](ChristodoulouBV/Frozen/CausalPast.lean) | $J^-(a,b)=\lbrace (u,v):0\le u\le a,\ u\lt v\lt b\rbrace $, with the printed open upper endpoint in $v$. |
| [`IsDomainOfDevelopment`](ChristodoulouBV/Frozen/DomainOfDevelopment.lean) | A subset of $\lbrace 0\le u\lt v\rbrace $ containing the causal past of each of its points; no openness or connectedness requirement. |
| [`outSeg`](ChristodoulouBV/Frozen/OutSeg.lean), [`inSeg`](ChristodoulouBV/Frozen/InSeg.lean) | Closed outgoing and incoming null segments. |
| [`IntervalPrimitive`](ChristodoulouBV/Frozen/IntervalPrimitive.lean) | An interval-integrable density and the exact endpoint increment identity for its primitive. |
| [`adjacentAxis`](ChristodoulouBV/Frozen/AdjacentAxis.lean), [`AxisVanishingVariation`](ChristodoulouBV/Frozen/AxisVanishingVariation.lean) | Diagonal points in the closure of the domain, and the four small-variation limits in BV item 4, with the printed ranges of the parameter $\delta$. |

The global domain and finite developments include $u=0$ so that initial data lie in the domain; the printed open developments do not include that edge. The axis itself is excluded. Axis conditions use limits along outgoing slices of the domain; at a terminal corner with an empty outgoing slice these conditions can be vacuous. Total variation is pointwise variation on the indicated slices, using Mathlib's `eVariationOn`.

The formalization starts from the reduced equations, rather than a derivation from the four-dimensional Einstein equations. Sections 2, 7, and 8 are outside the release scope. General analysis and area estimates used in the existence proofs are included, but they do not supply the deferred multiplicity-counted image-area conclusions as sealed theorems. See [the approved interpretive rulings](docs/AUTHOR-RULINGS.md) for these choices.

Lemma 6.2 is used in its lower-integral form, `ChristodoulouBV.lemma6_2_lintegral`. Lean counterexamples refute its printed L¹ conclusion (`ChristodoulouBV.lemma6_2_L1_conclusion_false`) and the lower-semicontinuity step in its proof (`ChristodoulouBV.lemma6_2_lsc_step_false`). These corrections and other departures from the printed arguments are documented in [ERRATA.md](ERRATA.md) and [ERRATA.pdf](ERRATA.pdf).

## Repository layout

The standalone Lake package is named `ChristodoulouBV`. Its 971 library modules comprise the import closure of the four sealed theorems together with the modules containing declarations cited in the errata.

| Location | Contents |
| --- | --- |
| `ChristodoulouBV/Frozen/` | 20 sealed files: 16 definitions and four theorem declarations. |
| `ChristodoulouBV/Provider/` | Four proof implementations closing the frozen theorem declarations. |
| `ChristodoulouBV/Uniqueness/` | Uniqueness, union extension, and continuation arguments. |
| `ChristodoulouBV/Existence/` | Global C¹ and BV constructions and supporting limit arguments. |
| `ChristodoulouBV/C1Solution/`, `ChristodoulouBV/BVSolution/` | Results about the two solution classes. |
| `ChristodoulouBV/AreaEstimates/` | Analytic estimates used by the proofs. |
| `ChristodoulouBV/ForMathlib/` | General analysis, including BV functions, Stieltjes calculus, Helly selection, Gronwall estimates, and Goursat ODEs. |
| `ChristodoulouBV.lean` | Library import entry point. |
| `scripts/`, `.github/workflows/ci.yml` | Build, axiom, frozen-file, and module checks; a manually dispatched GitHub Actions workflow. |

## Build and audit

The pinned toolchain is `leanprover/lean4:v4.35.0-rc3`; Mathlib is pinned to `7d6757bc18680044fc0ff6efc8ee20494b408556`. The package has its own `.lake/packages` dependencies. With elan and Lake available, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
scripts/check.sh
```

The first command retrieves the Mathlib cache. The final command runs the build, checks the axiom output, verifies all frozen-file hashes, and checks the library modules. The expected axiom output is:

```text
'ChristodoulouBV.theorem3_1_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ChristodoulouBV.theorem3_1_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
'ChristodoulouBV.theorem5_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ChristodoulouBV.theorem6_1_6_2_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard propositional extensionality, classical choice, and quotient soundness axioms. The four results have no admitted proofs or additional axioms.

## Frozen statements and certification

The definitions and theorem statements were independently reviewed and approved before the proofs were completed. Definitions were frozen as whole files. Each theorem retained its frozen statement and was sealed with a single line of the form `by exact ChristodoulouBV.Provider.theorem3_1_unique`, referring to its corresponding implementation. Independent seal audits checked statement identity, expanded hypotheses, proof dependencies, and axiom closure.

[CERTIFICATION.md](CERTIFICATION.md) records all 20 hashes and summarizes the audit history and its limits. The frozen files are byte-identical to the sealed state, so their original docstrings retain internal identifiers and references to development documents that are not public. Those annotations are intentionally preserved; comments outside the frozen files have been cleaned for release.

## Citation and license

For the formalization, use [CITATION.cff](CITATION.cff). Cite the underlying mathematics as:

> D. Christodoulou, *Bounded variation solutions of the spherically symmetric Einstein-scalar field equations*, Communications on Pure and Applied Mathematics **46** (1993), 1131–1220.

The code is licensed under [Apache-2.0](LICENSE). The paper is copyrighted by its publisher and is not included in this repository.
