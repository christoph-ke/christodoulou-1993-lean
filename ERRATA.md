# Errata to Christodoulou (1993), found by a Lean formalization

D. Christodoulou, *Bounded variation solutions of the spherically symmetric
Einstein-scalar field equations*, Comm. Pure Appl. Math. **46** (1993), 1131–1220.

**Scope.** This document records false statements or proof steps, substantive
missing arguments, and misprints affecting mathematical content encountered in
formalizing Sections 1 and 3–6. The numbering ERR-01–ERR-35 is stable. ERR-11 is a
clarification of an explicitly stated normalization, not a defect; ERR-12 is a
comparison with a later paper; ERR-34 records observations in Section 8, outside
the formalization's scope. Routine typographical slips are not enumerated here.
All page numbers are journal pages.

Theorem 3.1 (uniqueness and extension), Theorem 5.1, and the existence parts of
Theorems 6.1 and 6.2 are proved in Lean, sealed, and independently audited. Their
release declarations are `ChristodoulouBV.theorem3_1_unique`,
`ChristodoulouBV.theorem3_1_extend`, `ChristodoulouBV.theorem5_1`, and
`ChristodoulouBV.theorem6_1_6_2_exists`. **No defect below changes a main theorem
as formalized.** The precise readings and the deferred finite-area conclusions
are stated in the appendix.

The public evidence levels are:

- **Lean:** a sorry-free declaration in this repository proves the corrected
  form or refutes the printed one; the declaration is named in the entry.
- **reviewed:** an independent written review confirms the observation, without
  Lean evidence for that observation.
- **noted:** observed during the formalization, without independent written
  review of the observation.

A Lean proof of a correction does not by itself refute the printed statement.
Entries distinguish these kinds of evidence. An **Affects** field identifies the
argument needing repair, rather than an outstanding obligation in the released
main theorems. Analytic area measures used in proofs should be distinguished
from the paper's multiplicity image areas; see the appendix.

## False statements and proof steps

### ERR-01 — Lemma 6.2: the integrability conclusion is false

**Location:** p. 1189, Lemma 6.2 and the end of its proof.

The hypotheses give no uniform bound on the integrals of the nonnegative
functions $F_n$. Thus Fatou's lemma gives an inequality in $[0,\infty]$, not
$F\in L^1(0,1)$. There are data satisfying the hypotheses with every $F_n$
integrable but $\int^- F=\infty$. The corrected conclusion is

$$
\int^- F\leq\liminf_{n\to\infty}\int^- F_n.
$$

Here $\int^-$ is the lower Lebesgue integral; no measurability of $F$ is asserted.
Finiteness in applications must be obtained from the uniform smooth estimates.

**Status:** **Lean**, correction:
`ChristodoulouBV.lemma6_2_lintegral`; counterexample to the printed integrability
claim: `ChristodoulouBV.lemma6_2_L1_conclusion_false`.

**Affects:** the area-limit argument in the proofs of Theorems 6.1/6.2.

### ERR-02 — Lemma 6.2: the lower-semicontinuity step fails

**Location:** p. 1189, proof of Lemma 6.2.

The essential bound on a rectangle controls almost every section, not every
section outside the specified countable set. It therefore does not justify the
claimed dominated-convergence argument at each such point. A counterexample has
$y_n\in S$, $y_n\to y_0\notin S$, $F(y_n)=0$, and $F(y_0)=1$, so lower
semicontinuity fails. The example's $F$ is measurable: it refutes the proof step,
not measurability itself. Measurability from the printed hypotheses alone is
neither proved nor refuted here. Use the lower-integral conclusion of ERR-01 and
establish measurability separately for concrete applications.

**Status:** **Lean**, counterexample:
`ChristodoulouBV.lemma6_2_lsc_step_false`; corrected conclusion:
`ChristodoulouBV.lemma6_2_lintegral`.

**Affects:** the area-limit argument in the proofs of Theorems 6.1/6.2.

### ERR-03 — Continuity of area from above requires finiteness

**Location:** pp. 1156–1157, opening area discussion in Section 4.

Nested domains with empty intersection need not have areas tending to zero if
all their areas are infinite. For example, take the identity map on the tails
$\lbrace (u,v):0\lt u\lt1,\ v\gt n\rbrace $. Add the premise that the first domain has
finite area. For the Section 6 applications, finiteness must precede the
shrinking-tail argument.

**Status:** **Lean** for the finite analytic-area correction:
`ChristodoulouBV.analytic_area_continuity`. The counterexample to the unrestricted
claim is **reviewed**, without a separate Lean refutation.

**Affects:** area tails in the proofs of Theorems 6.1/6.2; the multiplicity
image-area conclusions remain deferred.

### ERR-04 — The strict approximation bound fails when the variation is zero

**Location:** p. 1184, smooth approximation of the data for Theorem 6.2.

The printed $D_n\lt\min\lbrace 2D,\varepsilon_{\ast}\rbrace $ is impossible for constant data,
where $D=0$. The approximation can instead satisfy $D_n\leq D$ and
$D_n\lt\varepsilon_{\ast}$. Consequently $D_n\lt2D$ when $D\gt0$, while $D_n=0$
when $D=0$.

**Status:** **Lean**: `ChristodoulouBV.smooth_data_below_epsilon` (arbitrary
point values) and
`ChristodoulouBV.smooth_data_below_epsilon_of_right_continuous`.

**Affects:** the constant-data case in the proof of Theorem 6.2.

## Substantive missing arguments

### ERR-05 — Local existence at the axis needs a construction

**Location:** p. 1180, proof of Theorem 6.1; p. 1179, final continuation step in
the proof of Theorem 5.1.

Local $C^1$ existence is invoked without a proof or reference. The boundary
$r=0$ is singular in the displayed equations, so this requires an axis-specific
argument. The formalization supplies a quantitative Picard construction using
$r$ and $r\phi$, reconstructs the fields, and propagates the mass constraint.
It also proves a lifetime uniform in a compact edge's $C^1$ bounds.

**Status:** **Lean**:
`ChristodoulouBV.C1Solution.exists_local_c1_solution` and
`ChristodoulouBV.C1Solution.exists_axis_triangle_solution_prescribed_compact`.

**Affects:** the proofs of Theorems 5.1 and 6.1.

### ERR-06 — The comparison estimates depend on BV representatives

**Location:** pp. 1149–1155, the comparison norms and (3.13)–(3.21).

The BV definition imposes no representative convention. Equal initial $r,\phi$
give equal initial derivative fields only almost everywhere. Changing $\lambda$
on one incoming null line can preserve the BV equations and $r,\phi,m$ while
invalidating the printed pointwise comparison estimate (3.13). The suprema used
there are therefore not representative-independent. Unqualified pointwise
coincidence of all fields, including the conformal factor, has the same issue.

The formal proof uses a common conull set of initial coordinates, finite
truncations, almost-everywhere transport identities, and recovery of $r,\phi,m$
from continuous primitives.

**Status:** **Lean** for the corrected uniqueness proof:
`ChristodoulouBV.Uniqueness.ComparisonData.goodV_norms_zero`,
`ChristodoulouBV.Uniqueness.ComparisonData.pointwise_of_goodV_norms_zero`, and
`ChristodoulouBV.theorem3_1_unique`. The representative counterexample is
**reviewed**, without a separate Lean refutation.

**Affects:** the proof and interpretation of Theorem 3.1; its formalized
conclusion concerns $r,\phi,m$.

### ERR-07 — The uniform incoming derivative bound is not proved

**Location:** p. 1174, definition of $D'(u_0)$; its uses in (5.3), (5.10), and
(5.12), pp. 1174–1177.

Individual $C^1$ solutions give bounds only on finite cutoffs. Finiteness of
$D'(u_0)$ uniformly up to the terminal parameter requires an additional estimate;
a direct bootstrap can be circular through its assumed lower bound for $1-\mu$.
The formal proof first bounds the flux without dividing by $1-\mu$, then obtains
lower expansion and mass-gap bounds and applies Gronwall to the derivative.

**Status:** **Lean**:
`ChristodoulouBV.Uniqueness.incoming_weighted_bound_before_star`.

**Affects:** the proof of Theorem 5.1.

### ERR-08 — Bounded derivatives do not supply a continuous terminal corner trace

**Location:** p. 1173 and p. 1177, after (5.12).

The asserted extension as a $C^1$ solution includes the closure and the terminal
axis corner. The displayed derivative bounds alone do not prove continuity of
the first derivatives there. The formal proof constructs off-axis terminal
traces by parameter-dependent integral equations and crosses the corner using
uniform local axis existence and $C^1$ uniqueness.

**Status:** **Lean**:
`ChristodoulouBV.Uniqueness.exists_uniform_alphaPrime_bound_before_star`,
`ChristodoulouBV.Uniqueness.exists_offAxisTerminalC1Packet`, and the extension in
ERR-09.

**Affects:** the proof of Theorem 5.1.

### ERR-09 — Strip continuation and gluing need additional justification

**Location:** pp. 1177–1179, continuation beyond $v_{\ast}$.

The strip argument invokes local continuation, a common strip width, corner
compatibility, and gluing without supplying the needed theorems. A weighted
bound on one derivative does not control all first derivatives. The formal proof
uses an alternative construction: a lower cover with a full $C^1$ terminal seam,
a uniform-lifetime axis triangle, identification by uniqueness, and gluing
across the vertical seam. The paper's strip estimates are available but are not
used in this construction.

**Status:** **Lean**:
`ChristodoulouBV.Uniqueness.exists_routeB_extension`, yielding
`ChristodoulouBV.theorem5_1`.

**Affects:** the proof of Theorem 5.1.

### ERR-10 — The coefficient in (5.21) needs a sharper mass estimate

**Location:** p. 1179, mass increment estimate and (5.21).

The preceding coarse mass estimate yields a coefficient $8/9$ after
multiplication by $2/r$, rather than the displayed $4/9$. The latter follows
from the sharper estimate
$\Delta m\leq M^2(r^2-r_{\ast}^2)/9$, together with $m(u,v_{\ast})\geq0$.
This sharper estimate is not printed.

**Status:** **Lean**:
`ChristodoulouBV.Uniqueness.strip_mass_increment_sharp` and
`ChristodoulouBV.Uniqueness.strip_mass_ratio_increment_le`.

**Affects:** the paper's strip proof, which the formal proof of Theorem 5.1
replaces as described in ERR-09.

### ERR-11 — Scalar normalization in Section 4 (clarification, not a defect)

**Location:** pp. 1157 and 1159, the scalar-shift normalization and the estimate
leading to (4.2a).

The paper explicitly uses scalar-shift invariance on p. 1157 to set
$\phi(0,0)=0$ before deriving the amplitude estimate on p. 1159. The bound
$|\alpha(0,v)|\leq D$ uses this declared normalization. To apply the estimate to
uncentered data, first center the scalar field and then shift the constructed
solution back; the variation is unchanged. The entry is kept, under its stable
number, because later uses of the Section 4 estimates must perform this centering.

**Status:** **Lean** for the paper's stated reduction:
`ChristodoulouBV.s4_initial_alpha_abs_le` (with its explicit centering premise)
and `ChristodoulouBV.scalar_shift`. This is not a counterexample and not a
missing premise in the printed argument.

**Affects:** reuse of the Section 4 estimates with uncentered data; no
correction to the paper is needed.

### ERR-12 — Theorem 6.2 does not state the quantitative conclusion cited later

**Location:** p. 1183, Theorem 6.2; compare Luk–Oh, Theorem 5.12, (5-29)–(5-31),
and Remark 5.13, p. 1633.

The printed theorem asserts global BV existence and finite image areas. It does
not explicitly state the bounds $1/3\leq\lambda\leq1/2$,
$1/3\leq-\nu\leq2/3$, $2/3\leq1-\mu\leq1$, the three-term linear variation
bounds with one universal constant, or right-continuous representatives that
Luk–Oh attribute to it. Extracting this stronger quantitative statement requires
additional bookkeeping, including scalar-shift invariance and BV quotient
estimates. This observation concerns the difference between the two stated
conclusions; it is not a counterexample to either existence assertion.

**Status:** **noted** for this comparison of statements.

**Affects:** use of Theorem 6.2 as a citation for the stronger quantitative
statement; no change to the formalized main theorems.

Reference: J. Luk and S.-J. Oh, Anal. PDE **8** (2015), 1603–1674,
Theorem 5.12 and Remark 5.13.

### ERR-13 — The area-limit applications require premises to be checked

**Location:** pp. 1190–1192, (6.4a)–(6.6), applications of Lemmas 6.1 and 6.2.

The argument does not establish the required differentiability of the limiting
section, derivative convergence, one countable exceptional set valid for every
section coordinate, integrability of the approximating functionals, or the
interchange of truncation suprema and lower limits. The formal proof supplies
absolutely continuous and almost-everywhere versions, regularizes the pointwise
primitives, proves measurability for the actual functionals, and exhausts the
cutoffs using uniform bounds. Coordinate factors are addressed in ERR-28.

**Status:** **Lean**:
`ChristodoulouBV.area_lsc_regularization`,
`ChristodoulouBV.common_section_measurability`,
`ChristodoulouBV.area_chart_section_lintegral_le_liminf`, and
`ChristodoulouBV.measure_global_le_of_areaOpenCutoff_bound`.

**Affects:** the limiting area estimates used to verify the BV conditions in
Theorem 6.2; this does not assert the deferred image-area conclusions.

### ERR-14 — The moving wedges are not nested

**Location:** p. 1182, area tails immediately before (6.1).

The rectangles $(0,u)\times(u,1)$ are not nested as $u$ increases. Continuity
from above therefore cannot be applied to them directly. Contain them in the
nested tails of the full triangle on which $v\gt u$, and first prove that the
full triangle has finite analytic area, as required by ERR-03.

**Status:** **Lean**: `ChristodoulouBV.s6_area_tail_geometry` and
`ChristodoulouBV.s6_endpoint_tails`.

**Affects:** the terminal-tail argument in the proof of Theorem 6.1 and the
smooth-solution construction used for Theorem 6.2.

### ERR-15 — Representative changes must preserve the pointwise equations

**Location:** pp. 1196–1197, one-sided replacements of $\nu$ and $\beta$.

The existence of compatible traces on a common collection of lines, and the
preservation of transport equations, mass and scalar-radius primitives, signs,
and pointwise variation conditions, need proof. The formal construction chooses
the incoming representatives simultaneously, proves stability of all primitive
equations, and verifies the axis conditions for the same fields. It retains the
prescribed outgoing data at every positive initial coordinate.

**Status:** **Lean**: `ChristodoulouBV.representative_stability`,
`ChristodoulouBV.incoming_right_fields_item4`, and
`ChristodoulouBV.representatives_incoming_corner`.

**Affects:** the BV witness in Theorem 6.2.

### ERR-16 — Other missing arguments in Section 3

**Location:** pp. 1147–1155, Theorem 3.1 and its proof, including (3.1a,b) and
the comparison estimates.

The following arguments are used without full justification: transferring the
signs and mass-gap inequalities to BV solutions; taking axis limits in the
logarithmic identities (3.1a,b); affine rescaling of BV solutions; finiteness of
the mass comparison norms before absorption; regular Goursat uniqueness away
from the axis; and gluing extensions with compatible BV representatives.

**Status:** **Lean**. Corresponding declarations include
`ChristodoulouBV.IsBVSolution.mass_ratio_bounds`,
`ChristodoulouBV.IsBVSolution.eq3_1a`,
`ChristodoulouBV.IsBVSolution.eq3_1b`,
`ChristodoulouBV.Uniqueness.rescaled_isBVSolution`,
`ChristodoulouBV.Uniqueness.ComparisonData.Gamma_uniform_bound`,
`ChristodoulouBV.Uniqueness.ComparisonData.GammaStar_uniform_bound`,
`ChristodoulouBV.Uniqueness.regular_rectangle_unique`, and
`ChristodoulouBV.Uniqueness.glued_isBVSolution`. The completed rescaling and
continuation arguments are used by `ChristodoulouBV.theorem3_1_unique` and
`ChristodoulouBV.theorem3_1_extend`.

**Affects:** the uniqueness and extension proofs of Theorem 3.1.

### ERR-17 — Other missing arguments in Sections 1, 4, and 5

**Location:** pp. 1137–1138, (1.14)–(1.18); pp. 1162–1164, (4.7)–(4.11);
pp. 1172–1177, Theorem 5.1 and (5.2)–(5.12).

Passing between the full and reduced systems requires nonvanishing of
$1-\mu$. The formalization takes the reduced system as its solution equations
and proves the needed signs separately. The commutation of mixed derivatives
used in Sections 4 and 5 needs regularity arguments. Treating a family as one
solution requires compatibility, the $C^1$-to-BV implication, and agreement of
initial scalar traces. Finally, terminal suprema must first be taken on finite
cutoffs, before traces or uniform bounds are available.

**Status:** **Lean** for these supplied sign, regularity, compatibility, and
cutoff arguments:
`ChristodoulouBV.Uniqueness.nu_neg_of_c1_domain`,
`ChristodoulouBV.Uniqueness.alphaPrime_deriv_u`,
`ChristodoulouBV.Uniqueness.family_fields_eq_on_common_development`,
`ChristodoulouBV.IsC1Solution.isBVSolution_development`, and
`ChristodoulouBV.Uniqueness.weightedSup_self_bound`.
The choice of reduced equations is an encoding convention, not a claim here of
a separate formal equivalence theorem for the full system.

**Affects:** the proofs of Theorems 5.1 and 6.1.

### ERR-18 — Other missing arguments in Section 6

**Location:** pp. 1180–1181, bootstrap; pp. 1184–1187, approximation and uniform
bounds; pp. 1192–1193, BV transport identities (6.7)–(6.12).

The bootstrap needs a short initial interval and a first-exit argument for
supremum-defined quantities. Smooth approximation must preserve arbitrary
point values, including values at jumps. Uniform amplitude bounds need a datum
offset: variation alone cannot bound constant data. Finally, the passage to BV
transport and ratio estimates requires Stieltjes product and jump calculus.
The formal proof supplies these arguments, keeping the amplitude offset out of
the universal variation constants.

**Status:** **Lean**: `ChristodoulouBV.bootstrap_start`,
`ChristodoulouBV.s6_exists_short_cone_sourceZ`,
`ChristodoulouBV.exists_smooth_approx_arbitrary_values`,
`ChristodoulouBV.uniform_smooth_bounds_for_sequence`,
`ChristodoulouBV.bv_stieltjes_transport`, and
`ChristodoulouBV.bv_ratio_bridge`. The bootstrap continuation is completed in
`ChristodoulouBV.theorem6_1_6_2_exists`.

**Affects:** the proofs of Theorems 6.1/6.2.

## Misprints affecting mathematical content

### ERR-19 — The sign in (3.12)

**Location:** p. 1152, (3.12).

The incoming coefficient $\mu_i\nu_i/((1-\mu_i)r_i)$ is nonpositive. The printed
upper bound on its integral is therefore vacuous; the comparison estimate needs
the upper bound on the negative of that integral:

$$
\sup_v\left[-\int_0^v
 \frac{\mu_i\nu_i}{(1-\mu_i)r_i}(u,v)\,du\right]\leq c\varepsilon.
$$

**Status:** **Lean**:
`ChristodoulouBV.Uniqueness.ComparisonData.incomingCoeff_integral_small`.

**Affects:** the proof of Theorem 3.1.

### ERR-20 — The incoming mass equation: denominator and integrating-factor reading

**Location:** p. 1154, incoming mass-difference equation and its integral formula.

The denominator multiplying $\zeta_2^2$ in the differential equation must be
$\nu_2$, rather than $\lambda_2$. With
$q=\zeta_2^2/(\nu_2r_1)\leq0$, the terminal-value equation
$\partial_u\Delta m=-q\Delta m+F/2$, $\Delta m(v,v)=0$, has solution

$$
\Delta m(u,v)=-\frac12\int_u^v
 \exp\!\left(\int_u^{u'}q(u'',v)\,du''\right)F(u',v)\,du'.
$$

The exponential is at most one. The typography of the inner limits on
pp. 1153–1154 is ambiguous: reading the incoming limits as $u$ to $u'$ requires
changing the printed minus sign; reading them in the opposite order gives the
same correct factor without a sign change. The denominator error is independent
of this ambiguity. The equation reference is corrected in ERR-21.

**Status:** **Lean** for the corrected equation and terminal formula:
`ChristodoulouBV.Uniqueness.ComparisonData.mass_in_difference_linear` and
`ChristodoulouBV.Uniqueness.ComparisonData.mass_in_terminal_formula`.
The ambiguity in the printed limits is **reviewed** and remains unresolved.

**Affects:** the incoming mass comparison in the proof of Theorem 3.1.

### ERR-21 — Crossed equation references in Section 3

**Location:** pp. 1147, 1148, 1153, and 1154.

The outgoing logarithmic identity on p. 1147 should cite (1.14b), (1.21b);
the incoming identity on p. 1148 should cite (1.14a), (1.21a).
The outgoing mass-difference equation on p. 1153 should cite (1.15b);
the incoming one on p. 1154 should cite (1.15a).

**Status:** **reviewed**. This is an observation about the printed references.

**Affects:** citation accuracy in the proof of Theorem 3.1.

### ERR-22 — The axis relation has the wrong sign

**Location:** p. 1161, axis traces in Section 4.

The relation is $\nu|_\Gamma=-\lambda|_\Gamma$. The printed equality without
the minus sign is incompatible with $r|_\Gamma=0$ and with the subsequent
relation $\beta|_\Gamma=-\alpha|_\Gamma$.

**Status:** **Lean**: `ChristodoulouBV.axis_traces`.

**Affects:** the Section 4 estimates used in the proofs of Theorems 6.1/6.2.

### ERR-23 — Signs in the incoming logarithmic correction

**Location:** pp. 1164–1165, the derivative of $f^{\ast}$ and (4.11b)–(4.13b);
p. 1169, (4.25a) and (4.26).

Writing $J$ for the $(u,v)$ Jacobian, the corrected derivative is

$$
\partial_v f^{\ast}=
 \frac{\lambda\zeta^2/\nu-\nu\theta^2/\lambda}{(1-\mu)r^2}
 +J(\phi,\alpha/\lambda).
$$

Both terms have the opposite sign to those printed. Consequently the quantity
inside the $v$ derivative in (4.11b) uses $+f^{\ast}$. The incoming residual in
(4.13a), (4.13b), the Jacobian algebra preceding (4.25a), and (4.25a) is
$\partial_u\log|\nu|-\mu\nu/((1-\mu)r)-f^{\ast}$.
The derivation of (4.26) uses this corrected residual; its displayed unsigned
area bound remains unchanged, as do the subsequent estimates. The correctly
signed outgoing residual in (4.12b) is unaffected.

**Status:** **Lean**: `ChristodoulouBV.sourceLogCorrectionStar_vertical_deriv`,
`ChristodoulouBV.eq4_11b_corrected`, `ChristodoulouBV.eq4_13b_corrected`,
`ChristodoulouBV.eq4_25a`, and `ChristodoulouBV.eq4_26`.

**Affects:** intermediate Section 4 identities used in the proofs of
Theorems 6.1/6.2.

### ERR-24 — Missing minus signs in (5.4), (5.6), and (5.9)

**Location:** p. 1174, (5.4), (5.6); p. 1176, (5.9).

The middle lines require $-\int_{u_0}^u r^{-1-\delta}\partial_u r\,du'$.
Without the minus sign they are nonpositive, since $\partial_u r=\nu\lt0$,
and cannot bound absolute values. The final bounds and coefficients are correct.

**Status:** **Lean** for the bounds using the correct signed integrals:
`ChristodoulouBV.Uniqueness.integralI₁_le_weightedSup`,
`ChristodoulouBV.Uniqueness.integralI₂_le_weightedSup`, and
`ChristodoulouBV.Uniqueness.integralI₃_le_weightedSup`.

**Affects:** the proof of Theorem 5.1.

### ERR-25 — The supremum before (5.10) needs a truncated domain

**Location:** p. 1176, immediately before (5.10).

Take the supremum over $\mathcal D(u_0,u_1,v_{\ast})$, first with finite terminal
cutoffs $t\lt v_{\ast}$. The printed full domain $\mathcal D(u_0,v_{\ast})$ gives a
supremum that may be infinite before absorption has proved a uniform bound.

**Status:** **Lean**: `ChristodoulouBV.Uniqueness.weightedSup_self_bound`.

**Affects:** the proof of Theorem 5.1.

### ERR-26 — The strip domain and the closing strict inequality

**Location:** p. 1177, (5.13); p. 1178, definition of $u_2$; p. 1179, closing
strip estimate.

In both (5.13) and the definition of $u_2$, the domain must be
$\mathcal D(u_0,u_1,v_{\ast}+\eta)$. The printed domain ending at $v_{\ast}$ does not
include the new strip. In the closing estimate on p. 1179 the relation should
be strict, $\sup_{U_\eta(u_2)}\mu\lt(\varepsilon+\varepsilon_1)/2$, rather
than equality, as required by the preceding strict bound.

**Status:** **reviewed** for these corrections to the strip argument.

**Affects:** the paper's strip proof, replaced in the formal proof of
Theorem 5.1 as described in ERR-09.

### ERR-27 — The exponent in the lower bound for the incoming expansion

**Location:** p. 1181, bound for $\inf\nu$ in the bootstrap argument.

The exponent must have the positive sign:
$\inf\nu\geq-\tfrac12\exp(cD^2)$.
The negative sign printed there would force $-\nu\lt1/2$ uniformly for
$D\gt0$, contrary to its corner limit $1/2$.

**Status:** **Lean** for the corrected bootstrap bound:
`ChristodoulouBV.s6_improve_null`; its proof obtains
$-\nu\leq\tfrac12\exp(CD^2)$ with positive $C$ before deriving the stated
uniform margin.

**Affects:** the proof of Theorem 6.1.

### ERR-28 — Missing coordinate factors in the area substitutions

**Location:** pp. 1190–1191, substitutions for (6.4a)–(6.4d).

The transformed section density must contain the signed derivative $v_x$ or
$u_x$ in both density terms. The transverse integration also contributes the
factor $a-\delta$. The absolute Jacobians are
$(a-\delta)^2(1-y)$ and $(a-\delta)^2y$ in the respective charts. Without
these factors, the section functional is not the claimed area density.

**Status:** **Lean**: `ChristodoulouBV.area_section_primitive_eq_physical`,
`ChristodoulouBV.areaUnitMap_abs_det`, and
`ChristodoulouBV.area_cutoff_chart_lintegral`.

**Affects:** the limiting area estimates in the proof of Theorem 6.2.

### ERR-29 — The shifted-edge term in (6.13a) is a residual variation

**Location:** p. 1194, (6.13a).

The right side cannot use the variation of the original datum $\alpha_0$.
Replacing it by the variation of $\alpha(a,\cdot)$ is still insufficient:
$\lambda(a,\cdot)$ is generally not constant on a shifted edge. Retain instead
the variation of the edge primitive of $d\alpha-\phi\,d\lambda$, as for the
logarithmic residual in (6.14a). This edge residual has vanishing variation on
the shrinking open interval, so (6.13b) and (6.15) follow.

**Status:** **Lean** for the corrected estimate and consequence:
`ChristodoulouBV.eq6_13a` and `ChristodoulouBV.eq6_13b`.
No Lean counterexample among full Einstein-scalar solutions is asserted here.

**Affects:** the axis variation conditions in the proof of Theorem 6.2.

### ERR-30 — The reference before (6.14a)

**Location:** p. 1194, immediately before (6.14a).

The cited equation should be (6.8a), rather than (6.8b); the argument is the
outgoing logarithmic residual estimate.

**Status:** **reviewed** for the printed cross-reference.

**Affects:** citation accuracy in the proof of Theorem 6.2.

### ERR-31 — The zero conclusion is missing in (6.15)

**Location:** p. 1194, (6.15).

Both displayed limits equal zero. Merely equating them, as printed, omits the
conclusion required for the axis variation condition and established by the
preceding residual estimates and smallness absorption.

**Status:** **Lean**: `ChristodoulouBV.eq6_15` proves both zero limits.

**Affects:** the axis variation conditions in the proof of Theorem 6.2.

### ERR-32 — The residual term is missing in (6.17b)

**Location:** p. 1195, (6.17b).

The integrand must be $|d\log|\nu|+g^{\ast}\,du|$, as in (6.17a), rather than the
variation of $\log|\nu|$ alone. It is this residual that the preceding
transport argument controls and the proof of (6.18) consumes.

**Status:** **Lean**: `ChristodoulouBV.eq6_17b`, with the corrected residual.

**Affects:** the incoming axis variation conditions in the proof of Theorem 6.2.

### ERR-33 — The final BV condition reference

**Location:** p. 1197, after the limit of $\alpha+\beta$ at the axis.

The limit verifies condition 6 of the BV definition on p. 1147, rather than
condition 4. Condition 4 concerns shrinking variation near the axis.

**Status:** **reviewed** for the printed cross-reference.

**Affects:** citation accuracy in the proof of Theorem 6.2.

### ERR-34 — Three sign observations in Section 8

**Location:** p. 1218, trapped-region bound for $r\lambda$; p. 1219, its
oscillation bound and the analogous bound for $r\nu$.

In the first and third bounds, delete the leading minus sign in front of the
factor $1-r/r_0$. As printed, the lower bound is positive although the quantity
being bounded is negative. In the second bound, insert a minus in front of
the right-hand factor $r\lambda$: the left side is nonnegative, whereas the
printed right side is negative.

**Status:** **noted**; these observations have no independent written review
and no Lean evidence.

**Affects:** Section 8, which is outside this formalization's scope.

### ERR-35 — The incoming area comparison must retain terminal-edge jumps

**Location:** p. 1195, (6.17a), and its use in (6.17b)–(6.18), pp. 1195–1196.

The incoming Stieltjes transport involves a half-open strip including its
terminal characteristic. A jump there can give the analytic area measure an
atom that the printed open triangle misses. Use the half-open triangle
$\lbrace a-\varepsilon\lt u\lt v\leq a\rbrace $ instead. For sufficiently small
$\varepsilon\gt0$ these sets lie in the global domain, have finite analytic
area, and decrease to the empty set. Their areas therefore tend to zero, giving
the required residual limits.

**Status:** **Lean** for the corrected estimate:
`ChristodoulouBV.eq6_17a`; continuity on these triangles:
`ChristodoulouBV.bv_analytic_area_incoming_half_open_triangle_tendsto`.
This correction does not claim a Lean counterexample to (6.17a) among full
Einstein-scalar solutions.

**Affects:** the incoming axis variation conditions in the proof of Theorem 6.2.

## Appendix: Readings and encoding choices (not defects)

- **Theorem 3.1.** Uniqueness is pointwise for the geometric and scalar
  quantities $r,\phi,m$. The derivative fields and conformal factor require
  representative qualifications; see ERR-06. The extension conclusion uses the
  same interpretation.
- **Theorems 6.1/6.2.** The release proves global $C^1$ and BV existence with
  the exact initial traces and one common positive smallness threshold. Their
  printed finite multiplicity image-area conclusions are deferred. The analytic
  area measures used internally to prove the BV conditions do not constitute
  those deferred conclusions.
- **Lemmas 6.1/6.2.** The section functional is the variation of the pointwise
  integration-by-parts primitive
  $G(x)=f(x)g(x)-f(0)g(0)-\int_0^x(gf'+h)$, and $L^\infty$ bounds are
  essential bounds. Lemma 6.2 is used only as
  $\int^-F\leq\liminf_n\int^-F_n$, with no measurability claim for $F$.
  The failed lower-semicontinuity step remains recorded in ERR-02. Measurability
  for concrete section functionals is proved separately.
- **Area in the BV proof.** A countably additive analytic area measure is
  obtained by integrating section variation measures. Pointwise closed-section
  variation and this measure can differ at jumps. Domination by the pointwise
  functional is used on open cutoffs; closed cutoffs are contained in larger
  open cutoffs before taking limits. These are proof choices, separate from the
  paper's image-area conclusions.
- **Initial data in Theorem 6.2.** There is no right-continuity premise. The
  initial trace of $\alpha$ is prescribed at every $v\gt0$, including arbitrary
  values at jumps. Choosing incoming representatives does not replace these
  outgoing data.
- **Domain and equations.** The global domain is $\lbrace (u,v):0\leq u\lt v\rbrace $,
  including the initial edge, with gauge $r(0,v)=v/2$. The solution predicates
  encode the reduced equations by interval primitive identities. The $C^1$
  regularity requirement is on the closure of the development domain.
- **Scope exclusions.** Sections 2, 7, and 8 are not formalized. ERR-34 is
  retained as an explicitly noted observation. Errors in the formalization's
  own preliminary arguments or administrative records are not paper errata.
