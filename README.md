# Additivity of classical communication

This project (**human written, AI-assisted**) focuses on studying when entangling codewords across independent uses of a quantum channel **cannot** increase the rate of classical communication. It accompanies the paper titled **“Classical communication over quantum channels: does entanglement help in nature?”**, [see the manuscript here](Manuscript.pdf).

A central open problem in this direction is to find an integer $`N\ge2`$ such that

```math
\mathcal C(\mathcal A)=\chi_{\max}(\mathcal A)
\quad\text{for every channel }\mathcal A:\mathbb M_d\to\mathbb M_d
\text{ with }d\le N,
```

while, for every $`d>N`$, there is an explicit channel $`\mathcal A:\mathbb M_d\to\mathbb M_d`$ satisfying

```math
\mathcal C(\mathcal A)>\chi_{\max}(\mathcal A).
```
See below for related definitions. I think the problem is far from being solves. To the best of the author's knowledge this N in [2. 2^{23}]. 

The progress in the manuscript is some incremental results:

| Channel class | Result | Manuscript |
| --- | --- | --- |
| All phase-covariant channels in a fixed basis, in arbitrary finite dimension | Strong Holevo additivity | Theorem 4.2 |
| Qubit-output channels with one coherent Kraus operator and commuting-output noise | Strong Holevo additivity  | Theorem 5.2 |
| All qubit-to-qubit channels | Strong Holevo additivity | Theorem 5.2 |
| All qubit-output channels with arbitrary input dimension | Remains open: beyond the class covered by Theorem 5.2 | Section 6 |

The common tool is the **Schur-weighted block entropy inequality** (Theorem 3.1), combined with the entropic criteria in Section 2. Strong Holevo additivity implies equality of classical capacity and single-use Holevo information.

## Repository guide

- [Lean/](Lean/) contains the verified Lean project, its build configuration, dependency licenses, and [verification record](Lean/verification.md).
- [Proofs/](Proofs/) contains mathematical proofs organized by the numbered results [in the manuscript](Manuscript.pdf).

## Contents

- [Problem statement](#capacity-problem-and-notation)
- [Entropic criteria for additivity](#entropic-criteria-for-additivity)
- [Schur-weighted block entropy inequality](#schur-weighted-block-entropy-inequality)
- [Strong additivity for phase-covariant channels](#strong-additivity-for-phase-covariant-channels)
- [Qubit-output channels and the all-qubit result](#qubit-output-channels-and-the-all-qubit-result)
- [Discussion and open directions](#discussion-and-open-directions)
- [Lean Formalization](#lean-formalization)
- [References](#references)
- [Citation](#citation)

## Classical capacity problem 

Can entangling the inputs across independent channel uses increase the rate of classical communication? This fundamental question in quantum information theory is more subtle than it first appears. We focus on establishing no-go result here, that is, no entanglement advantage.

All Hilbert spaces are finite dimensional, and a quantum channel is a completely positive, trace-preserving linear map. We write $`\mathbb{M}_d`$ for the complex $`d\times d`$ matrices and use logarithms to base two throughout.

For a channel $`\Phi`$, the optimal rate achievable with product-state codewords and collective decoding is its Holevo information:

```math
\chi_{\max}(\Phi)
=\max_{\{p_x,\rho_x\}}
\left[
S\left(\Phi(\bar\rho)\right)
-\sum_x p_x S\left(\Phi(\rho_x)\right)
\right],
\qquad
\bar\rho=\sum_xp_x\rho_x.
```

The maximum runs over finite ensembles of input states. For a state $`\rho`$, its von Neumann entropy is

```math
S(\rho)=-\mathrm{Tr}(\rho\log_2\rho).
```

Allowing entangled codewords gives the classical capacity through regularization:

```math
\mathcal{C}(\Phi)
=\lim_{n\to\infty}\frac{1}{n}
\chi_{\max}\left(\Phi^{\otimes n}\right).
```

See [Holevo](#references) and [Schumacher–Westmoreland](#references) for the coding theorems. 

We seek to characterize the channels satisfying $`\mathcal{C}(\Phi)=\chi_{\max}(\Phi)`$ and those satisfying $`\mathcal{C}(\Phi)>\chi_{\max}(\Phi)`$.

A channel $`\mathcal{A}`$ has **strongly additive Holevo information** if

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M})
```

for every finite-dimensional channel $`\mathcal{M}`$. In particular, strong additivity implies $`\mathcal{C}(\mathcal{A})=\chi_{\max}(\mathcal{A})`$.

## Entropic criteria for additivity

We review two entropic criteria below.

### Standard criterion: preserve both reduced states

The following sufficient condition is the pure-state ensemble formulation of superadditivity of the convex closure of output entropy in [Holevo–Shirokov, Theorem 1(iv)](https://arxiv.org/abs/quant-ph/0306196), which relates that property to additivity under arbitrary input constraints.

**Lemma 2.1 (entropic criterion for strong additivity).** Let $`\mathcal{A}:A\to B`$ and $`\mathcal{M}:A'\to B'`$ be channels. Suppose that, for every bipartite pure state $`\psi=|\psi\rangle\langle\psi|`$ on $`AA'`$, with reduced states $`\rho_A`$ and $`\rho_{A'}`$, there exist finite ensembles of states $`\{p_\ell,\eta_\ell\}`$ on $`A`$ and $`\{q_k,\tau_k\}`$ on $`A'`$ such that

```math
\rho_A=\sum_\ell p_\ell\eta_\ell,
\qquad
\rho_{A'}=\sum_k q_k\tau_k,
```

and

```math
S\left((\mathcal{A}\otimes\mathcal{M})(\psi)\right)
\ge
\sum_\ell p_\ell S\left(\mathcal{A}(\eta_\ell)\right)
+\sum_k q_k S\left(\mathcal{M}(\tau_k)\right).
```

Then

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M}).
```

**Lean verification of the standard criterion:** [`standard_entropic_criterion`](Lean/SchurEntropy/Capacity/StandardCriterion.lean), with the exact finite-ensemble hypothesis in [`StandardEntropicCriterion`](Lean/SchurEntropy/Capacity/Definitions.lean).

### Weaker criterion: preserve one output-center expectation

For any ensemble $`\{p_\ell,\eta_\ell\}`$ attaining $`\chi_{\max}(\mathcal{A})`$, the average output

```math
\sigma_{\mathcal{A}}
:=\sum_\ell p_\ell\mathcal{A}(\eta_\ell)
```

is independent of the chosen optimal ensemble. We call $`\sigma_{\mathcal{A}}`$ the **optimal output center**. Uniqueness follows from [Holevo–Shirokov, Corollary 1](https://arxiv.org/abs/quant-ph/0306196); see also [Schumacher–Westmoreland, “Optimal signal ensembles”](https://arxiv.org/abs/quant-ph/9912122) for the relative-entropy characterization of optimal ensembles.

If $`\sigma_{\mathcal{A}}`$ is singular, $`\log_2\sigma_{\mathcal{A}}`$ is interpreted on its support. Every output of $`\mathcal{A}`$ is supported there, so everything below is well defined.

**Proposition 2.2 (weaker entropic criterion).** Let $`\mathcal{A}:A\to B`$ and $`\mathcal{M}:A'\to B'`$ be channels. Suppose that, for every bipartite pure state $`\psi`$ on $`AA'`$, with reduced states $`\rho_A`$ and $`\rho_{A'}`$, there exist finite ensembles of states $`\{p_\ell,\eta_\ell\}`$ on $`A`$ and $`\{q_k,\tau_k\}`$ on $`A'`$ such that

```math
\sum_\ell p_\ell
\mathrm{Tr}\left(\mathcal{A}(\eta_\ell)\log_2\sigma_{\mathcal{A}}\right)
=\mathrm{Tr}\left(\mathcal{A}(\rho_A)\log_2\sigma_{\mathcal{A}}\right),
\qquad
\rho_{A'}=\sum_kq_k\tau_k,
```

and

```math
S\left((\mathcal{A}\otimes\mathcal{M})(\psi)\right)
\ge
\sum_\ell p_\ell S\left(\mathcal{A}(\eta_\ell)\right)
+\sum_k q_k S\left(\mathcal{M}(\tau_k)\right).
```

Then

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M}).
```

The standard compatibility condition implies the weaker one by linearity. The weaker condition fixes only the expectation of $`\log_2\sigma_{\mathcal{A}}`$ at the output of the first channel, while still preserving the second reduced input state. This relaxation is used in the manuscript's treatment of higher-dimensional phase-covariant channels.

**Lean verification of the weaker criterion:** [`output_center_entropic_criterion`](Lean/SchurEntropy/Capacity/OutputCenterCriterion.lean), with the exact hypothesis in [`OutputCenterEntropicCriterion`](Lean/SchurEntropy/Capacity/CriterionStatements.lean). The same file proves the criterion for the average output of **any** optimal ensemble. [Optimal-ensemble existence](Lean/SchurEntropy/Capacity/OptimalEnsemble.lean), [output support inclusion and center bounds](Lean/SchurEntropy/Capacity/OutputCenterRadius.lean), and [the implication from the standard hypothesis](Lean/SchurEntropy/Capacity/CriterionStatements.lean) are also proved. Uniqueness of the optimal output center is cited background; it is not separately formalized or needed by these proofs.

## Schur-weighted block entropy inequality

The central matrix inequality compares an entropy deficit for a block matrix with the corresponding deficit for a scalar matrix built from block traces.

### Block notation and entropy deficit

Fix $`m\ge1`$ and block sizes $`n_1,\ldots,n_m\ge1`$. Let

```math
\mathcal{H}=\bigoplus_{i=1}^{m}\mathbb{C}^{n_i},
\qquad
C=(c_{ij})\in\mathbb{M}_m,
\qquad
H=(H_{ij})_{i,j=1}^{m}\in\mathcal{B}(\mathcal{H}).
```

The **block Schur product** is

```math
C\odot H=(c_{ij}H_{ij})_{i,j=1}^{m}.
```

Let $`\mathcal{P}`$ denote pinching onto the diagonal blocks:

```math
\mathcal{P}(J)=\bigoplus_{i=1}^{m}J_{ii}.
```

When every $`n_i=1`$, this is ordinary diagonal pinching. For the matrix inequalities, entropy is extended to all positive semidefinite operators, without trace normalization:

```math
S(X)=-\mathrm{Tr}(X\log_2X),
\qquad X\ge0,
\qquad 0\log_2 0:=0.
```

For $`J\ge0`$ and block-diagonal $`W\ge0`$ on the same space, define

```math
\Delta(J,W)
:=S(J+W)-S\left(\mathcal{P}(J)\right)-S(W).
```

### Main matrix inequality

**Theorem 3.1 (Schur-weighted block entropy inequality).** Suppose $`C\ge0`$, $`H\ge0`$, and

```math
W=\bigoplus_{i=1}^{m}W_i,
\qquad W_i\ge0.
```

Set

```math
r_i=\mathrm{Tr}H_{ii},
\qquad
y_i=\mathrm{Tr}W_i,
\qquad
D_{\boldsymbol{r}}=\mathrm{diag}(r_1,\ldots,r_m),
\qquad
D_{\boldsymbol{y}}=\mathrm{diag}(y_1,\ldots,y_m).
```

Then

```math
\boxed{
\Delta(C\odot H,W)
\ge
\Delta\left(
D_{\boldsymbol{r}}^{1/2}CD_{\boldsymbol{r}}^{1/2},
D_{\boldsymbol{y}}
\right).
}
```

The deficit on the left uses pinching into the original blocks $`\mathbb{C}^{n_i}`$. The deficit on the right is evaluated on $`\mathbb{C}^m`$ and uses ordinary diagonal pinching.

### Two analytic ingredients

The proof of the block inequality uses two complementary properties of the entropy deficit: concavity after minimizing over the block-diagonal perturbation, and convexity of the scalar expression in its trace parameters.

#### Concavity after minimization

**Lemma 3.2 (concavity and minimum attainment).** Suppose

```math
\Lambda=\bigoplus_{i=1}^{m}\mu_iI_{n_i},
\qquad \mu_i<0.
```

For $`J\ge0`$ on $`\mathcal{H}`$, define

```math
G_\Lambda(J,W)
:=\Delta(J,W)-\mathrm{Tr}(\Lambda W),
```

and

```math
\widehat G_\Lambda(J)
:=\min_{\substack{W\ge0\\ W\text{ block diagonal}}}
G_\Lambda(J,W).
```

The minimum is attained, and the map $`J\mapsto\widehat G_\Lambda(J)`$ is concave on the positive semidefinite cone.

#### Joint convexity of the scalar expression

**Lemma 3.3 (joint convexity of the scalar entropy deficit).** For every $`C\ge0`$ in $`\mathbb{M}_m`$, the function

```math
f_C(\boldsymbol{r},\boldsymbol{y})
:=\Delta\left(
D_{\boldsymbol{r}}^{1/2}CD_{\boldsymbol{r}}^{1/2},
D_{\boldsymbol{y}}
\right)
```

is jointly convex on $`[0,\infty)^m\times[0,\infty)^m`$. Here the deficit uses ordinary diagonal pinching.

## Strong additivity for phase-covariant channels

This section is the first application of the block entropy inequality.

Fix an orthonormal basis of $`\mathbb{C}^d`$. Here **phase covariance** means covariance under every diagonal unitary in this basis:

```math
\mathcal{A}(U_{\boldsymbol{\theta}}\rho U_{\boldsymbol{\theta}}^{\dagger})
=U_{\boldsymbol{\theta}}\mathcal{A}(\rho)U_{\boldsymbol{\theta}}^{\dagger},
\qquad
U_{\boldsymbol{\theta}}
=\mathrm{diag}(e^{i\theta_1},\ldots,e^{i\theta_d}),
\qquad
\boldsymbol{\theta}\in\mathbb{R}^d.
```

We apply this symmetry to multilevel amplitude-damping, generalized dephasing, and damping–dephasing channels, as well as generalized amplitude-damping channels. It shows that all the examples discussed in [cite Leditzky et al.] are actually single-letter.

**Lemma 4.1 (phase-covariant normal form).** The [Singh–Nechita normal form](#references) expresses such a channel as

```math
\mathcal A(\rho)=C\odot\rho
+\sum_{i\ne j}p_{ij}\langle j|\rho|j\rangle |i\rangle\langle i|,
\qquad C\succeq0,\quad p_{ij}\ge0,\quad
\sum_i p_{ij}=1,\quad c_{ii}=p_{ii}.
```

Both covariance and Schur multiplication refer to the same fixed basis. The formalization proves this characterization from the covariance hypothesis.

**Theorem 4.2 (strong additivity for all phase-covariant channels).** Let $`d\ge2`$, and let $`\mathcal{A}:\mathbb{M}_d\to\mathbb{M}_d`$ be phase covariant in the sense above. For every finite-dimensional channel $`\mathcal{M}`$,

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M}).
```

**Lean verification:** [`phase_covariant_additivity` and `phase_covariant_angles_additivity`](Lean/SchurEntropy/PhaseCovariant/Results.lean). The hypothesis is actual covariance under every diagonal unitary in one fixed basis; the normal form is proved from it in [NormalForm.lean](Lean/SchurEntropy/PhaseCovariant/NormalForm.lean). The proof derives the pure-input entropy estimate from this repository's block inequality and applies the weaker entropic criterion at a diagonal optimal output center constructed by finite symmetry averaging. See the [proof](Proofs/phase-covariant.md) for the comparison input, noise-concavity step, and zero-weight conventions.

The exported variants `phase_covariant_states_additivity` and `phase_covariant_in_basis_additivity` accept covariance tested only on density matrices and covariance in any specified fixed orthonormal basis, respectively. The Lean theorem covers every positive finite dimension, including the trivial one-dimensional case.

## Qubit-output channels and the all-qubit result

The same block inequality also yields strong additivity for channels with a qubit output and one coherent Kraus operator. Specializing to qubit inputs recovers Kenta Kitamura’s all-qubit strong-additivity result; see [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity).

**Lemma 5.1 (qubit-output Kraus decomposition).** Every channel $`\mathcal A:\mathbb M_d\to\mathbb M_2`$, with $`d\ge1`$, admits a suitable output basis in which

```math
\mathcal A(\rho)=\sum_{s=1}^{d-1}K_s\rho K_s^\dagger
 +\sum_{i=0}^1\mathrm{Tr}(E_i\rho)|i\rangle\langle i|,
\qquad K_s=|0\rangle\langle a_s|+|1\rangle\langle b_s|,
```

where $`E_i\ge0`$, zero vectors are allowed, and $`\sum_s K_s^\dagger K_s+E_0+E_1=I_d`$. Thus for $`d=2`$ there is at most one coherent Kraus operator. **Lean verification:** [`exists_qubit_output_decomposition_general`](Lean/SchurEntropy/Qubit/DecompositionGeneral.lean), including exactly $`d-1`$ slots by zero padding.

**Theorem 5.2 (strong additivity for qubit-output channels with one coherent Kraus operator, and for all qubit channels).** Let $`\mathcal{A}:\mathbb{M}_d\to\mathbb{M}_2`$. Suppose there exist an orthonormal basis $`\{|0\rangle,|1\rangle\}`$ of $`\mathbb{C}^2`$, positive semidefinite operators $`E_0,E_1\in\mathbb{M}_d`$, and possibly zero, unnormalized vectors $`|a_0\rangle,|a_1\rangle\in\mathbb{C}^d`$ such that

```math
\mathcal{A}(\rho)
=K\rho K^{\dagger}
+\sum_{i=0}^{1}\mathrm{Tr}(E_i\rho)|i\rangle\langle i|,
\qquad
K=|0\rangle\langle a_0|+|1\rangle\langle a_1|,
```

and

```math
|a_0\rangle\langle a_0|
+|a_1\rangle\langle a_1|
+E_0+E_1=I_d.
```

Then, for every finite-dimensional channel $`\mathcal{M}:A'\to B'`$,

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M}).
```

In particular, every qubit-to-qubit channel $`\mathcal{A}:\mathbb{M}_2\to\mathbb{M}_2`$ satisfies strong additivity.

**Lean verification:** [`single_coherent_qubit_output_additivity` and `all_qubit_channels_additivity`](Lean/SchurEntropy/Qubit/Results.lean). The first theorem allows arbitrary finite input dimension and the stated single coherent Kraus operator. The second has no channel-specific hypothesis. The proof constructs the compatible ensembles and applies this repository's Schur-weighted block entropy theorem and standard entropic criterion. A [checked and completed version of the manuscript argument](Proofs/qubit-channels.md) explains the basis-selection, positive-remainder, support, phase-alignment, and zero-weight steps.

## Discussion and open directions

First, **strong additivity for all qubit-output channels** remains open beyond the class in Theorem 5.2. Lemma 5.1 gives at most $`d-1`$ coherent Kraus operators for a channel $`\mathcal A:\mathbb M_d\to\mathbb M_2`$. The proof of Theorem 5.2 handles one coherent Kraus operator; with several such operators, the current block entropy argument does not apply directly. Extending the block entropy inequality and the associated ensemble construction may address this larger class.

Second, **strong additivity for other physics-related channels**. Theorem 5.3 does not cover resonant amplitude damping channels, and other covariant channels. Only phase-covariance is established.

Finally, **dimension threshold for an entanglement advantage**: find $`N\ge2`$ such that every square channel of dimension $`d\le N`$ satisfies $`\mathcal C(\mathcal A)=\chi_{\max}(\mathcal A)`$, while every dimension $`d>N`$ admits an explicit square channel satisfying $`\mathcal C(\mathcal A)>\chi_{\max}(\mathcal A)`$. The all-qubit result settles the equality at $`d=2`$; it does not settle the threshold problem or all higher dimensions.


## Lean Formalization

The names and numbering below follow the updated manuscript. The mathematical proofs are collected in [Proofs/](Proofs/README.md); the corresponding verified sources are in [Lean/](Lean/).

| Manuscript result | Mathematical proof | Lean declaration and source |
| --- | --- | --- |
| **Lemma 2.1 — Entropic criterion for strong additivity** | [Entropic criteria](Proofs/entropic-criteria.md) | [`standard_entropic_criterion`](Lean/SchurEntropy/Capacity/StandardCriterion.lean) |
| **Proposition 2.2 — Weaker entropic criterion** | [Entropic criteria](Proofs/entropic-criteria.md) | [`output_center_entropic_criterion`](Lean/SchurEntropy/Capacity/OutputCenterCriterion.lean) |
| **Theorem 3.1 — Schur-weighted block entropy inequality** | [Block entropy inequality](Proofs/block-entropy.md) | [`block_entropy_inequality`](Lean/SchurEntropy/Results.lean) |
| **Lemma 3.2 — Concavity and minimum attainment** | [Analytic lemmas](Proofs/analytic-lemmas.md) | [`optimizedConcavity`](Lean/SchurEntropy/OptimizedBridge.lean) |
| **Lemma 3.3 — Joint convexity of the scalar entropy deficit** | [Analytic lemmas](Proofs/analytic-lemmas.md) | [`scalar_joint_convexity`](Lean/SchurEntropy/ScalarConvexity.lean) |
| **Lemma 4.1 — Phase-covariant normal form** | [Phase-covariant channels](Proofs/phase-covariant.md) | [`phaseCovariant_iff_normalForm`](Lean/SchurEntropy/PhaseCovariant/NormalForm.lean) |
| **Theorem 4.2 — Strong additivity for all phase-covariant channels** | [Phase-covariant channels](Proofs/phase-covariant.md) | [`phase_covariant_additivity`](Lean/SchurEntropy/PhaseCovariant/Results.lean) |
| **Lemma 5.1 — Qubit-output Kraus decomposition** | [Qubit channels](Proofs/qubit-channels.md) | [`exists_qubit_output_decomposition_general`](Lean/SchurEntropy/Qubit/DecompositionGeneral.lean) |
| **Theorem 5.2 — Strong additivity for one-coherent-Kraus qubit-output channels, including all qubit channels** | [Qubit channels](Proofs/qubit-channels.md) | [`single_coherent_qubit_output_additivity` and `all_qubit_channels_additivity`](Lean/SchurEntropy/Qubit/Results.lean) |

The [verification record](Lean/verification.md) records the exact scope, supporting results, pinned dependencies, and audit procedure. To reproduce the checks with Lean's `elan` version manager installed:

```sh
cd Lean
lake exe cache get
./scripts/check.sh
```

The recorded full build and axiom audit passed for **1,292** imported `SchurEntropy` declarations, with only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom dependencies. The classical-capacity coding and regularization theorems and uniqueness of the optimal output center are cited background, not separately formalized results.



## References

1. A. S. Holevo, **“The capacity of the quantum channel with general signal states.”** *IEEE Transactions on Information Theory* **44**, 269–273 (1998). [arXiv:quant-ph/9611023](https://arxiv.org/abs/quant-ph/9611023).
2. B. Schumacher and M. D. Westmoreland, **“Sending classical information via noisy quantum channels.”** *Physical Review A* **56**, 131–138 (1997). [DOI:10.1103/PhysRevA.56.131](https://doi.org/10.1103/PhysRevA.56.131).
3. A. S. Holevo and M. E. Shirokov, **“On Shor's channel extension and constrained channels.”** *Communications in Mathematical Physics* **249**, 417–430 (2004). [arXiv:quant-ph/0306196](https://arxiv.org/abs/quant-ph/0306196).
4. B. Schumacher and M. D. Westmoreland, **“Optimal signal ensembles.”** *Physical Review A* **63**, 022308 (2001). [arXiv:quant-ph/9912122](https://arxiv.org/abs/quant-ph/9912122). [DOI:10.1103/PhysRevA.63.022308](https://doi.org/10.1103/PhysRevA.63.022308).
5. S. Singh and I. Nechita, **“Diagonal unitary and orthogonal symmetries in quantum theory.”** *Quantum* **5**, 519 (2021). [DOI:10.22331/q-2021-08-09-519](https://doi.org/10.22331/q-2021-08-09-519).
6. Z. Tang, C. Zhu, G. Bai, and X. Wang, **“Classical capacity and entanglement cost of the amplitude damping channel.”** (2026). [arXiv:2609.28592v1](https://arxiv.org/abs/2609.28592v1).
7. K. Fang, **“The classical capacity of generalized amplitude-damping channels and its strong-converse exponent.”** (2026). [arXiv:2609.14621v2](https://arxiv.org/abs/2609.14621v2).
8. OpenAI, **“Classical capacity and entropy inequalities for generalized amplitude damping.”** OpenAI Math Release preprint (2026). [Github Repository](https://github.com/openai/math/blob/main/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/paper.pdf).
9. K. Kitamura, **“Lean proof of strong Holevo additivity for qubit channels.”** (2026). [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity).

## Citation

Peixue Wu, **“Classical communication over quantum channels: does entanglement help in nature?”**, 2026. Formal proofs: [Github Repository](https://github.com/pxwu24/additivity-of-classical-communication).

For the repository, the following BibTeX entry uses a clickable name rather than printing the URL (with `hyperref` enabled):

```bibtex
@misc{Wu2026LeanAdditivity,
  author = {Peixue Wu},
  title = {Additivity of classical communication: Lean verification},
  year = {2026},
  howpublished = {Lean companion to {Classical communication over quantum channels: does entanglement help in nature?}},
  note = {\href{https://github.com/pxwu24/additivity-of-classical-communication}{Github Repository}}
}
```
