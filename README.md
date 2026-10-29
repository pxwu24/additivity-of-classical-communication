# Additivity of classical communication

In this project, we hope to make meaningful progress on the ultimate goal of classical capacity of quantum channels: 

Find $N \ge 2$, such that for all channels $\mc A: \mb M_d \to \mb M_d$ with $d \le N$, we have $\mc C(\mc A) = \Cchi(\mc A)$ and if $d > N$, there exists a constructive channel $\mc A: \mb M_d \to \mb M_d$ such that $\mc C(\mc A) > \Cchi(\mc A)$. 

Current progress on additivity of classical capacity:

use the table attached


## Contents

- [Capacity problem and notation](#capacity-problem-and-notation)
- [Entropic criteria for additivity](#entropic-criteria-for-additivity)
- [Schur-weighted block entropy inequality](#schur-weighted-block-entropy-inequality)
- [Strong additivity for phase-covariant channels](#strong-additivity-for-phase-covariant-channels)
- [Qubit-output channels and the all-qubit result](#qubit-output-channels-and-the-all-qubit-result)
- [Discussion and open directions](#discussion-and-open-directions)
- [Lean Formalization](#formalization-index)
- [References](#references)
- [Citation](#citation)

## Capacity problem and notation

Can entangling the inputs across independent channel uses increase the rate of classical communication? The manuscript studies this question for channels describing physically relevant noise, using a common matrix entropy inequality.

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

We hope to characterize the channels for which \mathcal{C}(\Phi) = \chi_{\max}(\Phi), or \mathcal{C}(\Phi) > \chi_{\max}(\Phi).

A related definition: A channel $`\mathcal{A}`$ has **strongly additive Holevo information** if

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M})
```

for every finite-dimensional channel $`\mathcal{M}`$. In particular, strong additivity implies $`\mathcal{C}(\mathcal{A})=\chi_{\max}(\mathcal{A})`$.

## Entropic criteria for additivity

The channel applications use a lower bound on the output entropy of a bipartite pure input. The distinction between the two criteria below is the amount of information that the auxiliary ensemble must preserve on the first input system.

### Standard criterion: preserve both reduced states

The following sufficient condition is the pure-state ensemble formulation of superadditivity of the convex closure of output entropy in [Holevo–Shirokov, Theorem 1(iv)](https://arxiv.org/abs/quant-ph/0306196), which relates that property to additivity under arbitrary input constraints.

**Lemma (standard entropic criterion).** Let $`\mathcal{A}:A\to B`$ and $`\mathcal{M}:A'\to B'`$ be channels. Suppose that, for every bipartite pure state $`\psi=|\psi\rangle\langle\psi|`$ on $`AA'`$, with reduced states $`\rho_A`$ and $`\rho_{A'}`$, there exist finite ensembles of states $`\{p_\ell,\eta_\ell\}`$ on $`A`$ and $`\{q_k,\tau_k\}`$ on $`A'`$ such that

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

**Lean verification of the standard criterion:** [`standard_entropic_criterion`](SchurEntropy/Capacity/StandardCriterion.lean), with the exact finite-ensemble hypothesis in [`StandardEntropicCriterion`](SchurEntropy/Capacity/Definitions.lean).

### Weaker criterion: preserve one output-center expectation

For any ensemble $`\{p_\ell,\eta_\ell\}`$ attaining $`\chi_{\max}(\mathcal{A})`$, the average output

```math
\sigma_{\mathcal{A}}
:=\sum_\ell p_\ell\mathcal{A}(\eta_\ell)
```

is independent of the chosen optimal ensemble. We call $`\sigma_{\mathcal{A}}`$ the **optimal output center**. Uniqueness follows from [Holevo–Shirokov, Corollary 1](https://arxiv.org/abs/quant-ph/0306196); see also [Schumacher–Westmoreland, “Optimal signal ensembles”](https://arxiv.org/abs/quant-ph/9912122) for the relative-entropy characterization of optimal ensembles.

If $`\sigma_{\mathcal{A}}`$ is singular, $`\log_2\sigma_{\mathcal{A}}`$ is interpreted on its support. Every output of $`\mathcal{A}`$ is supported there, so everything below is well defined.

**Proposition (weaker entropic criterion).** Let $`\mathcal{A}:A\to B`$ and $`\mathcal{M}:A'\to B'`$ be channels. Suppose that, for every bipartite pure state $`\psi`$ on $`AA'`$, with reduced states $`\rho_A`$ and $`\rho_{A'}`$, there exist finite ensembles of states $`\{p_\ell,\eta_\ell\}`$ on $`A`$ and $`\{q_k,\tau_k\}`$ on $`A'`$ such that

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

**Lean verification of the weaker criterion:** [`output_center_entropic_criterion`](SchurEntropy/Capacity/OutputCenterCriterion.lean), with the exact hypothesis in [`OutputCenterEntropicCriterion`](SchurEntropy/Capacity/CriterionStatements.lean). The same file proves the criterion for the average output of **any** optimal ensemble. [Optimal-ensemble existence](SchurEntropy/Capacity/OptimalEnsemble.lean), [output support inclusion and center bounds](SchurEntropy/Capacity/OutputCenterRadius.lean), and [the implication from the standard hypothesis](SchurEntropy/Capacity/CriterionStatements.lean) are also proved. Uniqueness of the optimal output center is cited background; it is not separately formalized or needed by these proofs.

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

**Theorem (Schur-weighted block entropy inequality).** Suppose $`C\ge0`$, $`H\ge0`$, and

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

**Lemma (optimized concavity).** Suppose

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

**Lemma (scalar joint convexity).** For every $`C\ge0`$ in $`\mathbb{M}_m`$, the function

```math
f_C(\boldsymbol{r},\boldsymbol{y})
:=\Delta\left(
D_{\boldsymbol{r}}^{1/2}CD_{\boldsymbol{r}}^{1/2},
D_{\boldsymbol{y}}
\right)
```

is jointly convex on $`[0,\infty)^m\times[0,\infty)^m`$. Here the deficit uses ordinary diagonal pinching.

## Strong additivity for phase-covariant channels

This is the main channel application of the block entropy inequality.

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

The phases vary independently; covariance under a single Hamiltonian's time evolution is a different, generally weaker condition. The manuscript applies this symmetry to multilevel amplitude-damping, generalized dephasing, and damping–dephasing channels, as well as generalized amplitude-damping channels. Each application requires covariance under the full diagonal unitary group in the specified basis.

The [Singh–Nechita normal form](#references) expresses such a channel as

```math
\mathcal A(\rho)=C\odot\rho
+\sum_{i\ne j}p_{ij}\langle j|\rho|j\rangle |i\rangle\langle i|,
\qquad C\succeq0,\quad p_{ij}\ge0,\quad
\sum_i p_{ij}=1,\quad c_{ii}=p_{ii}.
```

Both covariance and Schur multiplication refer to the same fixed basis. The formalization proves this characterization from the covariance hypothesis.

**Theorem (strong additivity for phase-covariant channels).** Let $`d\ge2`$, and let $`\mathcal{A}:\mathbb{M}_d\to\mathbb{M}_d`$ be phase covariant in the sense above. For every finite-dimensional channel $`\mathcal{M}`$,

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M}).
```

**Lean verification:** [`phase_covariant_additivity` and `phase_covariant_angles_additivity`](SchurEntropy/PhaseCovariant/Results.lean). The hypothesis is actual covariance under every diagonal unitary in one fixed basis; the normal form is proved from it in [NormalForm.lean](SchurEntropy/PhaseCovariant/NormalForm.lean). The proof derives the pure-input entropy estimate from this repository's block inequality and applies the weaker entropic criterion at a diagonal optimal output center constructed by finite symmetry averaging. See the [proof](docs/phase-covariant-proof-review.md) for the comparison input, noise-concavity step, and zero-weight conventions.

The exported variants `phase_covariant_states_additivity` and `phase_covariant_in_basis_additivity` accept covariance tested only on density matrices and covariance in any specified fixed orthonormal basis, respectively. The Lean theorem covers every positive finite dimension, including the trivial one-dimensional case.

## Qubit-output channels and the all-qubit result

The same block inequality also yields strong additivity for channels with a qubit output and one coherent Kraus operator. Specializing to qubit inputs recovers Kenta Kitamura’s all-qubit strong-additivity result; see [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity).

**Decomposition lemma.** Every channel $`\mathcal A:\mathbb M_d\to\mathbb M_2`$, with $`d\ge1`$, admits a suitable output basis in which

```math
\mathcal A(\rho)=\sum_{s=1}^{d-1}K_s\rho K_s^\dagger
 +\sum_{i=0}^1\mathrm{Tr}(E_i\rho)|i\rangle\langle i|,
\qquad K_s=|0\rangle\langle a_s|+|1\rangle\langle b_s|,
```

where $`E_i\ge0`$, zero vectors are allowed, and $`\sum_s K_s^\dagger K_s+E_0+E_1=I_d`$. Thus for $`d=2`$ there is at most one coherent Kraus operator. **Lean verification:** [`exists_qubit_output_decomposition_general`](SchurEntropy/Qubit/DecompositionGeneral.lean), including exactly $`d-1`$ slots by zero padding.

**Theorem (strong additivity for a class of qubit-output channels).** Let $`\mathcal{A}:\mathbb{M}_d\to\mathbb{M}_2`$. Suppose there exist an orthonormal basis $`\{|0\rangle,|1\rangle\}`$ of $`\mathbb{C}^2`$, positive semidefinite operators $`E_0,E_1\in\mathbb{M}_d`$, and possibly zero, unnormalized vectors $`|a_0\rangle,|a_1\rangle\in\mathbb{C}^d`$ such that

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

**Lean verification:** [`single_coherent_qubit_output_additivity` and `all_qubit_channels_additivity`](SchurEntropy/Qubit/Results.lean). The first theorem allows arbitrary finite input dimension and the stated single coherent Kraus operator. The second has no channel-specific hypothesis. The proof constructs the compatible ensembles and applies this repository's Schur-weighted block entropy theorem and standard entropic criterion. A [checked and completed version of the manuscript argument](docs/qubit-proof-review.md) explains the basis-selection, positive-remainder, support, phase-alignment, and zero-weight steps.

## Discussion and open directions

The qubit-output decomposition has at most $`d-1`$ coherent Kraus operators, whereas the additivity theorem above handles a single coherent Kraus operator. It therefore proves the all-qubit result when $`d=2`$, but does not establish strong additivity for every channel $`\mathbb M_d\to\mathbb M_2`$. Extending the entropy argument to multiple coherent Kraus operators is an open direction in the manuscript.

The manuscript also proposes a conjecture about a dimension threshold for the equality $`\mathcal C(\mathcal A)=\chi_{\max}(\mathcal A)`$ among square channels $`\mathbb M_d\to\mathbb M_d`$: equality for every channel up to some $`N\ge3`$, and explicit counterexamples in every dimension above $`N`$. This is a conjecture, not a Lean theorem or a consequence of the results proved here. Equality for repeated uses of one channel is also weaker than strong additivity with every partner channel.

## Lean Formalization 

| Completed result | Lean declaration | Proof |
| --- | --- | --- |
| Optimized concavity and attainment | `SchurEntropy.optimizedConcavity` | [OptimizedBridge.lean](SchurEntropy/OptimizedBridge.lean) |
| Scalar joint convexity | `SchurEntropy.scalar_joint_convexity` | [ScalarConvexity.lean](SchurEntropy/ScalarConvexity.lean) |
| Schur-weighted block entropy inequality | `SchurEntropy.block_entropy_inequality` | [Results.lean](SchurEntropy/Results.lean) |
| Standard entropic criterion | `SchurEntropy.Capacity.standard_entropic_criterion` | [StandardCriterion.lean](SchurEntropy/Capacity/StandardCriterion.lean) |
| Weaker output-center criterion | `SchurEntropy.Capacity.output_center_entropic_criterion` | [OutputCenterCriterion.lean](SchurEntropy/Capacity/OutputCenterCriterion.lean) |
| All fixed-basis phase-covariant channels | `SchurEntropy.PhaseCovariant.phase_covariant_additivity` | [PhaseCovariant/Results.lean](SchurEntropy/PhaseCovariant/Results.lean) |
| Fixed-basis phase-covariant normal form | `SchurEntropy.PhaseCovariant.phaseCovariant_iff_normalForm` | [NormalForm.lean](SchurEntropy/PhaseCovariant/NormalForm.lean) |
| Single-coherent-Kraus qubit-output channels | `SchurEntropy.Qubit.single_coherent_qubit_output_additivity` | [Qubit/Results.lean](SchurEntropy/Qubit/Results.lean) |
| All qubit-to-qubit channels | `SchurEntropy.Qubit.all_qubit_channels_additivity` | [Qubit/Results.lean](SchurEntropy/Qubit/Results.lean) |
| General qubit-output decomposition with at most $`d-1`$ coherent Kraus operators | `SchurEntropy.Qubit.exists_qubit_output_decomposition_general` | [DecompositionGeneral.lean](SchurEntropy/Qubit/DecompositionGeneral.lean) |

The [verification index](docs/verification.md) records the exact scope, supporting results, pinned dependencies, and audit procedure. To reproduce the checks with Lean's `elan` version manager installed:

```sh
lake exe cache get
./scripts/check.sh
```

The recorded full build and axiom audit passed for **1,292** imported `SchurEntropy` declarations, with only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom dependencies. The classical-capacity coding and regularization theorems and uniqueness of the optimal output center are cited background, not separately formalized results.

The project builds on Kitamura’s matrix and channel-entropy library, pinned at commit `90e61c463deb42067c109c46f048c6374dfc5945`; see [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity/tree/90e61c463deb42067c109c46f048c6374dfc5945). It imports the generic standard entropic criterion and adapts several matrix-calculus and channel arguments. The local channel theorems derive their entropy bounds from this repository’s Schur-weighted block inequality. Source provenance and licenses are recorded in [third_party/NOTICE](third_party/NOTICE).

## References

1. A. S. Holevo, **“The capacity of the quantum channel with general signal states.”** *IEEE Transactions on Information Theory* **44**, 269–273 (1998). [arXiv:quant-ph/9611023](https://arxiv.org/abs/quant-ph/9611023).
2. B. Schumacher and M. D. Westmoreland, **“Sending classical information via noisy quantum channels.”** *Physical Review A* **56**, 131–138 (1997). [DOI:10.1103/PhysRevA.56.131](https://doi.org/10.1103/PhysRevA.56.131).
3. A. S. Holevo and M. E. Shirokov, **“On Shor's channel extension and constrained channels.”** *Communications in Mathematical Physics* **249**, 417–430 (2004). [arXiv:quant-ph/0306196](https://arxiv.org/abs/quant-ph/0306196).
4. B. Schumacher and M. D. Westmoreland, **“Optimal signal ensembles.”** *Physical Review A* **63**, 022308 (2001). [arXiv:quant-ph/9912122](https://arxiv.org/abs/quant-ph/9912122). [DOI:10.1103/PhysRevA.63.022308](https://doi.org/10.1103/PhysRevA.63.022308).
5. S. Singh and I. Nechita, **“Diagonal unitary and orthogonal symmetries in quantum theory.”** *Quantum* **5**, 519 (2021). [DOI:10.22331/q-2021-08-09-519](https://doi.org/10.22331/q-2021-08-09-519).
6. OpenAI, **“Classical capacity and entropy inequalities for generalized amplitude damping.”** OpenAI Math Release preprint (2026). [Github Repository](https://github.com/openai/math/blob/main/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/paper.pdf).
7. K. Kitamura, **“Lean proof of strong Holevo additivity for qubit channels.”** (2026). [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity).

## Citation

Peixue Wu, **“Classical communication over quantum channels: does entanglement help in nature?”** Manuscript in preparation (2026). Formal proofs: [Github Repository](https://github.com/pxwu24/additivity-of-classical-communication).

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
