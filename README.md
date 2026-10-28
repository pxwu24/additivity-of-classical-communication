# A Schur-weighted block entropy inequality and its application to classical capacity of quantum channels

This repository is the planned Lean companion to the forthcoming paper of the same title. It organizes the formalization of a Schur-weighted block entropy inequality, the entropic criteria connecting it to channel capacity, and the resulting strong-additivity statements for phase-covariant and qubit-output channels.

**Current status:** this initial version contains the mathematical overview and formalization plan. Lean proof files have not yet been supplied or incorporated. The statements below describe the forthcoming manuscript; they are not yet certified by a Lean build in this repository. See the [verification status](docs/verification.md) and [planned module organization](SchurEntropy/README.md).

## Contents

- [Capacity problem and notation](#capacity-problem-and-notation)
- [Main results](#main-results)
- [Entropic criteria for additivity](#entropic-criteria-for-additivity)
- [Schur-weighted block entropy inequality](#schur-weighted-block-entropy-inequality)
- [Technical ingredients](#technical-ingredients)
- [Formalization index](#formalization-index)
- [References](#references)
- [Citation](#citation)

## Capacity problem and notation

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

See [Holevo](#references) and [Schumacher–Westmoreland](#references) for the coding theorems. A channel $`\mathcal{A}`$ has **strongly additive Holevo information** if

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M})
```

for every finite-dimensional channel $`\mathcal{M}`$. In particular, strong additivity implies $`\mathcal{C}(\mathcal{A})=\chi_{\max}(\mathcal{A})`$.

## Main results

### 1. Phase-covariant channels

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

The phases vary independently; covariance under a single Hamiltonian's time evolution is a different, generally weaker condition. The examples considered in the manuscript include phase-covariant multilevel amplitude-damping channels, generalized amplitude-damping channels, and damping–dephasing channels.

**Theorem 1 (strong additivity for phase-covariant channels).** Let $`d\ge2`$, and let $`\mathcal{A}:\mathbb{M}_d\to\mathbb{M}_d`$ be phase covariant in the sense above. For every finite-dimensional channel $`\mathcal{M}`$,

```math
\chi_{\max}(\mathcal{A}\otimes\mathcal{M})
=\chi_{\max}(\mathcal{A})+\chi_{\max}(\mathcal{M}).
```

### 2. Qubit-output channels

**Theorem 2 (strong additivity for a class of qubit-output channels).** Let $`\mathcal{A}:\mathbb{M}_d\to\mathbb{M}_2`$. Suppose there exist an orthonormal basis $`\{|0\rangle,|1\rangle\}`$ of $`\mathbb{C}^2`$, positive semidefinite operators $`E_0,E_1\in\mathbb{M}_d`$, and possibly zero, unnormalized vectors $`|a_0\rangle,|a_1\rangle\in\mathbb{C}^d`$ such that

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

## Entropic criteria for additivity

The channel applications use a lower bound on the output entropy of a bipartite pure input. The distinction between the two criteria below is the amount of information that the auxiliary ensemble must preserve on the first input system.

### Standard criterion: preserve both reduced states

The following sufficient condition is the pure-state ensemble formulation of convex-roof entropy superadditivity in [Holevo–Shirokov, Theorem 1(iv)](https://arxiv.org/abs/quant-ph/0306196), which relates that property to additivity under arbitrary input constraints.

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

### Weaker criterion: preserve one output-center expectation

For any ensemble $`\{p_\ell,\eta_\ell\}`$ attaining $`\chi_{\max}(\mathcal{A})`$, the average output

```math
\sigma_{\mathcal{A}}
:=\sum_\ell p_\ell\mathcal{A}(\eta_\ell)
```

is independent of the chosen optimal ensemble. We call $`\sigma_{\mathcal{A}}`$ the **optimal output center**. Uniqueness follows from [Holevo–Shirokov, Corollary 1](https://arxiv.org/abs/quant-ph/0306196); see also [Schumacher–Westmoreland, “Optimal signal ensembles”](https://arxiv.org/abs/quant-ph/9912122) for the relative-entropy characterization of optimal ensembles.

If $`\sigma_{\mathcal{A}}`$ is singular, $`\log_2\sigma_{\mathcal{A}}`$ is interpreted on its support. Every output of $`\mathcal{A}`$ is supported there, so the trace pairings below are well defined.

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

## Technical ingredients

The proof of the block inequality uses two complementary properties of the entropy deficit: concavity after minimizing over the block-diagonal perturbation, and convexity of the scalar expression in its trace parameters.

### Concavity after minimization

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

### Joint convexity of the scalar expression

**Lemma (scalar joint convexity).** For every $`C\ge0`$ in $`\mathbb{M}_m`$, the function

```math
f_C(\boldsymbol{r},\boldsymbol{y})
:=\Delta\left(
D_{\boldsymbol{r}}^{1/2}CD_{\boldsymbol{r}}^{1/2},
D_{\boldsymbol{y}}
\right)
```

is jointly convex on $`[0,\infty)^m\times[0,\infty)^m`$. Here the deficit uses ordinary diagonal pinching.

## Formalization index

The following module names are planned destinations, not links to completed proofs. Exact Lean declarations and source links will be recorded when the proof files are added and checked.

| Manuscript result | Planned Lean module | Status |
| --- | --- | --- |
| Strong additivity for phase-covariant channels | `SchurEntropy.Channels.PhaseCovariant` | Pending source |
| Strong additivity for the qubit-output class and all qubit channels | `SchurEntropy.Channels.QubitOutput` | Pending source |
| Standard entropic criterion | `SchurEntropy.Capacity.StandardCriterion` | Pending source |
| Weaker entropic criterion | `SchurEntropy.Capacity.OutputCenterCriterion` | Pending source |
| Schur-weighted block entropy inequality | `SchurEntropy.Entropy.BlockInequality` | Pending source |
| Optimized concavity and attainment | `SchurEntropy.Entropy.OptimizedConcavity` | Pending source |
| Scalar joint convexity | `SchurEntropy.Entropy.ScalarConvexity` | Pending source |

See [verification status](docs/verification.md) for the current scope and [module organization](SchurEntropy/README.md) for the proposed source layout. Reproducible build instructions will be added with the pinned Lean toolchain and proof sources.

## References

1. A. S. Holevo, **“The capacity of the quantum channel with general signal states.”** *IEEE Transactions on Information Theory* **44**, 269–273 (1998). [arXiv:quant-ph/9611023](https://arxiv.org/abs/quant-ph/9611023).
2. B. Schumacher and M. D. Westmoreland, **“Sending classical information via noisy quantum channels.”** *Physical Review A* **56**, 131–138 (1997). [DOI:10.1103/PhysRevA.56.131](https://doi.org/10.1103/PhysRevA.56.131).
3. A. S. Holevo and M. E. Shirokov, **“On Shor's channel extension and constrained channels.”** *Communications in Mathematical Physics* **249**, 417–430 (2004). [arXiv:quant-ph/0306196](https://arxiv.org/abs/quant-ph/0306196).
4. B. Schumacher and M. D. Westmoreland, **“Optimal signal ensembles.”** *Physical Review A* **63**, 022308 (2001). [arXiv:quant-ph/9912122](https://arxiv.org/abs/quant-ph/9912122). [DOI:10.1103/PhysRevA.63.022308](https://doi.org/10.1103/PhysRevA.63.022308).

## Citation

The manuscript **“A Schur-weighted block entropy inequality and its application to classical capacity of quantum channels”** is in preparation. A complete bibliographic entry and an archival link will be added when available.
