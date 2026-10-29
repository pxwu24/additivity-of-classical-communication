# Entropic criteria for strong additivity

This note proves **Lemma 2.1** and **Proposition 2.2** of the updated manuscript. All systems are finite dimensional, all ensembles are finite, and logarithms are to base two. For a unit vector $|\psi\rangle$, write $\psi=|\psi\rangle\langle\psi|$.

For a channel $\Phi$, its Holevo information is

```math
\chi_{\max}(\Phi)
=\max_{\{t_x,\rho_x\}}
\left[S\!\left(\Phi\!\left(\sum_x t_x\rho_x\right)\right)
-\sum_x t_x S(\Phi(\rho_x))\right].
```

It suffices to optimize over pure input states: resolving each mixed input into pure states leaves the average output unchanged and, by entropy concavity, can only decrease the average output entropy.

## Lemma 2.1 — Entropic criterion preserving both reduced states

Let $\mathcal A:A\to B$ and $\mathcal M:A'\to B'$ be channels. Suppose that for every pure state $\psi$ on $AA'$, with reduced states $\rho_A$ and $\rho_{A'}$, there are ensembles $\{p_\ell,\eta_\ell\}$ and $\{q_k,\tau_k\}$ such that

```math
\rho_A=\sum_\ell p_\ell\eta_\ell,
\qquad
\rho_{A'}=\sum_k q_k\tau_k,
```

and

```math
S((\mathcal A\otimes\mathcal M)(\psi))
\ge \sum_\ell p_\ell S(\mathcal A(\eta_\ell))
+\sum_k q_k S(\mathcal M(\tau_k)).
```

Then

```math
\chi_{\max}(\mathcal A\otimes\mathcal M)
=\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M).
```

### Proof

Take any pure input ensemble $\{t_x,\psi_x\}$ for the product channel. Put $\omega_x=(\mathcal A\otimes\mathcal M)(\psi_x)$ and $\bar\omega=\sum_x t_x\omega_x$. For each $x$, choose the ensembles in the hypothesis, writing their probabilities as $p_{\ell|x}$ and $q_{k|x}$ and their states as $\eta_{\ell|x}$ and $\tau_{k|x}$.

The combined ensembles with probabilities $t_xp_{\ell|x}$ and $t_xq_{k|x}$ have average input states $\bar\rho_A$ and $\bar\rho_{A'}$, the marginals of $\sum_x t_x\psi_x$. Entropy subadditivity at the average output and the assumed lower bound for every $\omega_x$ give

```math
\begin{aligned}
S(\bar\omega)-\sum_x t_xS(\omega_x)
&\le S(\mathcal A(\bar\rho_A))
   -\sum_{x,\ell}t_xp_{\ell|x}S(\mathcal A(\eta_{\ell|x}))\\
&\quad+S(\mathcal M(\bar\rho_{A'}))
   -\sum_{x,k}t_xq_{k|x}S(\mathcal M(\tau_{k|x}))\\
&\le\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M).
\end{aligned}
```

Taking the maximum proves the upper bound. Taking product ensembles for the individual channels proves the reverse bound, since entropy is additive on tensor products. This proves the lemma.

This is the pure-state ensemble form of the convex-closure criterion in Holevo–Shirokov, *On Shor's channel extension and constrained channels*, Theorem 1(iv). The criterion concerns a specified pair of channels.

**Lean proof:** [`standard_entropic_criterion`](../Lean/SchurEntropy/Capacity/StandardCriterion.lean). Its exact ensemble hypothesis is defined in [Definitions.lean](../Lean/SchurEntropy/Capacity/Definitions.lean).

## Proposition 2.2 — Weaker entropic criterion using the optimal output center

Choose an optimal ensemble of $\mathcal A$ and let $\sigma_{\mathcal A}$ be its average output. This is the optimal output center. In finite dimension it is independent of the chosen optimal ensemble. The properties used below are

```math
\mathrm{supp}\,\mathcal A(\rho)\subseteq\mathrm{supp}\,\sigma_{\mathcal A},
\qquad
D(\mathcal A(\rho)\Vert\sigma_{\mathcal A})
\le\chi_{\max}(\mathcal A)
```

for every input state $\rho$, where

```math
D(\omega\Vert\sigma)
=\mathrm{Tr}\bigl(\omega(\log_2\omega-\log_2\sigma)\bigr).
```

When $\sigma$ is singular, its logarithm in this formula is evaluated on its support. The inclusion above makes the pairing finite. Zero eigenvalues of $\omega$ use $0\log_2 0=0$.

Suppose that for every bipartite pure input $\psi$, with marginals $\rho_A$ and $\rho_{A'}$, there are ensembles satisfying

```math
\sum_\ell p_\ell\mathrm{Tr}\bigl(\mathcal A(\eta_\ell)
\log_2\sigma_{\mathcal A}\bigr)
=\mathrm{Tr}\bigl(\mathcal A(\rho_A)\log_2\sigma_{\mathcal A}\bigr),
\qquad
\rho_{A'}=\sum_k q_k\tau_k,
```

and the same entropy lower bound as in Lemma 2.1. Then

```math
\chi_{\max}(\mathcal A\otimes\mathcal M)
=\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M).
```

### Proof

Let $\sigma_{\mathcal M}$ be an optimal output center for $\mathcal M$ and write $\Sigma=\sigma_{\mathcal A}\otimes\sigma_{\mathcal M}$. For a pure input $\psi$, put $\omega=(\mathcal A\otimes\mathcal M)(\psi)$. Its marginals are $\mathcal A(\rho_A)$ and $\mathcal M(\rho_{A'})$.

The support of $\omega$ lies in the tensor product of the two marginal supports, hence in the support of $\Sigma$. Indeed, a positive matrix whose marginal has zero weight on a subspace also has zero weight on the corresponding tensor-product subspace; positivity then forces its rows and columns there to vanish. Thus all relative entropies in the argument are finite.

The logarithm of a tensor product is the sum of the two logarithms on this support. Expanding relative entropy gives

```math
\begin{aligned}
D(\omega\Vert\Sigma)
&=-S(\omega)
-\mathrm{Tr}\bigl(\mathcal A(\rho_A)\log_2\sigma_{\mathcal A}\bigr)
-\mathrm{Tr}\bigl(\mathcal M(\rho_{A'})\log_2\sigma_{\mathcal M}\bigr)\\
&\le\sum_\ell p_\ell D(\mathcal A(\eta_\ell)\Vert\sigma_{\mathcal A})
+\sum_k q_k D(\mathcal M(\tau_k)\Vert\sigma_{\mathcal M})\\
&\le\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M).
\end{aligned}
```

The first inequality uses exactly the entropy hypothesis, preservation of the first logarithmic expectation, and preservation of the second marginal. The last inequality is the optimal-center radius bound for each channel.

Now take an arbitrary pure input ensemble $\{t_x,\psi_x\}$, set $\omega_x=(\mathcal A\otimes\mathcal M)(\psi_x)$, and let $\bar\omega=\sum_x t_x\omega_x$. Expanding the relative entropies and cancelling the linear logarithmic terms gives

```math
S(\bar\omega)-\sum_x t_xS(\omega_x)
=\sum_x t_xD(\omega_x\Vert\Sigma)-D(\bar\omega\Vert\Sigma).
```

The last term is nonnegative. The preceding bound for each pure input therefore bounds the Holevo information of this ensemble by $\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M)$. Pure input ensembles suffice, so this proves the upper bound for the channel. Product ensembles again give the reverse bound.

Linearity shows that the first marginal condition of Lemma 2.1 implies the first logarithmic-expectation condition here. Proposition 2.2 therefore retains only the scalar information needed by the relative-entropy argument.

**Lean proof:** [`output_center_entropic_criterion`](../Lean/SchurEntropy/Capacity/OutputCenterCriterion.lean), also exported for the average output of any specified optimal ensemble as `output_center_criterion_of_optimal_ensemble`. The support inclusion and radius bounds are derived from ensemble optimality in [OutputCenterRadius.lean](../Lean/SchurEntropy/Capacity/OutputCenterRadius.lean); finite optimal ensembles are constructed in [OptimalEnsemble.lean](../Lean/SchurEntropy/Capacity/OptimalEnsemble.lean). The implication from the standard hypothesis is [`standard_implies_outputCenter`](../Lean/SchurEntropy/Capacity/CriterionStatements.lean).

The formal proof works with a specified optimal ensemble and therefore does not need a separate uniqueness theorem for the center. The uniqueness statement above is background attributed to Holevo–Shirokov, Corollary 1; the relative-entropy characterization also appears in Schumacher–Westmoreland, *Optimal signal ensembles*.
