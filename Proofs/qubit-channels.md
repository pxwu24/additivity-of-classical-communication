# Qubit-output channels

This page proves **Lemma 5.1** and **Theorem 5.2** of the updated manuscript,
including its all-qubit consequence. All channels and Hilbert spaces are
finite dimensional, and logarithms are to base two.

## Lemma 5.1 — Qubit-output Kraus decomposition

Every channel $\mathcal A:\mathbb M_d\to\mathbb M_2$, with $d\ge1$, admits
an orthonormal output basis and positive operators $E_0,E_1$ such that

```math
\mathcal A(\rho)=\sum_{s=1}^{d-1}K_s\rho K_s^\dagger
 +\sum_{i=0}^1\mathrm{Tr}(E_i\rho)|i\rangle\langle i|,
\qquad
K_s=|0\rangle\langle a_s|+|1\rangle\langle b_s|,
```

where zero vectors are allowed and

```math
\sum_{s=1}^{d-1}
 (|a_s\rangle\langle a_s|+|b_s\rangle\langle b_s|)
 +E_0+E_1=I_d.
```

**Proof.**

Let the input dimension be $d\ge1$. In an initial output basis, write the
Choi matrix of the unital completely positive dual map as

```math
Q=\begin{pmatrix}A&B\\B^\dagger&D\end{pmatrix}\ge0,
\qquad A+D=I_d.
```

For the new orthonormal output basis

```math
|0\rangle=(\alpha,\beta)^T,
\qquad |1\rangle=(-\overline\beta,\overline\alpha)^T,
\qquad |\alpha|^2+|\beta|^2=1,
```

the off-diagonal dual block is exactly

```math
Q_{01}(\alpha,\beta)
=\alpha^2B-\beta^2B^\dagger+\alpha\beta(D-A).
```

Its determinant is a homogeneous **holomorphic** polynomial of degree $2d$,
possibly identically zero.
This is stronger than being a polynomial in variables and their conjugates;
that latter property alone would not imply a zero. If $\det B=0$, use
$(\alpha,\beta)=(1,0)$. Otherwise

```math
p(z)=\det\bigl(z^2B+z(D-A)-B^\dagger\bigr)
```

has degree $2d$, with leading coefficient $\det B\ne0$. The fundamental
theorem of algebra gives a root $z$. Normalize $(z,1)$ to obtain the desired
orthonormal basis. Homogeneity preserves the zero, so the new block has
rank $r\le d-1$.

Use this basis from now on, and rename its diagonal blocks $A,D$ and its
off-diagonal block $B$. Positivity of $Q$ gives

```math
\mathrm{ran}\,B\subseteq\mathrm{ran}\,A,
\qquad B^\dagger A^+B\le D,
```

where $A^+$ is the Moore–Penrose inverse. The second inequality can be seen
directly by evaluating the positive quadratic form of $Q$ on
$(-A^+Bx,x)$, using $AA^+B=B$.

Put $T=A^{+1/2}B$. Multiplication by $A^{+1/2}$ is injective on
$\mathrm{ran}\,A$, so $\mathrm{rank}\,T=r$. Take a reduced SVD

```math
T=\sum_{s=1}^{r}\lambda_s|u_s\rangle\langle v_s|,
\qquad \lambda_s>0,
```

and define $a_s=A^{1/2}u_s$, $b_s=\lambda_sv_s$. Then

```math
\sum_s|a_s\rangle\langle b_s|=A^{1/2}T=B.
```

With $P_U=\sum_s|u_s\rangle\langle u_s|\le I$,

```math
E_0=A-\sum_s|a_s\rangle\langle a_s|
    =A^{1/2}(I-P_U)A^{1/2}\ge0,
```

and

```math
E_1=D-\sum_s|b_s\rangle\langle b_s|
    =D-T^\dagger T=D-B^\dagger A^+B\ge0.
```

Thus the common Kraus operators
$K_s=|0\rangle\langle a_s|+|1\rangle\langle b_s|$ reproduce both
off-diagonal dual blocks, while $E_0,E_1$ supply the diagonal residuals.
Their dual maps agree on the four matrix units, hence the channels agree.
Unitality gives

```math
\sum_s K_s^\dagger K_s+E_0+E_1=I_d.
```

Pad by zero vectors to obtain $d-1$ Kraus operators; when $r=0$, the common
part is zero. Each summand is completely positive and trace-nonincreasing,
because its effect operator is positive and bounded by $I_d$. The residual
operation is entanglement-breaking and has commuting outputs. Neither
summand is required to be a trace-preserving channel.

The corresponding Lean theorem is
[`exists_qubit_output_decomposition_general`](../Lean/SchurEntropy/Qubit/DecompositionGeneral.lean).
The formal proof obtains the positive factors using Schur complements and a
compactness limit; the explicit pseudoinverse/SVD construction above gives
concrete vectors satisfying the same statement.

## Theorem 5.2 — Strong additivity for a class of qubit-output channels

A channel of the following single-coherent-Kraus form has strongly additive
Holevo information. In particular, every qubit-to-qubit channel is strongly
Holevo additive.

Suppose

```math
\mathcal A(\rho)=K\rho K^\dagger+
 \sum_{i=0}^1\mathrm{Tr}(E_i\rho)|i\rangle\langle i|,
\qquad K=|0\rangle\langle a_0|+|1\rangle\langle a_1|,
```

with positive $E_i$ and
$|a_0\rangle\langle a_0|+|a_1\rangle\langle a_1|+E_0+E_1=I_d$.
**Proof.** Fix a bipartite pure input $\psi$, and write its marginals as
$\rho_A,\rho_{A'}$. Set

```math
|v_i\rangle=(\langle a_i|\otimes I)|\psi\rangle,
\qquad \tau_i=\mathrm{Tr}_A[(E_i\otimes I)|\psi\rangle\langle\psi|].
```

Although the product inside this partial trace need not be Hermitian,

```math
\tau_i=\mathrm{Tr}_A[
 (E_i^{1/2}\otimes I)|\psi\rangle\langle\psi|(E_i^{1/2}\otimes I)]\ge0.
```

Completeness implies
$\rho_{A'}=\sum_i(|v_i\rangle\langle v_i|+\tau_i)$.
For an arbitrary partner channel $\mathcal M$, put
$H_{ij}=\mathcal M(|v_i\rangle\langle v_j|)$ and
$W_i=\mathcal M(\tau_i)$; the block matrix $H$ is positive by complete
positivity. Let $r_i=\|v_i\|^2$ and $y_i=\mathrm{Tr}\,\tau_i$.
The [block entropy theorem](block-entropy.md) with $C_{ij}=1$, followed by the unnormalized
entropy scaling identity, gives

```math
S((\mathcal A\otimes\mathcal M)(\psi))
\ge S(T)+\sum_{i:r_i>0}r_iS(\mathcal M(|v_i\rangle\langle v_i|/r_i))
       +\sum_{i:y_i>0}y_iS(\mathcal M(\tau_i/y_i)),
```

where

```math
T=\begin{pmatrix}
r_0+y_0&\sqrt{r_0r_1}\\
\sqrt{r_0r_1}&r_1+y_1
\end{pmatrix}.
```

Every omitted zero-weight numerator is itself zero by positivity. The
remaining partner states, weighted by $r_i,y_i$, form an ensemble of
$\rho_{A'}$.

It remains to construct an ensemble of $\rho_A$ whose mean output entropy
is at most $S(T)$. Let $P$ project onto $\mathrm{supp}\,\rho_A$ and
$m=\mathrm{rank}\,\rho_A\ge1$. On this support, the Hermitian operator

```math
X=\rho_A^{1/2}
 (r_1|a_0\rangle\langle a_0|-r_0|a_1\rangle\langle a_1|)
 \rho_A^{1/2}
```

has trace zero. Choose an eigenbasis $e_0,\ldots,e_{m-1}$ **of this support**
and its Fourier basis

```math
u_\ell=\frac1{\sqrt m}\sum_{k=0}^{m-1}
e^{2\pi i k\ell/m}e_k.
```

Then $\langle u_\ell,Xu_\ell\rangle=\mathrm{Tr}\,X/m=0$. Set

```math
p_\ell=\langle u_\ell,\rho_Au_\ell\rangle>0,
\qquad |\eta_\ell\rangle=\rho_A^{1/2}u_\ell/\sqrt{p_\ell}.
```

Since $\sum_\ell|u_\ell\rangle\langle u_\ell|=P$, this is a pure-state
ensemble of $\rho_A$. Write
$t_{\ell i}=|\langle a_i|\eta_\ell\rangle|^2$. The zero quadratic form gives

```math
r_1t_{\ell0}=r_0t_{\ell1}.
```

If $R=r_0+r_1>0$, set $c_\ell=(t_{\ell0}+t_{\ell1})/R$. The balance
identity gives $t_{\ell i}=c_\ell r_i$, including when one $r_i=0$, and
$\sum_\ell p_\ell c_\ell=1$. Consequently,

```math
\sum_\ell p_\ell\sqrt{t_{\ell0}t_{\ell1}}=\sqrt{r_0r_1}.
```

If $R=0$, all $t_{\ell i}$ vanish, and the same identity holds.
Choose a diagonal unitary $U_\ell$ which makes the off-diagonal entry of
$\mathcal A(|\eta_\ell\rangle\langle\eta_\ell|)$ nonnegative real;
use the identity when that entry is zero. Averaging the diagonal entries
uses the ensemble identity, while averaging the off-diagonal entry uses
the displayed square-root identity. Hence

```math
\sum_\ell p_\ell U_\ell
 \mathcal A(|\eta_\ell\rangle\langle\eta_\ell|)U_\ell^\dagger=T.
```

Entropy concavity and unitary invariance now give
$S(T)\ge\sum_\ell p_\ell S(\mathcal A(|\eta_\ell\rangle\langle\eta_\ell|))$.
Together with the partner ensemble and block bound, this verifies both
conditions of the [standard entropic criterion, Lemma 2.1](entropic-criteria.md). Therefore
$\chi_{\max}(\mathcal A\otimes\mathcal M)=
\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M)$.

For input dimension $d=2$, the decomposition lemma gives at most one
coherent Kraus operator, so every qubit-to-qubit channel satisfies the
theorem. For $d>2$, the decomposition lemma allows several coherent Kraus
operators; the single-Kraus theorem alone does not establish additivity
for all channels from $\mathbb M_d$ to $\mathbb M_2$.


### Lean proof

The exported declarations in [Results.lean](../Lean/SchurEntropy/Qubit/Results.lean)
are `single_coherent_qubit_output_additivity` and
`all_qubit_channels_additivity`. Supporting modules include:

- [DecompositionRotation.lean](../Lean/SchurEntropy/Qubit/DecompositionRotation.lean): output-basis selection by the holomorphic determinant polynomial.
- [PSDFactor.lean](../Lean/SchurEntropy/Qubit/PSDFactor.lean) and [RankFactorization.lean](../Lean/SchurEntropy/Qubit/RankFactorization.lean): positive rank-sized factors.
- [EnsembleBound.lean](../Lean/SchurEntropy/Qubit/EnsembleBound.lean): a balanced pure-state ensemble and its output entropy bound.
- [ChannelBound.lean](../Lean/SchurEntropy/Qubit/ChannelBound.lean): compatible partner ensembles and application of the block inequality.

The Lean ensemble construction uses a finite spectral sign frame in place
of the Fourier basis above; both give the same zero-expectation identity.
The all-qubit conclusion recovers Kenta Kitamura's result; the dependency
and attribution are recorded in [the third-party notice](../Lean/third_party/NOTICE).
