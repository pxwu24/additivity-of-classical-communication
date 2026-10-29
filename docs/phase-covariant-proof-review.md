# Proof check: phase covariance and strong additivity

The argument is valid after correcting two displayed formulas and making the
noise-block concavity step explicit. Phase covariance and the normal form use
the **same fixed orthonormal basis**. Covariance in every possible basis is not
an assumption of the theorem.

The comparison input is
$|\psi_{\boldsymbol r}\rangle=\sum_i\sqrt{r_i}|i\rangle$ in the first input
space, not $\sum_i\sqrt{r_i}|v_i\rangle$ in the partner space. The final scalar
entropy equals $S(\mathcal A(\psi_{\boldsymbol r}))$, not the entropy of the
joint output. Here a vector in a channel argument denotes its pure density
matrix.

## The fixed-basis normal form

Write $E_{ij}=|i\rangle\langle j|$. Covariance gives

```math
\mathcal A(U E_{ij}U^\dagger)
=U\mathcal A(E_{ij})U^\dagger,
\qquad U=\mathrm{diag}(z_1,\ldots,z_d),\quad |z_i|=1.
```

Thus a nonzero $(k,l)$ entry of $\mathcal A(E_{ij})$ requires
$z_i\overline{z_j}=z_k\overline{z_l}$ for every choice of phases. If $i=j$,
this forces $k=l$. If $i\ne j$, it forces $(k,l)=(i,j)$. Taking one coordinate
phase equal to $\mathrm{i}$ and all others equal to $1$ suffices to prove
these restrictions; signs alone would not distinguish $(i,j)$ from $(j,i)$.

Define $p_{ij}=\langle i|\mathcal A(E_{jj})|i\rangle$ and, for $i\ne j$,
define $c_{ij}$ by $\mathcal A(E_{ij})=c_{ij}E_{ij}$; put $c_{ii}=p_{ii}$.
The Choi matrix restricts on the span of $|i\rangle\otimes|i\rangle$ to
$C=(c_{ij})$. On its orthogonal complement it has the scalar diagonal
entries $p_{ij}$, $i\ne j$. Complete positivity therefore gives
$C\succeq0$ and $p_{ij}\ge0$, and trace preservation gives
$\sum_i p_{ij}=1$. Expanding an arbitrary matrix in matrix units yields

```math
\mathcal A(X)=C\odot X+
 \sum_{i\ne j}p_{ij}X_{jj}|i\rangle\langle i|.
```

Conversely, this formula commutes with diagonal conjugation. The normal form
is therefore equivalent to covariance in the specified basis.

## A diagonal optimal output center

Choose a finite ensemble attaining the Holevo information. For every
$\varepsilon\in\{-1,1\}^d$, let
$U_\varepsilon=\mathrm{diag}(\varepsilon_1,\ldots,\varepsilon_d)$. Replace
each ensemble state $\rho_x$ of weight $p_x$ by the states
$U_\varepsilon\rho_xU_\varepsilon^\dagger$ of weights $p_x/2^d$.

By covariance and unitary invariance of entropy, the mean individual output
entropy is unchanged. The new average output is the diagonal pinching of
the old one: averaging signs cancels every off-diagonal entry. Entropy
concavity makes the entropy of this average at least its previous value.
The new ensemble cannot exceed the Holevo optimum, so it is also optimal.
Its average output $\sigma$ is diagonal. This construction supplies an
actual diagonal optimal center without needing a separate uniqueness theorem.

The previously established weaker entropic criterion applies to this center,
including when it is singular. Every channel output lies in its support.
Accordingly, $\log_2\sigma$ may be evaluated on that support and extended by
zero on the kernel, as in the Lean definition.

## The entropy bound and compatible ensembles

Fix any partner channel $\mathcal M$ and any bipartite unit vector. Write

```math
|\psi\rangle=\sum_i\sqrt{r_i}|i\rangle\otimes|v_i\rangle,
\qquad r_i\ge0,\quad\sum_i r_i=1,\quad \|v_i\|=1.
```

For a zero $r_i$, choose any unit $v_i$; its value has no effect. Put

```math
H_{ij}=\sqrt{r_ir_j}\,\mathcal M(|v_i\rangle\langle v_j|),
\qquad W_i=\sum_{j\ne i}p_{ij}H_{jj},
\qquad y_i=\sum_{j\ne i}p_{ij}r_j.
```

Complete positivity gives $H\succeq0$, while $W=\bigoplus_iW_i\succeq0$.
The normal form gives
$(\mathcal A\otimes\mathcal M)(\psi)=C\odot H+W$.
Set $B=D_{\boldsymbol r}^{1/2}CD_{\boldsymbol r}^{1/2}$ and
$T=B+D_{\boldsymbol y}$. The Schur-weighted block entropy inequality,
together with $S(t\rho)=tS(\rho)-t\log_2t$ for a density matrix $\rho$,
gives

```math
S((\mathcal A\otimes\mathcal M)(\psi))
\ge S(T)+\sum_i p_{ii}r_iS(\mathcal M(v_i))
       +\sum_{i:y_i>0}y_iS(W_i/y_i).
```

The scalar $-t\log_2t$ terms cancel between the block and scalar deficits.
For each $y_i>0$, entropy concavity gives the additional needed step

```math
y_iS(W_i/y_i)
\ge\sum_{j\ne i}p_{ij}r_jS(\mathcal M(v_j)).
```

When $y_i=0$, every nonnegative coefficient $p_{ij}r_j$ in that row is zero,
so both sides contribute zero. Similarly, zero $r_i$ gives $H_{ii}=0$.
All normalized zero-weight terms can therefore be omitted. Column
stochasticity now yields

```math
S((\mathcal A\otimes\mathcal M)(\psi))
\ge S(T)+\sum_jr_jS(\mathcal M(v_j)).
```

Define the unit vector
$|\psi_{\boldsymbol r}\rangle=\sum_i\sqrt{r_i}|i\rangle$ and its density
matrix $\eta$. The normal form gives $\mathcal A(\eta)=T$. Also, $\eta$
and $\rho_A$ have the same diagonal $(r_i)$, hence their outputs have the
same diagonal $(\sum_jp_{ij}r_j)_i$. Since $\sigma$ and its spectral
logarithm are diagonal,

```math
\mathrm{Tr}(\mathcal A(\eta)\log_2\sigma)
=\mathrm{Tr}(\mathcal A(\rho_A)\log_2\sigma).
```

Use the singleton ensemble $\{1,\eta\}$ for the first system and
$\{r_i,|v_i\rangle\langle v_i|\}$ for the partner. The latter averages to
$\rho_{A'}$, and the preceding entropy inequality becomes

```math
S((\mathcal A\otimes\mathcal M)(\psi))
\ge S(\mathcal A(\eta))+\sum_i r_i S(\mathcal M(v_i)).
```

These are exactly the logarithmic compatibility, partner marginal, and
entropy requirements of the weaker entropic criterion. It follows that

```math
\chi_{\max}(\mathcal A\otimes\mathcal M)
=\chi_{\max}(\mathcal A)+\chi_{\max}(\mathcal M)
```

for every finite-dimensional partner channel.
