# Theorem 3.1 — Schur-weighted block entropy inequality

This is the central matrix inequality in Section 3 of the updated manuscript. Its two analytic ingredients are [Lemmas 3.2 and 3.3](analytic-lemmas.md).

For any positive semidefinite matrix $X$, use the unnormalized entropy

```math
S(X)=-\mathrm{Tr}(X\log_2X),\qquad 0\log_2 0:=0.
```

Fix $m\ge1$ and positive block sizes $n_1,\ldots,n_m$. Let $\mathcal P$ be pinching onto the diagonal blocks of $\bigoplus_i\mathbb C^{n_i}$, and define

```math
C\odot H=(c_{ij}H_{ij})_{i,j=1}^{m},
\qquad
\Delta(J,W)=S(J+W)-S(\mathcal P(J))-S(W).
```

On scalar matrices, $\mathcal P$ means ordinary diagonal pinching.

## Statement

Suppose $C=(c_{ij})\ge0$, $H=(H_{ij})\ge0$, and $W=\bigoplus_i W_i$ with $W_i\ge0$. Put

```math
r_i=\mathrm{Tr}H_{ii},\qquad y_i=\mathrm{Tr}W_i,
\qquad
D_{\boldsymbol r}=\mathrm{diag}(r_1,\ldots,r_m),
\qquad
D_{\boldsymbol y}=\mathrm{diag}(y_1,\ldots,y_m).
```

Then

```math
\Delta(C\odot H,W)
\ge\Delta\left(D_{\boldsymbol r}^{1/2}CD_{\boldsymbol r}^{1/2},D_{\boldsymbol y}\right).
```

The hypotheses impose no trace normalization and no unit-diagonal condition on $C$. Positivity of $C\odot H$ follows from the block Schur product theorem: factoring $C=\sum_a z_a z_a^\dagger$ expresses the product as a sum of diagonal-block congruences of $H$.

## Rank-one case

First let $H=uu^\dagger$, where $u=\bigoplus_i u_i$ and $r_i=\|u_i\|^2$. Write

```math
A=D_{\boldsymbol r}^{1/2}CD_{\boldsymbol r}^{1/2},
\qquad J=C\odot H.
```

Define an isometry $V:\mathbb C^m\to\bigoplus_i\mathbb C^{n_i}$ by sending the $i$th standard basis vector to $u_i/\sqrt{r_i}$ in the $i$th block when $r_i>0$. When $r_i=0$, choose any unit vector in that block. Distinct images lie in orthogonal blocks, and direct multiplication gives

```math
J=VAV^\dagger,
\qquad
\mathcal P(J)=V\,\mathrm{diag}(A)\,V^\dagger.
```

Here $\mathrm{diag}(A)$ denotes the diagonal matrix retaining the diagonal entries of $A$. These identities also hold when some or all $u_i$ vanish.

Let $Y=\bigoplus_i y_i I_{n_i}$. Its action on the range of $V$ is $D_{\boldsymbol y}$, and its orthogonal complement is invariant. The matrix $J$ vanishes on that complement. Isometry invariance and direct-sum additivity of unnormalized entropy imply

```math
S(\mathcal P(J))=S(\mathrm{diag}(A)),
\qquad
S(J+Y)-S(Y)=S(A+D_{\boldsymbol y})-S(D_{\boldsymbol y}).
```

A positive matrix is bounded above by its trace times the identity. Consequently $0\le W_i\le y_iI_{n_i}$, so $0\le W\le Y$.

For a fixed $J\ge0$, the entropy increment $S(J+B)-S(B)$ is nonincreasing in $B$ in the positive semidefinite order. To see this first when $B>0$, differentiate in a positive direction $R\ge0$:

```math
\frac{d}{dt}\bigl[S(J+B+tR)-S(B+tR)\bigr]
=-\mathrm{Tr}\!\left(R\left[\log_2(J+B+tR)-\log_2(B+tR)\right]\right)
\le0.
```

Operator monotonicity of the logarithm gives the sign. Replacing $B$ by $B+\varepsilon I$ and passing to the limit extends the comparison to singular matrices. Hence

```math
\begin{aligned}
\Delta(J,W)
&=S(J+W)-S(W)-S(\mathrm{diag}(A))\\
&\ge S(J+Y)-S(Y)-S(\mathrm{diag}(A))\\
&=S(A+D_{\boldsymbol y})-S(D_{\boldsymbol y})-S(\mathrm{diag}(A))\\
&=\Delta(A,D_{\boldsymbol y}).
\end{aligned}
```

This proves the rank-one case, including zero vectors and singular noise.

## Combining rank-one bounds

The deficit is nonlinear, so a spectral decomposition alone does not let us add the rank-one inequalities. The two analytic lemmas supply the required directions of Jensen's inequality.

First suppose $C$, $H$, and $W$ are positive definite. Then $r_i,y_i>0$ and $A=D_{\boldsymbol r}^{1/2}CD_{\boldsymbol r}^{1/2}>0$. Define

```math
f_C(\boldsymbol r,\boldsymbol y)
=\Delta(D_{\boldsymbol r}^{1/2}CD_{\boldsymbol r}^{1/2},D_{\boldsymbol y}),
\qquad
\mu_i=\frac{\partial f_C}{\partial y_i}(\boldsymbol r,\boldsymbol y)
=\log_2 y_i-[\log_2(A+D_{\boldsymbol y})]_{ii}.
```

Every $\mu_i$ is strictly negative. Indeed,

```math
\log_2(A+D_{\boldsymbol y})-\log_2D_{\boldsymbol y}
=\frac1{\ln2}\int_0^\infty
\left[(D_{\boldsymbol y}+sI)^{-1}-(A+D_{\boldsymbol y}+sI)^{-1}\right]ds.
```

The integrand is positive definite because $A>0$; therefore every diagonal entry of the integral is positive. Set $\Lambda=\bigoplus_i\mu_iI_{n_i}$. Lemma 3.3 gives a supporting inequality in the second variable:

```math
f_C(\boldsymbol r,\boldsymbol z)
\ge f_C(\boldsymbol r,\boldsymbol y)
+\boldsymbol\mu\cdot(\boldsymbol z-\boldsymbol y),
\qquad \boldsymbol z\in[0,\infty)^m.
```

The statement extends to boundary values of $\boldsymbol z$ by continuity.

Choose a finite convex rank-one decomposition

```math
H=\sum_{\alpha=1}^{q}p_\alpha u_\alpha u_\alpha^\dagger,
\qquad p_\alpha>0,\qquad \sum_\alpha p_\alpha=1.
```

For example, if $H=\sum_{\alpha=1}^q\lambda_\alpha e_\alpha e_\alpha^\dagger$ lists its positive eigenvalues, take $p_\alpha=1/q$ and $u_\alpha=\sqrt{q\lambda_\alpha}\,e_\alpha$. Thus no normalization of $H$ is needed. Put

```math
r_i^{(\alpha)}=\|u_{\alpha,i}\|^2,
\qquad
J^{(\alpha)}=C\odot u_\alpha u_\alpha^\dagger.
```

Then $\sum_\alpha p_\alpha\boldsymbol r^{(\alpha)}=\boldsymbol r$ and $\sum_\alpha p_\alpha J^{(\alpha)}=J$.

By Lemma 3.2, the optimized deficit

```math
\widehat G_\Lambda(K)
=\min_{\substack{Z\ge0\\ Z\text{ block diagonal}}}
\left[\Delta(K,Z)-\mathrm{Tr}(\Lambda Z)\right]
```

is concave in $K$, and each minimum is attained. For each $\alpha$, choose a minimizer $W^{(\alpha)}$ at $J^{(\alpha)}$, let $y_i^{(\alpha)}=\mathrm{Tr}W_i^{(\alpha)}$, and set $\overline{\boldsymbol y}=\sum_\alpha p_\alpha\boldsymbol y^{(\alpha)}$. Since $\mathrm{Tr}(\Lambda W)=\boldsymbol\mu\cdot\boldsymbol y$, we have

```math
\begin{aligned}
\Delta(J,W)-\boldsymbol\mu\cdot\boldsymbol y
&\ge\widehat G_\Lambda(J)\\
&\ge\sum_\alpha p_\alpha\widehat G_\Lambda(J^{(\alpha)})\\
&=\sum_\alpha p_\alpha
\left[\Delta(J^{(\alpha)},W^{(\alpha)})-\boldsymbol\mu\cdot\boldsymbol y^{(\alpha)}\right]\\
&\ge\sum_\alpha p_\alpha
\left[f_C(\boldsymbol r^{(\alpha)},\boldsymbol y^{(\alpha)})
-\boldsymbol\mu\cdot\boldsymbol y^{(\alpha)}\right]\\
&\ge f_C(\boldsymbol r,\overline{\boldsymbol y})
-\boldsymbol\mu\cdot\overline{\boldsymbol y}\\
&\ge f_C(\boldsymbol r,\boldsymbol y)
-\boldsymbol\mu\cdot\boldsymbol y.
\end{aligned}
```

In order, the steps are the definition of the minimum, optimized concavity, attainment, the rank-one bound, joint convexity of $f_C$, and the supporting inequality. Cancelling the final linear term proves the desired result for positive definite inputs.

## Semidefinite boundary

For arbitrary positive semidefinite $C$, $H$, and block-diagonal $W$, apply the positive definite result to $C+\varepsilon I_m$, $H+\varepsilon I$, and $W+\varepsilon I$. The last matrix remains block diagonal. Let $\varepsilon\downarrow0$.

Block traces, block Schur multiplication, and positive matrix square roots are continuous. The scalar function $-t\log_2t$, extended by zero at $t=0$, is continuous on $[0,\infty)$, so spectral entropy is continuous as well. Both sides converge to the stated expressions. This completes the proof for all positive semidefinite inputs.

## Lean proof

The final theorem is [`SchurEntropy.block_entropy_inequality`](../Lean/SchurEntropy/Results.lean). Its supporting files are:

- [RankOneInequality.lean](../Lean/SchurEntropy/RankOneInequality.lean): `rankOne_block_entropy`.
- [EntropyIncrement.lean](../Lean/SchurEntropy/EntropyIncrement.lean): `entropy_increment_antitone`.
- [RankOneEntropy.lean](../Lean/SchurEntropy/RankOneEntropy.lean): `entropy_blockColumns_increment`.
- [SpectralDecomposition.lean](../Lean/SchurEntropy/SpectralDecomposition.lean): `exists_uniform_rankOne_decomposition`.
- [SupportingMultiplier.lean](../Lean/SchurEntropy/SupportingMultiplier.lean): `SupportingMultiplier.exists_negative_support`.
- [BlockTheorem.lean](../Lean/SchurEntropy/BlockTheorem.lean): `blockEntropy_of_two_lemmas`.
- [BlockBoundary.lean](../Lean/SchurEntropy/BlockBoundary.lean): `blockEntropy_of_posDef`.

The two analytic hypotheses in the reduction theorem are discharged by the proved [Lemmas 3.2 and 3.3](analytic-lemmas.md); they are not assumptions of the exported final theorem.
