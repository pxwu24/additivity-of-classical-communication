# Lemmas 3.2 and 3.3 — Analytic properties of the entropy deficit

These are the two analytic ingredients in Section 3 of the updated manuscript. The first makes it possible to combine rank-one matrix bounds by concavity; the second combines their scalar trace parameters by convexity. The arguments below follow the actual Lean proofs, including attainment and singular boundary points.

Write $S(X)=-\mathrm{Tr}(X\log_2X)$ for an arbitrary positive semidefinite matrix, with $0\log_2 0=0$. No trace normalization is imposed. For the fixed block decomposition, let $\mathcal P$ be pinching onto the diagonal blocks and set

```math
\Delta(J,W)=S(J+W)-S(\mathcal P(J))-S(W).
```

## Lemma 3.2 — Concavity and attainment of the optimized entropy deficit

Let $\Lambda=\bigoplus_i\mu_i I_{n_i}$ with every $\mu_i<0$. Then, for every $J\ge0$,

```math
\widehat G_\Lambda(J)
=\min_{W\ge0,\ W\text{ block diagonal}}
\left[\Delta(J,W)-\mathrm{Tr}(\Lambda W)\right]
```

is attained, and $J\mapsto\widehat G_\Lambda(J)$ is concave on the whole positive semidefinite cone.

**Lean theorem:** `SchurEntropy.optimizedConcavity`, in [OptimizedBridge.lean](../Lean/SchurEntropy/OptimizedBridge.lean).

### 1. Natural logarithms and attainment

It is convenient to put $\Psi(X)=\mathrm{Tr}(X\ln X)$ and $\lambda_i=(\ln2)\mu_i<0$. For a block-diagonal $W=\bigoplus_iW_i$, define

```math
q_\lambda(J,W)
=\Psi(W)-\Psi(J+W)-\sum_i\lambda_i\mathrm{Tr}W_i,
\qquad
g_\lambda(J)=\Psi(\mathcal P(J))+\min_W q_\lambda(J,W).
```

Then $\widehat G_\Lambda(J)=g_\lambda(J)/\ln2$. In particular, the multiplier must be rescaled when passing from bits to natural logarithms.

Choose $c>0$ with $c\le-\lambda_i$ for all $i$, and write $j=\mathrm{Tr}J$ and $w=\mathrm{Tr}W$. The entropy increment estimate gives

```math
\Psi(W+J)-\Psi(W)
\le j\bigl(\ln(w+j)+1\bigr),
```

when $j>0$. Indeed, integrate the derivative along $W+tJ$, use $W+tJ\le(w+j)I$, and regularize singular matrices before passing to the limit. Consequently,

```math
q_\lambda(J,W)
\ge cw-j\bigl(\ln(w+j)+1\bigr)
\longrightarrow+\infty\qquad(w\longrightarrow\infty).
```

For $J=0$, the objective is simply $-\sum_i\lambda_i\mathrm{Tr}W_i\ge cw$, so the same coercivity conclusion holds. The admissible set is closed; its trace-bounded subsets are compact in finite dimension. The objective is continuous because $x\ln x$ extends continuously to zero. A minimum therefore exists for every $J\ge0$.

The precise boundary-safe statements are `objective_lower_bound_psd` and `exists_minOn_positiveCone_psd` in [OptimizedPSDExistence.lean](../Lean/SchurEntropy/OptimizedPSDExistence.lean).

### 2. Interior minimizers and stationarity

Assume for now that $J>0$, and let $W$ minimize the objective. Every block $W_i$ is positive definite. Otherwise, replacing $W$ by $W+tI$ produces a negative $t\ln t$ contribution from each zero eigenvalue of $W$, whereas the change in $\Psi(J+W)$ and the linear penalty is only $O(t)$. This would decrease the objective for small $t>0$.

Differentiating in every block-diagonal Hermitian direction yields

```math
\ln W_i=[\ln(J+W)]_{ii}+\lambda_i I_{n_i}.
```

These steps are proved by `positiveInterior_of_minOn` and `stationarity_of_minOn` in [OptimizedInterior.lean](../Lean/SchurEntropy/OptimizedInterior.lean).

For the curvature calculation, use the Hilbert–Schmidt inner product and the positive operators

```math
\mathcal K_T(X)=\int_0^1T^sXT^{1-s}\,ds,
\qquad
\mathcal L_T=\mathcal K_T^{-1}=D(\ln)_T.
```

Let $V$ be the isometric inclusion of the direct sum of the block matrix spaces into the full matrix space. Thus $V^*X=(X_{ii})_i$. Put

```math
T=J+W,\qquad
A=\mathcal K_T,\qquad
B=\bigoplus_i\mathcal K_{W_i},\qquad
D=\bigoplus_i\mathcal K_{J_{ii}}.
```

The residual $R=A-VBV^*$ is positive definite. To see this, for each $0\le s\le1$ compare the left/right multiplication operators $X\mapsto T^sXT^{1-s}$ with those for $W$, using $T-W=J>0$. The full operator for the block-diagonal $W$ restricts to $\bigoplus_i(X_i\mapsto W_i^sX_iW_i^{1-s})$ on the block matrix subspace; its contribution on the orthogonal complement is positive. Integrating gives $R>0$.

It follows that

```math
N=B^{-1}-V^*A^{-1}V>0.
```

This is exactly the Hessian of $q_\lambda(J,\cdot)$ in the noise directions. Thus the objective is strictly convex, the positive minimizer is unique, and the implicit function theorem applies to its stationarity equation. The minimizer consequently varies differentiably with $J>0$. See [OptimizedConvex.lean](../Lean/SchurEntropy/OptimizedConvex.lean) and `hasStrictFDerivAt_minimizer` in [OptimizedMinimizer.lean](../Lean/SchurEntropy/OptimizedMinimizer.lean).

### 3. The stationary matrix comparison

The analytic comparison needed at this stationary point is

```math
V^*AV\le B+D.
```

Its hypotheses are $T>0$, every $W_i>0$, $T-W>0$, and the displayed logarithmic stationarity equation. The result is proved as `MultiBlock.km_of_stationarity` in [MultiBlockComparison.lean](../Lean/SchurEntropy/MultiBlockComparison.lean). Here is the mechanism behind that comparison.

Define positive operators on matrix spaces by

```math
\mathcal Q_T(s)(X)=T^sXT^{1-s},
\qquad
F(s)=V^*\mathcal Q_T(s)V-\bigoplus_i\mathcal Q_{W_i}(s).
```

The generator of $\mathcal Q_T$ is $X\mapsto(\ln T)X-X\ln T$. Stationarity says that its compression to the block matrix subspace equals the direct sum of the corresponding generators for $W_i$: the scalar terms $\lambda_i I$ cancel from each commutator. Compressing the positive residual of the preceding step with the two columns given by $V$ and the generator applied to $V$ gives the Gram inequality

```math
\begin{pmatrix}F(s)&F'(s)\\F'(s)&F''(s)\end{pmatrix}\ge0.
```

At $s=0$ and $s=1$, $F(s)$ agrees with $\bigoplus_i\mathcal Q_{J_{ii}}(s)$. The matrix-curve maximum principle for a commuting positive exponential comparison family therefore gives

```math
F(s)\le\bigoplus_i\mathcal Q_{J_{ii}}(s),\qquad 0\le s\le1.
```

More precisely, this maximum principle asserts: if $Q'=KQ=QK$, $K$ is Hermitian, $Q>0$, the above Gram inequality holds for $F$, and $F\le Q$ at both endpoints, then $F\le Q$ throughout the interval. Its proof first compares with the strict barrier $e^{\varepsilon s(1-s)}Q(s)$ and then lets $\varepsilon\downarrow0$. The complete auxiliary proof is `QubitAdditivity.BetaBarrier.le_of_exponential` in the pinned dependency, invoked explicitly by `MultiBlock.pw_of_stationarity`. Thus the maximum principle is a proved supporting lemma, not an additional hypothesis of Lemma 3.2. Integrating the comparison in $s$ gives $V^*AV\le B+D$.

### 4. Eliminating the minimizing noise directions

Differentiating the stationarity equation determines the derivative $Z$ of the minimizing block noise in an input direction $H$:

```math
NZ=V^*A^{-1}H.
```

The envelope derivative then gives the Hessian of the actual minimized value:

```math
D^2g_\lambda(J)[H,H]
=\left\langle H,
\left(VD^{-1}V^*-A^{-1}
-A^{-1}VN^{-1}V^*A^{-1}\right)H\right\rangle.
```

By the inverse identity for $R=A-VBV^*$,

```math
R^{-1}=A^{-1}+A^{-1}VN^{-1}V^*A^{-1}.
```

The stationary comparison says $V^*RV\le D$. Since $R,D>0$, the Schur-complement criterion applied to

```math
\begin{pmatrix}R^{-1}&V\\V^*&D\end{pmatrix}
```

gives $VD^{-1}V^*\le R^{-1}$. Hence the Hessian above is nonpositive. Restricting to every affine segment in the positive definite cone proves concavity of $g_\lambda$ there.

The exact Hessian identity and its sign are `valueHessianRow_eq_eliminated_pairing` and `valueHessianRow_self_nonpos` in [OptimizedHessian.lean](../Lean/SchurEntropy/OptimizedHessian.lean); [OptimizedConcave.lean](../Lean/SchurEntropy/OptimizedConcave.lean) turns this into concavity.

### 5. Passing to singular inputs

Continuity of the objective alone would not justify continuity of an infimum over an unbounded set. The coercive estimate above is uniform when $J$ ranges over a trace-bounded positive semidefinite family: with $\mathrm{Tr}J\le M$ and $M\ge1$, the lower bound can be replaced by

```math
cw-M\bigl(\ln(w+M)+1\bigr).
```

Comparing with the admissible choice $W=0$ therefore places every local family of minimizers in one compact set. Joint continuity on this compact set proves continuity of the true minimum value, including at singular $J$. Apply the positive definite concavity inequality to $J+\varepsilon I$ and $K+\varepsilon I$, and let $\varepsilon\downarrow0$. This proves concavity on the full positive semidefinite cone. Finally divide by $\ln2$ to return to the stated entropy in bits.

See `continuousOn_value_psd` and `concaveOn_value_psd` in [OptimizedBoundary.lean](../Lean/SchurEntropy/OptimizedBoundary.lean), and `optimizedDeficit_attained` and `concaveOn_optimizedDeficit` in [OptimizedBridge.lean](../Lean/SchurEntropy/OptimizedBridge.lean).

## Lemma 3.3 — Joint convexity of the scalar entropy deficit

For every fixed $C\ge0$ in $\mathbb M_m$, the function

```math
f_C(\boldsymbol r,\boldsymbol y)
=\Delta\left(D_{\boldsymbol r}^{1/2}CD_{\boldsymbol r}^{1/2},D_{\boldsymbol y}\right)
```

is jointly convex on $[0,\infty)^m\times[0,\infty)^m$. Here pinching keeps the scalar diagonal.

**Lean theorem:** `SchurEntropy.scalar_joint_convexity`, in [ScalarConvexity.lean](../Lean/SchurEntropy/ScalarConvexity.lean).

### 1. Second variation along an arbitrary affine line

Work first with strictly positive coordinates $r_i,y_i$, and use natural logarithms. Along an affine line $\boldsymbol r(t)=\boldsymbol r+t\boldsymbol h$ and $\boldsymbol y(t)=\boldsymbol y+t\boldsymbol k$, put

```math
B(t)=D_{\boldsymbol r(t)}^{1/2}CD_{\boldsymbol r(t)}^{1/2}+Y(t),
\qquad Y(t)=D_{\boldsymbol y(t)}.
```

All quantities in the following calculation are evaluated at the same $t$. Define diagonal Hermitian matrices

```math
X=\mathrm{diag}\left(\frac{h_i}{r_i(t)}\right),
\qquad
E=\mathrm{diag}\left(k_i-y_i(t)\frac{h_i}{r_i(t)}\right).
```

Direct differentiation gives

```math
B'=\tfrac12(XB+BX)+E,
\qquad
B''=-\tfrac14[X,[X,B]].
```

With $c_i=c_{ii}\ge0$, the natural-logarithm deficit along the line is

```math
F(t)=-\mathrm{Tr}(B\ln B)
+\sum_i c_i r_i(t)\ln(c_i r_i(t))
+\sum_i y_i(t)\ln y_i(t).
```

Terms with $c_i=0$ are identically zero. Since $B\ge Y>0$, differentiating gives

```math
F''(t)=\sum_i\frac{c_i h_i^2}{r_i(t)}
+\sum_i\frac{k_i^2}{y_i(t)}
-\mathrm{Tr}\bigl(B'\mathcal L_B(B')\bigr)
+\tfrac14\mathrm{Tr}\bigl([X,[X,B]]\ln B\bigr).
```

The first two sums equal

```math
\mathrm{Tr}(X^2B)+2\mathrm{Tr}(XE)+\mathrm{Tr}(E^2Y^{-1}).
```

Because $Y\le B$, inverse monotonicity gives $B^{-1}\le Y^{-1}$. As $E^2\ge0$, replacing $Y^{-1}$ by $B^{-1}$ in the last trace can only decrease this expression. It remains to prove

```math
\begin{aligned}
0\le{}&\mathrm{Tr}(X^2B)+2\mathrm{Tr}(XE)+\mathrm{Tr}(E^2B^{-1})\\
&-\mathrm{Tr}\bigl(B'\mathcal L_B(B')\bigr)
+\tfrac14\mathrm{Tr}\bigl([X,[X,B]]\ln B\bigr).
\end{aligned}
```

The path identities and this reduction are proved in [ScalarConvexityCalculus.lean](../Lean/SchurEntropy/ScalarConvexityCalculus.lean) and [ScalarConvexityAlgebra.lean](../Lean/SchurEntropy/ScalarConvexityAlgebra.lean).

### 2. A scalar sum-of-squares certificate

Diagonalize $B$, with positive eigenvalues $a_i$. In this eigenbasis,

```math
\bigl(\mathcal L_B(Z)\bigr)_{ij}=\ell(a_i,a_j)Z_{ij},
\qquad
\ell(a,b)=
\begin{cases}
\dfrac{\ln a-\ln b}{a-b},&a\ne b,\\[4pt]
\dfrac1a,&a=b.
\end{cases}
```

The preceding trace expression is the sum over $i,j$ of the following quadratic form, with $a=a_i$, $b=a_j$, $x=X_{ij}$ and $z=E_{ij}$:

```math
Q_{a,b}(x,z)
=\left(\frac{a+b}{2}-ab\ell\right)|x|^2
+2\left(1-\frac{a+b}{2}\ell\right)\mathrm{Re}(\overline{x}z)
+\left(\frac{a+b}{2ab}-\ell\right)|z|^2.
```

Write $u=(a+b)/2$ and $s=\sqrt{ab}$. The logarithmic-mean inequality says $0\le s\ell\le1$, and the arithmetic–geometric mean inequality gives $u\ge s$. The exact identity

```math
Q_{a,b}(x,z)
=\frac{(u+s)(1-s\ell)}{2s^2}|sx+z|^2
+\frac{(u-s)(1+s\ell)}{2s^2}|sx-z|^2
```

therefore proves $Q_{a,b}\ge0$. For completeness, when $a\ge b$, the bound $s\ell\le1$ follows on setting $v=\sqrt{a/b}\ge1$ from

```math
2\ln v\le v-v^{-1};
```

the difference on the right minus the left vanishes at $v=1$ and has derivative $(v-1)^2/v^2\ge0$. The case $a<b$ follows by symmetry, and $a=b$ follows by the continuous value of $\ell$.

This proves $F''(t)\ge0$ along every affine line staying in the positive coordinate domain, hence joint convexity there. No invertibility of $C$ was used: the strictly positive $Y$ ensures $B>0$.

The certificate is `logarithmic_kernel_complex_nonneg` in [ScalarKernel.lean](../Lean/SchurEntropy/ScalarKernel.lean). Its sum over matrix entries is `diagonal_hessian_nonneg`, and the basis-independent estimate is `hessian_nonneg`, in [ScalarHessian.lean](../Lean/SchurEntropy/ScalarHessian.lean).

### 3. Zero coordinates and entropy in bits

The function $x\mapsto-x\ln x$ is continuous on $[0,\infty)$, and the diagonal square root is continuous. Thus the deficit is continuous jointly in $\boldsymbol r,\boldsymbol y$. Apply the convexity inequality to both endpoint pairs after adding $\varepsilon$ to every coordinate, and let $\varepsilon\downarrow0$. This includes every zero weight and every singular $C$. Dividing by the positive number $\ln2$ gives the statement in bits.

The boundary passage is `scalarConvexity_boundary` in [ScalarConvexityBoundary.lean](../Lean/SchurEntropy/ScalarConvexityBoundary.lean). The final assembly is [ScalarConvexity.lean](../Lean/SchurEntropy/ScalarConvexity.lean).

[Back to the manuscript proofs](README.md) · [Lean Formalization](../README.md#lean-formalization)
