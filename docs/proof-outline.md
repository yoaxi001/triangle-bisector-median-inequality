# A computer-assisted proof of Liu's triangle inequality

Updated: 2026-11-19. This exposition follows the estimates used in the completed Lean proof, including the equality classification. It explains the mathematical argument and the finite checker; the full subdivision data are in [Certificate.lean](../Certificate.lean).

The proof concerns the standard side-length formulas below. A derivation of those formulas from points, midpoints, and internal angle bisectors in a Euclidean geometry library is outside the formalization. Novelty and independent expert review have not been established.

## 1. Statement and definitions

Let $a,b,c>0$ satisfy the three strict triangle inequalities. Define

$$
m_a=\sqrt{\frac{2b^2+2c^2-a^2}{4}},\qquad
w_a=\sqrt{\frac{bc(a+b+c)(b+c-a)}{(b+c)^2}},\qquad
s=\frac{a+b+c}{2},
$$

and define the other lengths cyclically. We prove

$$
(w_a+w_b+w_c)(m_a^3+m_b^3+m_c^3)\ge s^4,
$$

with equality if and only if $a=b=c$.

This is Conjecture 5.1, formula (5.2), on p. 78 of Jian Liu, *Improvements of two inequalities in an acute triangle*, International Journal of Geometry 13 (2024), no. 4, 63–79. [Original article](https://ijgeometry.com/wp-content/uploads/2024/09/6.-63-79.pdf).

The argument does not assume the source article's asserted acute-triangle altitude inequality (5.3). The theorem here covers acute, right, and obtuse nondegenerate triangles.

## 2. Two radical estimates

For $-1/4\le x\le1/4$,

$$
\sqrt{1+x}\ge1+\frac{x}{2}-\frac{x^2}{6},\qquad
(\sqrt{1+x})^3\ge1+\frac{3x}{2}+\frac{x^2}{3}.
$$

Both right-hand sides are positive. The differences of squares are

$$
(1+x)-(1+x/2-x^2/6)^2
=x^2(1/12+x/6-x^2/36),
$$

$$
(1+x)^3-(1+3x/2+x^2/3)^2
=x^2(1/12-x^2/9).
$$

On this interval the bracketed factors are at least $23/576$ and $11/144$, respectively. Comparing the nonnegative quantities proves the estimates. These are `LiuReal.sqrt_lower` and `LiuReal.sqrt_cube_lower` in [RealBounds.lean](../RealBounds.lean).

## 3. A neighborhood of the equilateral triangle

First normalize the arithmetic mean of the sides to one, writing the sides as $1+p,1+q,1+r$, where

$$
p+q+r=0,\qquad |p|,|q|,|r|\le1/10.
$$

Put $T=p^2+q^2+r^2$, so $0\le T\le3/100$. Define cyclically

$$
u_p=-2p+\frac23T-p^2,\qquad
D_p=(q-r)^2,\qquad
z_p=\frac{1-2p}{(2-p)^2}D_p,\qquad d_p=-2p-z_p.
$$

Direct substitution in the length formulas gives

$$
m_a=\frac{\sqrt3}{2}\sqrt{1+u_p},\qquad
w_a=\frac{\sqrt3}{2}\sqrt{1+d_p}.
$$

We have $|u_p|\le23/100<1/4$ and $\sum u_p=T$. Also

$$
0\le\frac{1-2p}{(2-p)^2}\le\frac13,
$$

because $(2-p)^2-3(1-2p)=(1+p)^2$. Thus $0\le z_p\le D_p/3$, $D_p\le1/25$, $z_p\le1/75$, and $z_p^2\le D_p/225$. In particular, $|d_p|\le1/5+1/75<1/4$.

Since $\sum D_p=3T$, we obtain

$$
\sum z_p\le T,\qquad \sum z_p^2\le T/75,\qquad \sum d_p\ge-T.
$$

The elementary inequality $(2p+z_p)^2\le5p^2+5z_p^2$ follows from $(p-2z_p)^2\ge0$. Consequently,

$$
\sum d_p^2\le5T+5T/75\le\frac{11}{2}T.
$$

Set $M=\sum(\sqrt{1+u_p})^3$ and $W=\sum\sqrt{1+d_p}$. Applying Section 2, and discarding the nonnegative term $\frac13\sum u_p^2$ when bounding $M$, gives exactly the estimates used in Lean:

$$
M\ge3+\frac32T,\qquad
W\ge3+\frac12\sum d_p-\frac16\sum d_p^2
\ge3-\frac{17}{12}T.
$$

Both lower bounds are positive. Their product satisfies

$$
WM\ge\left(3-\frac{17}{12}T\right)\left(3+\frac32T\right)
=9+\frac14T-\frac{17}{8}T^2
\ge9+\frac18T,
$$

where the last inequality uses $T\le3/100<1/17$. Restoring the length factors yields the quantitative bound

$$
(\sum w_a)(\sum m_a^3)\ge\frac{81}{16}+\frac{9}{128}T.
$$

The semiperimeter is $3/2$, so its fourth power is $81/16$. This proves the target inequality throughout this neighborhood. Equality forces $T=0$, hence $p=q=r=0$.

The corresponding results are `aggregate_local_bounds_gap`, `local_radical_product_gap`, and `local_triangle_gap` in [RealBounds.lean](../RealBounds.lean), followed by `local_equality` in [Equality.lean](../Equality.lean). The older helper `local_product_bound` is not the estimate assembled in this final argument.

For general sides whose deviations from their mean $t=(a+b+c)/3$ are at most 10%, apply this result to $a/t,b/t,c/t$. All terms in the target inequality scale by $t^4$.

## 4. The global domain and subdivision

The target expression is symmetric and homogeneous of degree four. Sort the sides and rescale the longest side to one. Write the resulting sides as $x,y,1$. Every original triangle then lies in

$$
0\le x\le y\le1,\qquad x+y\ge1,
$$

inside the rectangle $[0,1]\times[1/2,1]$. This closed domain also contains degenerate boundary points. Its denominators $x+y$, $x+1$, and $y+1$ are positive.

The implementation uses $S=2^{24}$ and sides $A=Sx,B=Sy,S$. The initial integer box is $[0,S]\times[S/2,S]$. A box is $[A_0,A_1]\times[B_0,B_1]$; its endpoints are integers but the sides $A,B$ range over all real points in the box.

Each split bisects a longest coordinate interval at the integer midpoint, choosing the first coordinate in a tie. The two closed children cover the entire parent, including their common boundary. Induction on the recorded tree proves continuous coverage. This is not a test only at grid points.

Every leaf is checked in one of three ways:

1. **Empty:** $A_1+B_1<S$ or $A_0>B_1$. No point of the sorted triangle domain lies in that box.
2. **Analytic neighborhood:** all relevant points are within 10% of their mean, so Section 3 applies.
3. **Strict interval inequality:** rational lower bounds for the six lengths imply a strict product inequality throughout the box.

## 5. Analytic leaf checks

Let $L=A_0+B_0+S$. The analytic checker requires

$$
\begin{aligned}
10|2A_0-B_1-S|&\le L,&10|2A_1-B_0-S|&\le L,\\
10|2B_0-A_1-S|&\le L,&10|2B_1-A_0-S|&\le L,\\
10|2S-A_1-B_1|&\le L,&10|2S-A_0-B_0|&\le L.
\end{aligned}
$$

For a point in the box, the deviations of the sides from their mean, divided by that mean, are

$$
\frac{2A-B-S}{A+B+S},\qquad
\frac{2B-A-S}{A+B+S},\qquad
\frac{2S-A-B}{A+B+S}.
$$

The six tests bound the absolute numerators over the whole box, and $L>0$ bounds the denominator below. They therefore imply the hypotheses of Section 3. This implication is proved by `LiuMain.local_leaf_sound` and its equality counterpart `LiuEquality.local_leaf_equality`.

## 6. Strict interval leaf checks

Let $Q=2^{40}$. Each interval leaf supplies six natural numbers $M_a,M_b,M_c,W_a,W_b,W_c$. They represent lower bounds $SM_a/Q$ and $SW_a/Q$ for the actual lengths of the triangle with sides $A,B,S$.

For a generic length corresponding to a side in $[U_0,U_1]$, with the other sides in $[V_0,V_1]$ and $[Z_0,Z_1]$, the checker tests

$$
4S^2M^2\le Q^2(2V_0^2+2Z_0^2-U_1^2)_+,
$$

$$
S^2(V_1+Z_1)^2W^2
\le Q^2V_0Z_0(U_0+V_0+Z_0)(V_0+Z_0-U_1)_+,
$$

where $v_+=\max(0,v)$. Apply these tests to the three cyclic choices of intervals, using $[S,S]$ for the longest side. The final test is

$$
Q^4(A_1+B_1+S)^4
<16S^4(W_a+W_b+W_c)(M_a^3+M_b^3+M_c^3).
$$

Why these suffice: monotonic bounds on the squared length formulas imply $SM_a/Q\le m_a$ and $SW_a/Q\le w_a$, and cyclically. The semiperimeter is at most $(A_1+B_1+S)/2$. The final strict test therefore proves $(\sum w_a)(\sum m_a^3)>s^4$ for every domain point in that box.

All certificate arithmetic is natural-number arithmetic. In particular, subtraction is truncated at zero; it must not be silently interpreted as signed subtraction. The positive parts above express that convention. The real-number justification, including the zero lower-bound cases, is proved in `scaled_median_interval`, `scaled_bisector_interval`, and `certified_triangle_interval` in [RealBounds.lean](../RealBounds.lean).

## 7. Certificate, conclusion, and equality

The explicit tree contains 3030 strict interval leaves, 87 analytic-neighborhood leaves, 123 empty leaves, and 3239 binary splits: 6479 nodes in total, with no unresolved leaf. Its full data and Boolean checker are in [Certificate.lean](../Certificate.lean).

`certificate_passes : check root certificate = true` is proved by `by decide`. This establishes exact finite arithmetic. The separate soundness proofs are essential: [CheckerCoverage.lean](../CheckerCoverage.lean) proves coverage; [Main.lean](../Main.lean) supplies the real-number correctness of both nonempty leaf types, applies the checked tree, and removes the scale and ordering restrictions. Its final theorem is `LiuMain.liu_conjecture_5_1`.

For equality, no empty leaf contains a domain point and every interval leaf is strict. Any equality point must therefore fall in an analytic leaf. Section 3 forces all three sides to equal their mean. Rescaling and permuting preserve this conclusion. Conversely, for $a=b=c=\ell>0$, all six lengths equal $\sqrt3\,\ell/2$, and both sides of the target identity are $81\ell^4/16$. This proves `LiuEquality.equality_iff_equilateral` in [Equality.lean](../Equality.lean).

## 8. Replay and source map

Use the toolchain and dependency manifest committed in the repository. From its root:

```sh
lake exe cache get
lake build
lake env lean Main.lean
lake env lean Equality.lean
```

The commands require Git, Lean via elan, and network access on an initial setup. The certificate is already committed; no Python generator or exploratory search is needed for verification. The final two theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders, `native_decide`, or newly postulated mathematical axioms in the five proof sources.

| Mathematical step | Lean entry |
| --- | --- |
| Length definitions and real bounds | `LiuReal.median`, `bisector`, `certified_triangle_interval` |
| Quantitative local estimate | `LiuReal.local_triangle_gap` |
| Exact finite checker | `LiuCertificate.certificate_passes` |
| Coverage of all real points | `LiuCertificate.check_sound`, `verified_cover` |
| Actual leaf soundness | `LiuMain.local_leaf_sound`, `interval_leaf_sound` |
| All nondegenerate triangles | `LiuMain.liu_conjecture_5_1` |
| Complete equality classification | `LiuEquality.equality_iff_equilateral` |

See [research status](RESEARCH_STATUS.md) for replay records and the limits of the claim. Compiler verification and independent mathematical peer review are different checks.
