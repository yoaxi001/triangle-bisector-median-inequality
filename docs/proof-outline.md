# A self-contained computer-assisted proof candidate for Liu's Conjecture 5.1

Date: 2026-11-19. Status: analytic argument plus exact finite certificates. The complete real-number theorem has NOT yet been checked in Lean. This note supersedes the acute-case dependency in proof_candidate.md. Novelty and external mathematical review remain outstanding.

## The claim

For every nondegenerate triangle with medians m_a,m_b,m_c, internal bisectors w_a,w_b,w_c and semiperimeter s,

    (sum w_a)(sum m_a^3) >= s^4,

with equality only for equilateral triangles. The statement is Conjecture 5.1 of Jian Liu, International Journal of Geometry 13 (2024), no. 4, pp. 63–79, p. 78:
https://ijgeometry.com/wp-content/uploads/2024/09/6.-63-79.pdf

This argument does not invoke the source's asserted altitude inequality (5.3).

## 1. Two elementary radical bounds

For -1/4 <= x <= 1/4,

    sqrt(1+x) >= 1+x/2-x^2/6,
    (1+x)^(3/2) >= 1+3x/2+x^2/3.

Both right-hand sides are positive. Squaring is justified, and the differences of the squares are, respectively,

    (1+x) - (1+x/2-x^2/6)^2 = x^2(1/12+x/6-x^2/36),
    (1+x)^3 - (1+3x/2+x^2/3)^2 = x^2(1/12-x^2/9).

The bracketed factors are at least 23/576 and 11/144, respectively, on this interval. This proves both bounds without approximations.

## 2. Analytic neighborhood of the equilateral triangle

Normalize the arithmetic mean of the three sides to one. Write the sides as 1+p,1+q,1+r, where p+q+r=0, and assume

    |p|,|q|,|r| <= e=1/10.

Set T=p^2+q^2+r^2, so 0<=T<=3/100. Cyclic subscripts below refer to p,q,r. The median and bisector identities give

    m_p^2 = (3/4)(1+u_p),  u_p=-2p+(2/3)T-p^2,
    w_p^2 = (3/4)(1+d_p),  d_p=-2p-k_p(q-r)^2,
    k_p=(1-2p)/(2-p)^2.

The second identity follows by inserting the sides into

    w_a^2=bc(a+b+c)(b+c-a)/(b+c)^2.

Here 0<=k_p<=1/3: the latter inequality is equivalent to

    3(1-2p) <= (2-p)^2,

whose difference is (1+p)^2. Consequently

    |u_p| <= 2e+(2/3)T+e^2 <= 23/100 < 1/4,
    |d_p| <= 2e+(1/3)(2e)^2 = 16/75 < 1/4.

We have sum u_p=T. Put v_p=(2/3)T-p^2; then sum |v_p|<=3T. Thus

    sum u_p^2 = sum(-2p+v_p)^2
              >= 4T-4 sum |p v_p|
              >= (4-12e)T >= (5/2)T.

Applying the second bound in Section 1 yields

    sum m_p^3 >= (3 sqrt(3)/8)(3+(3/2)T+(1/3)(5/2)T)
              = (3 sqrt(3)/8)(3+(7/3)T).

Since sum(q-r)^2=3T, we also have sum d_p >= -T. For D_p=(q-r)^2, use D_p<=4e^2 to get

    sum d_p^2 <= 4T+(4e/3)sum D_p+(1/9)sum D_p^2
              <= (4+4e+(4/3)e^2)T <= 5T.

The first bound in Section 1 therefore gives

    sum w_p >= (sqrt(3)/2)(3-T/2-5T/6)
             = (sqrt(3)/2)(3-(4/3)T).

Both lower bounds are positive. Multiplying them,

    (sum w_p)(sum m_p^3)
      >= (9/16)(3-(4/3)T)(3+(7/3)T)
       = (9/16)(9+3T-(28/9)T^2)
      >= 81/16 = (3/2)^4 = s^4.

The penultimate inequality is strict when T>0 because T<=3/100. Thus the desired inequality holds throughout this entire neighborhood, with equality only at p=q=r=0.

## 3. Global normalization and finite certificate

By symmetry and homogeneity, instead normalize the longest side to c=1 and order a<=b. All triangles lie in the domain

    0<=a<=b<=1, a+b>=1,

inside [0,1] x [1/2,1]. Degenerate boundary points may be included for verification; no denominator a+b, a+1 or b+1 vanishes on this domain.

The exact interval formulas and subdivision rule are as in proof_candidate.md, with two changes:

* No box is excluded using the obtuse-angle condition.
* A box may be discharged using Section 2 whenever all its triangles have sides within 10% of their mean.

For integer box endpoints (A0,A1,B0,B1) at scale S=2^24, the latter is certified by the following six integer tests, with L=A0+B0+S:

    10 |2A0-B1-S| <= L,  10 |2A1-B0-S| <= L,
    10 |2B0-A1-S| <= L,  10 |2B1-A0-S| <= L,
    10 |2S-A1-B1| <= L,  10 |2S-A0-B0| <= L.

Indeed, the deviations from the mean are (2a-b-1)/(a+b+1), (2b-a-1)/(a+b+1), and (2-a-b)/(a+b+1). The tests bound each numerator over the entire box and bound the denominator below. They are sufficient, not necessary.

The full run visited 6479 nodes: 3030 interval leaves, 87 analytic-neighborhood leaves, 123 empty leaves, and 3239 binary splits. There were zero unresolved boxes. Every interval leaf satisfies the desired inequality strictly using rational lower bounds for radicals. Every analytic leaf is covered by Section 2. Empty leaves are excluded only by a+b<1 or a>b. The two children of each split cover their parent, including the shared boundary.

## 4. Verification and reproducibility

Commands from the workspace root:

    python work/liu51_obtuse_certificate.py --full
    python work/liu51_verify.py --full
    python work/liu51_make_lean.py

The independent Fraction-based verifier confirms all 3030 strict interval tests and all coverage. It also independently checks the analytic-neighborhood condition at all four corners of each box, using ratios of affine functions with positive denominator.

The generated Lean file verifies the Boolean finite certificate with `by decide`. This is distinct from proving its soundness over real numbers. Still required for a complete Lean formalization are: the interval soundness theorem, the analytic neighborhood theorem, and the geometric formula/normalization bridge. No claim of a fully formalized geometric theorem is made here.

No random sampling is used in this proof candidate. No claim about prior publication or mathematical novelty follows merely from successful certificate verification.
