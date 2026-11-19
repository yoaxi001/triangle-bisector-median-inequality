# Equality classification

The checked theorem is `LiuEquality.equality_iff_equilateral` in Equality.lean. For positive sides satisfying the three strict triangle inequalities, it states that the bisector-sum/median-cube product equals the fourth power of the semiperimeter if and only if a=b and b=c.

## Analytic neighborhood

Write the mean-normalized sides as 1+p,1+q,1+r, where p+q+r=0 and the three absolute deviations are at most 1/10. Set T=p²+q²+r². The new lemma `local_triangle_gap` proves the stronger lower bound

    product >= 81/16 + (9/128) T.

The proof uses normalized sums M>=3+3T/2 and W>=3-17T/12. Their product is at least 9+T/4-17T²/8, which is at least 9+T/8 for 0<=T<=3/100. Restoring the common length factor gives the displayed gap.

If equality holds, T=0, hence p=q=r=0. Homogeneity transfers this conclusion to the actual side lengths.

## Other certificate leaves

All interval leaves already certify a strict inequality. Equality is therefore impossible there. The same coverage theorem, instantiated with the equality implication as its target proposition, proves the classification across the entire normalized domain. Scaling and permutation lemmas then cover every valid side ordering and size.

## Attainment

For equilateral side a, each median and internal bisector has length sqrt(3)a/2. Direct substitution gives product 81a⁴/16, equal to (3a/2)⁴.

The final theorem's axiom report contains only propext, Classical.choice and Quot.sound, with no sorryAx or new mathematical assumptions. Independent expert review and novelty checking remain separate research tasks.
