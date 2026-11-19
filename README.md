# A Lean 4 Proof of Jian Liu’s Triangle Inequality for Angle Bisectors and Medians

**Theorem (Jian Liu’s Conjecture 5.1).** For any nondegenerate triangle, let $w_a,w_b,w_c$ be its internal angle-bisector lengths, $m_a,m_b,m_c$ its median lengths, and $s$ its semiperimeter. Then

$$
(w_a+w_b+w_c)(m_a^3+m_b^3+m_c^3)\ge s^4.
$$

Equality holds if and only if the triangle is equilateral.

[![Verify Lean proof](https://github.com/yoaxi001/triangle-bisector-median-inequality/actions/workflows/lean.yml/badge.svg)](https://github.com/yoaxi001/triangle-bisector-median-inequality/actions/workflows/lean.yml)

This repository proves the side-length formulation of Conjecture 5.1 in Jian Liu, *Improvements of two inequalities in an acute triangle*, International Journal of Geometry 13 (2024), no. 4, 63–79, p. 78.

[Original problem](https://ijgeometry.com/wp-content/uploads/2024/09/6.-63-79.pdf).

## Verification status

The main theorem is `LiuMain.liu_conjecture_5_1` in [Main.lean](Main.lean). Its only mathematical hypotheses are positivity of a,b,c and the three strict triangle inequalities. It uses the standard explicit side-length formulas for medians and internal bisectors, defined in [RealBounds.lean](RealBounds.lean). Euclidean points and a separate geometric derivation of these formulas are not formalized.

The theorem has been compiled locally using Lean 4.19.0 and mathlib v4.19.0. Its axiom report is:

```text
[propext, Classical.choice, Quot.sound]
```

The standard Lake build and the final axiom report also passed on GitHub's Ubuntu runner on 2026-11-19, for source commit `4e8d2db955efa1d80984bc869aa74fe4accb149e`: [successful verification run](https://github.com/yoaxi001/triangle-bisector-median-inequality/actions/runs/44510445305). This is a separate machine replay, not an independent mathematical peer review.

The proof has no `sorry`, `admit`, newly postulated mathematical axiom, or `native_decide`. The finite certificate uses `by decide`, checked by Lean's kernel.

The complete equality classification is formalized in `LiuEquality.equality_iff_equilateral` in [Equality.lean](Equality.lean): equality holds if and only if `a = b` and `b = c`. It has passed local compilation with the same standard axiom report; consult Actions for the remote replay of each revision.

This is an AI-assisted research result. Novelty, priority, and publication suitability have not been independently established. It has not received independent expert review. See [research status](docs/RESEARCH_STATUS.md) and [AI contribution disclosure](AI_DISCLOSURE.md).

## Reproduce

Install [Lean via elan](https://lean-lang.org/install/) and Git, then run from the repository root:

```sh
lake update
lake exe cache get
lake build
lake env lean Main.lean
```

The Lean toolchain and mathlib revision are pinned. GitHub Actions replays the build; consult the Actions tab for the outcome of subsequent revisions. The initial portable Lake workflow has passed in the run linked above.

The certificate computation is substantial compared with the analytic lemmas. The exact certificate, including its subdivision tree, is committed as source, so the Python search/generation environment is not required to verify the theorem.

## Proof structure

* [Certificate.lean](Certificate.lean): integer checker and explicit complete subdivision certificate.
* [RealBounds.lean](RealBounds.lean): radical bounds, analytic near-equilateral theorem, and integer-to-real interval soundness.
* [CheckerCoverage.lean](CheckerCoverage.lean): empty-box correctness and gap-free recursive coverage.
* [Main.lean](Main.lean): actual leaf correctness, certificate application, scaling, permutations, and the all-triangles theorem.
* [Equality.lean](Equality.lean): complete equality classification using a quantitative local gap and strict interval leaves.

The certificate contains 3030 strict interval leaves, 87 analytic-neighborhood leaves, and 123 empty leaves. Numerical sampling is not used as evidence inside the formal theorem.

[Human-readable proof outline](docs/proof-outline.md). The outline currently uses a slightly stronger local estimate than the Lean implementation; it should be harmonized before use as a paper.

## 中文说明

主不等式及“等号当且仅当三角形等边”的分类均已通过本地 Lean 验证。仓库用于公开源码、接受复现和审查，不宣称已确认首次解决，也不宣称已通过同行评审。剩余工作包括独立专家复核、核对形式化命题与原猜想、新颖性查证，以及整理与代码一致的论文。

Code and repository-authored documentation are released under the MIT license. The cited article and external dependencies retain their own licenses; the article itself is not redistributed here.
