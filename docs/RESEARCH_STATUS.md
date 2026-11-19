# Project status

Updated: 2026-11-19. This is a personal, AI-assisted mathematics exploration by a physics student, shared on GitHub for reading, reproduction, and feedback. Journal or arXiv submission is not a project requirement.

## Completed

* The inequality for every positive real triple satisfying all three strict triangle inequalities, using the standard side-length formulas for medians and internal angle bisectors.
* An analytic proof near equal sides, including a quantitative positive gap away from equality.
* Sound real interval bounds derived from natural-number certificates, including truncated subtraction.
* Complete recursive coverage of the normalized sorted triangle domain.
* Removal of normalization and side-order restrictions.
* Equality if and only if the three sides are equal.
* A [human-readable exposition](proof-outline.md) using the same local estimates as the final Lean implementation, with the finite checker and equality argument explained.
* A [Chinese reading guide](guide-zh.md) and public reproduction instructions.

The proof does not assume the source article's stated acute-triangle altitude inequality.

## Verification records

The five proof modules are `Certificate`, `RealBounds`, `CheckerCoverage`, `Main`, and `Equality`. They have passed local Lean 4.19.0 compilation. The final inequality and equality theorems have only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

The portable Lake build has also passed on GitHub's Ubuntu runner:

* [Initial inequality replay, run 44510445305](https://github.com/yoaxi001/triangle-bisector-median-inequality/actions/runs/44510445305), source commit `4e8d2db955efa1d80984bc869aa74fe4accb149e`.
* [Inequality and equality replay, run 44513726995](https://github.com/yoaxi001/triangle-bisector-median-inequality/actions/runs/44513726995), source commit `19fdc92d76548d176e8e8e8729f6028cd3ab918c`.

These are separate-machine replays, not independent expert reviews. Consult [Actions](https://github.com/yoaxi001/triangle-bisector-median-inequality/actions) for checks on later revisions.

## Scope and limits

The formal statement uses explicit algebraic formulas for the six lengths. A derivation of those formulas inside a Euclidean geometry library is not included. The final theorem has no unresolved leaf assumptions: the analytic and interval soundness hypotheses of the general coverage theorem are discharged in `Main.lean` and `Equality.lean`.

Exploratory computations helped find the certificate. They are not required as trusted evidence when replaying the committed Lean proof. The Python generation environment is not included as a reproduction dependency.

The 2026-11-19 search of the original title, author/conjecture terms, formula-related terms, arXiv-indexed pages, and GitHub repository/code search did not locate another proof of this precise inequality. Search indexes are incomplete; this is a dated search observation, not a proof of novelty or priority. No claim that the result is the first solution, independently reviewed, or accepted by a journal is made.

## Optional future exploration

Independent review, a shorter analytic proof, a smaller certificate, and a formal derivation of the geometric length formulas would all be useful additions. None is required to keep this GitHub project public or to replay the existing formal theorem. Reports of an earlier proof or a mismatch in the statement are welcome.
