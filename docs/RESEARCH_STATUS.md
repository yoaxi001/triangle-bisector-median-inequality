# Research status and remaining work

Date: 2026-11-19.

## Reproduction completed

The four proof modules were rebuilt from the independent D-drive repository. The portable Lake build then passed on GitHub's Ubuntu runner, including the final theorem axiom report: [run 44510445305](https://github.com/yoaxi001/liu51-proof/actions/runs/44510445305), source commit `4e8d2db955efa1d80984bc869aa74fe4accb149e`. The report contains only propext, Classical.choice and Quot.sound. This supplies a separate-machine replay; it does not supply independent expert review or novelty verification.

## Established in the formal proof

* The inequality for every positive real triple satisfying all three strict triangle inequalities.
* A local analytic proof near equal sides.
* Sound real interval bounds derived from natural-number certificates, including truncated subtraction.
* Complete recursive coverage of the normalized sorted triangle domain.
* Removal of normalization and side-order restrictions.

The proof does not assume the source article's stated acute-triangle altitude inequality.

## Before making a priority or publication claim

1. Ask an independent reviewer to replay and inspect the proof. The automated portable Lake replay on GitHub has passed; its logs are linked above.
2. Independently review the actual theorem assumptions and the definitions of median and bisector, not only compiler success.
3. Search later papers, alternate formulations, and public repositories for earlier solutions. Current searches are not a proof of novelty.
4. Reconcile the human-readable proof outline with the exact estimates used in Lean and prepare a concise mathematical exposition.

## Optional extensions

* Formalize that equality holds exactly for equilateral triangles. Equilateral attainment follows by direct substitution, but the converse is not part of the current checked theorem.
* Derive the side-length formulas inside a Euclidean geometry library.
* Seek a shorter purely analytic proof or reduce the certificate size.

No journal/arXiv acceptance, independent expert review, or first-solution claim is implied by this repository. These remaining tasks do not introduce assumptions into the already compiled inequality theorem.
