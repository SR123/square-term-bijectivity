# Undecidability of the square term matrix problem

**Søren Riis · Queen Mary University of London**

**Cite this version** · Søren Riis (2026), *Undecidability of the square term matrix problem*, version 1.0.0. [Paper, tutorial and Lean archive on Zenodo](https://doi.org/10.5281/zenodo.24448188).

Can three expressions in three variables encode their inputs without losing information? Each operation symbol is free to take any table, provided that every occurrence uses the same table. The paper proves that no algorithm can decide whether a given triple is bijective on the cube of **some finite alphabet of size at least two**. A single constant and three binary operation symbols suffice.

**[Read the three-page paper](paper/square-term-bijectivity.pdf)** · **[Work through the proof with examples](tutorial/how-three-terms-force-a-group.pdf)** · **[Check the Lean formalisation](lean/README.md)**

The reduction turns a word in a finitely presented group into three ordinary terms. Reversibility forces each relator to fix every point, while a final test forces the word to move a distinguished point. The letter permutations then provide a finite quotient in which the word survives. In the other direction, any such quotient supplies explicit tables witnessing bijectivity.

## The one-unit gap

For each fixed $d\ge 3$, compare two questions on the same ordinary term tuples. In each question both the shared tables and the alphabet size $n\ge 2$ may be chosen. The dispersion is the maximum number of distinct outputs.

| Can the dispersion reach this threshold for some $n$? | Decision complexity |
| --- | --- |
| $n^d$ | Undecidable |
| $n^d+1$ | Polynomial time |

Both conclusions already hold for $d+1$ listed variables and $d+1$ output terms over the fixed signature. A minimum cut in the graph of subterms decides the second question.

## How this extends the earlier term-coding paper

*One Unit Separates Polynomial Time from Undecidability in Term Coding* treats inputs subject to disequality tests, with $x,y$ as the first two outputs and $x\ne y$ required. For each fixed $d\ge 2$, its thresholds are $n^d-n^{d-1}$ and $n^d-n^{d-1}+1$. Its Lean development checks the forcing and finite-group reduction for that setting, cut and routing arguments, the strict criterion, and algorithmic results. Section 8 specifies the exact scope. [Earlier paper, §8](https://arxiv.org/html/2504.16265v4#S8) · [Earlier Lean repository](https://github.com/SR123/term-coding-disequality-lean) · [Archive of the earlier verification, DOI 10.5281/zenodo.22727895](https://doi.org/10.5281/zenodo.22727895)

The new construction admits every input. The eight Lean modules here check its literal three-term compiler, the finite-quotient equivalence in both directions, the exact count after padding, and the strict-threshold implication under explicit cut and routing hypotheses. The finite-group undecidability theorem, general unfiltered cut and routing estimates, and the polynomial running time of max-flow are cited mathematical inputs. [New verification guide and theorem names](lean/README.md)

The three-variable problem appeared as Problem 6.1 in *Term Coding and Dispersion*. The present proof supplies the missing forcing argument by a different construction. [Problem 6.1 and the earlier term-cut theorem](https://arxiv.org/abs/2602.08110v2) · [Bridson and Wilton, Theorem 2.1](https://doi.org/10.1007/s00222-015-0578-8)

## Files and reproduction

| Material | Files |
| --- | --- |
| Paper | [PDF](paper/square-term-bijectivity.pdf) · [LaTeX source](paper/square-term-bijectivity.tex) |
| Companion tutorial | [PDF](tutorial/how-three-terms-force-a-group.pdf) · [LaTeX source](tutorial/how-three-terms-force-a-group.tex) |
| Verification | [Lean sources and build instructions](lean/README.md) · [Fresh build record](lean/fresh-verification.txt) · [Theorem signatures and axioms](lean/verification.txt) |
| Credits for reused Lean material | [Upstream attribution and licence](lean/README.md#source-credits) |

Each PDF builds from its single source file with a standard TeX Live installation. From the repository root, run

```sh
latexmk -cd -pdf paper/square-term-bijectivity.tex
latexmk -cd -pdf tutorial/how-three-terms-force-a-group.tex
```

## Licences

The paper and tutorial are available under CC BY 4.0, and the Lean code under Apache 2.0. [Licence details and upstream attribution](LICENSE.md).
