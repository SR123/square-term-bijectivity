# Checking the square term matrix formalisation

The signature used by the paper has one constant `o` and three binary operations `D`, `G`, `H`. The syntax fixes exactly three input variables. For each finite presentation and word, the main theorem quantifies over all common interpretations on all finite nontrivial carriers. It proves that a bijective interpretation exists if and only if the word has nonidentity image under a surjective homomorphism onto a finite group. [Main equivalence](SquareReduction.lean)

## Reproduce the build

Use [Elan](https://github.com/leanprover/elan) with access to the pinned dependencies. From this directory run

```sh
lake exe cache get
lake --wfail build
```

The [toolchain](lean-toolchain) pins Lean 4.26.0. The [manifest](lake-manifest.json) pins Mathlib to commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and records the transitive dependency revisions. The two default targets build all eight local modules. Mathlib’s cache avoids rebuilding the external library.

The [fresh compilation record](fresh-verification.txt) lists every module, its SHA-256 and the axiom reports emitted by the compiler. This check started with empty build outputs for the project and reused dependency libraries at the pinned revisions. The [full signatures and original source check](verification.txt) and [Lake build output](lake-build.txt) provide complementary records. The audited declarations have only Lean's standard classical axioms among their dependencies.

## Reading the proof

| Mathematical step | Lean declaration or file |
| --- | --- |
| Build three literal terms in the fixed signature by simultaneous substitution | `SquareBijection.compile`, `compile_iff` in [SquareTerms](SquareTerms.lean) |
| Rule out a second row containing the marker by a collision | `Cycle372.exclusive`, `Cycle372.compile_identity` in [Cycle372Collision](Cycle372Collision.lean) |
| From arbitrary passing tables to a finite group action moving a point | `forced_laws`, `group_witness_of_action`, `compile_sound` in [SquareSoundness](SquareSoundness.lean) |
| From a separating finite group to passing tagged and cyclic tables | `compile_complete` in [SquareWitness](SquareWitness.lean) |
| Bridge between generator tables and quotients of a presented group | `finite_model_iff_quotient` in [SquareGroups](SquareGroups.lean) |
| Equivalence on numbered alphabets and on arbitrary finite nontrivial carriers | `compiledTriple_iff_finiteQuotient`, `arbitraryFiniteCarrier_iff_finiteQuotient` in [SquareReduction](SquareReduction.lean) |
| Exact padded maximum, fresh decoders, arithmetic for the extra output | `exact_maximum_iff_finiteQuotient`, `decoder_attains_image`, `oneUnit_iff_cutExponent` in [SquareGap](SquareGap.lean) |

The additional [PaperTriple](PaperTriple.lean) module checks an earlier construction using more operation symbols. Its order-preserving witness theorem concerns that construction. For the paper’s smaller signature, use **SquareReduction** above.

The numerical lemma `oneUnit_iff_cutExponent` assumes an upper bound $\delta(n)\le n^\rho$ for every $n\ge2$ and a routing estimate $n^\rho\le K\delta(n)$ for every sufficiently large $n$. The paper uses the explicit routing bound at sizes $sm$ instead. Both estimates are supplied by the published unfiltered term-cut theorem. The proof of undecidability invokes Bridson and Wilton’s fixed-presentation theorem, and the complexity claim uses the polynomial-time computation of a vertex cut. [Term-cut theorem and algorithm, §5](https://arxiv.org/html/2602.08110v2#S5) · [Finite-group input, Theorem 2.1](https://doi.org/10.1007/s00222-015-0578-8)

## Source credits

Søren Riis developed the square argument interactively with Astra and Claude. The collision lemma, tagged-letter construction and finite-quotient equivalence belong to this project. The signed-word and presented-group bridge in `SquareGroups.lean` adapts selected results from `Core.lean` and `PresentationBridge.lean` in the development for the author's previous paper. The new square proof can be built directly from this folder.

For the adapted upstream material, copyright 2026 Søren Riis, the original [Apache-2.0 licence](upstream/LICENSE) and [attribution notice](upstream/NOTICE.md) are included. These upstream files describe the earlier distribution. [Earlier paper and verification scope](https://arxiv.org/html/2504.16265v4#S8) · [Earlier proof repository](https://github.com/SR123/term-coding-disequality-lean) · [Earlier archived verification](https://doi.org/10.5281/zenodo.22727895)
