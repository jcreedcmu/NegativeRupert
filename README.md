# Noperthedron

This project formalizes the main result of
["A convex polyhedron without Rupert's property"](https://arxiv.org/abs/2508.18475)
by Jakob Steininger & Sergey Yurkevich (cited as `[SY25]` herein).

We prove, using the Lean 4 theorem prover, that the Noperthedron does not "[fit through itself](https://en.wikipedia.org/wiki/Prince_Rupert%27s_cube)".

<p align="center">
<img src="./home_page/assets/noperthedron.png" width="200" alt="noperthedron">
</p>

The definition of the main theorem's *proposition* lives in [MainTheorem.lean](Noperthedron/MainTheorem.lean).

The proof of the main theorem, given existence of a valid solution table, lives in
[ProofOfMainTheoremWithHole.lean](Noperthedron/ProofOfMainTheoremWithHole.lean).

Construction of a valid solution table requires a large case analysis. We provide
three different versions:

1. A kernel-only proof [KernelCaseAnalysis/ProofOfMainTheorem.lean](KernelCaseAnalysis/ProofOfMainTheorem.lean) that depends only on the standard 3 axioms `[propext, Classical.choice, Quot.sound]`. This proof takes ~80 minutes to check on a 16-core machine.

2. A `native_decide` proof [NativeCaseAnalysis/ProofOfMainTheorem.lean](NativeCaseAnalysis/ProofOfMainTheorem.lean) that takes ~2.5 minutes on a 16-core machine.

3. A native executable [`constructValidTable`](constructValidTable.lean) that takes ~30 seconds to run on a 16-core machine.

## Getting Started

[Install Lean](https://lean-lang.org/install/manual/), clone this project, then build it with:

```
lake exe cache get
lake build
```

To check the solution table, first make sure that you have `git-lfs`. Then unzip the table:

```
unzip solution_tree_v6.zip
```

To run the expensive kernel check (~24 core hours):
```
lake build KernelCaseAnalysis
```

To run the less expensive `native_decide` check (~40 core minutes):
```
lake build NativeCaseAnalysis
```

To run the even less expensive native executable check (~8 core minutes) :

```
lake exe constructValidTable solution_tree_v6.csv
```


To build the blueprint, install [leanblueprint](https://github.com/PatrickMassot/leanblueprint) with something like
```
pip install leanblueprint
```
Then you can build all HTML and PDF content and check correspondence of blueprint decls (i.e. uses of `\lean`) with
actual lean identifiers by doing
```
leanblueprint all
```
To run a server hosting the html, run
```
leanblueprint serve
```

## License Information

Portions of this project use Apache License 2.0–licensed code from
https://github.com/badly-drawn-wizards/noperthedron
©2025 Reuben Steenekamp
See LICENSE for details.
