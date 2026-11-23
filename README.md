# WOWII Conjecture 399b is false: a Lean proof

This repository is a Lean 4 package, laid out for the [Palomar registry](https://palomar-registry.org/),
that proves Conjecture 399b of E. DeLaViña's *Written on the Wall II* (conjectures of Graffiti.pc) false.

## The statement

Conjecture 399b says that every connected graph G on n > 2 vertices satisfies

γ₂(G) ≤ WP(Ḡ) + ⌊3/α(G[A₃])⌋,

where γ₂ is the 2-domination number (the least size of a set D such that every vertex outside D has at
least two neighbours in D), WP(Ḡ) is the Welsh–Powell invariant of the complement (the largest k with
k + d_k ≤ n, where d_1 ≤ … ≤ d_n are the degrees of G), A₃ is the set of vertices of degree at least
three, and α(G[A₃]) is the independence number of the subgraph induced by A₃.

The theorem `WrittenOnTheWallII.GraphConjecture399b.conjecture399b` proves the negation, for connected
graphs on more than two vertices whose set A₃ is nonempty (when A₃ is empty the source's 3/0 is
undefined, so this hypothesis only weakens the conjecture). The counterexample is a connected graph F₃
on 12 vertices, graph6 `KCOfFFb?~?[?`, with γ₂ = 7, WP(Ḡ) = 6 and α(G[A₃]) = 4, so that
7 > 6 = 6 + ⌊3/4⌋. The readings of the source's definitions are listed under `fidelity` in
`formalization.yaml`.

## Files

| File | Content |
|---|---|
| `Challenge.lean` | the definitions and the statement, ending in `sorry`; this is the file to audit |
| `Solution.lean` | the same definitions and theorem, proved, with bridge lemmas to the preprint's Lean supplement |
| `comparator.json` | the configuration for [Comparator](https://github.com/leanprover/comparator): the theorem compared and the permitted axioms (propext, Classical.choice, Quot.sound) |
| `formalization.yaml` | metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) v0.4 format: sources, readings of the source, AI use, review |
| `LICENSE` | Apache License 2.0 |

## Building

The toolchain is Lean `v4.37.0-rc1` (`lean-toolchain`) and Mathlib is pinned at commit
`31ce06eaadf4a200c0e1407c5f10953cf606b8f8` (`lake-manifest.json`). With
[elan](https://github.com/leanprover/elan) installed:

    lake exe cache get
    lake build

`Challenge` reports one `sorry`, the statement left for the Solution to prove. `Solution` uses only the
axioms propext, Classical.choice and Quot.sound.

## Sources

- The preprint, with its hand proof for the family F_q (q ≥ 3) and its own Lean supplement:
  [jirichmel/wowii-399b-counterexample](https://github.com/jirichmel/wowii-399b-counterexample)
  (version 1 at commit `8b450009c511d999d33746b3b87bb50fc489b731`).
- E. DeLaViña, *Written on the Wall II (Conjectures of Graffiti.pc)*:
  <http://cms.dt.uh.edu/faculty/delavinae/research/wowII/>, Conjecture 399b and definitions 90 and 113.
- `IsTwoDominating` and `twoDominationNumber` are copied from the open Formal Conjectures pull request
  [#7320](https://github.com/google-deepmind/formal-conjectures/pull/7320).

## Use of AI

The counterexample search, the proofs, the paper and this Lean formalization were produced by Claude
Opus 5.5 agents in Claude Code (Anthropic), under the direction of Jiří Chmel, who chose the problems
and the lines of work, set the working rules, and decided what to write up and publish. Further Claude
agents, writing programs of their own, refereed the proof and reviewed the formal statement. The Lean
kernel's check of the proof does not depend on any AI system. No human referee has reviewed this work
yet. Details are under `automation` and `review` in `formalization.yaml`.

## Author and licence

Jiří Chmel (GitHub: [jirichmel](https://github.com/jirichmel)) is the author and maintainer. The package
is released under the Apache License 2.0; the definitions taken from Formal Conjectures keep their
copyright line, "The Formal Conjectures Authors", also under Apache 2.0.
