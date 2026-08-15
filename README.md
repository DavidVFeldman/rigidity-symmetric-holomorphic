# Rigidity of Symmetric Holomorphic Functions on Infinite-Dimensional Sequence Spaces

David Feldman (University of New Hampshire) and Jon Bannon (Siena College)

[![DOI](https://zenodo.org/badge/1334872632.svg)](https://doi.org/10.5281/zenodo.21944129)

A holomorphic function on a permutation-invariant domain in an
infinite-dimensional sequence space, invariant under all finite permutations
of coordinates, is severely constrained. On domains modeled on the space
c₀ of null sequences, symmetry forces the first differential to vanish along
every constant tail, and constancy propagates along finitely supported
segments: on any c₀₀-chain-connected domain on which the differential
vanishes on the finitely supported directions, the function is constant.
The paper locates the exact boundary of the phenomenon: a proved obstruction
prevents the elementary argument from reaching the exceptional coordinates
of a non-constant point, and any Banach limit on ℓ^∞ shows that mere
topological connectedness admits non-constant symmetric entire functions.

## Formal verification

Every numbered mathematical statement of Sections 2–5 of the paper is
formally verified in Lean 4 against Mathlib. The development
(`lean/RequestProject/Main.lean`) compiles without `sorry`, and every
theorem depends only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`. In one respect the development exceeds the text:
Corollary 4.4(ii) is proved for normed targets with no separation
hypothesis, Hahn–Banach supplying the separating functionals. The
conditional Proposition 6.1 is not formalized as such; its rigidity input is
Corollary 4.4, and the Lifting Lemma on which it rests is stated in the
paper as an open problem.

| Lean name | Paper | Status |
|---|---|---|
| `C00ChainConnected` | Definition 2.1 (chain clause) | def |
| `AdmissiblyHolomorphic` | Definition 2.2 (admissible holomorphy) | def |
| `AdmissiblyHolomorphic.diff_symm` | Lemma 3.1 (base-point identity) | proved |
| `AdmissiblyHolomorphic.cesaro_vanish` | Lemma 3.3 (Cesàro vanishing) | proved |
| `tail_vanish` | Proposition 3.4 (tail vanishing) | proved |
| `diff_vanishes_at_constant` | Corollary 3.5 (vanishing at constants) | proved |
| `rigidity_along_c00` | Proposition 3.6 (segment rigidity) | proved |
| `rigidity_theorem`, `rigidity_theorem_paper` | Theorem 4.1 (rigidity) | proved |
| `diff_vanishes_at_constant` + `tail_vanish` | Proposition 4.2 (unconditional vanishing) | proved |
| `permAct_swap_moves_exceptional` | Remark 4.3 (obstruction) | proved |
| `nosection_scalar`, `nosection` | Corollary 4.4 (vector-valued) | proved |
| `literal_statement_false` | Example 5.1 (two-coset counterexample) | proved |
| `exists_finPermBanachLimit`, `connected_literal_statement_false` | Example 5.2 (Banach-limit counterexample) | proved |

The formalization was carried out with Aristotle (Harmonic) from written
work orders, archived in `verification/`. It corrected the original draft
twice: the permutation identity had omitted the movement of the base point,
and a local-to-global step was false outright, with the counterexample now
part of the development.

## Repository layout

- `paper/` — the paper (LaTeX source and PDF)
- `lean/` — the Lean 4 project; `lake build` inside this directory verifies
  the development against Mathlib (pinned by `lean-toolchain` and
  `lake-manifest.json`)
- `verification/` — the formalization plan, work orders, run summaries, and
  audit reports (the complete audit trail)
- `.github/workflows/ci.yml` — continuous verification on every push

## Building

Lean (requires [elan](https://github.com/leanprover/elan)):

```
cd lean
lake exe cache get
lake build
```

Paper:

```
cd paper
pdflatex rigidity-symmetric-holomorphic.tex
pdflatex rigidity-symmetric-holomorphic.tex
```

## Citation

Archived at Zenodo, concept DOI
[10.5281/zenodo.21944129](https://doi.org/10.5281/zenodo.21944129) (always
resolves to the latest release). See `CITATION.cff`. The formalization was produced with
[Aristotle](https://aristotle.harmonic.fun) (Harmonic).

## License

CC BY 4.0 — see `LICENSE`.
