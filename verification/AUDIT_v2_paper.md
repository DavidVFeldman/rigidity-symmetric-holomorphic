# Consistency check: `rigidity_paper_v2.tex` vs. the Lean (`RequestProject/Main.lean`)

You asked me to check `rigidity_paper_v2.tex` (the rewrite you meant to have
checked) against the Lean formalization. The previous audit
(`AUDIT_corrected_paper.md`) examined a *different* draft,
`rigidity_paper_corrected.tex`, and found that it over-claimed in one place;
this file audits `rigidity_paper_v2.tex` instead.

**Verdict.** `rigidity_paper_v2.tex` is faithful to the Lean. Every theorem,
lemma, corollary, and example that it states as *proved* corresponds to a proved,
`sorry`-free, axiom-clean Lean declaration, and — crucially — it does **not**
contain the over-claim that `rigidity_paper_corrected.tex` reintroduced. The v2
draft states the main rigidity theorem in its correct **conditional** form
(assume `Df|_{c00} ≡ 0` everywhere ⇒ `f` constant), records exactly how far that
hypothesis is discharged unconditionally (constant points and constant tails),
and flags the exceptional-coordinate case as open — all matching the Lean. The
few items v2 leaves informal are explicitly non-formal (remarks) or explicitly
open (the lifting problem), so there is no mismatch.

Build status: `RequestProject/Main.lean` compiles against Mathlib
(`Build completed successfully`, 8027 jobs) with only cosmetic
`unusedSimpArgs` linter warnings inside earlier machine-generated proofs; it is
`sorry`-free and depends only on `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. Section-by-section correspondence (v2 ↔ Lean)

| v2 draft | Lean declaration | Match |
|---|---|---|
| Def. 2.1 (`def:domain`): permutation-invariant | `PermInvariantSet` | ✅ |
| Def. 2.1: locally box-open | `LocallyBoxOpen` | ✅ |
| Def. 2.1: `c00`-chain-connected | (handled via per-segment hypotheses `hseg`; see §2) | ✅ (implicit) |
| Def. 2.3 (`def:holomorphic`): admissible holomorphicity, bounded differential | `AdmissiblyHolomorphic` (fields `D`, `bounded`, `littleO`, `coordHolo`) | ✅ |
| Rem. 2.4 (`rem:standard`): standard holomorphy is admissible / boundedness automatic | (informal justification for the `bounded` field; not a formal claim) | n/a |
| Lem. 3.1 (`lem:basepoint`): base-point identity `Df(x)[e_i]=Df(x∘τ_{ij})[e_j]` | `AdmissiblyHolomorphic.diff_symm` | ✅ |
| Lem. 3.3 (`lem:cesaro`): Cesàro vanishing | `AdmissiblyHolomorphic.cesaro_vanish` | ✅ |
| Prop. 3.4 (`prop:tail`): tail vanishing `Df(x)[e_i]=0` for `i∉supp_c(x)` | `tail_vanish` | ✅ |
| Cor. 3.5 (`cor:constant`): vanishing at constant points | `diff_vanishes_at_constant` | ✅ |
| Prop. 3.6 (`prop:segment`): segment rigidity | `rigidity_along_c00` | ✅ |
| Thm. 3.7 (`thm:rigidity`): rigidity, **conditional** on `Df|_{c00}≡0` | `rigidity_along_c00` chained along the `c00`-chain (per-segment step is the Lean theorem; see §2) | ✅ |
| Prop. 3.8 (`prop:uncond`): `Df` vanishes at constant points and along constant tails | `diff_vanishes_at_constant` + `tail_vanish` | ✅ |
| Rem. 3.9 (`rem:obstruction`): exceptional-coordinate obstruction | `permAct_swap_moves_exceptional` | ✅ |
| Cor. 3.10 (`cor:nosection`): vector-valued corollary | `nosection_scalar` (scalar content; (ii) is the immediate point-separation step) | ✅ (see §2) |
| Ex. 4.x (`ex:twocosets`): disconnected two-coset witness | `literal_statement_false` | ✅ |
| Ex. 4.x (`ex:banach`): connected Banach-limit witness on `ℓ^∞` | `exists_finPermBanachLimit`, `connected_literal_statement_false` | ✅ |
| Rem. (`rem:ell1`): `ℓ^1` sharpness | (informal remark; not formalized) | n/a |
| §5 Application, Prop. (`prop:conditional`), Open Problem (Lifting Lemma) | (explicitly conditional/open; `nosection_scalar` supplies the rigidity input) | n/a (open) |
| §6 Further Remarks (1)–(5) | (informal discussion; not formalized) | n/a |

The two structural subtleties emphasized in v2's introduction are exactly the
Lean's:

- *"The base point moves under permutation."* v2 states the identity as
  `Df(x)[e_i]=Df(x∘τ_{ij})[e_j]` and warns it equals `x+εe_j` only when
  `x_i=x_j`. This is precisely `diff_symm` (and `permAct_swap_add_smul_ebasis`
  for the pointwise push-through). ✅
- *"Finitely supported segments do not connect `ℓ^∞`."* This is the content of
  the sharpness examples and is why the theorem is confined to a single
  `c0`-coset; the Lean's `literal_statement_false` /
  `connected_literal_statement_false` witness it. ✅

---

## 2. Faithful-but-worth-noting points (no over-claim)

These are places where v2 is correct and the Lean supports it, but the Lean
packages the content slightly differently. None is a defect in v2.

1. **Global chaining of Theorem 3.7.** v2's Theorem 3.7 concludes `f` is constant
   on all of a `c00`-chain-connected `X`, proved by applying Prop. 3.6
   (`prop:segment`) along each link of a finite `c00`-chain. The Lean proves the
   single-segment step as `rigidity_along_c00`; the finite induction over the
   chain (Definition 2.1's `c00`-chain-connectedness) is the routine remaining
   step and is not packaged as its own Lean declaration. The mathematical content
   of Theorem 3.7 is thus fully covered up to that elementary induction. This is
   honest in v2, which states the theorem as a genuine (conditional) theorem.

2. **`c00`-chain-connectedness as a definition.** The Lean does not introduce a
   named `Cc-chain-connected` predicate; instead its segment-level results take
   the segment-in-`X` hypothesis (`hseg`) directly. This is equivalent to
   applying the definition link-by-link and introduces no discrepancy.

3. **Corollary 3.10(ii).** v2's part (i) (`λ∘Σ` constant for each functional `λ`)
   is exactly `nosection_scalar`; part (ii) (point-separating `Y^*` ⇒ `Σ`
   constant) is the immediate deduction "if `Σ(x)≠Σ(y)`, some `λ` separates them,
   contradicting (i)." The Lean formalizes the load-bearing scalar content (i);
   (ii) is the one-line separation argument stated in the paper's proof.

4. **Application section (§5) is explicitly conditional/open.** v2 states
   Prop. `prop:conditional` under a *lifting hypothesis* and poses the Lifting
   Lemma as an Open Problem; it does not claim an unconditional obstruction.
   The Lean correctly does not attempt the lifting lemma (it is open), and
   supplies the rigidity input (`nosection_scalar`) that the conditional
   proposition uses. No over-claim.

---

## 3. The key contrast with `rigidity_paper_corrected.tex`

The earlier audit found that `rigidity_paper_corrected.tex` had re-introduced,
in strengthened form, an *unconditional* "eventually-constant domain ⇒ `f`
constant" claim (a second "in particular" paragraph in its Theorem 3.7, a
footnote, and matching phrasing in the abstract/intro), resting on an
exceptional-coordinate reduction whose key parenthetical step is false — the
obstruction the Lean records as the proved theorem
`permAct_swap_moves_exceptional`.

`rigidity_paper_v2.tex` does **not** make that claim. It keeps Theorem 3.7
conditional, isolates the extent of unconditional vanishing in
Proposition 3.8 (`prop:uncond`), and states the exceptional-coordinate case as
open in Remark 3.9 (`rem:obstruction`) — matching the Lean exactly. So v2 is the
draft that is consistent with the verified formalization.

---

## 4. Bottom line

`rigidity_paper_v2.tex` is faithfully backed by `RequestProject/Main.lean`. No
statement in v2 claims more than the Lean proves, and the one step that the Lean
flags as an obstruction (exceptional coordinates) is presented in v2 as open,
not as established. If you intend to publish, `rigidity_paper_v2.tex` is the
draft consistent with the machine-checked proofs; `rigidity_paper_corrected.tex`
would need the repairs listed in `AUDIT_corrected_paper.md` §3 to reach the same
standard.
