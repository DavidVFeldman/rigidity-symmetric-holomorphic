# Work order: rigidity glue declarations (Theorem 3.7 and Corollary 3.10(ii))

## Context

Fresh session. All state is in the accompanying tarball; the tarball is ground
truth. The project builds a single target, `RequestProject/Main.lean`, which is
currently sorry-free and axiom-clean (`propext`, `Classical.choice`,
`Quot.sound` only). Do not modify any existing declaration.

The paper of record is `rigidity_paper_v2.tex`. Its Theorem 3.7
(`thm:rigidity`) and Corollary 3.10(ii) (`cor:nosection`) rest on the already
proved `rigidity_along_c00` and `nosection_scalar` plus two pieces of
elementary glue not yet packaged as declarations: the finite induction along a
`c₀₀`-chain, and the Hahn–Banach point-separation step. This work order adds
four declarations closing those gaps, so that every formally stated result in
v2 has a literal end-to-end Lean counterpart.

## Task

Append the following block to `RequestProject/Main.lean` (inside `namespace
Rigidity`, immediately after `nosection_scalar`), mirror it into `Main.lean` as
usual, and verify the whole file.

```lean
/-! ### Global rigidity along `c₀₀`-chains (Theorem 3.7) and the
vector-valued corollary (Corollary 3.10) -/

/-- **`c₀₀`-chain-connectedness (Definition 2.1, third clause).** Any two
points of `X` are joined by a finite chain `z 0, …, z m` in which each
increment is finitely supported (witnessed by `d ℓ`) and each segment
`z ℓ + t • d ℓ`, `t ∈ [0,1]`, lies in `X`. -/
def C00ChainConnected (X : Set CSeq) : Prop :=
  ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ X → ∃ (m : ℕ) (z : ℕ → CSeq) (d : ℕ → C00),
    z 0 = x ∧ z m = y ∧
    ∀ ℓ < m, z (ℓ + 1) = z ℓ + ((d ℓ : CSeq)) ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        (z ℓ + (((t : ℂ) • d ℓ : C00) : CSeq)) ∈ X

/-- **Theorem 3.7 (Rigidity on null-sequence domains), minimal form.** If the
differential vanishes on `c₀₀` at every point of a `c₀₀`-chain-connected `X`,
then `f` takes the same value at any two points of `X`. This is
`rigidity_along_c00` chained along the finite `c₀₀`-chain of
Definition 2.1; the paper's remaining hypotheses (permutation invariance,
local box-openness, containment in a `c₀`-coset) serve only to make the
vanishing hypothesis available and are not needed for the chaining. -/
theorem rigidity_theorem {f : CSeq → ℂ} {X : Set CSeq}
    (hf : AdmissiblyHolomorphic f X)
    (hvan : ∀ x ∈ X, ∀ h : C00, hf.D x h = 0)
    (hconn : C00ChainConnected X) :
    ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ X → f x = f y := by
  intro x hx y hy
  obtain ⟨m, z, d, hz0, hzm, hstep⟩ := hconn hx hy
  have key : ∀ ℓ, ℓ ≤ m → f (z ℓ) = f (z 0) := by
    intro ℓ hℓ
    induction ℓ with
    | zero => rfl
    | succ n ih =>
      have hn : n < m := Nat.lt_of_succ_le hℓ
      obtain ⟨hrec, hseg⟩ := hstep n hn
      have hvan' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          hf.D (z n + (((t : ℂ) • d n : C00) : CSeq)) (d n) = 0 :=
        fun t ht => hvan _ (hseg t ht) (d n)
      calc f (z (n + 1)) = f (z n + ((d n : CSeq))) := by rw [hrec]
      _ = f (z n) := rigidity_along_c00 hf (d n) hseg hvan'
      _ = f (z 0) := ih (Nat.le_of_lt hn)
  rw [← hz0, ← hzm]
  exact key m le_rfl

/-- **Theorem 3.7, paper-faithful statement.** Restatement of
`rigidity_theorem` carrying the full hypothesis list of the paper's
Theorem 3.7 (the extra hypotheses are mathematically inert here; see the
docstring of `rigidity_theorem`). -/
theorem rigidity_theorem_paper {f : CSeq → ℂ} {X : Set CSeq}
    (_hne : X.Nonempty) (_hperm : PermInvariantSet X) (_hbox : LocallyBoxOpen X)
    (_hsymm : PermInvariantFun f X)
    (hf : AdmissiblyHolomorphic f X)
    (hvan : ∀ x ∈ X, ∀ h : C00, hf.D x h = 0)
    (hconn : C00ChainConnected X) :
    ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ X → f x = f y :=
  rigidity_theorem hf hvan hconn

/-- **Corollary 3.10(ii).** If every scalarization `lam ∘ Sig` is admissibly
holomorphic with vanishing differential on a `c₀₀`-chain-connected `X`, then
`Sig` is constant on `X`. Part (i) is `nosection_scalar` applied through
`rigidity_theorem`; part (ii) follows because the continuous dual of a normed
space separates points (Hahn–Banach). -/
theorem nosection {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {X : Set CSeq} (Sig : CSeq → Y)
    (hf : ∀ lam : Y →L[ℂ] ℂ, AdmissiblyHolomorphic (fun x => lam (Sig x)) X)
    (hvan : ∀ lam : Y →L[ℂ] ℂ, ∀ x ∈ X, ∀ h : C00, (hf lam).D x h = 0)
    (hconn : C00ChainConnected X) :
    ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ X → Sig x = Sig y := by
  intro x hx y hy
  rw [NormedSpace.eq_iff_forall_dual_eq ℂ]
  intro lam
  exact rigidity_theorem (hf lam) (hvan lam) hconn hx hy
```

## Constraints

1. The four statements above (the `def` and the three theorem signatures) are
   frozen. Do not weaken, strengthen, or restate them. If a statement cannot
   be proved as given, report the failure and stop; do not repair the
   statement.
2. Proof bodies may be adjusted only to accommodate identifier drift against
   the pinned Mathlib (e.g., if `NormedSpace.eq_iff_forall_dual_eq` lives
   under a different name or requires `NormedSpace.Dual ℂ Y` in place of
   `Y →L[ℂ] ℂ` at the rewrite site, adapt the invocation). Any change beyond
   that is a report, not a repair.
3. Do not touch any existing declaration, `ARISTOTLE_SUMMARY.md`, or the tex
   files. Update the correspondence table in the file header of
   `RequestProject/Main.lean` with four new rows (v2 numbering: Thm 3.7,
   Cor 3.10(ii), plus the definition row for Def 2.1's chain clause).

## Closure criteria

Closure means all of the following, evidenced in the run output:

- `lake build` completes with no errors and no `sorry` anywhere in the file;
- `#print axioms` for each of `C00ChainConnected`-consuming theorems
  (`rigidity_theorem`, `rigidity_theorem_paper`, `nosection`) shows only
  `propext`, `Classical.choice`, `Quot.sound`;
- the previously proved declarations (`rigidity_along_c00`,
  `nosection_scalar`, `tail_vanish`, `diff_vanishes_at_constant`,
  `connected_literal_statement_false`) still elaborate and remain axiom-clean.

Deliver the updated project as a tarball. Report anything that fails as
stated rather than repairing it.
