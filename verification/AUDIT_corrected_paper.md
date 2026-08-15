# Consistency check: `rigidity_paper_corrected.tex` vs. the Lean (`RequestProject/Main.lean`)

You asked me to check that the latest draft (`rigidity_paper_corrected.tex`,
matching `rigidity_paper_corrected.pdf`) says only what the Lean actually
confirms — i.e. that the revision did not misread my earlier corrections.

**Verdict.** Most of the paper is faithfully backed by the Lean, which rebuilds
cleanly and is `sorry`-free and axiom-clean (only `propext`, `Classical.choice`,
`Quot.sound`). **But the revision has re-introduced, in a strengthened form, the
one step that the Lean audit flagged as unsupported** — the passage from the
analytic core to an *unconditional* conclusion on eventually-constant domains.
Concretely, the second (“In particular … the conclusion holds outright: $f$ is
constant”) paragraph of Theorem 3.7 (`thm:rigidity`) and its footnote, together
with the corresponding unconditional phrasing in the abstract and the
“main result, informally” subsection, assert more than the Lean proves, and rest
on a step that is incorrect under the theorem’s stated hypotheses.

Everything else checks out. Details below.

---

## 1. What the Lean *does* confirm (faithful matches)

| Paper (corrected) | Lean declaration | Confirmed |
|---|---|---|
| Lemma 3.1, base-point identity $Df(x)[e_i]=Df(x\circ\tau_{ij})[e_j]$ | `AdmissiblyHolomorphic.diff_symm` | ✅ |
| Lemma 3.3, Cesàro/averaging vanishing | `AdmissiblyHolomorphic.cesaro_vanish` | ✅ |
| Prop. 3.4, tail vanishing: $Df(x)[e_i]=0$ for tail indices $i$ ($x_i=c$) of an eventually-constant $x$ | `tail_vanish` | ✅ |
| Cor. 3.5, vanishing at constant points: $Df(c\mathbf1)|_{\cc}=0$ | `diff_vanishes_at_constant` | ✅ |
| Prop. 3.6, segment rigidity ($Df$ vanishes along a $\cc$-segment ⇒ $f$ constant along it) | `rigidity_along_c00` | ✅ |
| Theorem 3.7, **main sentence**: *if* $Df(x)|_{\cc}=0$ at every $x\in X$, then $f$ is constant | `rigidity_along_c00` (chained) | ✅ |
| Theorem 3.7, **first “in particular”**: $Df|_{\cc}=0$ at a point with empty exceptional set | `diff_vanishes_at_constant` | ✅ |
| Cor. 3.9(i), scalar vector-valued corollary | `nosection_scalar` | ✅ |
| Example 5.1, disconnected two-coset witness (non-constant symmetric holomorphic $f$) | `literal_statement_false` | ✅ |
| Example 5.2, connected witness on $\ell^\infty$ via a finite-permutation-invariant Banach limit | `exists_finPermBanachLimit`, `connected_literal_statement_false` | ✅ |

The base-point correction (the “base point moves under permutation’’ subtlety)
and the “finitely supported segments do not connect $\ell^\infty$’’ subtlety are
both exactly as the Lean has them, and the sharpness examples confirm the
boundedness / chain-connectedness hypotheses cannot be dropped.

---

## 2. The one place the paper over-claims relative to the Lean

### 2a. Location in the paper

Theorem 3.7 (`thm:rigidity`), **second paragraph**:

> *In particular, the hypothesis $Df(x)|_{\cc}=0$ holds automatically … and — when
> $X$ consists of eventually-constant sequences — the conclusion holds outright:
> $f$ is constant.*

together with the proof paragraph beginning *“When every point of $X$ is
eventually constant, we argue that $Df(x)|_{\cc}=0$ throughout …’’* and its
footnote. The same unconditional statement is echoed in the **abstract**
(“any such function with a bounded differential is constant’’) and in the
**introduction** (“then $f$ is constant’’, before the hypotheses are qualified).

### 2b. Why the Lean does not confirm it

The Lean proves the theorem **only in its conditional form** (main sentence:
assume $Df|_{\cc}=0$ everywhere). It deliberately does **not** assert the
eventually-constant ⇒ constant conclusion, and it records a concrete obstruction
as a *proved* theorem, `permAct_swap_moves_exceptional`.

The gap is in the exceptional-coordinate reduction. To get $Df(x)[e_k]=0$ at an
**exceptional** coordinate ($x_k=a\ne c$), the paper connects $x$ to the “zeroed”
point $y=x-(x_k-c)e_k$ by the single segment $t\mapsto y+t\,(x_k-c)e_k$,
$t\in[0,1]$, and claims (parenthetically):

> *(The verification that the $e_k$-derivative vanishes along the connecting
> segment uses Proposition 3.4 at each interior point, whose exceptional set does
> not contain $k$.)*

This parenthetical is **false**. The interior points of that segment have
$k$-th coordinate $c+t(x_k-c)$, which is $\ne c$ for every $t\in(0,1)$ (because
$x_k\ne c$). So $k$ **is** in the exceptional set of every interior point, and
Proposition 3.4 (tail vanishing), which gives vanishing only in *tail*
directions, does **not** apply to $e_k$ there. Hence the segment argument needs
exactly what it is trying to prove — the reduction is circular.

Equivalently, in terms of the Lean tools: at an exceptional $k$, `diff_symm`
gives $Df(x)[e_k]=Df(x\circ\tau_{kj})[e_j]$, a derivative at the *different*
point $x\circ\tau_{kj}$, where the exceptional value has merely been *moved*
from $k$ to $j$ (so $j$ is exceptional there); it is **not** a point where $k$ is
a tail coordinate. `permAct_swap_moves_exceptional` proves precisely that
$x\circ\tau_{kj}$ and the zeroed point’s permute disagree at coordinate $j$, so
the identity at $x$ cannot be transported to $y$. And since each
eventually-constant sequence has only *finitely many* exceptional coordinates,
the averaging step `cesaro_vanish` (which needs *infinitely many* equal
coordinate derivatives at *one* base point) cannot reach them either.

### 2c. The footnote’s escape hatch also does not deliver what it claims

The footnote suggests the reader may instead take “$X$ consists of constant
sequences together with their $\cc$-perturbations’’, *“where tail vanishing
already gives $Df|_{\cc}=0$ at every point directly.’’* This is not right either:
a point $c\mathbf1+h$ with $h\in\cc$, $h\ne 0$, has exceptional coordinates
exactly $\operatorname{supp}(h)$ (finitely many but nonempty), and tail vanishing
gives $Df[e_k]=0$ only for $k\notin\operatorname{supp}(h)$. So on that domain
tail vanishing gives $Df|_{\cc}=0$ **only at the genuinely constant points**, not
at every point. This is the same obstruction again.

### 2d. The paper already contains the correct statement — in Remark 3.8

Remark 3.8 (`rem:standing`) says, correctly, that to obtain $Df|_{\cc}=0$ at
*all* points one uses **continuity of $x\mapsto Df(x)$** (“for general
Fréchet-holomorphic $f$ … by a standard limiting argument; we do not develop
this here’’). That continuity is **not** among Theorem 3.7’s hypotheses (which
assume only a *bounded* differential). So the Theorem’s “in particular’’
paragraph is internally at odds with its own Remark 3.8: it claims to reach
every point *without* continuity, via the elementary reduction — and that
reduction does not work.

---

## 3. Suggested repairs (so the writing matches the Lean)

Any one of the following makes the draft consistent with what is proved:

1. **Preferred / cleanest.** State Theorem 3.7 purely in its conditional form
   (assume $Df(x)|_{\cc}=0$ for all $x\in X$ ⇒ $f$ constant), keep the first
   “in particular’’ (empty exceptional set), and **delete** the second “in
   particular’’ paragraph, its proof paragraph, and the footnote. Move the
   honest status to Remark 3.8: the hypothesis is discharged unconditionally at
   constant points (Cor. 3.5) and along constant tails (Prop. 3.4), and in
   general requires sup-norm continuity of $x\mapsto Df(x)$ (which then gives it
   at all points). Correspondingly soften the abstract and introduction from
   “$f$ is constant’’ to the conditional/“along $\cc$-directions with vanishing
   differential’’ phrasing. This is exactly the formulation of the earlier
   `rigidity_paper_v2.tex`, which *is* faithful to the Lean.

2. **If you want the unconditional conclusion on eventually-constant domains**,
   add sup-norm continuity of $x\mapsto Df(x)$ as a hypothesis and prove the
   all-points vanishing by the limiting argument of Remark 3.8 (a tail point
   sequence approaching $x$), rather than by the exceptional-coordinate
   reduction. Then the “in particular’’ paragraph becomes correct — but note the
   *elementary* claim (bounded differential only) would still be unsupported.

Either way, the exceptional-coordinate reduction paragraph/footnote should be
removed or replaced: as written it asserts a false intermediate step
(interior points of the connecting segment are not tail points for $e_k$).

---

## 4. Build status

`RequestProject/Main.lean` compiles against Mathlib with only cosmetic
“unused simp argument’’ linter warnings (pre-existing, inside earlier
machine-generated proofs). All theorems named above are `sorry`-free and depend
only on `propext`, `Classical.choice`, `Quot.sound`.
