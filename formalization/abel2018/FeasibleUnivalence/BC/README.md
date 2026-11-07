# Bellantoni–Cook Safe Recursion & `FP` Equivalence (`FeasibleUnivalence.BC`)

This directory contains a self-contained, axiom-clean Lean 4 formalization (zero external dependencies, no Mathlib, no `Classical.choice`) of Bellantoni and Cook's function algebra $B$ of **safe recursion on notation** and a complete bidirectional proof that the unary functions definable in $B$ coincide with the complexity class $\mathsf{FP}$ of polynomial-time computable word functions on deterministic multi-tape Turing machines:

$$\forall f : \mathrm{Word} \to \mathrm{Word},\quad \bigl(\exists\,\mathrm{prog} : \mathrm{BC.Fn}\;1\;0,\;\forall x,\;\mathrm{prog.eval}\;[x]\;[] = f(x)\bigr) \;\Longleftrightarrow\; \mathrm{BC.FP}\;f.$$

## References

1. **Stephen Bellantoni and Stephen Cook**, *"A new recursion-theoretic characterization of the polytime functions"*, Computational Complexity **2** (1992), 97–110.
2. **Sylvain Heraud and David Nowak**, *"A formalization of polytime functions"*, Interactive Theorem Proving (ITP 2011), LNCS 6898, Springer, 2011, 139–154.

---

## Module Overview

| File | Lines | Contents |
| :--- | ---: | :--- |
| [`Poly.lean`](./Poly.lean) | 90 | Univariate polynomials (`Poly`) over $\mathbb{N}$ with non-negative coefficients, evaluation, monotonicity (`eval_mono`), composition (`comp`), and finite sums (`sumFin`). |
| [`Syntax.lean`](./Syntax.lean) | 364 | Binary words (`Word := List Bool`), Bellantoni–Cook syntax `Fn n m` indexed by normal arity $n$ and safe arity $m$, denotational semantics `Fn.eval`, and the syntactic polynomial max-output-length bound `Fn.eval_length_le_sizePoly` (Bellantoni–Cook Lemma 2.1). |
| [`StackProg.lean`](./StackProg.lean) | 69 | Imperative multi-stack programs (`Stmt`) operating on binary-word stacks (`Stacks := Nat → Word`) with big-step cost relation `Exec : Stmt → Stacks → Nat → Stacks → Prop`. |
| [`TM.lean`](./TM.lean) | 155 | Standard deterministic $k$-tape Turing machines (`TM`), configurations (`Cfg`), single-step transition (`TM.step`), bounded-step execution (`TM.HaltsWithin`), and the machine-based definition of `FP`. |
| [`CompileStmt.lean`](./CompileStmt.lean) | 633 | Verified compiler from `StackProg.Stmt` to `TM` (`stmtToTM`), mapping each stack register to a dedicated Turing tape with the tape head invariant at the top of the stack, proving step-bound preservation (`stmtToTM_haltsWithin`). |
| [`Soundness.lean`](./Soundness.lean) | 1608 | Compiler from `BC.Fn n m` to `StackProg.Stmt` (`compileBC`), syntactic running-time polynomial `Fn.timePoly`, joint correctness and polynomial step-bound theorem `exec_compileBC`, and **Soundness** (`bc_soundness : ∀ f, BCDefinable f → FP f`). |
| [`Completeness.lean`](./Completeness.lean) | 1523 | Encoding of $k$-tape Turing machine configurations as fixed-width block tables in `BC.Fn`, single-step transition via safe recursion on notation (`stepCfgBC`), $T$-step iteration (`runCfgBC`), output extraction (`outputCfgBC`), **Completeness** (`bc_completeness : ∀ f, FP f → BCDefinable f`), and the **Headline Equivalence** (`defFun_eq_FP`). |

---

## Headline Theorems

### 1. Syntactic Polynomial Length Bound ([`Syntax.lean`](./Syntax.lean))

Every `f : Fn n m` has a syntactically synthesized polynomial `f.sizePoly : Poly` (constructed by structural recursion on `f`, never by running `f`) such that for all normal inputs `xs` with `∀ x ∈ xs, x.length ≤ N` and safe inputs `ys`:

```lean
theorem Fn.eval_length_le_sizePoly {n m : Nat} (f : Fn n m) (xs ys : List Word)
    {N : Nat} (hxs : ∀ x ∈ xs, x.length ≤ N) :
    (f.eval xs ys).length ≤ f.sizePoly.eval N + maxLen ys
```

In particular, for normal-only functions (`m = 0`), $|f(\vec{x}; [])| \le q_f(|\vec{x}|)$ (`Fn.eval_normal_length_le`), and for unary functions `f : Fn 1 0`, $|f([x]; [])| \le p_f(|x|)$ (`Fn.eval_one_length_le`).

### 2. Polynomial-Time Soundness ([`Soundness.lean`](./Soundness.lean))

Every `f : Fn 1 0` is compiled to a deterministic multi-tape Turing machine `topCompileBC f : TM` and a syntactically synthesized polynomial `topTimePoly f : Poly` such that `(topCompileBC f).HaltsWithin x ((topTimePoly f).eval x.length) (f.eval [x] [])`:

```lean
theorem bc_soundness (f : Word → Word) (h : BCDefinable f) : FP f
```

### 3. Polynomial-Time Completeness & Equivalence ([`Completeness.lean`](./Completeness.lean))

Every function `f : Word → Word` computable within `p(|x|)` steps on a deterministic $k$-tape Turing machine `M : TM` is computed by the closed Bellantoni–Cook program `simTM M p : Fn 1 0`:

```lean
theorem bc_completeness (f : Word → Word) (h : FP f) : BCDefinable f

theorem defFun_eq_FP (f : Word → Word) :
    (∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f
```

---

## Comparison with Heraud & Nowak (ITP 2011)

Heraud and Nowak (*"A formalization of polytime functions"*, ITP 2011) formalized Bellantoni and Cook's characterization of $\mathsf{FP}$ in Coq. Our Lean 4 development shares the high-level two-stage structure of Bellantoni & Cook (1992) and Heraud & Nowak (2011), with several key architectural choices tailored to a dependency-free, constructive Lean 4 kernel:

1. **Intrinsic Normal/Safe Arities (`Fn n m`)**:
   - Like Heraud & Nowak, we index the syntax `Fn n m` directly by the number of normal arguments `n : Nat` and safe arguments `m : Nat`.
   - Safe composition `Fn.comp (h : Fn n' m') (gs : Fin n' → Fn n 0) (hs : Fin m' → Fn n m) : Fn n m` enforces at the type level that normal arguments of `h` receive only expressions `gs i : Fn n 0` that cannot read the outer safe variables, whereas safe arguments of `h` may read both normal and safe variables (`hs j : Fn n m`).
   - Safe recursion on notation `Fn.srec (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1)) : Fn (n + 1) m` places the recursion parameter at normal index `0` and passes the recursive accumulator at safe index `0`.

2. **Machine Model (`StackProg` + `TM`)**:
   - Heraud & Nowak use a multi-stack machine (where each stack holds binary words and supports top-of-stack push/pop/case-split) directly as their machine model defining $\mathsf{FP}$.
   - In our formalization, we factor the soundness proof through *both* models:
     1. [`Soundness.lean`](./Soundness.lean) compiles `BC.Fn n m` to an imperative multi-stack program `StackProg.Stmt` (`compileBC`), using a flat register allocation convention where each recursive call level uses a disjoint register frame `[base .. base + n + m + 1)`.
     2. [`CompileStmt.lean`](./CompileStmt.lean) then compiles `StackProg.Stmt` down to a standard deterministic multi-tape Turing machine `TM` (`stmtToTM`) over a ternary tape alphabet $\{blank, 0, 1\}$, maintaining the invariant that each tape head sits on the top bit of its stack (with reversed stack contents to the left and blanks to the right). Every stack instruction translates to 1 or 2 Turing machine transitions, giving a direct machine-level `TM.HaltsWithin` witness.

3. **Completeness via Sliding-Window Block Tables ([`Completeness.lean`](./Completeness.lean))**:
   - To simulate a $k$-tape Turing machine `M` for $T = p(|x|)$ steps in `BC.Fn 1 0`, we observe that the left and right half-tapes of `M.init x` have length at most $|x|$ and grow by at most 1 cell per step, so all active cells remain strictly within horizon $N = |x| + p(|x|) + 1$.
   - We encode a configuration `c : Cfg M.k M.Q M.G` up to horizon $N$ as a single safe word `encCfg M N c` consisting of $N$ fixed-width blocks of width $D = \mathrm{blockWidth}\;M = Q + k + 2kG$ bits:
     - Block $0$ stores the binary-encoded machine state `c.state`, the head symbols `(c.tapes i).head`, and position-$0$ cells of the left and right half-tapes.
     - Block $j$ ($0 < j < N$) stores the $j$-th cell of the left and right half-tapes of each of the $k$ tapes (`(c.tapes i).left[j - 1]` and `(c.tapes i).right[j - 1]`).
   - Because each Turing step shifts `(c.tapes i).left` and `(c.tapes i).right` by at most $\pm 1$ position, the new block $j$ at step $t + 1$ is a finite boolean function of **block $0$** (the machine state and head symbols) together with the **3-block sliding window** $(\text{block}_{j-1}, \text{block}_j, \text{block}_{j+1})$ at step $t$.
   - Using `branchPrefix` (which inspects a constant number $B$ of leading bits of a safe word via nested safe conditionals `.cond` and `.pred` without any normal clock), `stepBlockBC` decodes block $0$ and the $3D$-bit sliding window, evaluates the finite transition table of `M` in Lean, and outputs the updated $D$-bit block as a constant-depth sequence of safe successors on `constZero`.
   - One full Turing transition `stepCfgBC M : Fn 1 1` is then a single safe recursion on the spatial clock $W$ (`|W| = N`) followed by block-table reversal `revBlocks D`, and $T$ transitions `runCfgBC M : Fn 2 1` are a second safe recursion on the time clock $T$ (`|T| = p(|x|)`).

4. **Constructive Kernel Verification**:
   - The entire `FeasibleUnivalence.BC` library is constructive: `AxiomAudit.lean` verifies that all declarations depend only on `[propext, Quot.sound]` (no `Classical.choice`, no `sorry`, and no custom axioms).
