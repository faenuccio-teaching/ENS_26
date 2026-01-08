# Introduction

For this and all other classes, excellent material can be found in
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/), by J. Avigad, L. de Moura, S. Kong, S. Ullrich
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), by J. Avigad and P. Massot

Let's see an example before moving on

`⌘`

## Tactics

`Lean` relies on the *Curry–Howard isomorphisms*, or as the
  > Propositions-as-Types and Proofs as-Terms Correspondence

(more on this next time).
+++In a nutshell
Each statement (or proposition) `P` is seen as a one-slot drawer: it either contains *one* gadget (a/the proof of `P`, or nothing. In the first case `P` is true, in the second is "false" (or unproven, or unprovable...).
+++
To prove a proposition `P : Prop` boils down to producing a/the term `hp : p`.

This is typically done by
1. Finding somewhere a *true* proposition `Q` and a term `hq : Q`;
1. Producing a function `f : P → Q` ("an implication").
1. Defining `hp := f hq`.

This is often painful: to simplify our life, or to build more convoluted implications, we use *tactics*.

+++ `intro`, `exact`, `apply` and `rfl`
* Given an implication `p → q`, the tactic `intro hp` introduces a term `hp : p`.

* On the other hand, given a term `hq : q` and a goal `⊢ q`, the tactic `exact hq` closes the goal, instructing Lean to use `hq` as the sought-for term in `q`.
* `apply` is the crucial swiss-knife for *backwards reasoning*: in a situation like

    | hpq : p → q
      ⊢ q

the tactic `apply hpq` changes the goal to `⊢ p`: it tells Lean that, granted `hpq` it suffices to construct a term in `p` to deduce a term in `q`.


* If your goal is `a = a`, the tactic `rfl` closes it.

`⌘`
+++

+++ `rw`
This tactic takes an assumption `h : a = b` and replaces all occurrences of `a` in the goal to `b`. Its variant

    rw [h] at h1

replaces all occurrences of `a` in `h1` with `b`.

* Unfortunately, `rw` is not symmetric: if you want to change `b` to `a` use `rw [← h]` (type `←` using `\l`): **beware the square brackets!**

`⌘`
+++


+++ Conjunction ( "And", `∧`) and Disjunction ( "Or", `∨`)
For both logical connectors, there are two use-cases: we might want to *prove* a statement of that form, or we might want to *use* an assumption of that form.

### And
* `constructor` transforms a goal `⊢ p ∧ q` into the two goals `⊢ p` and `⊢ q`.
* `.left` and `.right` (or `.1` and `.2`) are the projections from `p ∧ q` to `p` and `q`.

### Or
* `right` and `left` transform a goal `p ∨ q` in `p` and in `q`, respectively.
* `cases p ∨ q` creates two goals: one assuming `p` and the other assuming `q`.
+++
