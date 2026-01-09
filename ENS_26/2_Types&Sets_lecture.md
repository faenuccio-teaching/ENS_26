# More on Types

So far, we've seen how to *work* with types, and we want to give a somewhat more robust account of their theory.


## The hierarchy
We've seen that propositions are all types of a certain kind `Prop`; and that `ℕ` or `ℝ` are types of a different kind (both have more than one term!), called `Type`.

There is actually a whole hierarchy of types

    Prop : Type 0 : Type 1 : ... Type n : ...

So, `Prop` is a *term* of the *type* `Type 0`, itself a *term* of the type `Type 1`, etc.

Lean shortens `Type 0` to `Type`, omitting the index. It is where most known mathematical objects (like `ℕ`, `ℤ`, `ℂ`, etc) live: these algebraic objects are terms of the type `Type` ( `= Type 0`).

`⌘`

## Constructing new types
+++ Function types
Given two types `X` and `Y`, it exists the type `X → Y`. Its term can be interpreted as functions from `X` to `Y`, and are written
```
λ (x : X) ↦ (f x) : Y
```
or
```
fun (x : X) ↦ f x : Y
```
+++

+++ Π-types and Σ-types


What is the type of
```
fun (α : Type) ↦ (fun x : α ↦ x)
```
namely the assignment sending a type to its identity function?

The "problem" is that for every element in the domain, the image lies in a different place: there is no "codomain".

It belongs to the Π-type (called pi-type, or forall-type)
```
Π (α : Type), α → α
∀ (α : Type), α → α
(α : Type) → (α → α)
```

More generally, given a type `A` and an "indexing family" `I : A → Type`, a term in
```
Π (a : A), I a
∀ (a : A), I a
(a : A) → I a
```
is the type whose terms are collections `(a, xₐ)` where `xₐ : I a`. These are written `λ a : A ↦ xₐ`, or `fun a : A ↦ xₐ`.

* If you've got a geometric intuition, this looks very much like a fibration, where `A` is the base and `I a` is the fiber above `a : A`.

* As the `λ` or `fun` notation suggest, `X → Y` is a special case of a Π-type, where `I : X → Type` is the constant function `fun x ↦ I x = Y`.

Similarly, terms of the Σ-type
```
Σ (a : A), I a
(a : A) × I a
```
are pairs `⟨a, xₐ⟩` where `xₐ : I a`.

* These constructions of types that depend on terms gives the name "dependent type theory" (or "dependent λ-calculus) to the underlying theory.

+++

+++ ∀ and ∃
Consider the statement
> For every `n : ℕ` there exists a prime `p` such that `n < p`.

Or
```math
∀\; n ∈ ℕ, ∃\; p \text{prime such that } n < p
```
It is a Π-type, with `I : ℕ → Prop` being `I := fun n ↦ ∃ p prime, n < p`.

Euclid's proof is a *term* of the above type.

* You can the *prove* a ∀ `intro`ducing a variable (thought of as a "generic element", do `intro x` to call this element `x`), and by proving `P x`.
* If you have `H : ∀ x : α, P x` and also a term `y : α`, you can specialise `H` to `y`:

        specialize H y (:= P y)

* If the goal is `⊢ P y`, you might simply want to do `exact H y`, remembering that implications, `∀` and functions are all the same thing.

Similarly, consider the statement
> There exists `n : ℕ` such that `n ^ 2 + 37 * n < e ^ n`.

Or
```math
∃\; n ∈ ℕ, n^2+37 · n < 2 ^ n.
```
**qui ven sera**

`∃` is a Σ-type: consider

Once more,
* To prove `∃ x, P x`, you first produce `x`, and then prove it satisfies `P x`: once you have constructed `x`, do `use x` to have Lean ask you for `⊢ P x`.
* If you have `H : ∃ x, P x`, do `obtain ⟨x, hx⟩ := H` to obtain the term `x` together with a proof that `P x`.

`⌘`
+++

+++ `¬` and Proofs by contradiction
* The *definition* of `¬ P` is

    P → `False`

* The `exfalso` tactic changes *any* goal to proving `False` (useful if you have an assumption ` ... → False`).

* Proofs by contradiction, introduced using the `by_contra` tactic, require you to prove `False` assuming `not (the goal)`: if your goal is `⊢ p`, typing `by_contra h` creates

    | h : ¬ P
      ⊢ False

* The difference between `exfalso` and `by_contra` is that the first does not introduce anything, and forgets the actual goal; the second negates the goal and asks for `False`.
+++

`⌘`

## Inductive Types

BLABLABLA (constructors, Rob's yoga of "everything and nothing more", induction, ... ?).

Having this theoretical framework at our disposal, we can revisit some of the previous constructions **don't list them here, just in the code, at least for the first four**

* `False` is defined as...
* `True` is defined as...
* `Bool` is defined as...
* `ℕ` is defined as ...
* `∧` is a term of `Prop → Prop → Prop` whose constructors are.../that is defined as...
* `↔ : Prop → Prop → Prop` represents *equivalences* and is defined as.../its constructors are...

    An equivalence can be either *proved* or *used*.

    * A goal `⊢ P ↔ Q` can broken into the goals `⊢ P → Q` and `⊢ Q → P` using `constructor`.
    * The projections `(P ↔ Q).1` (or `(P ↔ Q).mp`) and `(P ↔ Q).2` (or `(P ↔ Q).mpr`) are the implications `P → Q` and `Q → P`, respectively.

`⌘`

+++ Structures
Among inductive types (*i. e.* all types...), some are remarkably useful for formalising mathematical objects: *structures*. Typically, they are used to *bundle* objects and properties together.

As an example, let's see what a Monoid is:
```
structure (α : Type*) Monoid where
...
...
```

> **Definition**
>> A structure is an inductive type with a unique constructor.

+++

# Sets

## Introduction
Sets are **primitive** objects when doing classical, pen-and-paper mathematics:
* no *definition*;
* only *rules* about how these objects work (unions, intersections, etc.).

That's all you need: do you ever look at $f\colon S \to T$ as $f\subseteq S\times T$?

Objects normally represented by a set are formalised in Lean as *types* with some extra-structure.

So, for Lean, sets are **no longer primitive objects**; yet
* sometimes we still want to speak about *sets* as collections of elements
* we want then to play the usual games.


## Definitions

+++ Every set lives in a **given** type, it is a set of elements (*terms*) in it:

    variable (α : Type) (S : Set α)

expresses that `α` is a type and `S` is a set of elements/terms of the type `α`. On the other hand,
```lean
variable (S : Set)
```
does not mean "let `S` be a set": it means nothing and it is an error.

`⌘`
+++

+++ A set coincides with the test-function defining it.

 Given a type `α`, a set `S` (of elements/terms of `α`) is a *function*
```lean
S : α → Prop
```
so `(Set α) = (α → Prop)`.

* This function is the "characteristic function" of the set `S`;
* the `a ∈ S` symbol means that the value of `S` is `True` when evaluated  at the element `a`;
* So, the positive integers are a *function*!

    `⌘`

Yet, given a function `P : α → Prop` we prefer to write `setOf P : Set α` to denote the set, rather then `P : Set α`, to avoid _abusing definitional equality_.

### Some examples:
1. How to prove that something belongs to a set?
1. Positive naturals;
1. Even numbers;
1. An abstract set of `α` given by some `P`.

`⌘`
+++

+++ Sub(sub-sub-sub)sets are not treated as sets-inside-sets.

Given a (old-style) set $S$, what is a subset $T$ of $S$? At least two answers:
1. Another set such that $x\in T\Rightarrow x \in S$.
1. A collection of elements of $S$.

Now,
1. stresses that $T$ is a honest set satisfying some property;
1. stresses that it is a set whose elements "come from" $S$.

We take the **first approach**: being a subset is *an implication*
```lean
    def (T ⊆ S : Prop) := ∀ a, a ∈ T → a ∈ S
```

One can also _upgrade_ sets to types: `T : Set S` for `S : Set α` means `T : Set ↑S = Set (S : Type*)`.

### Some examples:
1. Double inclusions;
1. Subsets as sets;
1. This upgrade (_coercion_) from `Set α` to `Type*`.

`⌘`
+++

## Operations on Sets
+++ **Intersection**
Given sets `S T : Set α`  have the
```lean
def (S ∩ T : Set α) := fun a ↦ a ∈ S ∧ a ∈ T
```
* Often need **extensionality**: equality of sets can be tested on elements;
* related to _functional extensionality_ : two functions are equal if and only they have if they take the same values on same arguments;
* not strange: sets *are* functions.

`⌘`

+++

+++ **Union**
Given sets `S T : Set α` we have the
```lean
def (S ∪ T : Set α) := fun a ↦ a ∈ S ∨ a ∈ T
```

And if `S : Set α` but `T : Set β`? **ERROR!**

`⌘`
+++

+++ **Universal set & Empty set**
* The first (containing all terms of `α`) is the constant function `True : Prop`
```lean
def (univ : Set α) := fun a ↦ True
```
* The second is the constant function `False : Prop`
```lean
def (∅ : Set α) := fun a ↦ False
```
**Bonus**: There are infinitely many empty sets!

+++



+++ **Complement and Difference**
* The complement is defined by the negation of the defining property, denoted `Sᶜ`.
```lean
Sᶜ = {a : α | ¬a ∈ S}
```
The superscript `ᶜ` can be typed as `\^c`.

* The difference `S \ T : Set α`, corresponds to the property
```lean
def (S \ T : Set α) = fun a ↦ a ∈ S ∧ a ∉ T
```

`⌘`
+++

+++ **Indexed Intersections & Indexed Unions**
* Can allow for fancier indexing sets (that will actually be *types*, *ça va sans dire*): given an index type `I` and a collection `A : I → Set α`, the union `(⋃ i, A i) : Set α` consists of the union of all the sets `A i` for `i : I`.
* Similarly, `(⋂ i, A i) : Set α` is the intersection of all the sets `A i` for `i : I`.
* These symbols can be typed as `\U = ⋃` and `\I = ⋂`.

`⌘`
+++
