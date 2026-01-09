
### Constructing types
+++ Function types
blaa
+++

+++ Σ-types and Π-types (dependent!)
blabla
+++

+++ ∀ and ∃
* `∀` is a `Π`-type **GIVE THE TRUE DEF**

* You can the prove it by `intro`ducing a variable (thought of as a "generic element", do `intro x` to call this element `x`), and by proving `P x`.
* If you have `H : ∀ x : α, P x` and also a term `y : α`, you can specialise `H` to `y`:

        specialize H y (:= P y)

If the goal is `⊢ P y`, you might simply want to do `exact H y`, remembering that implications, `∀` and functions are all the same thing.

* `∃` is a Σ-type **GIVE THE TRUE DEF**

Once more,
* To prove `∃ x, P x`, you first produce `x`, and then prove it satisfies `P x`: once you have constructed `x`, do `use x` to have Lean ask you for `⊢ P x`.
* If you have `H : ∃ x, P x`, do `obtain ⟨x, hx⟩ := H` to obtain the term `x` together with a proof that `P x`.

`⌘`
+++

+++ The hierarchy
There is actually a whole hierarchy of types

    Prop : Type 0 : Type 1 : ... Type n : ...

So, `Prop` is a *term* of the *type* `Type 0`, itself a *term* of the type `Type 1`, etc.

Lean shortens `Type 0` to `Type`, omitting the index. It is where most known mathematical objects (like `ℕ`, `ℤ`, `ℂ`, etc) live: they are terms of this type.

`⌘`

+++



* The `exfalso` tactic changes *any* goal to proving `False` (useful if you have an assumption ` ... → False`).

* The *definition* of `¬ P` is

    P → False

and proofs by contradiction, introduced using the `by_contra` tactic, require you to prove `False` assuming `not (the goal)`: if your goal is `⊢ p`, typing `by_contra h` creates

    | h : ¬ P
      ⊢ False

* The difference between `exfalso` and `by_contra` is that the first does not introduce anything, and forgets the actual goal; the second negates the goal and asks for `False`.

`⌘`



+++ Equivalences
As above, an equivalence can be either *proved* or *used*.

* A goal `⊢ P ↔ Q` can broken into the goals `⊢ P → Q` and `⊢ Q → P` using `constructor`.
* The projections `(P ↔ Q).1` (or `(P ↔ Q).mp`) and `(P ↔ Q).2` (or `(P ↔ Q).mpr`) are the implications `P → Q` and `Q → P`, respectively.

`⌘`
+++

## Quantifiers
Again, the two quantifiers `∀ ... ` and `∃ ...` can either occur in assumptions or in goals.

+++ `∀`
* Internally, the `∀` construction is a generalization of an implication.

* You can the prove it by `intro`ducing a variable (thought of as a "generic element", do `intro x` to call this element `x`), and by proving `P x`.
* If you have `H : ∀ x : α, P x` and also a term `y : α`, you can specialise `H` to `y`:

        specialize H y (:= P y)

If the goal is `⊢ P y`, you might simply want to do `exact H y`, remembering that implications, `∀` and functions are all the same thing.
+++

+++ `∃`
Once more,
* To prove `∃ x, P x`, you first produce `x`, and then prove it satisfies `P x`: once you have constructed `x`, do `use x` to have Lean ask you for `⊢ P x`.
* If you have `H : ∃ x, P x`, do `obtain ⟨x, hx⟩ := H` to obtain the term `x` together with a proof that `P x`.

`⌘`
+++
