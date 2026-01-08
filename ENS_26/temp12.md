



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
