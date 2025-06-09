# Some things to know
- `;` is used to conjoin lines, `<;>` is used to perform repeat applications.

## The full meaning of `->`
In this document, I sometimes describe expressions of the form `A -> B`. This can represent an implication or a forall. Also, negation `¬A` is represented as `A -> False`.

## Questions
- When can I use `at h`?
- What is the difference between `↦`, `→`, `=>`, and all the other connectors?
- Is there a key I can press to convert the current phrase into the symbol? Like `\and` -> `∧`
- Is there a way to condense things onto a single line without `;`?
- How does `convert` work? (I know they explained it but it's just a bit shaky right now.) And wth is `using 1` at the end of `convert`?

## Wishes
- I wish there was a way to autocomplete the structure of a proof with `sorry`s

# All the lean tactics

## `rfl`
`rfl` my beloved. I forgor exactly what `rfl` does though.

## `assumption`
`assumption` will find an existing term (like a hypothesis) you already have and will solve the goal using it. If no such term exists, the tactic will fail.

## `constructor`
At least in the case of `∧`, `constructor` will split the goal `A ∧ B` into two goals, `A` and `B`.

## `rcases`
Kinda the opposite of `constructor`. For example, given a term `A ∧ B`, it will break it down into two terms `A` and `B`. Use like `rcases h with ⟨h₀, h₁⟩`.

## `apply`
This will take a term of the form `A1 -> ... -> An -> B` and will solve a goal that matches `B`, replacing it with the goals `A1` through `An`. Sometimes `B` depends on some variables in `A1` through `An`, which may require some manual adjustment to get Lean to understand what you want. (I wish there was a more ergonomic way to do this in general.)

This tactic may be slightly more powerful than described, but the same spirit of the tactic applies.

## `intro`
If you have a goal of the form `A -> B`, you can write `intro A` to bring `A` into the context and change the goal to just `B`.

## `rintro`
A more powerful form of `intro` that can also destruct constructors like `rcases`.

## `rw`
Syntax is `rw [f]` or `rw [f1 f2 f3]` or `rw [f1 f2 f3] at h`. Given a term of the form `f := x = y`, `rw [f]` will replace all instances of `x` with `y` in the goal (or term `h` if using `at h`). Sometimes `f` is parameterized, in which case `rw` will just set the parameterization based on the first instance it can find, and then make as many rewrites using that parameterization as possible.

### `nth_rw`
This is a special version of `rw`, called using `nth_rw n [f]`, that will only perform a rewrite on the `n`th matching instance.

## `simp`
According to the documentation, `simp` simplifies the main goal target using lemmas tagged with the attribute

You can use `at h` to simplify within a hypothesis.

## `exact`
`exact`ly what you think it does
can function like return.

## `contrapose`
Use `contrapose! ¬A` to swap the term `¬A` and goal `¬B` with the term `B` and the goal `A`. This causes the term `¬A` to be removed from the context.

## `ext`
Takes a goal of the form `fun x => f x = fun x => g x`, intros `x`, and replaces the goal with `f x = g x`. Works with multiple arguments as well.

## `congr`
Given goal `f x = f y`, replaces the goal with `x = y`.

## `convert`
`convert` is kind of magic. It seems like it let's you assume that you've proved certain relations, finishes the proof using everything you've supplied, and then politely returns the relations it inferred it needed.
