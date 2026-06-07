import Mathlib.Tactic
/-!
# Writing proof terms by hand

In these exercises, you will have some practice writing term proofs by hand for
some trivial logic.

Normally you would never write these by hand (you'd use high-level tactics!) but
the purpose of this is to become acquainted with the structure of proof terms.
-/

/-!
## Natural deduction glossary

Logical connectives and how to type them in VS Code
+----+---------+
| ∧  | \and    |
| ∨  | \or     |
| →  | \to     |
| ↔  | \iff    |
| ¬  | \not    |
| ∀  | \all    |
| ∃  | \exists |
+----+---------+
You can hover over these symbols to see how to type them. You can also use
abbrevations for these and use tab completion.
(Use `\\` if you ever need `\` itself.)

The rest of this section has all the introduction and elimination rules for
these connectives. We're using `#check` so you can hover over them to see
their types.
-/

/-!
### Conjunction
-/
-- Operator: `p ∧ q`
#check And
-- Introduction rule
#check And.intro
-- Elimination rule
#check And.elim
-- Additional elimination rules
#check And.left
#check And.right

/-!
### Disjunction
-/
-- Operator: `p ∨ q`
#check Or
-- Introduction rules
#check Or.inl
#check Or.inr
-- Elimination rule
#check Or.elim

/-!
### Implication
In the propositions-as-types setting, implication is represented using the
function type from the underlying type theory. The rules aren't represented
by constants, but rather lambda calculus rules.
-/
section
variable (p q : Prop) -- there is no `Implies`; adding propositions to the
                      -- context so we can make use of the notations
-- Operator: `p → q`
#check p → q
-- Introduction rule (`sorry` represents a proof of `q` that can use `hp`)
example : p → q :=
  fun (hp : p) => sorry
               -- ^ put your cursor here and look at the
               -- context in the "Expected type" area of the InfoView
-- Elimination rule (modus ponens)
example (hp : p) (hpq : p → q) : q :=
  hpq hp
end

/-!
### Biconditional ("iff")
The biconditional `p ↔ q` could be defined as `(p → q) ∧ (q → p)`, but it
has its own type for convenience. (It is also to help ensure that Lean's
automation never accidentally sees a biconditional as a conjunction! This is
important since `↔` is used as an equality operation for propositions.)
-/
-- Operator: `p ↔ q`
#check Iff
-- Introduction rule
#check Iff.intro
-- Elimination rule
#check Iff.elim
-- Additional elimination rules
#check Iff.mp
#check Iff.mpr
-- These names might be strange. The idea is that you can use `mp` and `mpr`
-- to apply modus ponens in a particular direction. Examples:
example (p q : Prop) (h : p ↔ q) (hp : p) : q :=
  h.mp hp   -- modus ponens of `p ↔ q` in the forward direction
            -- (hover over `mp` to see that it is `Iff.mp`)
example (p q : Prop) (h : p ↔ q) (hq : q) : p :=
  h.mpr hq  -- modus ponens of `p ↔ q` in the *r*everse direction
            -- (hover over `mpr` to see that it is `Iff.mpr`)
-- These are using "dot notation" to conveniently apply the elimination rules.
-- Generally speaking, Lean resolves dot notation by looking at the type of
-- the term that dot notation is being applied to, then looking for the name
-- of the field in that type's namespace.

/-!
### True
-/
-- Constant
#check True
-- Introduction rule
#check True.intro
-- No need for an elimination rule since `True` contains no information; we
-- can see that since the introduction rule has no parameters — parameters
-- correspond to some sort of information. Compare to `And.intro`.

/-!
### False
This proposition represents a contradiction: something that implies everything,
and which can only be proven in contradictory contexts. The theory is
*consistent* if `⊢ False` cannot be proven (i.e., from an empty context).
-/
-- Constant
#check False
-- No introduction rule since `False` must not be provable (it represents a contradiction)
-- Elimination rule (principle of explosion, "ex falso quodlibet")
#check False.elim

/-!
### Negation
The notation `¬p` is an abbreviation for `p → False`, that assuming `p`
leads to a contradiction.
-/
-- Definition (unlike `#check`, the `#print` command shows the full definition)
#print Not
-- Introduction rule (`sorry` represents a proof of `False` that can use `hp`)
example (p : Prop) : ¬p :=
  fun (hp : p) => sorry
               -- ^ Put your cursor here to see the local context
-- Elimination rule 1 (modus ponens, using definition)
example (p : Prop) (hnp : ¬p) (hp : p) : False :=
  hnp hp
-- Elimination rule 2
example (p q : Prop) (hnp : ¬p) (hp : p) : q :=
  -- `absurd` is a convenient wrapper for `False.elim (hnp hp)` (try it!)
  absurd hp hnp
-- Additional axiom, double negation elimination
#check Classical.not_not
example (p : Prop) (h : ¬¬p) : p := Classical.not_not.mp h
-- Additional axiom, law of excluded middle
#check Classical.em

/-!
## Exercises
-/

-- The `variable` command is a way to weakly add additional parameters to every
-- declaration. For `theorem`, only those variables referenced in the theorem
-- statement will be added as parameters. For `def`, only those variables used
-- in the type or body will be added as parameters. (There are some additional
-- rules surrounding instance implicit arguments, which we won't get into here.)
variable {p q r p' q' r' : Prop}

/-
**Hint:** When constructing these proofs, you may find it helpful to use
placeholders so that the term is always well-formed. For example,
you can write `And.intro sorry sorry`.

You may also find it helpful to use `have` syntax to collect derived facts.
Here is a template for a proof `h` of a proposition `p`.
```
have h : p := sorry
sorry
```
-/

/-!
Use `And.elim` to derive the `And.left` elimination rule.
-/
theorem And.left' : p ∧ q → p :=
  fun aandb => And.elim (fun p => fun _ => p) (aandb)

-- (Hover over `And.left'` above to see its type. Notice only `p` and `q` are
-- included as parameters, and the others are not. That's `variable` at work.)

/-!
Use `Or.elim` and its introduction rules:
-/
theorem Or.symm' : p ∨ q → q ∨ p :=
  fun p_or_q => Or.elim p_or_q (fun p' => Or.inr p') (fun q' => Or.inl q')

/-!
Study the following `#print` outputs and determine which natural deduction
rules are represented.
-/
#print And
#print Or
-- You can also try taking a look at the very general elimination rule that
-- comes with each of these types. It's always `TypeName.rec` (`rec` stands for
-- "recursor"). All elimination rules are defined in terms of these `rec` rules.
#check And.rec
#check Or.rec

/-!
Assorted exercises. Use only the rules we've mentioned, and do not use
`Classical.not_not` or `Classical.em` unless it is specifically allowed in
the exercise.
-/

theorem iff_iff_and : (p ↔ q) ↔ (p → q) ∧ (q → p) := Iff.intro
  (fun h => And.intro (Iff.mp h) (Iff.mpr h))
  (fun h => Iff.intro (And.left h) (And.right h))

theorem Or.imp' (h : p ∨ q) (hp : p → p') (hq : q → q') : p' ∨ q' := Or.elim h
  (fun P => Or.inl (hp P)) (fun Q => Or.inr (hq Q))

theorem Or.resolve_left' (h : p ∨ q) (hnp : ¬p) : q := Or.elim h
  (fun P => False.elim (hnp P)) id

theorem and_false' : p ∧ False ↔ False := Iff.intro And.right False.elim

theorem not_not_em' : ¬¬(p ∨ ¬p) :=
  fun nem => nem (Or.inr (fun p' => nem (Or.inl p')))

-- You can use `not_not_em'` and `Classical.not_not`.
theorem em'' : p ∨ ¬p :=
  Classical.not_not.mp not_not_em'

-- You can use `Classical.em` and/or `Classical.not_not`.
theorem not_or_of_imp' : (p → q) → (¬p ∨ q) :=
  fun hpq => Or.elim (Classical.em p) (fun p' => Or.inr (hpq p')) Or.inl

-- Prove this using `Classical.em` to do a case analysis on `p`.
theorem not_iff_not_self : ¬(p ↔ ¬p) :=
  fun h => Or.elim (Classical.em p) (fun p' => (Iff.mp h) p' p') (fun np' => np' ((Iff.mpr h) np'))

-- Prove this *without* using `Classical.em` or `Classical.not_not`.
theorem not_iff_not_self' : ¬(p ↔ ¬p) := fun h =>
  (fun p' => Iff.mp h p' p') (Iff.mpr h (fun p' => Iff.mp h p' p'))

/-!
Notice that the parameters for constants have at least two different forms:
- `(p : Prop)` means that `p` is a parameter that must be given explicitly
- `{p : Prop}` means that `p` is a parameter that Lean will attempt to infer
  based on context. This is called an "implicit argument".

You can use a `@` prefix to make all implicit arguments be explicit.
For example, you would need to write `@And.intro p q hp hq` instead
of `And.intro hp hq`.

You can use `set_option pp.explicit true` to have the pretty printer use `@`
prefixes to ensure no implicit arguments are hidden.
-/

/-!
When you write the following proof, use `@` prefixes for every constant.
You can use `_` for implicit arguments as are composing the term (this is called
a *placeholder*, and it causes an argument to become implicit), however, be
sure to replace all placeholders with actual terms by the end.
-/
theorem and_assoc_mp (h : p ∧ q ∧ r) : (p ∧ q) ∧ r :=
  And.intro (And.intro (And.left h) (And.left (And.right h))) (And.right (And.right h))

/-!
Extra

You can use the `#explode` command to see a theorem in Fitch-like notation,
rather than the lambda calculus notation.
-/
--#explode not_iff_not_self'
