import Mathlib.Tactic
/-!
# Calculus of Constructions exercises
-/

namespace CoC

/-!
Since `Prop` is an "impredicative" universe, we can define propositions by
quantifying over all propositions, which includes the proposition we're
defining itself. We can encode each proposition using the type of its
elimination rule.

Note: we need to be careful to use `And`, `Or`, etc., rather than `∧`, `∨`,
etc., to use these encodings rather than the core Lean definitions.
-/

def True := ∀ (p : Prop), p → p
def False := ∀ (p : Prop), p
def And (p q : Prop) := ∀ (r : Prop), (p → q → r) → r
def Or (p q : Prop) := ∀ (r : Prop), (p → r) → (q → r) → r
def Exists {α : Type} (p : α → Prop) := ∀ (r : Prop), ((x : α) → p x → r) → r
def Not (p : Prop) := p → False
def Iff (p q : Prop) := And (p → q) (q → p)

/-!
Assorted exercises. Let's prove properties of the above using only the above
definitions and lambda calculus. Do not use any other definitions or tactics.

Hint: the proofs for the elimination rules should be very easy!
-/

variable {p q r : Prop} {α : Type}

theorem True.trivial : True := fun _ p' => p'

theorem False.elim : False → p := fun f => f p

theorem And.intro (hp : p) (hq : q) : And p q := fun _ h => h hp hq

theorem And.left (h : And p q) : p := h p (fun p' _ => p')

theorem And.right (h : And p q) : q := h q (fun _ q' => q')

theorem Or.inl (hp : p) : Or p q := fun _ pr _ => pr hp

theorem Or.inr (hq : q) : Or p q := fun _ _ qr => qr hq

theorem Or.elim (h : Or p q) (hpq : p → r) (hqq : q → r) : r := h r hpq hqq

theorem Iff.intro (hpq : p → q) (hqp : q → p) : Iff p q := fun _ h => h hpq hqp

theorem Iff.mp (h : Iff p q) : p → q := h (p -> q) (fun p' _ => p')

theorem Iff.mpr (h : Iff p q) : q → p := h (q -> p) (fun _ q' => q')

theorem Exists.intro {p : α → Prop} (x : α) (hp : p x) : Exists p := fun _ h => h x hp

theorem Exists.elim {p : α → Prop}
    (h : Exists p) (hx : ∀ (x : α), p x → r) : r := h r hx

/-!
There's no reason to prove theorems about these connectives, since by giving
the correct introduction and elimination rules, we've proved they're the same
as the usual ones. You should be able to take proofs from `E1_TermProofs.lean`
and copy them here to see this (after replacing `∧` with `And`, etc.).
-/

end CoC
