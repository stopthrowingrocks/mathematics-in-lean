import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs, xu⟩
  exact ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x ⟨xs, xtu⟩
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩) <;> use xs
  · left; exact xt
  · right; exact xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, nxtu⟩
  constructor
  · {
    use xs
    contrapose! nxtu with nxt
    left
    assumption
  }
  · {
    contrapose! nxtu with nxu
    right
    assumption
  }

-- crazy-ass negation manipulation
example : s \ (t ∪ u) ⊆ (s \ t) \ u := fun x ⟨xs, nxtu⟩ =>
  ⟨⟨xs, fun h => nxtu (Or.inl h)⟩, fun h => nxtu (Or.inr h)⟩

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor <;> rintro ⟨xs, xt⟩ <;> exact ⟨xt, xs⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ (by constructor <;> exact fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩)

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) (fun _ ⟨xt, xs⟩ ↦ ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s :=
  Set.ext fun x => ⟨fun ⟨xs, _⟩ => xs, fun xs => ⟨xs, (Or.inl xs)⟩⟩

example : s ∪ s ∩ t = s :=
  Set.ext fun x => ⟨
    (by rintro (xs | ⟨xs, _⟩) <;> exact xs),
    fun xs => (Or.inl xs)
  ⟩

example : s \ t ∪ t = s ∪ t :=
  Set.ext fun x => ⟨
    (by
      rintro (⟨xs, _⟩ | xt)
      · left; exact xs
      · right; exact xt
    ),
    (by
      rintro (xs | xt)
      · by_cases xt : (x ∈ t)
        · right; exact xt
        · left; exact ⟨xs, xt⟩
      · right; exact xt
    ),
  ⟩

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := Set.ext fun x => ⟨
  fun h => (by
    rcases h with (⟨xs, nxt⟩ | ⟨xt, nxs⟩)
    · exact ⟨
      (by left; exact xs),
      fun ⟨_, xt⟩ => nxt xt
    ⟩
    · exact ⟨
      (by right; exact xt),
      fun ⟨xs, _⟩ => nxs xs
    ⟩
  ),
  fun ⟨xst, nxst⟩ => (by
    rcases xst with xs | xt
    · left; exact ⟨xs, fun xt => nxst ⟨xs, xt⟩⟩
    · right; exact ⟨xt, fun xs => nxst ⟨xs, xt⟩⟩
  )
⟩

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n ⟨hp, hg⟩
  simp at *
  rcases Nat.Prime.eq_two_or_odd hp with eq2 | hodd
  · rw [eq2] at hg; contradiction
  exact Nat.odd_iff.mpr hodd

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · exact h₀ x xs
  exact h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  have ⟨x, xs, _, prime_x⟩ := h
  use x

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  have xt := ssubt xs
  exact ⟨h₀ x xt, h₁ x xt⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, hp⟩
  use x, ssubt xs
end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp
  constructor
  · {
    rintro (xs | xA) i
    · right; exact xs
    · left; exact xA i
  }
  · {
    intro h
    by_cases xs₀ : x ∈ s
    · left; assumption
    · {
      right
      intro i
      rcases h i with (xA | xs)
      · assumption
      · contradiction
    }
  }

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext x
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  simp
  contrapose!
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  have ⟨p, xlep, pp⟩ := Nat.exists_infinite_primes x
  exact ⟨p, pp, xlep⟩

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
