import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  match le_or_gt 0 x with
    | Or.inl h =>
      rw [abs_of_nonneg h]
    | Or.inr h =>
      linarith [abs_nonneg x]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  match le_or_gt 0 x with
    | Or.inl h =>
      linarith [neg_nonpos_of_nonneg h, abs_nonneg x]
    | Or.inr h =>
      rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  match le_or_gt 0 (x + y) with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      linarith [le_abs_self x, le_abs_self y]
    | Or.inr h =>
      rw [abs_of_neg h]
      linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := ⟨
  fun h1 => (by
    rcases le_or_gt 0 y with h | h
    · {
      left
      linarith [abs_of_nonneg h]
    }
    · {
      right
      linarith [abs_of_neg h]
    }
  ),
  (by
    rintro (h | h)
    · linarith [le_abs_self y]
    · linarith [neg_le_abs_self y]
  )
⟩

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := ⟨
  fun h => ⟨
    (by linarith [neg_le_abs_self x]),
    (by linarith [le_abs_self x])
  ⟩,
  fun h0 => (by
    rcases le_or_gt 0 x with h | h
    · linarith [abs_of_nonneg h]
    · linarith [abs_of_neg h]
  )
⟩

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right
    exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, ⟨y, rfl | rfl⟩⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1) * (x + 1) = 0 := by
    ring_nf
    rw [h]
    simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x - y) * (x + y) = 0 := by
    ring_nf
    rw [h]
    simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1) * (x + 1) = 0 := by
    ring_nf
    rw [h]
    simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with e | e
  · {
    left
    have g := sub_eq_iff_eq_add.mp e
    simp at g
    exact g
  }
  · {
    right
    exact eq_comm.mp (neg_eq_of_add_eq_zero_left e)
  }

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x - y) * (x + y) = 0 := by
    ring_nf
    rw [h]
    simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with e | e
  · {
    left
    have g := sub_eq_iff_eq_add.mp e
    simp at g
    exact g
  }
  · {
    right
    exact eq_comm.mp (neg_eq_of_add_eq_zero_left e)
  }

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · {
    intro h
    by_cases p : P
    · {
      right
      exact h p
    }
    · {
      left
      exact p
    }
  }
  · {
    rintro (h | h) p
    · {
      exfalso
      exact h p
    }
    · exact h
  }
