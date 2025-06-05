import MIL.Common
import Mathlib.Analysis.SpecialFunctions.Log.Basic

#check mul_comm
#check two_mul
#check sub_self
#check add_sub
#check sub_add
#check sub_sub
#check add_zero
#check mul_sub
#check pow_two

section
variable (R : Type*) [Ring R]
variable {G : Type*} [Group G]
variable (a b c d e : ℝ)

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_zero : ∀ a : R, a + 0 = a)
#check (sub_self : ∀ a : R, a - a = 0)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (add_neg_cancel : ∀ a : R, a + -a = 0)
#check (neg_add_cancel_left : ∀ (a b : R), -a + (a + b) = b)
#check (add_neg_cancel_right : ∀ (a b : R), a + b + -b = a)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
#check (mul_zero : ∀ a : R, a * 0 = 0)
#check (zero_mul : ∀ a : R, 0 * a = 0)
#check (sub_eq_add_neg : ∀ a b : R, a - b = a + -b)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)

#check (mul_le_mul_of_nonneg_left)
#check (mul_le_mul_of_nonneg_right)
#check (mul_lt_mul_of_pos_right)
#check (abs_nonneg)
#check (le_of_lt)
#check (mul_div_cancel)

-- rw, nth_rw
-- ring
-- rfl
-- exact
-- apply
