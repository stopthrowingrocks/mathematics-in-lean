import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

theorem _my_inf_comm {α : Type*} [SemilatticeInf α] (x y : α) : x ⊓ y ≤ y ⊓ x :=
  le_inf (inf_le_right (a := x) (b := y)) (inf_le_left (a := x) (b := y))
theorem my_inf_comm {α : Type*} [SemilatticeInf α] (x y : α) : x ⊓ y = y ⊓ x :=
  le_antisymm (_my_inf_comm x y) (_my_inf_comm y x)

theorem my_inf_assoc {α : Type*} [SemilatticeInf α] (x y z : α) : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  trans (x ⊓ y)
  apply inf_le_left
  apply inf_le_left
  apply le_inf
  trans (x ⊓ y)
  apply inf_le_left
  apply inf_le_right
  apply inf_le_right
  apply le_inf
  apply le_inf
  apply inf_le_left
  trans (y ⊓ z)
  apply inf_le_right
  apply inf_le_left
  trans (y ⊓ z)
  apply inf_le_right
  apply inf_le_right

theorem _my_sup_comm {α : Type*} [SemilatticeSup α] (x y : α) : y ⊔ x ≤ x ⊔ y :=
  sup_le (le_sup_right (a := x) (b := y)) (le_sup_left (a := x) (b := y))
theorem my_sup_comm {α : Type*} [SemilatticeSup α] (x y : α) : x ⊔ y = y ⊔ x :=
  le_antisymm (_my_sup_comm y x) (_my_sup_comm x y)

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  apply le_sup_left
  trans (y ⊔ z)
  apply le_sup_left
  apply le_sup_right
  trans (y ⊔ z)
  apply le_sup_right
  apply le_sup_right
  apply sup_le
  trans (x ⊔ y)
  apply le_sup_left
  apply le_sup_left
  apply sup_le
  trans (x ⊔ y)
  apply le_sup_right
  apply le_sup_left
  apply le_sup_right

#check min_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  rfl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  rfl
  apply inf_le_left
  apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

theorem inf_sup_cancel {α : Type*} [Lattice α] (x y : α) : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  rfl
  apply le_sup_left

theorem sup_inf_cancel {α : Type*} [Lattice α] (x y : α) : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  rfl
  apply inf_le_left
  apply le_sup_left

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h (a ⊔ b), inf_comm (a ⊔ b), inf_sup_cancel, inf_comm (a ⊔ b)]
  rw [h, sup_comm (c ⊓ a), ← sup_assoc, inf_comm c]
  apply le_antisymm
  apply le_sup_left
  apply sup_le
  rfl
  trans a
  apply inf_le_right
  apply le_sup_left

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h (a ⊓ b), sup_comm (a ⊓ b), sup_inf_cancel, sup_comm (a ⊓ b)]
  rw [h, inf_comm (c ⊔ a), ← inf_assoc, sup_comm c]
  apply le_antisymm
  apply le_inf
  rfl
  trans a
  apply inf_le_left
  apply le_sup_right
  apply inf_le_left

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← neg_add_eq_sub, ← neg_add_cancel a]
  exact add_le_add_left h (-a)

example (h: 0 ≤ b - a) : a ≤ b := by
  have g := add_le_add_left h (a)
  rw [← neg_add_eq_sub, add_neg_cancel_left, add_zero] at g
  exact g

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [← add_zero (a * c), ← add_sub_cancel_left (a * c) (b * c), add_sub_assoc]
  apply add_le_add_left
  rw [← sub_mul]
  apply mul_nonneg _ h'
  rw [← neg_add_eq_sub, ← neg_add_cancel a]
  exact add_le_add_left h (-a)
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h := dist_triangle x y x
  rw [dist_self, dist_comm y, ← two_mul, ← mul_zero 2] at h
  apply le_of_mul_le_mul_left h
  norm_num
end
