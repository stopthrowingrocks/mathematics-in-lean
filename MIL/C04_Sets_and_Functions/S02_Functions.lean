import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · {
    intro h x xs
    apply h
    exact ⟨x, ⟨xs, rfl⟩⟩
  }
  · {
    rintro h x ⟨y, ⟨ys, rfl⟩⟩
    exact h ys
  }

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ⟨ys, feq⟩⟩
  rwa [h feq] at ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro _ ⟨y, h, rfl⟩
  exact h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro x xu
  rcases h x with ⟨y, rfl⟩
  use y, xu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro _ ⟨y, ys, rfl⟩
  use y, h ys

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x hu
  exact h hu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro _ ⟨y, ⟨ys, yt⟩, rfl⟩
  constructor
  · exact ⟨y, ys, rfl⟩
  · exact ⟨y, yt, rfl⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro x ⟨⟨y, ys, rfl⟩, ⟨z, zt, hz⟩⟩
  rw [h hz] at zt
  use y, ⟨ys, zt⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro x ⟨⟨y, ys, rfl⟩, r⟩
  use y, ⟨ys, (by
    contrapose! r
    use y
  )⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨xu, nxv⟩
  use xu, nxv
  -- just `simp` also works

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x; constructor
  · rintro ⟨⟨y, ys, rfl⟩, xv⟩
    exact ⟨y, ⟨ys, xv⟩, rfl⟩
  · rintro ⟨y, ⟨ys, xv⟩, rfl⟩
    exact ⟨⟨y, ys, rfl⟩, xv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro _ ⟨y, ⟨ys, xu⟩, rfl⟩
  exact ⟨⟨y, ys, rfl⟩, xu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, xu⟩
  exact ⟨⟨x, xs, rfl⟩, xu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fu)
  · left; exact ⟨x, ⟨xs, rfl⟩⟩
  · right; exact fu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x; constructor
  · rintro ⟨y, h, rfl⟩
    simp at *
    have ⟨i, yAi⟩ := h
    use i, y
  · rintro h
    simp at *
    -- For some reason I can't put this into the `rintro`.
    have ⟨i, y, yAi, rf⟩ := h
    exact ⟨y, ⟨i, yAi⟩, rf⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro _ ⟨y, h, rfl⟩
  simp at *
  intro i
  use y, h i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro x h
  simp at *
  rcases h i with ⟨a, aAi, rfl⟩
  use a
  constructor; case right => rfl
  intro j
  rcases h j with ⟨b, bAj, heq⟩
  rw [injf heq] at bAj
  exact bAj

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; constructor <;> simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; constructor <;> simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x hx y hy hf
  simp at hx hy
  calc
    x = √x ^ 2 := eq_comm.mp (sq_sqrt hx)
    _ = √y ^ 2 := by rw [hf]
    _ = y := sq_sqrt hy


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy hf
  simp at *
  calc
    x = √(x ^ 2) := eq_comm.mp (sqrt_sq hx)
    _ = √(y ^ 2) := by rw [hf]
    _ = y := sqrt_sq hy

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro h
    simp at *
    rcases h with ⟨x, hx, rfl⟩
    exact sqrt_nonneg x
  · rintro h
    simp at *
    use (y ^ 2)
    exact ⟨sq_nonneg y, sqrt_sq h⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro h
    simp at *
    rcases h with ⟨ysqrt, rfl⟩
    exact sq_nonneg ysqrt
  · rintro h
    simp at *
    use √y
    exact sq_sqrt h

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro finj x
    have e : ∃ z, f z = f x := by use x
    rw [inverse, dif_pos e]
    exact finj (Classical.choose_spec e)
  · rintro finv x y feq
    calc
      x = inverse f (f x) := eq_comm.1 (finv x)
      _ = inverse f (f y) := by rw [feq]
      _ = y := finv y

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · rintro fsur x
    rcases fsur x with ⟨a, rfl⟩
    have e : ∃ z, f z = f a := by use a
    rw [inverse, dif_pos e]
    exact Classical.choose_spec e
  · rintro h x
    use inverse f x
    exact h x

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [h] at h₁
    exact h₁
  contradiction

end
