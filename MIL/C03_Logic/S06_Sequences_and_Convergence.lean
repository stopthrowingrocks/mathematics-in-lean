import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  exact εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs _ ε2pos with ⟨Ns, hs⟩
  rcases ct _ ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have g : |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
  linarith [
    abs_add (s n - a) (t n - b),
    hs n (le_of_max_le_left nge),
    ht n (le_of_max_le_right nge)
  ]


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  have εcpos : 0 < ε / |c| := div_pos εpos acpos
  rcases cs _ εcpos with ⟨N, Nh⟩
  use N
  intro n ngeN
  dsimp
  rw [← mul_sub c]
  rw [abs_mul]
  exact (lt_div_iff₀' acpos).mp (Nh n ngeN)

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n ≥ N, |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n nge
  linarith [
    h n nge,
    abs_sub_abs_le_abs_sub (s n) a
  ]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct (ε / B) pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nge
  have h₀' := h₀ n (le_of_max_le_left nge)
  have h₁' := h₁ n (le_of_max_le_right nge)
  simp at h₁'
  simp
  rw [abs_mul]
  convert mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt h₀') h₁' (abs_nonneg _) Bpos
  rw [mul_div_cancel₀]
  exact ne_of_gt Bpos

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    rw [add_neg_cancel]
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_pos.mpr
    contrapose! abne
    rw [← sub_eq_zero]
    exact abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (by rfl))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (by rfl))
  have : |a - b| < |a - b| := by
    have : ε + ε = |a - b| := by ring
    have : |s N - a| + |s N - b| < ε + ε := add_lt_add absa absb
    have : |(s N - b) - (s N - a)| ≤ |s N - b| + |s N - a| := abs_sub (s N - b) (s N - a)
    have : |(s N - b) - (s N - a)| = |a - b| := by congr 1; ring
    linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
