import MIL.Common

open ENNReal

variable {α : Type*} [MeasurableSpace α]
variable {μ : MeasureTheory.Measure α}

example {f : α → ℝ≥0∞} {a : ℝ≥0∞} (hs : MeasurableSet {x | a ≤ f x}) (hp : 0 ≤ f) :
    a * μ.measureOf {x | a ≤ f x} ≤ (∫⁻ x, f x ∂μ) := by
  -- Recommended by ChatGPT
  have h₁ : a * μ.measureOf {x | a ≤ f x} = a * (μ.restrict {x | a ≤ f x}) Set.univ := by simp
  rw [h₁, ← MeasureTheory.lintegral_const (μ := μ.restrict {x | a ≤ f x}) a]
  rw [← MeasureTheory.lintegral_indicator hs]
  apply MeasureTheory.lintegral_mono
  intro x
  rw [Set.indicator]
  by_cases hfa : a ≤ f x
  · simp; rw [if_pos hfa]; exact hfa
  · simp; rw [if_neg hfa]; apply hp
