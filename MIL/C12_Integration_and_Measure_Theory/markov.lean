import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Function
open MeasureTheory ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

/-- Markov's inequality: for nonnegative measurable `f` and `a > 0`,
    the measure of the set where `f ≥ a` is bounded by `∫ f / a`. -/
theorem markov_inequality
    {f : α → ℝ≥0∞} (hf : Measurable f) {a : ℝ≥0∞} (ha : 0 < a) :
    μ {x | a ≤ f x} ≤ (∫⁻ x, f x ∂μ) / a := by
  -- Use the fact that on {x | a ≤ f x}, we have a ≤ f x
  have bound : ∀ x, a ≤ f x → a ≤ f x := fun x hx => hx
  calc
    μ {x | a ≤ f x} = ∫⁻ x, 1 ∂(μ.restrict {x | a ≤ f x}) := by
        rw [lintegral_one, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ x, f x / a ∂(μ.restrict {x | a ≤ f x}) := by
      apply lintegral_mono
      intro x hx
      by_cases h : a ≤ f x
      · rw [one_le_div ha]
        exact h
      · exact zero_le _
      rw [one_le_div ha] at hx
      exact one_le_div (bound x hx) ha.ne'
    _ = (∫⁻ x in {x | a ≤ f x}, f x ∂μ) / a := by rw [lintegral_div_const]
    _ ≤ (∫⁻ x, f x ∂μ) / a := lintegral_mono_set (measurableSet_le measurable_const hf) (fun x hx ↦ le_rfl)
