import MIL.Common
import Mathlib.Probability.Distributions.Gaussian

variable {X : Type*} [MetricSpace X] (a b c : X)


open MeasureTheory ProbabilityTheory NNReal Real Set ENNReal Function


-- variable {Ω : Type} [MeasureSpace Ω]
-- variable {μ : ℝ} {v : ℝ≥0}
-- variable {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v)
-- #check X

structure SingletonGaussian
  {X : Type} [MetricSpace X]
  (x : X) (μ : ℝ) (v : ℝ≥0)
  -- [MeasurableSpace ({x' : X // x' = x} → ℝ)]
extends Measure ({x' : X // x' = x} → ℝ)
where
  measureOf : {x' : X // x' = x} → ℝ≥0∞ := sorry
  -- empty : measureOf ∅ = 0 := sorry
  -- mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  -- iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
  --   measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i) := sorry

structure RandomField
  {X : Type} [MetricSpace X]
  (xs : Set X) (μ : X → ℝ) (v : ℝ≥0)
where
  φ : ∀(xs₀ : Set X), xs₀ ⊆ xs → Measure (xs₀ → ℝ)
  hμ : ∀ (x : X) (hx : x ∈ xs), (φ ({x}) (by simp; exact hx) = (where
    measureOf := sorry))
  -- conditional_probability : ∀ : φs, ∫⁻ φ
