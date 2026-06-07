import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Notation


/-- A point in the plane. -/
structure Point where
  x : ℝ
  y : ℝ

/-- Noncomputable Euclidean distance. -/
noncomputable def dist (p q : Point) : ℝ :=
  Real.sqrt ((p.x - q.x) ^ 2 + (p.y - q.y) ^ 2)

/-- D‐entry using coordinatewise equality. -/
noncomputable def Dentry (b p q : Point) : ℝ :=
  if p.x = q.x ∧ p.y = q.y then dist b p
  else (dist b p + dist b q - dist p q) / 2

open Matrix


/-- Build D‐matrix from xs and ys with baseline b. -/
noncomputable def rfDMatrix {n m : Type} [Finite n] [Finite m]
  (b : Point) (xs : n → Point) (ys : m → Point) : Matrix n m ℝ :=
  fun i j => Dentry b (xs i) (ys j)

/-- Conditional mean φ(q) given existing xs with values φ_e. -/
noncomputable def conditionalMean {n : Type} [Finite n]
  (b : Point) (xs : n → Point) (φ : n → ℝ) (q : Point) : ℝ :=
  let D_ee := rfDMatrix b xs xs              -- (n×n)
  let A := D_ee⁻¹               -- (n×n)
  let α    := A.mulVec φ                     -- (n)
  let k    := rfDMatrix b xs fun _ => q      -- (n×1) as matrix
  (kᵀ.mulVec α) 0

/-- Conditional variance Var[φ(q)] | φ_e. -/
noncomputable def conditionalVar {n : Type} [Finite n]
  (ν : ℝ) (b : Point) (xs : n → Point) (φ : n → ℝ) (q : Point) : ℝ :=
  let φ0  := φ default
  let D_ee:= rfDMatrix b xs xs               -- (n×n)
  let K_ee:= ν • D_ee                       -- (n×n)
  let A := K_ee⁻¹               -- (n×n)
  let D_en:= rfDMatrix b xs fun _ => q       -- (n×1)
  let k    := ν • D_en                      -- (n×1)
  ν * Dentry b q q - (kᵀ.mulVec (A.mulVec fun i => φ i - φ0)) 0

#eval let b : Point := { x := 0, y := 0 }
#eval let xs : Fin 2 → Point := fun i => if i = 0 then { x := 1, y := 0 } else { x := 0, y := 1 }
#eval conditionalMean b xs (fun i => if i = 0 then 1.0 else 2.0) { x := 0.5, y := 0.5 }
