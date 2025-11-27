# Random Fields Formalization - Status Report

This document summarizes the current state of the formalization of random fields over metric spaces in Lean 4.

## Summary

We have successfully formalized the core mathematical structure described in the article "Generalizing Brownian motion: Modeling random fields over arbitrary geometries". The formalization includes definitions, basic theorems, and outlines for the main results.

## What's Been Completed

### 1. Distance Matrix (✓ Complete)
- **Definition**: The n×n distance matrix D for n+1 points in a metric space
  - Diagonal entries: `D[i,i] = d(x₀, xᵢ)`
  - Off-diagonal: `D[i,j] = (d(x₀,xᵢ) + d(x₀,xⱼ) - d(xᵢ,xⱼ))/2`

- **Theorems Proved**:
  - `distanceMatrix_symm`: The distance matrix is symmetric
  - `distanceMatrix_diag`: Diagonal entries equal distances from base point
  - `distanceMatrix_off_diag`: Off-diagonal entries have the stated form
  - `distanceMatrix_nonneg`: All entries are non-negative

### 2. Two-Point Correlation Functions (✓ Complete)
- **Definitions**:
  - `twoPointExponent`: Exponent of the 2-point correlation
  - `twoPointCorrelation`: The full correlation function

- **Theorems Proved**:
  - `twoPointCorrelation_symm`: Correlation is symmetric in field values

### 3. Three-Point Correlation Functions (✓ Complete)
- **Definitions**:
  - `threePointFieldVec`: Field strength vector for 3 points
  - `threePointDistanceMatrix`: 2×2 distance matrix
  - `threePointExponent`: Exponent ✅ **IMPLEMENTED**
  - `threePointCorrelation`: Full correlation function

- **Theorems Proved**:
  - `threePointDistanceMatrix_explicit`: Explicit 2×2 matrix form

### 4. General n-Point Correlation Functions (✓ Complete)
- **Definitions**:
  - `fieldVector`: General field strength vector
  - `correlationExponent`: General exponent ✅ **IMPLEMENTED**
  - `correlationFunction`: General correlation function

### 5. Main Theorems (Stated, Proofs Pending)
- `distanceMatrix_minor`: Matrix minor relationship for induction
- `correlation_integration_property`: Integration over one variable yields lower-dimensional correlation

## Known Issues (RESOLVED!)

### ~~Parser Error with Matrix Operations~~ ✅ FIXED
**Issue**: There was a mysterious Lean parser error when the final expression in a function was a negative product like `-c * qf`. The error message reported "unexpected token '/--'" at various locations, which was misleading.

**Root Cause**: The parser was looking for more tokens after the `-` operator and got confused when it hit the end of the definition followed by a doc comment.

**Solution**: Adding parentheses around the final expression: `(-c * qf)` instead of `-c * qf`.

**Working Implementation**:
```lean
noncomputable def correlationExponent (...) : ℝ :=
  let D := distanceMatrix x0 x
  let pv := fieldVector phi0 phi
  let Dinv := D⁻¹
  let w := Dinv *ᵥ pv
  let qf := dotProduct pv w
  let c := 1 / (2 * nu)
  (-c * qf)  -- Parentheses required!
```

## File Structure

```
src/random-fields.lean (235 lines)
├── Imports and module documentation
├── DistanceMatrix section
│   ├── distanceMatrix definition
│   └── Basic properties (4 theorems)
├── TwoPointCase section
│   ├── twoPointExponent
│   ├── twoPointCorrelation
│   └── Symmetry theorem
├── ThreePointCase section
│   ├── threePointFieldVec
│   ├── threePointDistanceMatrix
│   ├── threePointExponent (sorry)
│   └── threePointCorrelation
├── GeneralCase section
│   ├── fieldVector
│   ├── correlationExponent (sorry)
│   └── correlationFunction
└── MainTheorems section
    ├── distanceMatrix_minor (sorry)
    └── correlation_integration_property (sorry)
```

## Next Steps

1. ~~**Resolve parser error**~~: ✅ **DONE** - Fixed with parentheses
2. ~~**Implement correlation exponents**~~: ✅ **DONE** - All exponent functions implemented
3. **Prove matrix properties**: Show D is positive definite (when points are distinct)
4. **Prove integration property**: Complete the proof that integrating out variables works correctly
5. **Prove matrix minor theorem**: Show the inductive structure of distance matrices
6. **Add Markov property**: Formalize the conditional independence property
7. **Connect to probability theory**: Link correlation functions to actual probability measures

## Dependencies

- `Mathlib.Data.Matrix.Basic`
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Mathlib.LinearAlgebra.Matrix.DotProduct`
- `Mathlib.Analysis.SpecialFunctions.Exp`
- `Mathlib.Topology.MetricSpace.Basic`

## Compilation Status

✅ **File compiles successfully with NO errors!**
- 2 expected `sorry` warnings (for main theorems to be proved)
- 2 unused variable warnings (for invertibility hypotheses not yet used)
✓ All type signatures are correct
✓ All completed proofs verify
✓ All correlation exponent functions fully implemented

---

Generated: 2025-01-16
Updated: 2025-01-16 (parser issue resolved)
