import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Unique
import Mathlib.Data.Nat.Prime.Defs

open Matrix

-- @[simp] allows the simp tactic to use this lemma
@[simp] lemma eq_comm' {α : Type*} {i j : α} : (i = j) = (j = i) := by
  simp
  apply eq_comm

/-- Helper function to identify the single nonzero index in a stdBasisMatrix. -/
lemma stdBasis_apply
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {R : Type} [Semiring R] (r : R)
  (k : n) (l : m) (i : n) (j : m)
: stdBasisMatrix k l r i j = if (i, j) = (k, l) then r else 0 := by simp [stdBasisMatrix]

/-- A derivation on matrices of type `n`×`m`,
where `n` and `m` are permitted by `ValidIndex`. -/
@[ext] structure MatrixDerivationFamily
  -- TODO: It may be possible to change the proofs below to support all Semirings or Rings instead of just CommRings
  (R : Type) [Semiring R] (ValidIndex : ℕ → Prop)
where
  D :
    ∀ {n m : ℕ} (_vn : ValidIndex n) (_vm : ValidIndex m),
    Matrix (Fin n) (Fin m) R → Matrix (Fin n) (Fin m) R
  linearity :
    ∀ {n m : ℕ} (vn : ValidIndex n) (vm : ValidIndex m),
    ∀ {s : Type} [Fintype s] [DecidableEq s]
    (a : s -> R)
    (A : s -> Matrix (Fin n) (Fin m) R),
      D vn vm (∑ (t : s), (a t) • (A t)) = ∑ (t : s), (a t) • D vn vm (A t)
  product_rule :
    ∀ {n k m : ℕ} (vn : ValidIndex n) (vk : ValidIndex k) (vm : ValidIndex m)
    (A : Matrix (Fin n) (Fin k) R) (B : Matrix (Fin k) (Fin m) R),
      D vn vm (A * B) = A * (D vk vm B) + (D vn vk A) * B

/-- A family of “generator” matrices `G n` for each dimension `n` satisfying `ValidIndex n`.
Used to construct MatrixDerivationFamilys. -/
structure GeneratorFamily
  (R : Type) [Semiring R] (ValidIndex : ℕ → Prop)
where
  G : ∀ {n : ℕ} (_vn : ValidIndex n), Matrix (Fin n) (Fin n) R

/-- Proof of equality for two GeneratorFamilys if their generating functions are equal. -/
@[ext] theorem GeneratorFamily.ext
  {R : Type} [Semiring R] {ValidIndex : ℕ → Prop}
  {F₁ F₂ : GeneratorFamily R ValidIndex}
  (h : ∀ {n : ℕ} (vn : ValidIndex n), F₁.G vn = F₂.G vn)
: F₁ = F₂ := by
  cases F₁
  · cases F₂
    · congr; funext n vn
      apply h

/-- From a `GeneratorFamily`, construct a full `MatrixDerivationFamily` using the formula `D A = G n * A - A * G m` -/
def GeneratorFamily.toMatrixDerivationFamily
  {R : Type} [CommRing R] (self : GeneratorFamily R ValidIndex) : MatrixDerivationFamily R ValidIndex where
  D {n m} vn vm A := (self.G vn) * A - A * (self.G vm)
  linearity := by
    intro n m vn vm s _ _ a A
    simp
    have inst := @Matrix.semiring (Fin n) R _ _ _
    rw [show self.G vn * ∑ t : s, a t • A t = ∑ t : s, self.G vn * a t • A t by
      unfold Finset.sum
      apply map_sum (Matrix.addMonoidHomMulLeft (self.G vn))
    ]
    rw [show (∑ t : s, a t • A t) * self.G vm = ∑ t : s, a t • A t * self.G vm by
      unfold Finset.sum
      apply map_sum (Matrix.addMonoidHomMulRight (self.G vm))
    ]
    rw [sub_eq_iff_eq_add]
    rw [← Finset.sum_add_distrib]
    congr; ext _ _ _
    simp [mul_sub]
  product_rule := by
    intro n k m vn vk vm A B
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- From a MatrixDerivationFamily `F`, reconstruct a specific generator matrix `G n`
by returning how `F` derives basis vectors of size `n`. -/
def MatrixDerivationFamily.generatorOf
  {R : Type} [Semiring R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : ℕ} (vn : ValidIndex n)
  (v₁ : ValidIndex 1)
: Matrix (Fin n) (Fin n) R :=
  fun i j => (self.D vn v₁ (stdBasisMatrix j 0 1)) i 0 -- idk if this is the right order

/-- From a MatrixDerivationFamily, reconstruct what its GeneratorFamily might have been. -/
def MatrixDerivationFamily.toGeneratorFamily
  {R : Type} [Semiring R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  (v₁ : ValidIndex 1)
: GeneratorFamily R ValidIndex where
  G {n} (vn : ValidIndex n) := by
    exact self.generatorOf vn v₁

/-- Converting a `GeneratorFamily` to a `MatrixDerivationFamily` and back recovers the original. -/
theorem GeneratorFamily.toMatrixDerivationIsInvertible
  {R : Type} [CommRing R] {ValidIndex : ℕ → Prop}
  (self : GeneratorFamily R ValidIndex)
  {v₁ : ValidIndex 1}
  -- 1×1 generator matrix is zero. When this comes from a MatrixDerivationFamily it's guaranteed but not in general.
  (h₁ : self.G v₁ = 0)
: self.toMatrixDerivationFamily.toGeneratorFamily v₁ = self := by
  apply GeneratorFamily.ext; intros n vn
  -- now we must show pointwise equality of the G‐fields:
  funext i j
  rw [MatrixDerivationFamily.toGeneratorFamily]
  rw [GeneratorFamily.toMatrixDerivationFamily]
  simp [MatrixDerivationFamily.generatorOf]
  rw [sub_eq_self.mpr]
  rw [Matrix.mul_apply]
  rw [h₁]
  simp

/-- Helper lemma that says that the Matrix Derivation of a scalar (1×1 matrix) is zero. -/
lemma MatrixDerivationFamily.generatorOfScalar
  {R : Type} [Ring R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  (v₁ : ValidIndex 1)
  (scalarVec : Matrix (Fin 1) (Fin 1) R)
: self.D v₁ v₁ scalarVec = 0 := by
  have u := Fin.instUnique
  have h : ∀ svec : Matrix (Fin 1) (Fin 1) R, svec = ∑ _ : (Fin 1), svec 0 0 • stdBasisMatrix 0 0 (1 : R) := by
    intro svec
    simp
    ext i j
    rw [stdBasis_apply]
    rw [u.uniq i, u.uniq j, u.uniq 0]
    simp

  rw [h scalarVec]
  rw [self.linearity]
  simp
  have h₂ := calc
    self.D v₁ v₁ (stdBasisMatrix 0 0 1) + 0
      = self.D v₁ v₁ (stdBasisMatrix 0 0 1 * stdBasisMatrix 0 0 1) := by simp
    _ = self.D v₁ v₁ (stdBasisMatrix 0 0 1)
        + self.D v₁ v₁ (stdBasisMatrix 0 0 1) := by
      rw [self.product_rule v₁ v₁ v₁]
      ext _u₃ _u₄; rw [u.uniq _u₃, u.uniq _u₄, u.uniq 0]
      rw [Matrix.add_apply]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp

  simp [add_left_cancel (Eq.symm h₂)]

/-- Helper lemma that says that the Matrix Derivation of a vector `colVec` is `G n * colVec`. -/
lemma MatrixDerivationFamily.generatorOfCol
  {R : Type} [CommRing R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : ℕ} (vn : ValidIndex n)
  (v₁ : ValidIndex 1)
  (colVec : Matrix (Fin n) (Fin 1) R)
: self.D vn v₁ colVec = (self.generatorOf vn v₁) * colVec := by
  have u := Fin.instUnique
  ext i _u₁; rw [u.uniq _u₁]
  rw [Matrix.mul_apply]
  have hcol : colVec = ∑ (i : Fin n), colVec i u.default • stdBasisMatrix i u.default 1 := by
    ext k _u₂; rw [u.uniq _u₂]
    rw [Fintype.sum_apply, Fintype.sum_apply]
    rw [← Fintype.sum_ite_eq k (fun k' => colVec k' u.default)]
    congr; ext i
    simp [stdBasis_apply]
  nth_rw 1 [hcol]
  rw [self.linearity]
  rw [Fintype.sum_apply, Fintype.sum_apply]
  congr; ext j
  rw [MatrixDerivationFamily.generatorOf]
  simp
  rw [mul_comm, u.uniq 0]

/-- Helper lemma that describes the structure of the generator matrix. -/
lemma MatrixDerivationFamily.generatorOfCols
  {R : Type} [CommRing R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : ℕ} (vn : ValidIndex n)
  (v₁ : ValidIndex 1)
: self.generatorOf vn v₁
  = fun (i j : Fin n) => ((stdBasisMatrix 0 i (1 : R)) * self.D vn v₁ (stdBasisMatrix j 0 (1 : R))) 0 0 := by
  ext i j
  rw [MatrixDerivationFamily.generatorOfCol]
  simp

/-- Helper lemma that says that the Matrix Derivation of a row vector `rowVec` is `- rowVec * G n`. -/
lemma MatrixDerivationFamily.generatorOfRow
  {R : Type} [CommRing R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : ℕ} (vn : ValidIndex n)
  (v₁ : ValidIndex 1)
  (rowVec : Matrix (Fin 1) (Fin n) R)
: self.D v₁ vn rowVec = - rowVec * (self.generatorOf vn v₁) := by
  have u := Fin.instUnique
  ext _u₁ i; rw [u.uniq _u₁]
  rw [MatrixDerivationFamily.generatorOfCols]
  rw [Matrix.mul_apply]
  simp
  rw [← Matrix.mul_apply]
  trans (self.D v₁ vn rowVec * stdBasisMatrix i (0 : Fin 1) (1 : R)) 0 0
  · simp [u.uniq 0]
  rw [neg_eq_zero_sub]
  apply Eq.symm
  rw [sub_eq_iff_eq_add]
  rw [u.uniq 0]
  rw [← Matrix.add_apply]
  rw [add_comm]
  rw [← self.product_rule]
  rw [self.generatorOfScalar]
  simp

/-- Converting a `MatrixDerivationFamily` to a `GeneratorFamily` and back recovers the original. -/
theorem MatrixDerivationFamily.toGeneratorIsInvertible
  {R : Type} [CommRing R] {ValidIndex : ℕ → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  (v₁ : ValidIndex 1)
: GeneratorFamily.toMatrixDerivationFamily (self.toGeneratorFamily v₁) = self := by
  have u := Fin.instUnique
  apply MatrixDerivationFamily.ext
  funext n m vn vm mat i j
  have hmat : mat = ∑ ((i, j) : (Fin n) × (Fin m)), mat i j • stdBasisMatrix i j 1 := by
    ext k l
    rw [show mat k l = match (k, l) with | (k', l') => mat k' l' by rfl]
    rw [Fintype.sum_apply, Fintype.sum_apply]
    have h := Fintype.sum_ite_eq (k, l) (fun (k', l') => mat k' l')
    rw [← h] -- idk why it needs to be this way :(
    congr; ext ⟨i, j⟩
    simp [stdBasis_apply]
  rw [hmat]
  rw [MatrixDerivationFamily.linearity]
  rw [MatrixDerivationFamily.linearity]
  rw [Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply, Fintype.sum_apply]
  congr; ext ⟨k, l⟩
  dsimp [GeneratorFamily.toMatrixDerivationFamily]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply congrArg

  rw [sub_eq_iff_eq_add]
  trans ∑ x : Fin n, if k = x then
      if j = l then self.D vn v₁ (stdBasisMatrix x u.default 1) i u.default else 0
    else 0
  · congr; ext x
    rw [stdBasis_apply]
    by_cases hkx : k = x
    · simp [hkx, MatrixDerivationFamily.toGeneratorFamily, MatrixDerivationFamily.generatorOf, u.uniq 0]
    · simp [hkx, mt Eq.symm hkx]
  trans if j = l then self.D vn v₁ (stdBasisMatrix k u.default 1) i u.default else 0
  · apply Fintype.sum_ite_eq
  trans ((self.D vn v₁ (stdBasisMatrix k u.default 1)) * (stdBasisMatrix l u.default (1 : R))ᵀ) i j
  · by_cases hjl : j = l
    · simp [hjl, Matrix.mul_apply]
    · simp [hjl, mt Eq.symm hjl, Matrix.mul_apply]

  rw [add_comm, ← sub_eq_iff_eq_add]
  apply Eq.symm
  trans ∑ x : Fin m, if l = x then
      if i = k then self.D vm v₁ (stdBasisMatrix j u.default 1) x u.default else 0
    else 0
  · congr; ext x
    rw [stdBasis_apply]
    simp
    by_cases hlx : l = x
    · simp [hlx, MatrixDerivationFamily.toGeneratorFamily, MatrixDerivationFamily.generatorOf, u.uniq 0]
    · simp [hlx, mt Eq.symm hlx]
  trans if i = k then self.D vm v₁ (stdBasisMatrix j u.default 1) l u.default else 0
  · apply Fintype.sum_ite_eq

  rw [show
    stdBasisMatrix k l (1 : R) = (stdBasisMatrix k u.default (1 : R)) * (stdBasisMatrix l u.default (1 : R))ᵀ
    by simp]
  rw [self.product_rule vn v₁ vm]
  simp
  rw [self.generatorOfRow]
  by_cases hik : i = k
  · simp [hik, MatrixDerivationFamily.generatorOf, u.uniq 0]
  · simp [hik]

-- PRIMARY RESULT ------------------------------------------------------------------------------------------------------
-- At this point, we have proven that GeneratorFamily.toMatrixDerivationFamily and
-- MatrixDerivationFamily.toGeneratorFamily are inverses of each other (given certain conditions) and therefore
-- the structures are isomorphic to each other. The primary result of
-- https://stopthrowingrocks.github.io/matrix-derivation/ is precisely that every MatrixDerivationFamily is reducible
-- to a GeneratorFamily, and therefore every MatrixDerivationFamily can be constructed from a GeneratorFamily.

-- EXAMPLE USAGE -------------------------------------------------------------------------------------------------------
-- The following example is an actual instantiation of a MatrixDerivationFamily that satisfies the necessary properties
-- by first constructing a GeneratorFamily and from that constructing a MatrixDerivationFamily. We conclude by
-- evaluating the Matrix Derivation of a few example vectors and matrices using this MatrixDerivationFamily.

/-- This GeneratorFamily is defined by a sequence of matrices that rotate the index up. For example, `G * e2 = e3`
where `ei` is the `i`th basis vector. -/
def rotateGenFamily
  (R : Type) [CommRing R] (ValidIndex : ℕ → Prop)
: GeneratorFamily R ValidIndex where
  G {n} _vn i j :=
    if n > 1 then if i = (j.val + 1) % n then 1 else 0 else 0

-- See the rotation matrix of sizes 0 through 3
-- (I wish I could #assert)
#eval @(rotateGenFamily ℚ (fun _ => True)).G 0 (by tauto) = ![]
#eval @(rotateGenFamily ℚ (fun _ => True)).G 1 (by tauto) = ![![0]]
#eval @(rotateGenFamily ℚ (fun _ => True)).G 2 (by tauto) = ![![0, 1], ![1, 0]]
#eval @(rotateGenFamily ℚ (fun _ => True)).G 3 (by tauto) = ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]

/-- Restrict the valid matrix indices to only 1 and prime numbers just because we can. -/
def rotateValidIndex (n : ℕ) : Prop := n = 1 ∨ Nat.Prime n

/-- Construct a MatrixDerivationFamily from our GeneratorFamily -/
def rotateMatrixDerivationFamily := (rotateGenFamily ℚ rotateValidIndex).toMatrixDerivationFamily

-- Some theorems that 1,2,3 are valid indices
theorem rotate1 : rotateValidIndex 1 := by
  rw [rotateValidIndex]
  left; rfl
theorem rotate2 : rotateValidIndex 2 := by
  rw [rotateValidIndex]
  right; exact Nat.prime_two
theorem rotate3 : rotateValidIndex 3 := by
  rw [rotateValidIndex]
  right; exact Nat.prime_three

-- Here we are actually evaluating the derivation of these matrices, given the kind of derivation we have defined.
#eval rotateMatrixDerivationFamily.D rotate3 rotate1 ![![0], ![1], ![0]] -- Rotate the index up
#eval rotateMatrixDerivationFamily.D rotate1 rotate3 ![![0, 1, 0]] -- Rotate the index down and multiply by -1
-- For the below 3×2 matrices, (Rotate the row index up) - (Rotate the column index down)
#eval rotateMatrixDerivationFamily.D rotate3 rotate2 ![![0, 0], ![1, 0], ![0, 0]]
#eval rotateMatrixDerivationFamily.D rotate3 rotate2 ![![0, 0], ![1, 1], ![0, 0]] -- Linear combination of effects
