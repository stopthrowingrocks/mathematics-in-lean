import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NoncommRing
import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Matrix

-- This @[simp] allows the simp tactic to apply this lemma
@[simp] lemma eq_comm' {α : Type*} {i j : α} : (i = j) = (j = i) := by
  simp
  apply eq_comm

lemma stdBasis_apply
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {R : Type} [Semiring R]
  (k : n) (l : m) (i : n) (j : m)
: stdBasisMatrix k l 1 i j = if (i, j) = (k, l) then (1 : R) else 0 := by simp [stdBasisMatrix]

/-- A derivation on matrices of fixed shape (n × m). -/
@[ext] structure MatrixDerivationFamily
  (R : Type) [Semiring R] (ValidIndex : Type → Prop)
where
  D
    : ∀ {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (_vn : ValidIndex n) (_vm : ValidIndex m),
      Matrix n m R → Matrix n m R
  linearity
    : ∀ {n m s : Type} [Fintype n] [Fintype m] [Fintype s] [DecidableEq n] [DecidableEq m]
    (_vn : ValidIndex n) (_vm : ValidIndex m)
    (a : s -> R)
    (A : s -> Matrix n m R),
      D _vn _vm (∑ (t : s), (a t) • (A t)) = ∑ (t : s), (a t) • D _vn _vm (A t)
  product_rule :
    ∀ {n k m : Type} [Fintype n] [Fintype k] [Fintype m] [DecidableEq n] [DecidableEq k] [DecidableEq m]
    (_vn : ValidIndex n) (_vk : ValidIndex k) (_vm : ValidIndex m)
    (A : Matrix n k R) (B : Matrix k m R),
      D _vn _vm (A * B) = A * (D _vk _vm B) + (D _vn _vk A) * B

/--
A family of “generator” matrices `G n` for each dimension `n`
that induce a consistent derivation:
  D A = G n * A - A * G m.
-/
structure GeneratorFamily
  (R : Type) [CommRing R] (ValidIndex : Type → Prop)
where
  G : ∀ {n : Type} [Fintype n] [DecidableEq n] (_vn : ValidIndex n), Matrix n n R

@[ext] theorem GeneratorFamily.ext
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  {F₁ F₂ : GeneratorFamily R ValidIndex}
  (h : ∀ {n : Type} [Fintype n] [DecidableEq n] (vn : ValidIndex n), F₁.G vn = F₂.G vn)
: F₁ = F₂ := by
  cases F₁
  · cases F₂
    · congr; funext n _ _ vn
      apply h

/-- From a `GeneratorFamily`, build a full `MatrixDerivationFamily`. -/
def GeneratorFamily.toMatrixDerivationFamily
  {R : Type} [CommRing R] (self : GeneratorFamily R ValidIndex) : MatrixDerivationFamily R ValidIndex where
  D {n m} fin_n fin_m dn dm _vn _vm A := (self.G _vn) * A - A * (self.G _vm)
  linearity := by
    intro n m s _ _ _ _ _ vn vm a A
    simp
    have inst := @Matrix.semiring n R _ _ _
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
    intro n k m _ _ _ _ _ _ vn vk vm A B
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- Reconstruct the generator matrix Gₙ from a derivation `D`
    by seeing how it acts on column basis vectors. -/
def MatrixDerivationFamily.generatorOf
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : Type} [Fintype n] [DecidableEq n] (_vn: ValidIndex n) (vu : ValidIndex Unit)
: Matrix n n R :=
  fun i j => (self.D _vn vu (stdBasisMatrix j () 1)) i () -- idk if this is the right order

/-- Convert an entire derivation family back into a `GeneratorFamily`. -/
def MatrixDerivationFamily.toGeneratorFamily
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  (vu : ValidIndex Unit)
: GeneratorFamily R ValidIndex where
  G {n} {_fn : Fintype n} {_dn : DecidableEq n} (vn : ValidIndex n) := by
    exact self.generatorOf vn vu

/-- Converting a `GeneratorFamily` to a `MatrixDerivationFamily` and back recovers the original. -/
theorem GeneratorFamily.iso_MatrixDerivation
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : GeneratorFamily R ValidIndex)
  {vu : ValidIndex Unit}
  /- Generator of u is zero. When this comes from a MatrixDerivationFamily it's guaranteed but not in general. -/
  (hu : self.G vu = 0)
: self.toMatrixDerivationFamily.toGeneratorFamily vu = self := by
  apply GeneratorFamily.ext; intros n _ _ vn
  -- now we must show pointwise equality of the G‐fields:
  funext i j
  rw [MatrixDerivationFamily.toGeneratorFamily]
  rw [GeneratorFamily.toMatrixDerivationFamily]
  simp [MatrixDerivationFamily.generatorOf]
  rw [sub_eq_self.mpr]
  rw [Matrix.mul_apply]
  rw [hu]
  simp

lemma MatrixDerivationFamily.generatorOfScalar
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  (vu : ValidIndex Unit)
  (scalarVec : Matrix Unit Unit R)
: self.D vu vu scalarVec = 0 := by
  ext _u₁ _u₂
  have h : scalarVec = ∑ _ : Unit, scalarVec () () • stdBasisMatrix () () (1 : R) := by
    ext i j
    simp
  rw [h]
  rw [self.linearity]
  simp
  have h₂ := calc
    self.D vu vu (stdBasisMatrix () () 1) + 0
      = self.D vu vu (stdBasisMatrix () () 1 * stdBasisMatrix () () 1) := by simp
    _ = self.D vu vu (stdBasisMatrix () () 1) + self.D vu vu (stdBasisMatrix () () 1) := by
      rw [self.product_rule]
      ext _u₃ _u₄
      simp
      exact vu
  simp [add_left_cancel (Eq.symm h₂)]

lemma MatrixDerivationFamily.generatorOfCol
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : Type} [Fintype n] [DecidableEq n] (vn : ValidIndex n)
  (vu : ValidIndex Unit)
  (colVec : Matrix n Unit R)
: self.D vn vu colVec = (self.generatorOf vn vu) * colVec := by
  ext i _u
  rw [Matrix.mul_apply]
  have hcol : colVec = ∑ (i : n), colVec i () • stdBasisMatrix i () 1 := by
    ext k _
    rw [Fintype.sum_apply, Fintype.sum_apply]
    rw [← Fintype.sum_ite_eq k (fun k' => colVec k' ())]
    congr; ext i
    simp [stdBasis_apply]
  nth_rw 1 [hcol]
  rw [self.linearity]
  rw [Fintype.sum_apply, Fintype.sum_apply]
  congr; ext j
  rw [MatrixDerivationFamily.generatorOf]
  simp
  rw [mul_comm]

lemma MatrixDerivationFamily.generatorOfCols
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : Type} [Fintype n] [DecidableEq n] (vn : ValidIndex n)
  (vu : ValidIndex Unit)
: self.generatorOf vn vu
  = fun (i j : n) => ((stdBasisMatrix () i (1 : R)) * self.D vn vu (stdBasisMatrix j () (1 : R))) () () := by
  ext i j
  rw [MatrixDerivationFamily.generatorOfCol]
  simp

lemma MatrixDerivationFamily.generatorOfRow
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  {n : Type} [Fintype n] [DecidableEq n] (vn : ValidIndex n)
  (vu : ValidIndex Unit)
  (rowVec : Matrix Unit n R)
: self.D vu vn rowVec = - rowVec * (self.generatorOf vn vu) := by
  ext _u i
  rw [MatrixDerivationFamily.generatorOfCols]
  rw [Matrix.mul_apply]
  simp
  rw [← Matrix.mul_apply]
  trans (self.D vu vn rowVec * stdBasisMatrix i () (1 : R)) () ()
  · simp
  · rw [neg_eq_zero_sub]
    apply Eq.symm
    rw [sub_eq_iff_eq_add]
    rw [← Matrix.add_apply]
    rw [add_comm]
    rw [← self.product_rule]
    rw [self.generatorOfScalar]
    simp

theorem MatrixDerivationFamily.iso_Generator
  {R : Type} [CommRing R] {ValidIndex : Type → Prop}
  (self : MatrixDerivationFamily R ValidIndex)
  (vu : ValidIndex Unit)
: GeneratorFamily.toMatrixDerivationFamily (self.toGeneratorFamily vu) = self := by
  apply MatrixDerivationFamily.ext
  funext n m _ _ _ _ vn vm mat i j
  have hmat : mat = ∑ ((i, j) : n × m), mat i j • stdBasisMatrix i j 1 := by
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
  trans ∑ x : n, if k = x then
      if j = l then self.D vn vu (stdBasisMatrix x () 1) i () else 0
    else 0
  · congr; ext x
    rw [stdBasis_apply]
    by_cases hkx : k = x
    · simp [hkx, MatrixDerivationFamily.toGeneratorFamily, MatrixDerivationFamily.generatorOf]
    · simp [hkx, mt Eq.symm hkx]
  trans if j = l then self.D vn vu (stdBasisMatrix k () 1) i () else 0
  · apply Fintype.sum_ite_eq
  trans ((self.D vn vu (stdBasisMatrix k () 1)) * (stdBasisMatrix l () (1 : R))ᵀ) i j
  · by_cases hjl : j = l
    · simp [hjl, Matrix.mul_apply]
    · simp [hjl, mt Eq.symm hjl, Matrix.mul_apply]

  rw [add_comm, ← sub_eq_iff_eq_add]
  apply Eq.symm
  trans ∑ x : m, if l = x then
      if i = k then self.D vm vu (stdBasisMatrix j () 1) x () else 0
    else 0
  · congr; ext x
    rw [stdBasis_apply]
    simp
    by_cases hlx : l = x
    · simp [hlx, MatrixDerivationFamily.toGeneratorFamily, MatrixDerivationFamily.generatorOf]
    · simp [hlx, mt Eq.symm hlx]
  trans if i = k then self.D vm vu (stdBasisMatrix j () 1) l () else 0
  · apply Fintype.sum_ite_eq

  rw [show stdBasisMatrix k l (1 : R) = (stdBasisMatrix k () (1 : R)) * (stdBasisMatrix l () (1 : R))ᵀ by simp]
  rw [self.product_rule vn vu vm]
  simp
  rw [self.generatorOfRow]
  by_cases hik : i = k
  · simp [hik, MatrixDerivationFamily.generatorOf]
  · simp [hik]

/-- The "one-step rotation" permutation matrix on `Fin n`. -/
def rotationMatrix
  (R : Type) [CommRing R]
  (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)]
: Matrix (Fin n) (Fin n) R :=
  fun i j => if n > 1 then if j = (i.val + 1) % n then 1 else 0 else 0

#eval @rotationMatrix ℚ _ 0 _ _
#eval @rotationMatrix ℚ _ 1 _ _
#eval @rotationMatrix ℚ _ 2 _ _
#eval @rotationMatrix ℚ _ 3 _ _

-- set_option pp.all true
-- set_option pp.notation false

def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

/-- A family of generators indexed by “being equal to `Fin n`”. -/
def rotateGenFamily (R : Type) [CommRing R] {ValidIndex : Type → Prop}
  (h : ∀ α, ValidIndex α → Σ (n : ℕ), α → Fin n) :
  GeneratorFamily R ValidIndex where
  G {α} _ _ vα := by
    obtain ⟨n, f⟩ := h α vα
    exact fun i j => rotationMatrix R n (f i) (f j)

def ValidShape : Type → Prop
| Unit
| Fin 3 => True

asd
