import Mathlib

def PosNat := { n : Nat // n > 0 }

structure Config where
  stars : Nat
  size : Nat
  hsize : size > 0

structure Pos (cfg : Config) where
  col: Fin cfg.size
  row: Fin cfg.size
  deriving DecidableEq

inductive Cell | star | elim
  deriving BEq, DecidableEq

@[simp] lemma Cell.star_beq_star : (Cell.star == Cell.star) = true := rfl
@[simp] lemma Cell.star_beq_elim : (Cell.star == Cell.elim) = false := rfl
@[simp] lemma Cell.elim_beq_star : (Cell.elim == Cell.star) = false := rfl
@[simp] lemma Cell.elim_beq_elim : (Cell.elim == Cell.elim) = true := rfl

inductive Constraint (cfg : Config)
  | star: Pos cfg -> Constraint cfg
  | elim: Pos cfg -> Constraint cfg
  | count: Nat -> List (Pos cfg) -> Constraint cfg
  | or: List (Constraint cfg) -> Constraint cfg
  | and: List (Constraint cfg) -> Constraint cfg
  | not: Constraint cfg -> Constraint cfg
  | False
  | True

-- A Puzzle is a binding between cells and shape numbers. Every cell has a unique shape number
-- and every shape number should be inhabited by at least one cell but you know what if it's not
-- then oh well
-- There should be at most cfg.stars shapes
abbrev Puzzle (cfg : Config) := Pos cfg -> Fin cfg.size
def getPositions (cfg : Config) : List (Pos cfg) :=
  (Array.ofFn (fun i : Fin (cfg.size * cfg.size) => ⟨
    ⟨i % cfg.size, Nat.mod_lt ↑i cfg.hsize⟩,
    ⟨i / cfg.size, Nat.div_lt_of_lt_mul i.isLt⟩
  ⟩)).toList

def neighbors {cfg : Config} (p : Pos cfg) : List (Pos cfg) :=
  let offsets : List (Int × Int) := [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]
  offsets.filterMap fun (dc, dr) =>
    let c := (p.col.val : Int) + dc
    let r := (p.row.val : Int) + dr
    if h : 0 ≤ c ∧ c < cfg.size ∧ 0 ≤ r ∧ r < cfg.size
    then some ⟨⟨c.toNat, by omega⟩, ⟨r.toNat, by omega⟩⟩
    else none

-- Puzzle -> Constraint
def makeConstraint {cfg : Config} (puz : Puzzle cfg) : Constraint cfg :=
  Constraint.and ((
    Array.ofFn (fun i : Fin cfg.size =>
      Constraint.count cfg.stars (
        (Array.ofFn (fun j : Fin cfg.size => (Pos.mk i j))).toList
      )
    ) ++
    Array.ofFn (fun i : Fin cfg.size =>
      Constraint.count cfg.stars (
        (Array.ofFn (fun j : Fin cfg.size => (Pos.mk j i))).toList
      )
    ) ++
    Array.ofFn (fun shapeID : Fin cfg.size =>
      Constraint.count cfg.stars (
        (getPositions cfg).filter (fun pos => puz pos == shapeID)
      )
    )
  ).toList ++
  (getPositions cfg).map (fun p =>
    Constraint.or [.elim p, Constraint.and (.star p :: (neighbors p).map .elim)]
  ))

abbrev Solution (cfg : Config) := Pos cfg -> Cell
-- solves Solution Constraint
def solves {cfg : Config} (sl : Solution cfg) : Constraint cfg -> Bool
  | .star p => sl p == .star
  | .elim p => sl p == .elim
  | .count count ps => (ps.filter (fun p => sl p == .star)).length == count
  | .or [] => false
  | .or (c :: cs) => solves sl c || solves sl (.or cs)
  | .and [] => true
  | .and (c :: cs) => solves sl c && solves sl (.and cs)
  | .not c => !solves sl c
  | .True => true
  | .False => false


-- A reduction maps a subset of Constraint cfg to a different Constraint cfg and attaches
-- a proof that the same kinds of solutions apply to both
-- This proof will take the form forall sl : Solution cfg => solves sl c1 == solves sl c2 which is a Prop
def constraintEquiv {cfg : Config} (c1 c2 : Constraint cfg) : Prop :=
  ∀ sl : Solution cfg, solves sl c1 = solves sl c2

instance {cfg : Config} : Setoid (Constraint cfg) where
  r := constraintEquiv
  iseqv := {
    refl  := fun _ _ => rfl
    symm  := fun h sl => (h sl).symm
    trans := fun h1 h2 sl => (h1 sl).trans (h2 sl)
  }

structure Transformation (cfg : Config) where
  map : Constraint cfg -> Constraint cfg
  equiv : ∀ c : Constraint cfg, constraintEquiv c (map c)

def removeOrFalse {cfg : Config} : Transformation cfg where
  map
    | .or cs => .or (cs.filter (fun
      | .False => false
      | _ => true
    ))
    | c => c
  equiv c sl := by
    symm
    match c with
    | .or cs =>
      induction cs with
      | nil => simp [solves]
      | cons head tail ih =>
        simp [List.filter, solves]
        split
        · simp [solves, ih]
        · next heq =>
          have : head = .False := by
            split at heq <;> simp_all
          simp [this, solves]
          assumption
    | .star _ | .elim _ | .count _ _ | .and _ | .not _ | .True | .False =>
      simp

def noop {cfg : Config} : Transformation cfg where
  map a := a
  equiv c := by simp [constraintEquiv]

def notsingle {cfg : Config} : Transformation cfg where
  map
    | .not (.star p) => .elim p
    | .not (.elim p) => .star p
    | c => c
  equiv c sl := by
    symm
    cases c with
    | not inner =>
      cases inner with
      | star p => simp [solves]; cases sl p <;> rfl
      | elim p => simp [solves]; cases sl p <;> rfl
      | _ => rfl
    | _ => rfl

-- private def liftOrBranch {cfg : Config} (branch : Constraint cfg) (outer : List (Constraint cfg)) : Constraint cfg :=
--   match branch with
--   | .and innerCs => .and (innerCs ++ outer)
--   | _ => .and (branch :: outer)

-- private def liftOrInList {cfg : Config} : List (Constraint cfg) → List (Constraint cfg) → Constraint cfg
--   | acc, [] => .and acc.reverse
--   | acc, .or branches :: rest =>
--     .or (branches.map (liftOrBranch · (acc.reverse ++ rest)))
--   | acc, c :: rest => liftOrInList (c :: acc) rest

-- def liftOr {cfg : Config} : Transformation cfg where
--   map
--     | .and cs => liftOrInList [] cs
--     | c => c
--   equiv c := by sorry

def split {cfg : Config} (p : Pos cfg) : Transformation cfg where
  map c := .or [.and [.star p, c], .and [.elim p, c]]
  equiv c sl := by symm; cases h : sl p <;> simp [solves, h]

-------------------------------------------
--- EXAMPLE SECTION
-------------------------------------------

abbrev exampleConfig : Config := { stars := 1, size := 4, hsize := by omega }

def examplePuzzle : Puzzle exampleConfig := fun pos =>
  let grid : Fin 4 → Fin 4 → Fin 4 := ![
    ![0, 0, 1, 1],
    ![0, 0, 0, 1],
    ![2, 2, 0, 3],
    ![2, 2, 3, 3]
  ]
  grid pos.row pos.col

-- Convenient position constructor: epos col row
private def epos (c r : Fin 4) : Pos exampleConfig := ⟨c, r⟩

-------------------------------------------
--- UNIQUENESS PROOF
-------------------------------------------

theorem exampleUnique : ∃! sl : Solution exampleConfig,
    solves sl (makeConstraint examplePuzzle) = true := by
  refine ⟨sorry, ?_, ?_⟩
  · sorry -- existence: native_decide once solution is defined
  · intro sl h
    -- Step 1: (col=2, row=2) must be elim
    have h_22_elim : sl (epos 2 2) = .elim := by
      by_contra h_ne
      have h_22_star : sl (epos 2 2) = .star := by
        cases h_val : sl (epos 2 2) <;> simp_all
      -- Row 2 already has its 1 star at (2,2), so (3,2) must be elim
      have h_32_elim : sl (epos 3 2) = .elim := sorry
      -- Col 2 already has its 1 star at (2,2), so (2,3) must be elim
      have h_23_elim : sl (epos 2 3) = .elim := sorry
      -- Adjacency: (2,2) is star so diagonal neighbor (3,3) must be elim
      have h_33_elim : sl (epos 3 3) = .elim := sorry
      -- Shape 3 = {(3,2),(2,3),(3,3)}, all elim, but needs exactly 1 star
      have h_shape3 : solves sl (Constraint.count 1 [epos 3 2, epos 2 3, epos 3 3]) = true := sorry
      simp [solves, h_32_elim, h_23_elim, h_33_elim] at h_shape3
    -- ... continue pinning down remaining positions ...
    sorry
