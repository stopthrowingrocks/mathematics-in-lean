import Mathlib

structure Config where
  stars : Nat
  size  : Nat
  hsize : size > 0

structure Pos (cfg : Config) where
  col : Fin cfg.size
  row : Fin cfg.size
  deriving DecidableEq

instance {cfg : Config} : Fintype (Pos cfg) :=
  Fintype.ofEquiv (Fin cfg.size × Fin cfg.size)
    ⟨fun ⟨c, r⟩ => ⟨c, r⟩, fun p => ⟨p.col, p.row⟩, fun _ => rfl, fun _ => rfl⟩

inductive Cell | star | elim
  deriving BEq, DecidableEq, Repr

@[simp] lemma Cell.star_beq_star : (Cell.star == Cell.star) = true  := rfl
@[simp] lemma Cell.star_beq_elim : (Cell.star == Cell.elim) = false := rfl
@[simp] lemma Cell.elim_beq_star : (Cell.elim == Cell.star) = false := rfl
@[simp] lemma Cell.elim_beq_elim : (Cell.elim == Cell.elim) = true  := rfl

abbrev Puzzle   (cfg : Config) := Pos cfg → Fin cfg.size
abbrev Solution (cfg : Config) := Pos cfg → Cell

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

structure PuzzleConstraints (cfg : Config) (puz : Puzzle cfg) (sl : Solution cfg) : Prop where
  rowCount   : ∀ i : Fin cfg.size,
      ((Array.ofFn (fun j : Fin cfg.size => Pos.mk j i)).toList.filter (fun p => sl p == .star)).length = cfg.stars
  colCount   : ∀ i : Fin cfg.size,
      ((Array.ofFn (fun j : Fin cfg.size => Pos.mk i j)).toList.filter (fun p => sl p == .star)).length = cfg.stars
  shapeCount : ∀ s : Fin cfg.size,
      (((getPositions cfg).filter (fun p => puz p == s)).filter (fun p => sl p == .star)).length = cfg.stars
  adj        : ∀ {p : Pos cfg} (_ : sl p = .star), ∀ n ∈ neighbors p, sl n = .elim

@[simp] private lemma filter_star_cons_elim {cfg : Config} {sl : Solution cfg}
    {p : Pos cfg} {l : List (Pos cfg)}
    (h : sl p = .elim) :
    (p :: l).filter (fun q => sl q == .star) = l.filter (fun q => sl q == .star) := by
  simp [h]

@[simp] private lemma filter_star_cons_star {cfg : Config} {sl : Solution cfg}
    {p : Pos cfg} {l : List (Pos cfg)}
    (h : sl p = .star) :
    (p :: l).filter (fun q => sl q == .star) = p :: l.filter (fun q => sl q == .star) := by
  simp [h]

@[simp] private lemma filter_star_cons_elim_length {cfg : Config} {sl : Solution cfg}
    {p : Pos cfg} {l : List (Pos cfg)}
    (h : sl p = .elim) :
    ((p :: l).filter (fun q => sl q == .star)).length = (l.filter (fun q => sl q == .star)).length := by
  simp [h]

@[simp] private lemma filter_star_cons_star_length {cfg : Config} {sl : Solution cfg}
    {p : Pos cfg} {l : List (Pos cfg)}
    (h : sl p = .star) :
    ((p :: l).filter (fun q => sl q == .star)).length = (l.filter (fun q => sl q == .star)).length+1 := by
  simp [h]


-------------------------------------------
--- EXAMPLE SECTION
-------------------------------------------

abbrev exampleConfig : Config := { stars := 1, size := 4, hsize := by omega }

def examplePuzzle : Puzzle exampleConfig := fun pos =>
  let grid : Fin 4 → Fin 4 → Fin 4 := ![
    ![0, 0, 1, 1],
    ![2, 0, 0, 1],
    ![2, 2, 0, 3],
    ![2, 2, 3, 3]
  ]
  grid pos.row pos.col

private abbrev epos (c r : Fin 4) : Pos exampleConfig := ⟨c, r⟩

lemma Cell.ne_elim_iff {c : Cell} : c ≠ .elim ↔ c = .star := by cases c <;> simp

-------------------------------------------
--- UNIQUENESS PROOF
-------------------------------------------

@[simp]
private def exampleShapes : Fin 4 → List (Pos exampleConfig)
  | 0 => [epos 0 0, epos 1 0, epos 1 1, epos 2 1, epos 2 2]
  | 1 => [epos 2 0, epos 3 0, epos 3 1]
  | 2 => [epos 0 1, epos 0 2, epos 1 2, epos 0 3, epos 1 3]
  | 3 => [epos 3 2, epos 2 3, epos 3 3]

private lemma exampleShapes_spec (s : Fin 4) :
    (getPositions exampleConfig).filter (fun p => examplePuzzle p == s) = exampleShapes s := by
  fin_cases s <;> native_decide

theorem exampleUnique : ∃! sl : Solution exampleConfig,
    PuzzleConstraints exampleConfig examplePuzzle sl := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun p =>
      let grid : Fin 4 → Fin 4 → Cell := ![
        ![.elim, .star, .elim, .elim],
        ![.elim, .elim, .elim, .star],
        ![.star, .elim, .elim, .elim],
        ![.elim, .elim, .star, .elim]
      ]
      grid p.row p.col
  · constructor <;> native_decide -- existence
  · intro sl h
    have h_shape : ∀ s : Fin 4,
        (exampleShapes s |>.filter (fun p => sl p == .star)).length = 1 :=
      fun s => exampleShapes_spec s ▸ h.shapeCount s

    -- Step 1: (2,2) must be elim
    have h_22_elim : sl (epos 2 2) = .elim := by
      by_contra h_ne
      have h_nbrs := h.adj (Cell.ne_elim_iff.mp h_ne)
      have hsubset : exampleShapes 3 ⊆ neighbors (epos 2 2) := by native_decide
      have h_shape3 := h_shape 3
      simp [fun p hp => h_nbrs p (hsubset hp)] at h_shape3
    have h_21_elim : sl (epos 2 1) = .elim := by
      by_contra h_ne
      have h_nbrs := h.adj (Cell.ne_elim_iff.mp h_ne)
      have hsubset : exampleShapes 1 ⊆ neighbors (epos 2 1) := by native_decide
      have h_shape1 := h_shape 1
      simp [fun p hp => h_nbrs p (hsubset hp)] at h_shape1
    have h_20_elim : sl (epos 2 0) = .elim := by
      by_contra h_ne
      have h_20_star := Cell.ne_elim_iff.mp h_ne
      have h_nbrs := h.adj h_20_star
      have h_10_elim : sl (epos 1 0) = .elim := h_nbrs _ (by native_decide)
      have h_11_elim : sl (epos 1 1) = .elim := h_nbrs _ (by native_decide)
      have h_00_elim : sl (epos 0 0) = .elim := by
        have HHH := h.rowCount 0
        have : (Array.ofFn (fun j : Fin 4 => Pos.mk j (0 : Fin 4))).toList =
          [epos 0 0, epos 1 0, epos 2 0, epos 3 0] := by native_decide

        simp [h_10_elim] at HHH
        sorry
      -- Shape 0 has all positions .elim except (0,0), so (0,0) must be .star
      have h_00_star : sl (epos 0 0) = .star := by
        by_contra h_00_ne
        -- have h_00_elim : sl (epos 0 0) = .elim := by
        --   cases h : sl (epos 0 0)
        --   · exact absurd h h_00_ne
        --   ·
        have h_shape0 := h_shape 0
        have hne : ∀ p ∈ exampleShapes 0, sl p = .elim := fun p hp => by
          simp only [exampleShapes, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl
          · exact h_00_elim
          · exact h_10_elim
          · exact h_11_elim
          · exact h_21_elim
          · exact h_22_elim
        simp [exampleShapes, hne] at h_shape0
      -- Row 0 now has stars at (0,0) and (2,0), contradicting colCount 0 = 1
      have h_30_elim : sl (epos 3 0) = .elim := h_nbrs _ (by native_decide)
      have h_col0 : (Array.ofFn (fun j : Fin 4 => Pos.mk j (0 : Fin 4))).toList =
          [epos 0 0, epos 1 0, epos 2 0, epos 3 0] := by native_decide
      have h_row0 := h.colCount 0
      rw [h_col0] at h_row0
      simp [show ∀ p ∈ [epos 0 0, epos 1 0, epos 2 0, epos 3 0],
                sl p = if p = epos 0 0 ∨ p = epos 2 0 then .star else .elim from fun p hp => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl <;> simp [h_00_star, h_10_elim, h_20_star, h_30_elim]
           ] at h_row0
    sorry
