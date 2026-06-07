import Mathlib

/-!
# Sokoban in Lean 4
Mirrors the GDL rulesheet: same cell types, same move logic, same level.
-/


/-──────────────────────────────────────────────────────────
  Types
──────────────────────────────────────────────────────────-/

inductive Cell | empty | wall | player | box | target
  deriving DecidableEq, Repr, Inhabited

inductive Dir | up | down | left | right
  deriving DecidableEq, Repr

structure Config where
  width : Nat
  height : Nat


-- This should be converted into a property of the level like Pos m n
structure Pos (cfg : Config) where
  col : Fin cfg.width
  row : Fin cfg.height
  deriving DecidableEq

abbrev Board (cfg : Config) := Pos cfg → Cell

structure State where
  cfg : Config
  board : Board cfg


/-──────────────────────────────────────────────────────────
  Adjacency  (mirrors inc / dec in GDL)
──────────────────────────────────────────────────────────-/

def adj {cfg : Config} (p : Pos cfg) : Dir → Option (Pos cfg)
  | .up => -- Decrement row
    if p.row.val = 0 then none else
    some ⟨p.col, ⟨p.row.val - 1, by omega⟩⟩
  | .down => -- Increment row
    if h : p.row.val + 1 < cfg.height
    then some ⟨p.col, ⟨p.row.val + 1, h⟩⟩
    else none
  | .left => -- Decrement row
    if p.col.val = 0 then none else
    some ⟨⟨p.col.val - 1, by omega⟩, p.row⟩
  | .right => -- Increment row
    if h : p.col.val + 1 < cfg.width
    then some ⟨⟨p.col.val + 1, h⟩, p.row⟩
    else none

/-──────────────────────────────────────────────────────────
  Board update
──────────────────────────────────────────────────────────-/

-- TODO this feels inefficient
def Board.update {cfg : Config} (b : Board cfg) (p : Pos cfg) (c : Cell) : Board cfg :=
  fun q => if q == p then c else b q

@[simp] theorem Board.update_eq {cfg : Config} (b : Board cfg) (p : Pos cfg) (c : Cell) :
    (b.update p c) p = c := by simp [Board.update]

@[simp] theorem Board.update_ne {cfg : Config} (b : Board cfg) (p q : Pos cfg) (c : Cell) (h : q ≠ p) :
    (b.update p c) q = b q := by simp [Board.update, h]

/-──────────────────────────────────────────────────────────
  Step function (mirrors GDL operations)
──────────────────────────────────────────────────────────-/

def step_actor {cfg : Config}
  (b : Board cfg) (actor : Pos cfg) (d : Dir)
: Option (Board cfg) :=
  if b actor = .player then
    match adj actor d with
    | none   => none
    | some p =>
      match b p with
      | .empty =>
          some (b
            |>.update actor .empty
            |>.update p .player
          )
      | .box   =>
          match adj p d with
          | none   => none
          | some q =>
            match b q with
            | .empty  => some (b
                |>.update actor .empty
                |>.update p .player
                |>.update q .box
            )
            | .target => some (b
              |>.update actor .empty
              |>.update p .player
              |>.update q .empty
            )
            | _       => none
      | _      => none
  else none

/-──────────────────────────────────────────────────────────
  Legal predicate  (mirrors GDL legal rules)
──────────────────────────────────────────────────────────-/

-- def legal (s : State) (actor : Pos) (d : Dir) : Prop :=
--   s.board actor = .player ∧
--   match adj actor d with
--   | none   => False
--   | some n =>
--     s.board n = .empty ∨
--     (s.board n = .box ∧
--       match adj n d with
--       | none   => False
--       | some m => s.board m = .empty ∨ s.board m = .target)

-- -- step succeeds iff the move is legal
-- theorem step_some_iff_legal (s : State) (actor : Pos) (d : Dir) :
--     (∃ s', step s actor d = some s') ↔ legal s actor d := by
--   simp only [step, legal]
--   constructor
--   · intro ⟨s', h⟩
--     split at h <;> simp_all
--     split at h <;> simp_all
--     split at h <;> simp_all
--     split at h <;> simp_all
--   · intro ⟨hpl, hdir⟩
--     split <;> simp_all
--     split at hdir <;> simp_all
--     rcases hdir with hempty | ⟨hbox, hpush⟩
--     · simp [hempty]
--     · simp [hbox]
--       split at hpush <;> simp_all
--       rcases hpush with h | h <;> simp [h]

/-──────────────────────────────────────────────────────────
  Goal / Terminal
──────────────────────────────────────────────────────────-/

def hasTarget (s : State) : Prop := ∃ p, s.board p = .target

def solved (s : State) : Prop := ¬ hasTarget s

-- Decidable instance: check all 165 board positions
-- TODO fix this
instance  {s : State} : Decidable (hasTarget s) := sorry
  -- if h : ∃ p : Pos s.cfg, s.board p = .target then isTrue h else isFalse h

/-──────────────────────────────────────────────────────────
  Invariants
──────────────────────────────────────────────────────────-/

-- Walls are never modified
theorem walls_preserved {cfg : Config}
  {b b' : Board cfg} {actor : Pos cfg} {d : Dir}
  (hstep : some b' = step_actor b actor d)
  {p : Pos cfg} (hwall : b p = .wall)
: b' p = .wall := by
  simp only [step_actor] at hstep
  split at hstep
  · rename_i hactor
    have npa : p ≠ actor := by
      intro hpa
      rw [hpa, hactor] at hwall
      contradiction
    split at hstep
    · contradiction
    · rename_i q hq
      split at hstep
      · rename_i hbq
        have npq : p ≠ q := by
          intro hpq
          rw [← hpq, hwall] at hbq
          contradiction
        simp at hstep
        simp [hstep, Board.update, npq, npa]
        assumption
      · rename_i hbq
        have npq : p ≠ q := by
          intro hpq
          rw [← hpq, hwall] at hbq
          contradiction
        split at hstep
        · contradiction
        · rename_i r hr
          split at hstep
          · rename_i hbr
            have npr : p ≠ r := by
              intro hpr
              rw [← hpr, hwall] at hbr
              contradiction
            simp at hstep
            simp [hstep, Board.update, npr, npq, npa]
            assumption
          · rename_i hbr
            have npr : p ≠ r := by
              intro hpr
              rw [← hpr, hwall] at hbr
              contradiction
            simp at hstep
            simp [hstep, Board.update, npr, npq, npa]
            assumption
          · contradiction
      · contradiction
  · contradiction

-- Step only touches at most three positions; everything else is a frame
theorem step_frame {cfg : Config}
  {b b' : Board cfg} {actor : Pos cfg} {d : Dir}
  (hstep : some b' = step_actor b actor d) {p : Pos cfg}
  (npa : p ≠ actor)
  (npq : ∀ q, adj actor d = some q → p ≠ q)
  (npr : ∀ q r, adj actor d = some q → adj q d = some r → p ≠ r)
: b' p = b p := by
  simp only [step_actor] at hstep
  split at hstep
  · rename_i hba
    split at hstep
    · contradiction
    · rename_i q hq
      split at hstep
      · rename_i hbq
        simp at hstep
        simp [hstep, Board.update, npq q hq]
        intro hpa
        exact (npa hpa).elim
      · rename_i hbq
        split at hstep
        · contradiction
        · rename_i r hr
          split at hstep
          repeat first
          | contradiction
          | simp at hstep
            simp [hstep, Board.update, npr q r hq hr, npq q hq, npa]
      · contradiction
  · contradiction

theorem infer_actor {cfg : Config} {b b' : Board cfg} {actor : Pos cfg} {d : Dir}
  (hstep : some b' = step_actor b actor d)
: b actor = .player := by
  simp only [step_actor] at hstep
  split at hstep
  · assumption
  · contradiction

-- Uniqueness of player is preserved
theorem unique_player_preserved
  {cfg : Config} {b b' : Board cfg} {actor : Pos cfg} {d : Dir}
  (hstep : some b' = step_actor b actor d)
  (huniq : ∀ p, b p = .player → p = actor)
: ∀ p', b' p' = .player → some p' = adj actor d := by
  simp only [step_actor] at hstep
  split at hstep
  · rename_i hba
    intro p hb'p
    split at hstep
    · contradiction
    · rename_i q hq
      simp [hq]
      split at hstep
      · rename_i hbq
        simp at hstep
        simp [hstep, Board.update] at hb'p
        by_cases hpq : p = q
        · assumption
        · simp [hpq] at hb'p
          by_cases hpa : p = actor
          · simp [hpa] at hb'p
          · simp [hpa] at hb'p
            have H := huniq p hb'p
            contradiction
      · rename_i hbq
        split at hstep
        · contradiction
        · rename_i r hr
          split at hstep
          · rename_i hbr
            simp at hstep
            simp [hstep, Board.update] at hb'p
            by_cases hpq : p = q
            · assumption
            · simp [hpq] at hb'p
              by_cases hpr : p = r
              · simp [hpr] at hb'p
              · simp [hpr] at hb'p
                by_cases hpa : p = actor
                · simp [hpa] at hb'p
                · simp [hpa] at hb'p
                  have H := huniq p hb'p
                  contradiction
          · rename_i hbq
            simp at hstep
            simp [hstep, Board.update] at hb'p
            by_cases hpq : p = q
            · assumption
            · simp [hpq] at hb'p
              by_cases hpr : p = r
              · simp [hpr] at hb'p
              · simp [hpr] at hb'p
                by_cases hpa : p = actor
                · simp [hpa] at hb'p
                · simp [hpa] at hb'p
                  have H := huniq p hb'p
                  contradiction
          · contradiction
      · contradiction
  · contradiction

instance {cfg : Config} : Fintype (Pos cfg) :=
  Fintype.ofEquiv (Fin cfg.width × Fin cfg.height)
    { toFun := fun ⟨c, r⟩ => ⟨c, r⟩
      invFun := fun p => ⟨p.col, p.row⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def count {cfg : Config} (b : Board cfg) (c : Cell) : Nat :=
  (Finset.univ : Finset (Pos cfg)).filter (fun p => b p = c) |>.card

-- Updating a position that wasn't .player to a non-.player value doesn't change the count
private lemma count_player_update_ne {cfg : Config} (b : Board cfg)
    (r : Pos cfg) (c : Cell) (h1 : b r ≠ .player) (h2 : c ≠ .player) :
    count (b.update r c) .player = count b .player := by
  simp only [count]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Board.update, beq_iff_eq]
  by_cases hpr : p = r
  · subst hpr; constructor <;> intro h <;> simp_all
  · simp [hpr]

-- Moving the player from `actor` to any non-player `q` preserves the count
-- (bijection: q↦actor, everything else is identity on the player-filter)
private lemma count_player_of_move {cfg : Config} {b : Board cfg}
    {actor q : Pos cfg}
    (hba : b actor = .player) (hbq : b q ≠ .player) :
    count (b.update actor .empty |>.update q .player) .player = count b .player := by
  simp only [count]
  refine Finset.card_bij (fun x _ => if x = q then actor else x) ?_ ?_ ?_
  · -- maps filter(b') into filter(b)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    split_ifs with h
    · subst h; exact hba
    · have hxa : x ≠ actor := by
        intro e; subst e
        simp [Board.update] at hx
        contradiction
      simp [Board.update, h, hxa] at hx; exact hx
  · -- injective
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    by_cases h1 : x₁ = q <;> by_cases h2 : x₂ = q <;> simp_all
  · -- surjective: actor's preimage is q; everything else maps to itself
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    by_cases haa : a = actor
    · exact ⟨q, by simp [Finset.mem_filter, Board.update], by simp [haa]⟩
    · have haq' : a ≠ q := by intro e; subst e; exact hbq ha
      exact ⟨a, by simp [Finset.mem_filter, Board.update, haq', haa, ha], by simp [haq']⟩


theorem count_player_preserved
  {cfg : Config} {b b' : Board cfg} {actor : Pos cfg} {d : Dir}
  (hstep : some b' = step_actor b actor d)
  {n : Nat} (count_player : count b .player = n)
: count b' .player = n := by
  rw [← count_player]
  simp only [step_actor] at hstep
  split at hstep
  · rename_i hba
    split at hstep
    · contradiction
    · rename_i q hq
      split at hstep
      · rename_i hbq
        simp at hstep; subst hstep
        exact count_player_of_move hba (by simp [hbq])
      · rename_i hbq
        split at hstep
        · contradiction
        · rename_i r hr
          split at hstep
          · rename_i hbr
            simp at hstep; subst hstep
            have hrq : r ≠ q := fun e => by subst e; rw [hbr] at hbq; simp at hbq
            have hra : r ≠ actor := fun e => by subst e; rw [hbr] at hba; simp at hba
            rw [count_player_update_ne (b.update actor .empty |>.update q .player) r .box
              (by simp [Board.update, hrq, hra, hbr]) (by simp)]
            exact count_player_of_move hba (by simp [hbq])
          · rename_i hbr
            simp at hstep; subst hstep
            have hrq : r ≠ q := fun e => by subst e; rw [hbr] at hbq; simp at hbq
            have hra : r ≠ actor := fun e => by subst e; rw [hbr] at hba; simp at hba
            rw [count_player_update_ne (b.update actor .empty |>.update q .player) r .empty
              (by simp [Board.update, hrq, hra, hbr]) (by simp)]
            exact count_player_of_move hba (by simp [hbq])
          · contradiction
      · contradiction
  · contradiction

-- How a single Board.update changes the count of any target cell (as an Int equation)
private lemma count_update_int {cfg : Config} (b : Board cfg)
    (pos : Pos cfg) (c target : Cell) :
    (count (b.update pos c) target : Int) =
    count b target + (if c = target then 1 else 0) - (if b pos = target then 1 else 0) := by
  simp only [count]
  rcases Decidable.em (c = target) with hc | hc <;> rcases Decidable.em (b pos = target) with hb | hb
  · have : Finset.univ.filter (fun x : Pos cfg => (b.update pos target) x = target) =
           Finset.univ.filter (fun x : Pos cfg => b x = target) := by
      ext x; simp [Finset.mem_filter, Board.update, beq_iff_eq]
      by_cases h : x = pos <;> simp [h, hb, ← hc]
    simp [hc, hb, this]
  · simp [hc]
    rw [show Finset.univ.filter (fun x : Pos cfg => (b.update pos target) x = target) =
          insert pos (Finset.univ.filter (fun x : Pos cfg => b x = target)) from by
      ext x; simp [Finset.mem_filter, Finset.mem_insert, Board.update, beq_iff_eq, hc]
      by_cases h : x = pos <;> simp [h, hb],
      Finset.card_insert_of_notMem (by simp [hb])]
    simp [hb]
  · rw [show Finset.univ.filter (fun x : Pos cfg => b x = target) =
          insert pos (Finset.univ.filter (fun x : Pos cfg => (b.update pos c) x = target)) from by
      ext x; simp [Finset.mem_filter, Finset.mem_insert, Board.update, beq_iff_eq]
      by_cases h : x = pos <;> simp [h, hb, hc],
      Finset.card_insert_of_notMem (by simp [Board.update, hc])]
    simp [hb, hc]
  · have : Finset.univ.filter (fun x : Pos cfg => (b.update pos c) x = target) =
           Finset.univ.filter (fun x : Pos cfg => b x = target) := by
      ext x; simp [Finset.mem_filter, Board.update, beq_iff_eq]
      by_cases h : x = pos <;> simp [h, hb, hc]
    simp [hc, hb, this]

theorem count_target_box_preserved
  {cfg : Config} {b b' : Board cfg} {actor : Pos cfg} {d : Dir}
  (hstep : some b' = step_actor b actor d)
  {n : Int} (count_target_boxs : (count b .target : Int) - count b .box = n)
: (count b' .target : Int) - count b' .box = n := by
  rw [← count_target_boxs]
  simp only [step_actor] at hstep
  split at hstep
  · rename_i hba
    split at hstep
    · contradiction
    · rename_i p hp
      split at hstep
      · rename_i hbp
        simp at hstep; subst hstep
        have hap : actor ≠ p := by intro e; subst e; simp at hba hbp
        have ep : (b.update actor .empty) p = b p := by simp [hap.symm]
        have e1t := count_update_int b actor .empty .target
        have e1bx := count_update_int b actor .empty .box
        have e2t := count_update_int (b.update actor .empty) p .player .target
        have e2bx := count_update_int (b.update actor .empty) p .player .box
        simp (config := { decide := true }) [hba, hbp, ep] at e1t e1bx e2t e2bx
        push_cast at e1t e1bx e2t e2bx ⊢; linarith
      · rename_i hbp
        split at hstep
        · contradiction
        · rename_i q hq
          split at hstep
          · rename_i hbq
            simp at hstep; subst hstep
            have hap : actor ≠ p := by intro e; subst e; simp at hba hbp
            have haq : actor ≠ q := by intro e; subst e; simp at hba hbq
            have hpq : p ≠ q := by intro e; subst e; simp at hbp hbq
            have ep : (b.update actor .empty) p = b p := by simp [hap.symm]
            have eq' : (b.update actor .empty |>.update p .player) q = b q := by simp [hpq.symm, haq.symm]
            have e1t := count_update_int b actor .empty .target
            have e1bx := count_update_int b actor .empty .box
            have e2t := count_update_int (b.update actor .empty) p .player .target
            have e2bx := count_update_int (b.update actor .empty) p .player .box
            have e3t := count_update_int (b.update actor .empty |>.update p .player) q .box .target
            have e3bx := count_update_int (b.update actor .empty |>.update p .player) q .box .box
            simp (config := { decide := true }) [hba, hbp, hbq, ep, eq'] at e1t e1bx e2t e2bx e3t e3bx
            push_cast at e1t e1bx e2t e2bx e3t e3bx ⊢; linarith
          · rename_i hbq
            -- push box to target: box -1, target -1 → difference preserved
            simp at hstep; subst hstep
            have hap : actor ≠ p := by intro e; subst e; simp at hba hbp
            have haq : actor ≠ q := by intro e; subst e; simp at hba hbq
            have hpq : p ≠ q := by intro e; subst e; simp at hbp hbq
            have ep : (b.update actor .empty) p = b p := by simp [hap.symm]
            have eq' : (b.update actor .empty |>.update p .player) q = b q := by simp [hpq.symm, haq.symm]
            have e1t := count_update_int b actor .empty .target
            have e1bx := count_update_int b actor .empty .box
            have e2t := count_update_int (b.update actor .empty) p .player .target
            have e2bx := count_update_int (b.update actor .empty) p .player .box
            have e3t := count_update_int (b.update actor .empty |>.update p .player) q .empty .target
            have e3bx := count_update_int (b.update actor .empty |>.update p .player) q .empty .box
            simp (config := { decide := true }) [hba, hbp, hbq, ep, eq'] at e1t e1bx e2t e2bx e3t e3bx
            push_cast at e1t e1bx e2t e2bx e3t e3bx ⊢; linarith
          · contradiction
      · contradiction
  · contradiction

/-──────────────────────────────────────────────────────────
  Multi-step execution
──────────────────────────────────────────────────────────-/

def execMoves {cfg : Config} (b : Board cfg) : List (Pos cfg × Dir) → Option (Board cfg)
  | []            => some b
  | (p, d) :: ms  => (step_actor b p d) >>= fun b' => execMoves b' ms

structure Strategy where
  cfg : Config
  state_t : Type
  init_state_t : Board cfg -> state_t
  policy : (s : state_t, b : Board cfg) -> (state_t, Board cfg)

-- execMoves preserves walls
theorem execMoves_walls_preserved {cfg : Config} {init : State} (moves : List (Pos × Dir))
    {s : State} (hexec : execMoves init moves = some s)
    {p : Pos} (hwall : init.board p = .wall) :
    s.board p = .wall := by
  induction moves generalizing init with
  | nil  => simp [execMoves] at hexec; subst hexec; exact hwall
  | cons hd tl ih =>
    simp [execMoves, Option.bind] at hexec
    obtain ⟨s', hstep, hexec'⟩ := hexec
    exact ih hexec' (walls_preserved hstep hwall)

/-──────────────────────────────────────────────────────────
  Initial board  (matches GDL init facts)

    col:  1 2 3 4 5 6
    row 1: # # # # # #
    row 2: # O . . O #    O = target
    row 3: # . . . . #
    row 4: # . 0 0 . #    0 = box
    row 5: # . . @ . #    @ = player
    row 6: # # # # # #
──────────────────────────────────────────────────────────-/

def initBoard : Board := fun p =>
  match p.col.val, p.row.val with
  | 1,1|2,1|3,1|4,1|5,1|6,1 => .wall
  | 1,2                      => .wall
  | 2,2                      => .target
  | 3,2|4,2                  => .empty
  | 5,2                      => .target
  | 6,2                      => .wall
  | 1,3|6,3                  => .wall
  | 2,3|3,3|4,3|5,3          => .empty
  | 1,4                      => .wall
  | 2,4                      => .empty
  | 3,4                      => .box
  | 4,4                      => .box
  | 5,4                      => .empty
  | 6,4                      => .wall
  | 1,5                      => .wall
  | 2,5|3,5                  => .empty
  | 4,5                      => .player
  | 5,5                      => .empty
  | 6,5                      => .wall
  | 1,6|2,6|3,6|4,6|5,6|6,6 => .wall
  | _,_                      => .empty

def initState : State := { board := initBoard }

/-──────────────────────────────────────────────────────────
  Position helper
──────────────────────────────────────────────────────────-/

def mkPos (c r : Nat) (hc : c < 15 := by decide) (hr : r < 11 := by decide) : Pos :=
  ⟨⟨c, hc⟩, ⟨r, hr⟩⟩

/-──────────────────────────────────────────────────────────
  Solution for the sample level  (15 moves)

  Trace:
    1  move  (4,5)→left   → player@(3,5)
    2  shove (3,5)→up     → player@(3,4), box(3,4)→(3,3)
    3  shove (3,4)→up     → player@(3,3), box(3,3)→(3,2)
    4  move  (3,3)→right  → player@(4,3)
    5  move  (4,3)→up     → player@(4,2)
    6  dest  (4,2)→left   → player@(3,2), box(3,2)+target(2,2) removed
    7  move  (3,2)→down   → player@(3,3)
    8  move  (3,3)→down   → player@(3,4)
    9  move  (3,4)→down   → player@(3,5)
    10 move  (3,5)→right  → player@(4,5)
    11 shove (4,5)→up     → player@(4,4), box(4,4)→(4,3)
    12 shove (4,4)→up     → player@(4,3), box(4,3)→(4,2)
    13 move  (4,3)→left   → player@(3,3)
    14 move  (3,3)→up     → player@(3,2)
    15 dest  (3,2)→right  → player@(4,2), box(4,2)+target(5,2) removed  ✓
──────────────────────────────────────────────────────────-/

def solution : List (Pos × Dir) := [
  (mkPos 4 5, .left),
  (mkPos 3 5, .up),
  (mkPos 3 4, .up),
  (mkPos 3 3, .right),
  (mkPos 4 3, .up),
  (mkPos 4 2, .left),
  (mkPos 3 2, .down),
  (mkPos 3 3, .down),
  (mkPos 3 4, .down),
  (mkPos 3 5, .right),
  (mkPos 4 5, .up),
  (mkPos 4 4, .up),
  (mkPos 4 3, .left),
  (mkPos 3 3, .up),
  (mkPos 3 2, .right)
]

/-──────────────────────────────────────────────────────────
  Verification helpers
──────────────────────────────────────────────────────────-/

def isSolved (s : State) : Bool :=
  (List.range 15).all fun c =>
  (List.range 11).all fun r =>
  match (c, r) with
  | (c, r) =>
    if hc : c < 15 then if hr : r < 11 then
      s.board ⟨⟨c, hc⟩, ⟨r, hr⟩⟩ != .target
    else true else true

def showBoard (s : State) : String :=
  "\n" ++ String.join ((List.range 8).map fun r =>
    (String.join ((List.range 8).map fun c =>
      if hc : c < 15 then if hr : r < 11 then
        match s.board ⟨⟨c, hc⟩, ⟨r, hr⟩⟩ with
        | .wall   => "#" | .empty  => "." | .player => "@"
        | .box    => "$" | .target => "O"
      else "" else "") ++ "\n"))

/-──────────────────────────────────────────────────────────
  Computational verification

  Run with:   lean --run sokoban.lean
  Or in VSCode: evaluate the #eval lines
──────────────────────────────────────────────────────────-/

#eval showBoard initState
-- Expected:
--   ######
--   #O..O#
--   #....#
--   #.00.#
--   #..@.#
--   ######

#eval do
  let finalState ← execMoves initState solution
  return (isSolved finalState, showBoard finalState)
-- Expected: (true, board with no targets or boxes)

/-──────────────────────────────────────────────────────────
  Reachability theorem  (follows from the verified solution)
──────────────────────────────────────────────────────────-/

theorem sample_level_reachable : ∃ s, execMoves initState solution = some s ∧ solved s := by
  native_decide
