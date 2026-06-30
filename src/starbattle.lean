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

instance : LawfulBEq Cell where
  eq_of_beq {a b} h := by cases a <;> cases b <;> revert h <;> decide
  rfl {a} := by cases a <;> rfl

abbrev Puzzle   (cfg : Config) := Pos cfg → Fin cfg.size
abbrev Solution (cfg : Config) := Pos cfg → Cell

def neighbors {cfg : Config} (p : Pos cfg) : List (Pos cfg) :=
  let offsets : List (Int × Int) := [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]
  offsets.filterMap fun (dc, dr) =>
    let c := (p.col.val : Int) + dc
    let r := (p.row.val : Int) + dr
    if h : 0 ≤ c ∧ c < cfg.size ∧ 0 ≤ r ∧ r < cfg.size
    then some ⟨⟨c.toNat, by omega⟩, ⟨r.toNat, by omega⟩⟩
    else none

structure PuzzleConstraints {cfg : Config} (puz : Puzzle cfg) (sl : Solution cfg) : Prop where
  rowCount   : ∀ i : Fin cfg.size,
      ∑ j : Fin cfg.size, (if sl (Pos.mk j i) = .star then 1 else 0) = cfg.stars
  colCount   : ∀ i : Fin cfg.size,
      ∑ j : Fin cfg.size, (if sl (Pos.mk i j) = .star then 1 else 0) = cfg.stars
  shapeCount : ∀ s : Fin cfg.size,
      ∑ p : Pos cfg, (if puz p = s ∧ sl p = .star then 1 else 0) = cfg.stars
  adj        : ∀ {p : Pos cfg} (_ : sl p = .star), ∀ n ∈ neighbors p, sl n = .elim


-----------------------
--- LEMMAS
-----------------------

lemma Cell.ne_elim_iff {c : Cell} : c ≠ .elim ↔ c = .star := by cases c <;> simp
lemma Cell.ne_star_iff {c : Cell} : c ≠ .star ↔ c = .elim := by cases c <;> simp

/-- Expand a sum over `Fin 10` into ten summands with literal `Fin 10` indices.
    Mathlib only ships `Fin.sum_univ_*` up to eight; unlike `Fin.sum_univ_succ`, this
    keeps the indices as clean `(i : Fin 10)` literals (no leftover `9 + 1` sizes), so
    the resulting `Pos.mk i j` atoms match hand-written `⟨i, j⟩` cells for `omega`. -/
theorem Fin.sum_univ_ten {M : Type*} [AddCommMonoid M] (f : Fin 10 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- Expand a sum over all positions of a board into a double sum over the two
    coordinates, so `Fin.sum_univ_*` can then enumerate it. The region predicate in
    `shapeCount` prunes the irrelevant cells once the puzzle is concrete. -/
lemma Pos.sum_univ {cfg : Config} {M : Type*} [AddCommMonoid M] (f : Pos cfg → M) :
    ∑ p, f p = ∑ c : Fin cfg.size, ∑ r : Fin cfg.size, f ⟨c, r⟩ :=
  calc ∑ p, f p
      = ∑ x : Fin cfg.size × Fin cfg.size, f ⟨x.1, x.2⟩ :=
        Fintype.sum_equiv
          ⟨fun p => (p.col, p.row), fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩
          f (fun x => f ⟨x.1, x.2⟩) (fun _ => rfl)
    _ = ∑ c : Fin cfg.size, ∑ r : Fin cfg.size, f ⟨c, r⟩ := Fintype.sum_prod_type _

/-- Restrict a `shapeCount` sum (over the whole board) to a sum over just the region's
    cells. `region` is the explicit cell-list of shape `s`; both side goals
    (`region` is duplicate-free, and it is exactly the shape-`s` cells) are closed by
    `decide`/`native_decide`. This avoids ever expanding all `size²` board cells. -/
lemma shapeCount_region {cfg : Config} {puz : Puzzle cfg} {sl : Solution cfg}
    {s : Fin cfg.size} (region : List (Pos cfg)) (hnd : region.Nodup)
    (hmem : ∀ p, puz p = s ↔ p ∈ region) :
    (∑ p : Pos cfg, if puz p = s ∧ sl p = .star then 1 else 0)
      = (region.map (fun p => if sl p = .star then 1 else 0)).sum := by
  have key : (Finset.univ.filter fun p => puz p = s) = region.toFinset := by
    ext p; simp [hmem p]
  calc (∑ p : Pos cfg, if puz p = s ∧ sl p = .star then 1 else 0)
      = ∑ p, if puz p = s then (if sl p = .star then 1 else 0) else 0 :=
        Finset.sum_congr rfl fun p _ => by by_cases hp : puz p = s <;> simp [hp]
    _ = ∑ p ∈ Finset.univ.filter fun p => puz p = s, if sl p = .star then 1 else 0 := by
        rw [← Finset.sum_filter]
    _ = ∑ p ∈ region.toFinset, if sl p = .star then 1 else 0 := by rw [key]
    _ = (region.map (fun p => if sl p = .star then 1 else 0)).sum :=
        List.sum_toFinset _ hnd

/-- If a cell's `if … = .star then 1 else 0` tally is `0`, the cell is `.elim`.
    This discharges the per-cell goal left after expanding a line sum with
    `Fin.sum_univ_*` and isolating one summand with `omega`. -/
lemma Cell.eq_elim_of_ite_zero {c : Cell} (h : (if c = .star then 1 else 0) = 0) : c = .elim := by
  cases c <;> simp_all

/-- Dual of `eq_elim_of_ite_zero`: if a cell's tally is `1`, the cell is `.star`. -/
lemma Cell.eq_star_of_ite_one {c : Cell} (h : (if c = .star then 1 else 0) = 1) : c = .star := by
  cases c <;> simp_all

/-- An `if … = .star then 1 else 0` tally never exceeds one. This is the upper bound
    `omega` lacks (it abstracts each `if` as an opaque `≥ 0`): feed one per summand and
    `omega` can conclude every term is `1` when a line's star count is saturated. -/
lemma Cell.ite_star_le_one (c : Cell) : (if c = .star then 1 else 0) ≤ 1 := by
  cases c <;> simp

/-- A two-cell tally of `2`: both cells are stars (the saturated two-cell case). -/
lemma Cell.ite_pair_eq_two {a b : Cell}
    (h : (if a = .star then 1 else 0) + (if b = .star then 1 else 0) = 2) :
    a = .star ∧ b = .star := by
  cases a <;> cases b <;> simp_all

-----------------------
--- TACTICS
-----------------------

open Lean Meta Elab Tactic in
/-- Drop one summand `t` from a `+`-tree `e`, returning the tree without it. -/
private partial def removeSummand (t e : Expr) : MetaM (Option Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    if ← isDefEq a t then return some b
    else if ← isDefEq b t then return some a
    else if let some a' ← removeSummand t a then return some (← mkAppM ``HAdd.hAdd #[a', b])
    else if let some b' ← removeSummand t b then return some (← mkAppM ``HAdd.hAdd #[a, b'])
    else return none
  | _ => return none

open Lean Meta Elab Tactic in
/-- `sub_summand h using e` rewrites `h : S = n` by dropping a summand of the `+`-sum `S`:

    * if `e : ℕ` is the summand `t` itself, `h` becomes `S' = n - t`;
    * if `e : t = k` is a *proof* that the summand equals `k`, `h` becomes `S' = n - k`
      (the value `k` is subtracted instead of the symbolic term).

    `S'` is `S` with that summand removed; the result is discharged by `omega` (which also
    uses the supplied equation when `e` is a proof). For a summand whose value is known,
    passing the `= k` proof gives the cleaner `n - k`. -/
elab "sub_summand " hId:ident " using " eStx:term : tactic => do
  let (lhsStx, rhsStx) ← (← getMainGoal).withContext do
    let e ← elabTerm eStx none
    -- `e : t = k` ⇒ remove `t`, subtract `k`; otherwise `e` is the summand, subtract `e`.
    let (t, k) :=
      match (← instantiateMVars (← inferType e)).eq? with
      | some (_, t, k) => (t, k)
      | none => (e, e)
    let hLocal ← getLocalDeclFromUserName hId.getId
    let some (_, lhs, rhs) := (← instantiateMVars hLocal.type).eq?
      | throwError "hypothesis {hId} is not an equality"
    let some lhs' ← removeSummand t lhs
      | throwError "summand not found in the left-hand sum"
    return (← PrettyPrinter.delab lhs', ← PrettyPrinter.delab (← mkAppM ``HSub.hSub #[rhs, k]))
  evalTactic (← `(tactic| replace $hId : $lhsStx = $rhsStx := by omega))

open Lean Meta Elab Tactic in
/-- Flatten a `+`-tree into the list of its leaf summands. -/
private partial def collectSummands (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => collectSummands a ++ collectSummands b
  | _ => #[e]

open Lean Meta Elab Tactic in
/-- Given proof `e : t₁ + … + tₙ = k` and an equality `lhs = rhs`, return delaborated
    syntax for `lhs` with each `tᵢ` removed, and for `rhs - k`. -/
private def subsumPieces (eStx : Term) (lhs rhs : Expr) : TacticM (Term × Term) := do
  (← getMainGoal).withContext do
    let e ← elabTerm eStx none
    let some (_, t, k) := (← instantiateMVars (← inferType e)).eq?
      | throwError "the argument must prove `t₁ + … + tₙ = k`"
    let mut cur := lhs
    for ti in collectSummands t do
      let some cur' ← removeSummand ti cur
        | throwError "summand {← ppExpr ti} not found in the sum"
      cur := cur'
    let lhs' ← mkAppM ``HAdd.hAdd #[cur, k]
    return (← PrettyPrinter.delab lhs',
        ← PrettyPrinter.delab rhs)

/-- `subsum ht`, where `ht : t₁ + … + tₙ = k`, drops each `tᵢ` from a `+`-sum and
    subtracts `k` from the total:

    * `subsum ht at h` turns `h : S = n` into `h : S' = n - k`;
    * `subsum ht` turns a goal `S = n` into `S' = n - k`.

    `S'` is `S` with each `tᵢ` removed; the bridge is discharged by `omega` (which uses
    `ht`, so pass a hypothesis name). -/
syntax "subsum " term (" at " ident)? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| subsum $e:term at $hId:ident) => do
    let hType ← (← getMainGoal).withContext do
      instantiateMVars (← getLocalDeclFromUserName hId.getId).type
    let some (_, lhs, rhs) := hType.eq? | throwError "hypothesis {hId} is not an equality"
    let (lhsStx, rhsStx) ← subsumPieces e lhs rhs
    evalTactic (← `(tactic| replace $hId : $lhsStx = $rhsStx := by omega))
  | `(tactic| subsum $e:term) => do
    let some (_, lhs, rhs) := (← getMainTarget).eq? | throwError "goal is not an equality"
    let (lhsStx, rhsStx) ← subsumPieces e lhs rhs
    evalTactic (← `(tactic| suffices hsubsum : $lhsStx = $rhsStx by omega))

open Lean Meta Elab Tactic in
/-- Like `subsumPieces`, but silently skips any `tᵢ` not present in `lhs` (so removed
    terms are a *subset* of the `tᵢ`), returning `(cur + k, rhs)`. -/
private def subsumLeqPieces (eStx : Term) (lhs rhs : Expr) : TacticM (Term × Term) := do
  (← getMainGoal).withContext do
    let e ← elabTerm eStx none
    let some (_, t, k) := (← instantiateMVars (← inferType e)).eq?
      | throwError "the argument must prove `t₁ + … + tₙ = k`"
    let mut cur := lhs
    for ti in collectSummands t do
      if let some cur' ← removeSummand ti cur then
        cur := cur'
    return (← PrettyPrinter.delab (← mkAppM ``HAdd.hAdd #[cur, k]), ← PrettyPrinter.delab rhs)

/-- `subsum_leq ht at h`, where `ht : t₁ + … + tₙ = k`, removes from `h : S = n` each `tᵢ`
    that *occurs* in `S` (silently skipping any `tᵢ` absent from `S`) and replaces `h` with
    the inequality `S' + k ≥ n`. Unlike `subsum` (which needs every `tᵢ` present and yields
    an equality), this stays sound when only some of the `tᵢ` are in the line. `omega`. -/
syntax "subsum_leq " term " at " ident : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| subsum_leq $e:term at $hId:ident) => do
    let hType ← (← getMainGoal).withContext do
      instantiateMVars (← getLocalDeclFromUserName hId.getId).type
    let some (_, lhs, rhs) := hType.eq? | throwError "hypothesis {hId} is not an equality"
    let (lhsStx, rhsStx) ← subsumLeqPieces e lhs rhs
    evalTactic (← `(tactic| replace $hId : $lhsStx ≥ $rhsStx := by omega))

open Lean Meta in
/-- Extract the condition `p` from a summand `if p then 1 else 0` (unfolding reducibly). -/
private def iteCond? (e : Expr) : MetaM (Option Expr) := do
  match (← whnfR e).getAppFnArgs with
  | (``ite, #[_, p, _, _, _]) => return some p
  | _ => return none

/-- All length-`n` boolean masks with exactly `k` `true`s (the `n choose k` subsets). -/
private partial def chooseMasks : Nat → Nat → List (List Bool)
  | 0,    0    => [[]]
  | 0,    _+1  => []
  | n+1,  0    => (chooseMasks n 0).map (false :: ·)
  | n+1,  k+1  => (chooseMasks n k).map (true :: ·) ++ (chooseMasks n (k+1)).map (false :: ·)

open Lean Meta in
/-- Right-associated fold of binary `op` over `xs`, returning `unit` when empty. -/
private def foldBin (op : Name) (unit : Expr) : List Expr → MetaM Expr
  | []      => pure unit
  | [x]     => pure x
  | x :: xs => do mkAppM op #[x, ← foldBin op unit xs]

/-- A `0/1` indicator is at most one — the upper bound `omega` needs. -/
lemma ite_one_le {p : Prop} [Decidable p] : (if p then (1:ℕ) else 0) ≤ 1 := by split <;> simp
/-- `if p then 1 else 0 = 1 ↔ p` — converts an arithmetic disjunct back to the proposition. -/
lemma ite_one_eq_one_iff {p : Prop} [Decidable p] : (if p then (1:ℕ) else 0) = 1 ↔ p := by
  split <;> simp_all
/-- `if p then 1 else 0 = 0 ↔ ¬p`. -/
lemma ite_one_eq_zero_iff {p : Prop} [Decidable p] : (if p then (1:ℕ) else 0) = 0 ↔ ¬p := by
  split <;> simp_all

open Lean Meta Elab Tactic in
/-- `expand_count h`, where `h : (if p₁ then 1 else 0) + … + (if pₙ then 1 else 0) = k`,
    replaces `h` with the `n choose k` disjunction: one disjunct per way of choosing which
    `k` of the `pᵢ` hold (the rest negated). Generalizes the `Cell.ite_pair_eq_*` lemmas.

    The disjunction is proved in arithmetic form (`termᵢ = 1`/`= 0`) by a single `omega`
    (fed a `≤ 1` bound per summand), then converted to `pᵢ`/`¬pᵢ` form. So it scales to
    large `n` for *extreme* `k` (`0, 1, n-1, n`, where the disjunction stays small); the
    middle `k` are still combinatorially large in the output regardless. -/
elab "expand_count " hId:ident : tactic => do
  let (DpropStx, DarithStx, termStxs) ← (← getMainGoal).withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← getLocalDeclFromUserName hId.getId).type).eq?
      | throwError "hypothesis {hId} is not an equality"
    let some k := (← whnf rhs).nat?
      | throwError "the right-hand side must be a numeral"
    let terms := (collectSummands lhs).toList
    let conds ← terms.mapM fun s => do
      let some p ← iteCond? s | throwError "a summand is not an `if _ then 1 else 0`"
      pure p
    let masks := chooseMasks conds.length k
    let Dprop ← foldBin ``Or (mkConst ``False) (← masks.mapM fun m => do
      foldBin ``And (mkConst ``True) (← (conds.zip m).mapM fun (p, b) =>
        if b then pure p else mkAppM ``Not #[p]))
    let Darith ← foldBin ``Or (mkConst ``False) (← masks.mapM fun m => do
      foldBin ``And (mkConst ``True) (← (terms.zip m).mapM fun (t, b) =>
        mkAppM ``Eq #[t, mkNatLit (if b then 1 else 0)]))
    return (← PrettyPrinter.delab Dprop, ← PrettyPrinter.delab Darith,
            ← terms.mapM fun t => do pure (← PrettyPrinter.delab t))
  for tStx in termStxs do
    evalTactic (← `(tactic| have : $tStx ≤ 1 := ite_one_le))
  evalTactic (← `(tactic| have hexpand : $DarithStx := by omega))
  evalTactic (← `(tactic|
    replace $hId : $DpropStx := by
      simpa only [ite_one_eq_one_iff, ite_one_eq_zero_iff] using hexpand))
  evalTactic (← `(tactic| clear hexpand))

-------------------------------------------
--- TINY PUZZLE
-------------------------------------------

abbrev tinyConfig : Config := { stars := 1, size := 4, hsize := by omega }

def tinyPuzzle : Puzzle tinyConfig := fun pos =>
  let grid : Fin 4 → Fin 4 → Fin 4 := ![
    ![0, 0, 1, 1],
    ![2, 0, 0, 1],
    ![2, 2, 0, 3],
    ![2, 2, 3, 3]
  ]
  grid pos.row pos.col

theorem tinyProof : ∃! sl : Solution tinyConfig,
    PuzzleConstraints tinyPuzzle sl := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun p =>
      let grid : Fin 4 → Fin 4 → Cell := ![
        ![.elim, .star, .elim, .elim],
        ![.elim, .elim, .elim, .star],
        ![.star, .elim, .elim, .elim],
        ![.elim, .elim, .star, .elim]
      ]
      grid p.row p.col
  · constructor <;> native_decide
  · intro sl h
    have h_22_elim : sl ⟨2, 2⟩ = .elim := by
      by_contra h_ne
      have h_nbrs := h.adj (Cell.ne_elim_iff.mp h_ne)
      have h_shape3 := h.shapeCount 3
      simp only [Pos.sum_univ, Fin.sum_univ_four] at h_shape3
      simp (config := { decide := true }) [h_nbrs] at h_shape3
    have h_21_elim : sl ⟨2, 1⟩ = .elim := by
      by_contra h_ne
      have h_nbrs := h.adj (Cell.ne_elim_iff.mp h_ne)
      have h_shape1 := h.shapeCount 1
      simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape1
      simp (config := { decide := true }) [h_nbrs] at h_shape1
    have h_20_elim : sl ⟨2, 0⟩ = .elim := by
      by_contra h_ne
      have h_20_star := Cell.ne_elim_iff.mp h_ne
      have h_nbrs := h.adj h_20_star
      have h_00_elim : sl ⟨0, 0⟩ = .elim := by
        have h_row0 := h.rowCount 0
        simp only [Fin.sum_univ_four] at h_row0
        simp (config := { decide := true }) [h_20_star, h_nbrs] at h_row0
        exact Cell.ne_star_iff.mp h_row0
      have h_shape0 := h.shapeCount 0
      simp only [Pos.sum_univ, Fin.sum_univ_four] at h_shape0
      simp (config := { decide := true }) [h_00_elim, h_21_elim, h_22_elim, h_nbrs] at h_shape0
    have h_23_star : sl ⟨2, 3⟩ = .star := by
      have h_col2 := h.colCount 2
      simp only [Fin.sum_univ_four] at h_col2
      simp (config := { decide := true }) [h_22_elim, h_21_elim, h_20_elim] at h_col2
      exact h_col2
    have h_02_star : sl ⟨0, 2⟩ = .star := by
      have h_row2 := h.rowCount 2
      simp only [Fin.sum_univ_four] at h_row2
      simp (config := { decide := true }) [h.adj h_23_star] at h_row2
      exact h_row2
    have h_31_star : sl ⟨3, 1⟩ = .star := by
      have h_row1 := h.rowCount 1
      simp only [Fin.sum_univ_four] at h_row1
      simp (config := { decide := true }) [h_21_elim, h.adj h_02_star] at h_row1
      exact h_row1
    have h_10_star : sl ⟨1, 0⟩ = .star := by
      have h_col1 := h.colCount 1
      simp only [Fin.sum_univ_four] at h_col1
      simp (config := { decide := true }) [h.adj h_02_star] at h_col1
      exact h_col1
    funext ⟨c, r⟩
    fin_cases c <;> fin_cases r <;> simp (config := { decide := true }) [
      h_10_star, h.adj h_10_star,
      h_31_star, h.adj h_31_star,
      h_02_star, h.adj h_02_star,
      h_23_star, h.adj h_23_star
    ]

-------------------------------------------
--- HARD PUZZLE
-------------------------------------------

abbrev hardConfig : Config := { stars := 2, size := 10, hsize := by omega }

def hardPuzzle : Puzzle hardConfig := fun pos =>
  let grid : Fin 10 → Fin 10 → Fin 10 := ![
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1],
    ![2, 0, 0, 0, 0, 0, 1, 1, 3, 3],
    ![2, 2, 0, 0, 0, 0, 4, 1, 3, 3],
    ![2, 5, 5, 0, 0, 0, 4, 4, 3, 3],
    ![2, 5, 5, 5, 5, 5, 4, 6, 6, 3],
    ![2, 2, 2, 5, 5, 6, 6, 6, 6, 6],
    ![7, 7, 7, 5, 5, 6, 6, 6, 6, 6],
    ![7, 8, 8, 5, 5, 6, 6, 6, 6, 6],
    ![7, 8, 8, 8, 8, 8, 6, 9, 9, 6],
    ![8, 8, 8, 8, 8, 8, 8, 9, 9, 9]
  ]
  grid pos.row pos.col


set_option maxHeartbeats 400000
theorem hardProof : ∃! sl : Solution hardConfig,
    PuzzleConstraints hardPuzzle sl := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun p =>
      let grid : Fin 10 → Fin 10 → Cell := ![
        ![.elim, .elim, .elim, .elim, .elim, .star, .elim, .star, .elim, .elim],
        ![.elim, .elim, .elim, .star, .elim, .elim, .elim, .elim, .elim, .star],
        ![.elim, .star, .elim, .elim, .elim, .elim, .star, .elim, .elim, .elim],
        ![.elim, .elim, .elim, .elim, .star, .elim, .elim, .elim, .star, .elim],
        ![.elim, .elim, .star, .elim, .elim, .elim, .star, .elim, .elim, .elim],
        ![.star, .elim, .elim, .elim, .star, .elim, .elim, .elim, .elim, .elim],
        ![.elim, .elim, .star, .elim, .elim, .elim, .elim, .elim, .star, .elim],
        ![.star, .elim, .elim, .elim, .elim, .star, .elim, .elim, .elim, .elim],
        ![.elim, .elim, .elim, .star, .elim, .elim, .elim, .star, .elim, .elim],
        ![.elim, .star, .elim, .elim, .elim, .elim, .elim, .elim, .elim, .star]
      ]
      grid p.row p.col
  · constructor <;> native_decide
  · intro sl h
    have h_shape9 := h.shapeCount 9
    simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape9
    have h_89_elim : sl ⟨8, 9⟩ = .elim := by
      by_contra h_ne
      have h_89_star := Cell.ne_elim_iff.mp h_ne
      have h_shape9 := h.shapeCount 9
      simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape9
      simp (config := { decide := true }) [h_89_star, h.adj h_89_star] at h_shape9
    have h_88_elim : sl ⟨8, 8⟩ = .elim := by
      by_contra h_ne
      have h_88_star := Cell.ne_elim_iff.mp h_ne
      simp (config := { decide := true }) [h_88_star, h.adj h_88_star] at h_shape9
    have h_99_star : sl ⟨9, 9⟩ = .star := by
      by_cases h_99 : sl ⟨9, 9⟩ = .star
      · assumption
      · simp (config := { decide := true }) [h_89_elim, h_88_elim, h_99] at h_shape9
        -- region 9's two stars would have to be ⟨7,8⟩ and ⟨7,9⟩
        obtain ⟨h_78_star, h_79_star⟩ := Cell.ite_pair_eq_two h_shape9
        -- but they are vertically adjacent
        simp [h.adj h_78_star ⟨7, 9⟩ (by decide)] at h_79_star
    have h_98_elim := h.adj h_99_star ⟨9, 8⟩ (by decide)

    simp (config := { decide := true }) [h_99_star, h_88_elim, h_89_elim] at h_shape9
    have h_shape4 := h.shapeCount 4
    rw [shapeCount_region [⟨6,2⟩, ⟨6,3⟩, ⟨7,3⟩, ⟨6,4⟩] (by decide) (by native_decide)] at h_shape4
    have h_63_elim : sl ⟨6, 3⟩ = .elim := by
      by_contra h_ne
      have h_63_star := Cell.ne_elim_iff.mp h_ne
      simp (config := { decide := true }) [h_63_star, h.adj h_63_star] at h_shape4
    have h_73_elim : sl ⟨7, 3⟩ = .elim := by
      by_contra h_ne
      have h_73_star := Cell.ne_elim_iff.mp h_ne
      simp (config := { decide := true }) [h_73_star, h.adj h_73_star] at h_shape4
    simp [h_63_elim, h_73_elim] at h_shape4
    have ⟨h_62_star, h_64_star⟩ : sl ⟨6, 2⟩ = .star ∧ sl ⟨6, 4⟩ = .star := by
      have hb_62 := Cell.ite_star_le_one (sl ⟨6, 2⟩)
      have hb_64 := Cell.ite_star_le_one (sl ⟨6, 4⟩)
      constructor <;> exact Cell.eq_star_of_ite_one (by omega)
    have h_51_elim := h.adj h_62_star ⟨5, 1⟩ (by decide)
    have h_52_elim := h.adj h_62_star ⟨5, 2⟩ (by decide)
    have h_53_elim := h.adj h_62_star ⟨5, 3⟩ (by decide)
    have h_72_elim := h.adj h_62_star ⟨7, 2⟩ (by decide)
    have h_71_elim := h.adj h_62_star ⟨7, 1⟩ (by decide)
    have h_61_elim := h.adj h_62_star ⟨6, 1⟩ (by decide)
    have h_74_elim := h.adj h_64_star ⟨7, 4⟩ (by decide)
    have h_75_elim := h.adj h_64_star ⟨7, 5⟩ (by decide)
    have h_65_elim := h.adj h_64_star ⟨6, 5⟩ (by decide)
    have h_55_elim := h.adj h_64_star ⟨5, 5⟩ (by decide)
    have h_54_elim := h.adj h_64_star ⟨5, 4⟩ (by decide)
    clear h_shape4

    have h_col6 := h.colCount 6
    simp only [Fin.sum_univ_ten] at h_col6
    simp (config := { decide := true }) [h_62_star, h_64_star] at h_col6
    have h_60_elim : sl ⟨6, 0⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_66_elim : sl ⟨6, 6⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_67_elim : sl ⟨6, 7⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_68_elim : sl ⟨6, 8⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_69_elim : sl ⟨6, 9⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    clear h_col6

    have h_shape1 := h.shapeCount 1
    simp only [Pos.sum_univ, Fin.sum_univ_ten] at h_shape1
    simp (config := {decide := true}) only [h.adj h_62_star] at h_shape1
    simp at h_shape1
    have h_row0 := h.rowCount 0
    simp only [Fin.sum_univ_ten] at h_row0
    simp [← h_shape1, Cell.ne_star_iff, and_assoc] at h_row0
    obtain ⟨h_00_elim, h_10_elim, h_20_elim, h_30_elim, h_40_elim⟩ := h_row0
    have h_81_elim : sl ⟨8, 1⟩ = .elim := by
      by_contra h_ne
      have h_81_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) only [h.adj h_81_star, h_60_elim] at h_shape1
      by_cases h_50 : sl ⟨5, 0⟩ = .star <;> simp [h_50] at h_shape1

    have h_shape7 := h.shapeCount 7
    simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape7
    simp (config := {decide := true}) at h_shape7
    have h_shape2 := h.shapeCount 2
    simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape2
    simp (config := {decide := true}) at h_shape2
    have h_col0 := h.colCount 0
    simp only [Fin.sum_univ_ten] at h_col0
    -- simp (config := { decide := true }) at h_col0
    have h_17_elim : sl ⟨1, 7⟩ = .elim := by
      by_contra h_ne
      have h_17_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_17_star] at h_shape7
    have h_15_elim : sl ⟨1, 5⟩ = .elim := by
      by_contra h_ne
      have h_15_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_15_star] at h_shape7
      obtain ⟨h_07_star, h_08_star⟩ := Cell.ite_pair_eq_two h_shape7
      simp [h.adj h_07_star ⟨0, 8⟩ (by decide)] at h_08_star
    have h_col1 := h.colCount 1
    simp only [Fin.sum_univ_ten] at h_col1
    simp (config := { decide := true }) [h_10_elim, h_15_elim, h_17_elim] at h_col1

    have hn_shape7_col0 : (if sl ⟨0, 6⟩ = .star then 1 else 0) + (if sl ⟨0, 8⟩ = .star then 1 else 0) ≠ 2 := by
      intro h_ne
      obtain ⟨h_06_star, h_08_star⟩ := Cell.ite_pair_eq_two h_ne
      subsum h_ne at h_col0
      have h_col0_elims : (if sl ⟨0, 1⟩ = .star then 1 else 0) + (if sl ⟨0, 2⟩ = .star then 1 else 0) + (if sl ⟨0, 3⟩ = .star then 1 else 0) + (if sl ⟨0, 4⟩ = .star then 1 else 0) + (if sl ⟨0, 5⟩ = .star then 1 else 0) = 0 := by omega
      subsum h_col0_elims at h_shape2
      simp [h_15_elim] at h_shape2
      obtain ⟨h_12_star, h_25_star⟩ := Cell.ite_pair_eq_two h_shape2
      simp (config := { decide := true }) [h_12_star, h.adj h_12_star, h.adj h_25_star, h.adj h_08_star] at h_col1
    have h_27_elim : sl ⟨2, 7⟩ = .elim := by
      by_contra h_ne
      have h_27_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_27_star] at h_shape7
      have h_07_elim : sl ⟨0, 7⟩ = .elim := by
        by_contra h_ne
        have h_07_star := Cell.ne_elim_iff.mp h_ne
        simp (config := {decide := true}) [h_07_star, h.adj h_07_star] at h_shape7
      simp [h_07_elim] at h_shape7
      exact hn_shape7_col0 h_shape7
    have h_shape7_col0 : (if sl ⟨0, 6⟩ = .star then 1 else 0) + (if sl ⟨0, 7⟩ = .star then 1 else 0) + (if sl ⟨0, 8⟩ = .star then 1 else 0) = 1 := by
      have neq_0 : (if sl ⟨0, 6⟩ = .star then 1 else 0) + (if sl ⟨0, 7⟩ = .star then 1 else 0) + (if sl ⟨0, 8⟩ = .star then 1 else 0) ≠ 0 := by
        intro h_e
        simp at h_e
        simp (config := { decide := true }) [h_e] at h_shape7
        obtain ⟨h_16_star, h_26_star⟩ := Cell.ite_pair_eq_two h_shape7
        simp [h.adj h_16_star ⟨2, 6⟩ (by decide)] at h_26_star
      by_cases h_07 : sl ⟨0, 7⟩ = .star
      · simp (config := { decide := true }) [h_07, h.adj h_07]
      · simp [h_07]
        have h7 : (if sl ⟨0, 7⟩ = .star then 1 else 0) = 0 := by simp [h_07]
        simp only [h7, add_zero] at neq_0
        have b6 := Cell.ite_star_le_one (sl ⟨0, 6⟩)
        have b8 := Cell.ite_star_le_one (sl ⟨0, 8⟩)
        omega
    clear hn_shape7_col0
    have h_shape7_row6 : (if sl ⟨1, 6⟩ = .star then 1 else 0) + (if sl ⟨2, 6⟩ = .star then 1 else 0) = 1 := by
      subsum h_shape7_col0 at h_shape7
      exact Eq.symm ((fun {a b} ↦ Nat.succ_inj.mp) (id (Eq.symm h_shape7)))
    have h_25_elim : sl ⟨2, 5⟩ = .elim := by
      by_contra h_ne
      have h_25_star : sl ⟨2, 5⟩ = .star := by exact Cell.ne_elim_iff.mp h_ne -- For some reason if we remove the `by exact` it kinda fucks things up a little bit like you can comment out the line below and it still seems to compile
      simp (config := { decide := true }) [h.adj h_25_star] at h_shape7_row6
    have h_12_star : sl ⟨1, 2⟩ = .star := by
      by_contra h_ne
      have h_12_elim := Cell.ne_star_iff.mp h_ne
      subsum h_shape7_col0 at h_col0
      simp [h_12_elim, h_15_elim, h_25_elim] at h_shape2
      subsum h_shape2 at h_col0
      omega
    have h_01_elim := h.adj h_12_star ⟨0, 1⟩ (by decide)
    have h_02_elim := h.adj h_12_star ⟨0, 2⟩ (by decide)
    have h_03_elim := h.adj h_12_star ⟨0, 3⟩ (by decide)
    have h_13_elim := h.adj h_12_star ⟨1, 3⟩ (by decide)
    have h_23_elim := h.adj h_12_star ⟨2, 3⟩ (by decide)
    have h_22_elim := h.adj h_12_star ⟨2, 2⟩ (by decide)
    have h_21_elim := h.adj h_12_star ⟨2, 1⟩ (by decide)
    have h_11_elim := h.adj h_12_star ⟨1, 1⟩ (by decide)
    simp [h_00_elim, h_01_elim, h_02_elim, h_03_elim] at h_col0
    simp [h_12_star, h_01_elim, h_02_elim, h_03_elim, h_15_elim, h_25_elim] at h_shape2
    subsum h_shape2 at h_col0
    subsum h_shape7_col0 at h_col0
    simp at h_col0
    have h_09_elim : sl ⟨0, 9⟩ = .elim := Cell.ne_star_iff.mp h_col0
    clear h_col0
    have h_14_elim : sl ⟨1, 4⟩ = .elim := by
      by_contra h_ne
      have h_14_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_14_star] at h_shape2

    have h_row2 := h.rowCount 2
    simp only [Fin.sum_univ_ten] at h_row2
    simp (config := {decide := true}) [h_02_elim, h_12_star, h_22_elim, h_52_elim, h_62_star, h_72_elim] at h_row2
    have h_32_elim : sl ⟨3, 2⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_42_elim : sl ⟨4, 2⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_82_elim : sl ⟨8, 2⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_92_elim : sl ⟨9, 2⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    clear h_row2

    have h_shape3 := h.shapeCount 3
    simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape3
    simp (config := {decide := true}) [h_81_elim, h_82_elim, h_92_elim] at h_shape3
    have h_col9 := h.colCount 9
    simp only [Fin.sum_univ_ten] at h_col9
    simp (config := {decide := true}) [h_99_star, h.adj h_99_star, h_92_elim] at h_col9
    have h_shape3_col9 : (if sl ⟨9, 1⟩ = .star then 1 else 0) +
      (if sl ⟨9, 3⟩ = .star then 1 else 0) + (if sl ⟨9, 4⟩ = .star then 1 else 0) = 1 := by
      have neq_2 : (if sl ⟨9, 1⟩ = .star then 1 else 0) +
      (if sl ⟨9, 3⟩ = .star then 1 else 0) + (if sl ⟨9, 4⟩ = .star then 1 else 0) ≠ 2 := by
          by_contra h_ne
          subsum h_ne at h_col9
          omega
      have neq_2 : (if sl ⟨9, 1⟩ = .star then 1 else 0) +
      (if sl ⟨9, 3⟩ = .star then 1 else 0) + (if sl ⟨9, 4⟩ = .star then 1 else 0) ≠ 0 := by
        by_contra h_ne
        subsum h_ne at h_shape3
        rw [add_zero] at h_shape3
        have b_83 := Cell.ite_star_le_one (sl ⟨8, 3⟩)
        omega
      omega
    subsum h_shape3_col9 at h_shape3
    simp at h_shape3
    rename _ => h_83_star
    have h_92_elim := h.adj h_83_star ⟨9, 2⟩ (by decide)
    have h_93_elim := h.adj h_83_star ⟨9, 3⟩ (by decide)
    have h_94_elim := h.adj h_83_star ⟨9, 4⟩ (by decide)
    have h_84_elim := h.adj h_83_star ⟨8, 4⟩ (by decide)
    have h_82_elim := h.adj h_83_star ⟨8, 2⟩ (by decide)
    simp (config := {decide := true}) [h.adj h_83_star] at h_shape3_col9
    rename _ => h_91_star
    have h_90_elim := h.adj h_91_star ⟨9, 0⟩ (by decide)

    simp [h_90_elim, h_91_star, h_93_elim, h_94_elim] at h_col9
    have h_95_elim : sl ⟨9, 5⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_96_elim : sl ⟨9, 6⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_97_elim : sl ⟨9, 7⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    clear h_col9
    simp (config := {decide := true}) [h_60_elim, h.adj h_91_star] at h_shape1
    obtain ⟨h_50_star, h_70_star⟩ := Cell.ite_pair_eq_two h_shape1
    clear h_shape1
    have h_80_elim := h.adj h_70_star ⟨8, 0⟩ (by decide)

    have h_col7 := h.colCount 7
    simp only [Fin.sum_univ_ten] at h_col7
    simp [*] at h_col7
    subsum h_shape9 at h_col7
    have h_76_elim : sl ⟨7, 6⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    have h_77_elim : sl ⟨7, 7⟩ = .elim := Cell.eq_elim_of_ite_zero (by omega)
    clear h_col7

    have h_shape8 := h.shapeCount 8
    simp only [Pos.sum_univ, Fin.sum_univ_succ] at h_shape8
    simp (config := {decide := true}) [h_17_elim, h_27_elim, h_69_elim] at h_shape8
    have h_row8 := h.rowCount 8
    simp only [Fin.sum_univ_ten] at h_row8
    simp [h_68_elim, h_88_elim, h_98_elim] at h_row8
    have h_row9 := h.rowCount 9
    simp only [Fin.sum_univ_ten] at h_row9
    simp [h_69_elim, h_89_elim, h_99_star] at h_row9
    have h_rows89 := congrArg₂ (· + ·) h_row8 h_row9
    simp at h_rows89
    subsum h_shape8 at h_rows89
    subsum h_shape9 at h_rows89
    simp at h_rows89
    have h_08_elim := Cell.ne_star_iff.mp h_rows89
    clear h_rows89
    simp [h_08_elim] at h_shape7_col0
    have h_16_elim : sl ⟨1, 6⟩ = .elim := by
      by_contra h_ne
      have h_16_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_16_star] at h_shape7_col0
    simp [h_16_elim] at h_shape7_row6
    rename _ => h_26_star
    simp (config := {decide := true}) [h.adj h_26_star, h_12_star, h.adj h_12_star, h_14_elim] at h_col1
    subsum (show 1 = 1 by rfl) at h_col1
    simp at h_col1
    have h_28_elim : sl ⟨2, 8⟩ = .elim := by
      by_contra h_ne
      have h_28_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_28_star] at h_col1
    have h_29_elim : sl ⟨2, 9⟩ = .elim := by
      by_contra h_ne
      have h_29_star := Cell.ne_elim_iff.mp h_ne
      simp (config := {decide := true}) [h.adj h_29_star] at h_col1
    have h_col2 := h.colCount 2
    simp only [Fin.sum_univ_ten] at h_col2
    simp (config := {decide := true}) [h_20_elim, h.adj h_12_star, h_26_star, h.adj h_26_star, h_28_elim, h_29_elim] at h_col2
    rename _ => h_24_star
    have h_33_elim := h.adj h_24_star ⟨3, 3⟩ (by decide)
    have h_34_elim := h.adj h_24_star ⟨3, 4⟩ (by decide)
    have h_35_elim := h.adj h_24_star ⟨3, 5⟩ (by decide)
    have h_36_elim := h.adj h_26_star ⟨3, 6⟩ (by decide)
    have h_37_elim := h.adj h_26_star ⟨3, 7⟩ (by decide)

    have h_row3 := h.rowCount 3
    simp only [Fin.sum_univ_ten] at h_row3
    simp [*] at h_row3
    rename _ => h_43_star
    have h_44_elim := h.adj h_43_star ⟨4, 4⟩ (by decide)
    have h_04_elim : sl ⟨0, 4⟩ = .elim := by
      have h_row4 := h.rowCount 4
      simp only [Fin.sum_univ_ten] at h_row4
      simp [*] at h_row4
      exact Cell.ne_star_iff.mp h_row4
    simp [h_04_elim] at h_shape2
    rename _ => h_05_star
    have h_06_elim := h.adj h_05_star ⟨0, 6⟩ (by decide)
    simp [h_06_elim] at h_shape7_col0
    rename _ => h_07_star
    have h_18_elim := h.adj h_07_star ⟨1, 8⟩ (by decide)
    clear h_shape7
    simp [h_18_elim] at h_col1
    rename _ => h_19_star

    simp [h_09_elim, h_19_star, h_29_elim] at h_row9
    subsum (show 1 = 1 by rfl) at h_row9
    simp at h_row9
    have h_39_elim := Cell.ne_star_iff.mp h_row9.1.1.1
    have h_49_elim := Cell.ne_star_iff.mp h_row9.1.1.2
    have h_59_elim := Cell.ne_star_iff.mp h_row9.1.2
    have h_79_elim := Cell.ne_star_iff.mp h_row9.2
    clear h_row9
    simp [h_79_elim] at h_shape9
    rename _ => h_78_star
    have h_87_elim := h.adj h_78_star ⟨8, 7⟩ (by decide)

    have h_col3 := h.colCount 3
    simp only [Fin.sum_univ_ten] at h_col3
    simp [*] at h_col3
    obtain ⟨h_31_star, h_38_star⟩ := Cell.ite_pair_eq_two h_col3
    clear h_col3
    have h_41_elim := h.adj h_31_star ⟨4, 1⟩ (by decide)
    have h_47_elim := h.adj h_38_star ⟨4, 7⟩ (by decide)
    have h_48_elim := h.adj h_38_star ⟨4, 8⟩ (by decide)
    have h_row7 := h.rowCount 7
    simp only [Fin.sum_univ_ten] at h_row7
    simp [*] at h_row7
    rw [add_comm] at h_row7
    simp at h_row7
    rename _ => h_57_star
    have h_46_elim := h.adj h_57_star ⟨4, 6⟩ (by decide)
    have h_56_elim := h.adj h_57_star ⟨5, 6⟩ (by decide)
    have h_58_elim := h.adj h_57_star ⟨5, 8⟩ (by decide)
    clear h_shape8
    clear h_row8
    have h_col4 := h.colCount 4
    simp only [Fin.sum_univ_ten] at h_col4
    simp [*] at h_col4
    rw [add_comm] at h_col4
    simp at h_col4
    rename _ => h_45_star
    have h_row6 := h.rowCount 6
    simp only [Fin.sum_univ_ten] at h_row6
    simp [*] at h_row6
    rw [add_comm] at h_row6
    simp at h_row6
    rename _ => h_86_star
    have h_85_elim := h.adj h_86_star ⟨8, 5⟩ (by decide)

    funext ⟨c, r⟩
    fin_cases c <;> fin_cases r <;> assumption
