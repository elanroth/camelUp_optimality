-- CamelUp.Model.Step
-- The transition relation for Camel Up.
-- Phase 1: only the `Roll` move (draw a die and move a camel).
import CamelUp.Model.Types

namespace CamelUp

/-! ## Moves -/

/-- Legal player actions.  Die outcomes are embedded in `Roll` so that `step`
    is a pure function: `GameState → Move → Option GameState`. -/
inductive Move where
  | Roll        (outcome : DieOutcome)  -- die draw; outcome supplied by simulator
  | BetLeg      (c : CamelColor)        -- take next leg-bet tile for camel c
  | BetRaceWin  (c : CamelColor)        -- place a race-winner card for camel c
  | BetRaceLose (c : CamelColor)        -- place a race-loser card for camel c
  | PlaceTile   (sq : Nat) (positive : Bool)  -- oasis (+1) or mirage (−1) on sq
  deriving BEq, Repr

instance : ToString Move where
  toString
    | .Roll o          => s!"Roll({o.camel},{o.value.toNat})"
    | .BetLeg c        => s!"BetLeg({c})"
    | .BetRaceWin c    => s!"BetRaceWin({c})"
    | .BetRaceLose c   => s!"BetRaceLose({c})"
    | .PlaceTile sq true  => s!"Oasis({sq})"
    | .PlaceTile sq false => s!"Mirage({sq})"

/-! ## Private helpers -/

-- Generic array-element update (same structure as Board.setStack but polymorphic).
private def updateArr {α} (arr : Array α) (i : Nat) (v : α) : Array α :=
  let rec go : List α → Nat → List α
    | [],         _     => []
    | _ :: rest,  0     => v :: rest
    | x :: rest,  i + 1 => x :: go rest i
  (go arr.toList i).toArray

theorem updateArr_size {α} (arr : Array α) (i : Nat) (v : α) :
    (updateArr arr i v).size = arr.size := by
  have hgo : ∀ (l : List α) (j : Nat), (updateArr.go v l j).length = l.length := by
    intro l; induction l with
    | nil         => intro j; simp [updateArr.go]
    | cons x t ih => intro j; cases j with
      | zero   => simp [updateArr.go]
      | succ k => simp [updateArr.go, ih k]
  show (updateArr arr i v).size = arr.size
  simp only [updateArr]
  have h1 : ((updateArr.go v arr.toList i).toArray).size
              = (updateArr.go v arr.toList i).length := by simp
  have h2 : arr.size = arr.toList.length := by simp
  rw [h1, h2, hgo]

/-- Award `delta` coins to player `p`. -/
def awardPlayer (scores : Array Int) (p : Nat) (delta : Int) : Array Int :=
  updateArr scores p (scores.getD p 0 + delta)

theorem awardPlayer_size (scores : Array Int) (p : Nat) (delta : Int) :
    (awardPlayer scores p delta).size = scores.size :=
  updateArr_size scores p _

-- 0-based index of the first occurrence of `a` in `xs`.
private def findIdxOf {α} [BEq α] (xs : List α) (a : α) : Option Nat :=
  let rec go : List α → Nat → Option Nat
    | [],     _   => none
    | x :: t, idx => if x == a then some idx else go t (idx + 1)
  go xs 0

-- Safe list element access with default.
private def listGetD {α} (xs : List α) (i : Nat) (d : α) : α :=
  let rec go : List α → Nat → α
    | [],      _     => d
    | x :: _,  0     => x
    | _ :: t,  i + 1 => go t i
  go xs i

/-- Advance turn to the next player (wraps around). -/
def advancePlayer (cur : Nat) (n : Nat) : Nat :=
  if n = 0 then 0 else (cur + 1) % n

/-! ## Board mutation (M3: carry-above + finish-line; M8: modifier tiles) -/

/-- Apply a die outcome to the board, including modifier tile effects.

    1. Locate the rolled camel; split its square into staying/moving groups.
    2. Compute primarySq = sq + dieValue.
    3. If a modifier tile exists at primarySq, nudge the movers ±1 and return
       the tile owner (who earns 1 coin, awarded by `step`).
    4. Place movers on top of destination stack, or cross the finish line. -/
def applyDie (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    : Board × List CamelColor × Option Nat :=
  match findCamelOnBoard board outcome.camel with
  | none           => (board, finished, none)
  | some (sq, idx) =>
      let stack    := board.getStack sq
      let staying  := stack.take idx     -- camels below the mover stay put
      let moving   := stack.drop idx     -- mover + camels above ride along
      let board'   := board.setStack sq staying
      let primarySq := sq + outcome.value.toNat
      -- Check for a modifier tile at the primary landing square.
      let (adjSq, mTileOwner) : Nat × Option Nat :=
        if primarySq >= numSquares then (primarySq, none)
        else
          match mods.getD primarySq none with
          | none      => (primarySq, none)
          | some tile =>
              -- Nat subtraction saturates at 0; primarySq ≥ 1 always (safe).
              let adj := if tile.effect > 0 then primarySq + 1
                         else if primarySq = 0 then 0
                         else primarySq - 1
              (adj, some tile.owner)
      if adjSq >= numSquares then
        (board', finished ++ moving, mTileOwner)
      else
        let destStack := board'.getStack adjSq
        (board'.setStack adjSq (destStack ++ moving), finished, mTileOwner)

/-! ## Bet resolution (M4) -/

/-- Payout for the n-th correct race bet (0-indexed): 8, 5, 3, 2, 1, 1, 1, … -/
def racePayoutAt (idx : Nat) : Int :=
  listGetD ([8, 5, 3, 2, 1] : List Int) idx 1

/-- Resolve all leg bets against `ranking` (index 0 = 1st place).
    1st → tile face value; 2nd → 1 coin; else → −1 coin. -/
def resolveLegBets (scores : Array Int) (ranking : List CamelColor)
    (bets : List LegBetEntry) : Array Int :=
  bets.foldl (fun sc bet =>
    let delta : Int :=
      match findIdxOf ranking bet.camel with
      | none   => -1
      | some 0 => bet.payout
      | some 1 => 1
      | _      => -1
    awardPlayer sc bet.player delta) scores

/-- Resolve race-winner bets.  Correct bets (predicted `winner`) earn
    [8, 5, 3, 2, 1, 1, …] in the order they were placed; others pay −1. -/
def resolveRaceWinBets (scores : Array Int) (winner : CamelColor)
    (bets : List RaceBetEntry) : Array Int :=
  (bets.foldl (fun (pair : Array Int × Nat) bet =>
    let sc  := pair.1
    let idx := pair.2
    if bet.camel == winner then
      (awardPlayer sc bet.player (racePayoutAt idx), idx + 1)
    else
      (awardPlayer sc bet.player (-1), idx))
   (scores, 0)).1

/-- Resolve race-loser bets.  Same payout structure as win bets but for `loser`. -/
def resolveRaceLoseBets (scores : Array Int) (loser : CamelColor)
    (bets : List RaceBetEntry) : Array Int :=
  (bets.foldl (fun (pair : Array Int × Nat) bet =>
    let sc  := pair.1
    let idx := pair.2
    if bet.camel == loser then
      (awardPlayer sc bet.player (racePayoutAt idx), idx + 1)
    else
      (awardPlayer sc bet.player (-1), idx))
   (scores, 0)).1

/-! ## Step function -/

/-- Pure state transition: `step gs move = some gs'` iff `move` is legal from `gs`.
    Returns `none` for illegal moves (wrong die, no tiles, game already over). -/
def step (gs : GameState) (move : Move) : Option GameState :=
  if gs.gameOver then none
  else match move with
  | .Roll outcome =>
      if !gs.diceBag.contains outcome.camel then none
      else
        -- Rolling player earns 1 coin from the pyramid immediately.
        let scores₁               := awardPlayer gs.scores gs.currentPlayer 1
        let newBag                 := gs.diceBag.erase outcome.camel
        let (newBoard, newFinished, mTileOwner) :=
          applyDie gs.board gs.modifiers gs.finishedCamels outcome
        -- M8: award 1 coin to modifier tile owner if a tile was triggered.
        let scores₁ := match mTileOwner with
          | none   => scores₁
          | some p => awardPlayer scores₁ p 1
        let nextPlayer             := advancePlayer gs.currentPlayer gs.numPlayers
        let ranking                := legRanking newBoard newFinished
        if !newFinished.isEmpty then
          -- Race over: resolve leg bets + all accumulated race bets.
          let winner  := newFinished.head?.getD .White
          let loser   := ranking.getLast?.getD .Blue
          let scores₂ := resolveLegBets    scores₁ ranking gs.legBetsPlaced
          let scores₃ := resolveRaceWinBets scores₂ winner gs.raceBetsWin
          let scores₄ := resolveRaceLoseBets scores₃ loser gs.raceBetsLose
          some { gs with board          := newBoard
                         diceBag        := []
                         finishedCamels := newFinished
                         currentPlayer  := nextPlayer
                         scores         := scores₄
                         legBetsPlaced  := []
                         gameOver       := true }
        else if newBag.isEmpty then
          -- Leg ends (race not yet over): resolve leg bets, reset for next leg.
          let scores₂ := resolveLegBets scores₁ ranking gs.legBetsPlaced
          some { gs with board          := newBoard
                         diceBag        := CamelColor.all
                         legNo          := gs.legNo + 1
                         finishedCamels := newFinished
                         currentPlayer  := nextPlayer
                         scores         := scores₂
                         legBetTiles    := initialLegBetTiles
                         legBetsPlaced  := [] }
        else
          some { gs with board          := newBoard
                         diceBag        := newBag
                         finishedCamels := newFinished
                         currentPlayer  := nextPlayer
                         scores         := scores₁ }
  | .BetLeg c =>
      let idx   := c.toIdx
      let tiles := gs.legBetTiles.getD idx []
      match tiles with
      | []              => none   -- no tiles remaining for this camel this leg
      | tileVal :: rest =>
          let newTiles := updateArr gs.legBetTiles idx rest
          let bet : LegBetEntry :=
            { camel := c, payout := tileVal, player := gs.currentPlayer }
          some { gs with legBetTiles   := newTiles
                         legBetsPlaced := gs.legBetsPlaced ++ [bet]
                         currentPlayer := advancePlayer gs.currentPlayer gs.numPlayers }
  | .BetRaceWin c =>
      let bet : RaceBetEntry :=
        { betType := .Win, camel := c, player := gs.currentPlayer }
      some { gs with raceBetsWin   := gs.raceBetsWin ++ [bet]
                     currentPlayer := advancePlayer gs.currentPlayer gs.numPlayers }
  | .BetRaceLose c =>
      let bet : RaceBetEntry :=
        { betType := .Lose, camel := c, player := gs.currentPlayer }
      some { gs with raceBetsLose  := gs.raceBetsLose ++ [bet]
                     currentPlayer := advancePlayer gs.currentPlayer gs.numPlayers }
  | .PlaceTile sq positive =>
      -- Legal when: sq ≠ 0, sq on-board, no camel there, no tile there.
      if sq == 0 then none
      else if sq >= numSquares then none
      else if !(gs.board.getStack sq).isEmpty then none
      else if (gs.modifiers.getD sq none).isSome then none
      else
        let eff : Int := if positive then 1 else -1
        let tile : ModifierTile := { owner := gs.currentPlayer, effect := eff }
        some { gs with modifiers     := updateArr gs.modifiers sq (some tile)
                       currentPlayer := advancePlayer gs.currentPlayer gs.numPlayers }

/-! ## Legal-move enumeration -/

/-- All die outcomes still drawable this leg. -/
def legalDieOutcomes (gs : GameState) : List DieOutcome :=
  if gs.gameOver then []
  else
    gs.diceBag.foldl (fun acc c =>
      acc ++ DieValue.all.map (fun v => ({ camel := c, value := v } : DieOutcome))) []

/-- All legal moves from `gs`.  Used by the Controller for EV/policy evaluation. -/
def legalMoves (gs : GameState) : List Move :=
  if gs.gameOver then []
  else
    let rollMoves :=
      (legalDieOutcomes gs).map Move.Roll
    let legBetMoves :=
      CamelColor.all.foldl (fun acc c =>
        if (gs.legBetTiles.getD c.toIdx []).isEmpty then acc
        else acc ++ [Move.BetLeg c]) []
    let winMoves  := CamelColor.all.map Move.BetRaceWin
    let loseMoves := CamelColor.all.map Move.BetRaceLose
    -- M8: tile placement on empty squares (skip sq 0 and occupied/tiled squares).
    let tileMoves :=
      (List.range numSquares).foldl (fun acc sq =>
        if sq == 0 then acc
        else if !(gs.board.getStack sq).isEmpty then acc
        else if (gs.modifiers.getD sq none).isSome then acc
        else acc ++ [Move.PlaceTile sq true, Move.PlaceTile sq false]) []
    rollMoves ++ legBetMoves ++ winMoves ++ loseMoves ++ tileMoves

end CamelUp
