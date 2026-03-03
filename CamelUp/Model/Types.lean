/-!
# CamelUp.Model.Types

Core data types for the Camel Up board game.
Phase 1 scope: five racing camels, 16-square track, leg dice bag, no modifier tiles.
-/
namespace CamelUp

/-! ## Camel colors -/

/-- The five racing camels. -/
inductive CamelColor where
  | White | Black | Green | Yellow | Blue
  deriving BEq, Repr, Hashable, DecidableEq

instance : ToString CamelColor where
  toString
    | .White  => "W"
    | .Black  => "B"
    | .Green  => "G"
    | .Yellow => "Y"
    | .Blue   => "L"

/-- Canonical list of all five camels. -/
def CamelColor.all : List CamelColor :=
  [.White, .Black, .Green, .Yellow, .Blue]

/-- Map each camel to a 0-based index for array lookups (legBetTiles). -/
def CamelColor.toIdx : CamelColor → Nat
  | .White  => 0
  | .Black  => 1
  | .Green  => 2
  | .Yellow => 3
  | .Blue   => 4

/-! ## Board -/

/-- Number of squares on the track (0-indexed, 0..15). -/
def numSquares : Nat := 16

/-- A stack of camels on one square, listed bottom-to-top.
    The rightmost element is the "top" camel (furthest ahead in a stack). -/
abbrev Stack := List CamelColor

/-- The board is an array of 16 stacks.
    Index = square number.  Camels that move past index 15 finish the race. -/
abbrev Board := Array Stack

/-- An empty board: all squares empty. -/
def Board.empty : Board := (List.replicate numSquares []).toArray

/-- Safely read a square's stack; returns [] for out-of-range indices. -/
def Board.getStack (b : Board) (sq : Nat) : Stack := b.getD sq []

/-- Update a square's stack. No-op when `sq` is out of range (i.e. past finish). -/
def Board.setStack (b : Board) (sq : Nat) (s : Stack) : Board :=
  let rec setAt : List Stack → Nat → List Stack
    | [],         _     => []
    | _ :: rest,  0     => s :: rest
    | x :: rest,  i + 1 => x :: setAt rest i
  (setAt b.toList sq).toArray

/-! ## Dice -/

/-- A die face value in {1,2,3}, stored as a `Fin 3` (value = face − 1). -/
abbrev DieValue := Fin 3

/-- The actual face value shown on the die (1, 2, or 3). -/
def DieValue.toNat (d : DieValue) : Nat := d.val + 1

/-- The three possible die faces. -/
def DieValue.all : List DieValue := [(0 : Fin 3), 1, 2]

/-- A single die outcome: which camel's die was drawn and what face it showed. -/
structure DieOutcome where
  camel : CamelColor
  value : DieValue
  deriving BEq, Repr

/-! ## Bet structures -/

/-- A leg-bet entry: player `player` holds a tile for camel `camel` worth `payout` coins. -/
structure LegBetEntry where
  camel  : CamelColor
  payout : Nat         -- tile value: 5, 3, or 2
  player : Nat
  deriving BEq, Repr

/-- Whether the race bet predicts the overall winner or loser. -/
inductive RaceBetType | Win | Lose deriving BEq, Repr

/-- A race-bet entry: player `player` bets camel `camel` wins/loses the race. -/
structure RaceBetEntry where
  betType : RaceBetType
  camel   : CamelColor
  player  : Nat
  deriving BEq, Repr

/-! ## Modifier tiles -/

/-- A desert tile placed on a board square.
    `effect = 1` = oasis (bump forward 1); `effect = -1` = mirage (bump back 1).
    When any camel stack primary-lands on this square the owner earns 1 coin. -/
structure ModifierTile where
  owner  : Nat   -- player who placed this tile
  effect : Int   -- +1 (oasis) or -1 (mirage)
  deriving BEq, Repr

/-! ## Game State -/

/-- Available leg-bet tiles per camel at the start of each fresh leg.
    Indexed by CamelColor.toIdx.  Head of each list = next tile to be taken. -/
def initialLegBetTiles : Array (List Nat) :=
  (List.replicate 5 ([5, 3, 2] : List Nat)).toArray

/-- Complete game state for Camel Up. -/
structure GameState where
  -- Board
  board          : Board
  diceBag        : List CamelColor   -- dice not yet rolled this leg
  legNo          : Nat               -- current leg (0-indexed)
  finishedCamels : List CamelColor   -- camels past finish, in crossing order
  -- Players
  numPlayers     : Nat               -- number of players (≥ 1)
  currentPlayer  : Nat               -- whose turn (0-indexed)
  scores         : Array Int         -- cumulative coins; length = numPlayers
  -- Leg bets (reset each leg)
  legBetTiles    : Array (List Nat)  -- remaining tiles per camel (head = next)
  legBetsPlaced  : List LegBetEntry  -- bets placed in current leg
  -- Race bets (cumulative until race end)
  raceBetsWin    : List RaceBetEntry
  raceBetsLose   : List RaceBetEntry
  -- Modifier tiles (persist until game end; indexed by square; none = unoccupied)
  modifiers      : Array (Option ModifierTile)
  -- Race status
  gameOver       : Bool
  deriving Repr

/-- Construct a fresh game state for `nPlayers` players on the given board. -/
def GameState.initial (nPlayers : Nat) (board : Board) : GameState :=
  let n := max nPlayers 1
  { board          := board
    diceBag        := CamelColor.all
    legNo          := 0
    finishedCamels := []
    numPlayers     := n
    currentPlayer  := 0
    scores         := (List.replicate n (0 : Int)).toArray
    legBetTiles    := initialLegBetTiles
    legBetsPlaced  := []
    raceBetsWin    := []
    raceBetsLose   := []
    modifiers      := (List.replicate numSquares (none : Option ModifierTile)).toArray
    gameOver       := false }

/-! ## Ranking and board queries -/

/-- All 5 camels ordered 1st–5th place.

    Finished camels precede board camels (first-crosser = rank 0).
    Board camels are ordered high-sq-first; within a square, top-of-stack first.
    This is the canonical ordering used for leg-bet and race-bet resolution. -/
def legRanking (board : Board) (finished : List CamelColor) : List CamelColor :=
  let boardRanked :=
    (List.range numSquares).reverse.foldl (fun acc i =>
      acc ++ (board.getStack i).reverse) []
  finished ++ boardRanked

/-! ## Board queries -/

/-- Find the position and height of a camel in the stack it occupies.
    Returns `some (sq, idx)` where idx 0 = bottom of stack.
    Returns `none` if the camel is not on the board (invalid state). -/
def findCamelOnBoard (board : Board) (c : CamelColor) : Option (Nat × Nat) :=
  let rec searchSquares : List Nat → Option (Nat × Nat)
    | [] => none
    | sq :: rest =>
        let stack := board.getStack sq
        let rec searchStack : List CamelColor → Nat → Option Nat
          | [],      _   => none
          | x :: xs, i  => if x == c then some i else searchStack xs (i + 1)
        match searchStack stack 0 with
        | none     => searchSquares rest
        | some idx => some (sq, idx)
  searchSquares (List.range numSquares)

/-- Current leader (1st-place camel by legRanking). -/
def GameState.leader (gs : GameState) : Option CamelColor :=
  (legRanking gs.board gs.finishedCamels).head?

/-- Race winner: first camel to have crossed the finish line. -/
def GameState.raceWinner (gs : GameState) : Option CamelColor :=
  gs.finishedCamels.head?

/-- Race loser: last-place camel in current ranking. -/
def GameState.raceLoser (gs : GameState) : Option CamelColor :=
  (legRanking gs.board gs.finishedCamels).getLast?

/-- All camels on board squares. -/
def GameState.boardCamels (gs : GameState) : List CamelColor :=
  (List.range numSquares).foldl (fun acc i => acc ++ gs.board.getStack i) []

/-- Whether the race has ended. -/
def GameState.isRaceOver (gs : GameState) : Bool := gs.gameOver

/-! ## Validity predicate -/

/-- Structural invariants for a legal game state.

    1. `board_size`    — board array is exactly `numSquares` wide.
    2. `camel_unique`  — every colour appears exactly once across board + finished.
    3. `bag_sub`       — bag entries are all valid colours.
    4. `bag_each_once` — no colour appears twice in the bag.
    5. `scores_size`   — scores array length equals numPlayers.
    6. `tiles_size`    — legBetTiles has exactly 5 entries (one per camel).
    7. `player_valid`  — currentPlayer is in-range when numPlayers > 0.

    Proof that `step` preserves these: `CamelUp.Proofs.Invariants`. -/
structure ValidState (gs : GameState) : Prop where
  board_size    : gs.board.size = numSquares
  camel_unique  : ∀ c : CamelColor,
    gs.finishedCamels.count c +
    (List.range numSquares).foldl (fun acc i => acc + (gs.board.getStack i).count c) 0 = 1
  bag_sub       : ∀ c ∈ gs.diceBag, c ∈ CamelColor.all
  bag_each_once : ∀ c : CamelColor, gs.diceBag.count c ≤ 1
  scores_size   : gs.scores.size = gs.numPlayers
  tiles_size    : gs.legBetTiles.size = 5
  player_valid  : gs.numPlayers > 0 → gs.currentPlayer < gs.numPlayers
  mods_size     : gs.modifiers.size = numSquares

end CamelUp
