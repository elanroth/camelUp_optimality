-- CamelUp.View.Parser
-- Parse a game state from command-line arguments.
--
-- Format (all flags optional; defaults produce a fresh 2-player game):
--
--   --board  "0:B 1:Y 3:WG 5:L"   square:stack pairs; stack = bottom→top letters
--   --bag    "WBGYL"               letters of dice still in the bag this leg
--   --players 2                    number of human players
--   --scores "5,3"                 comma-separated coin totals (length = players)
--   --leg    1                     current leg number (0-indexed)
--   --player 0                     whose turn it is (0-indexed)
--
-- Camel letters: W=White  B=Black  G=Green  Y=Yellow  L=Blue
--
-- Example (the exampleBoard from the demo):
--   camelup --board "0:B 1:Y 3:WG 5:L" --bag "WBGYL" --players 2
import CamelUp.Model.Types
import CamelUp.Model.Step

namespace CamelUp.Parser

open CamelUp

-- ─── Color codec ─────────────────────────────────────────────────────────────

def charToColor : Char → Option CamelColor
  | 'W' => some .White
  | 'B' => some .Black
  | 'G' => some .Green
  | 'Y' => some .Yellow
  | 'L' => some .Blue
  | _   => none

-- Parse a run of color letters ("WG" → [.White, .Green]).
def parseStack (s : String) : Option Stack :=
  s.toList.foldr (fun c acc =>
    match acc, charToColor c with
    | none,   _      => none
    | _,      none   => none
    | some xs, some col => some (col :: xs)) (some [])

-- Parse the bag string "WBGYL" into a list of CamelColor.
def parseBag (s : String) : Option (List CamelColor) :=
  s.toList.foldr (fun c acc =>
    match acc, charToColor c with
    | none,   _         => none
    | _,      none      => none
    | some xs, some col => some (col :: xs)) (some [])

-- ─── Board parser ─────────────────────────────────────────────────────────────

-- Parse a single "sq:stack" token.
private def parsePair (token : String) : Option (Nat × Stack) :=
  let parts := token.splitOn ":"
  match parts with
  | [sqStr, stackStr] =>
      match sqStr.toNat?, parseStack stackStr with
      | some sq, some stk => some (sq, stk)
      | _, _              => none
  | _ => none

-- Parse board string "0:B 1:Y 3:WG 5:L".
def parseBoard (s : String) : Option Board :=
  let tokens := s.splitOn " " |>.filter (· ≠ "")
  tokens.foldl (fun acc token =>
    match acc, parsePair token with
    | none,   _              => none
    | _,      none           => none
    | some b, some (sq, stk) => some (b.setStack sq stk)) (some Board.empty)

-- ─── Scores parser ────────────────────────────────────────────────────────────

def parseScores (s : String) : Option (Array Int) :=
  let parts := s.splitOn "," |>.filter (· ≠ "")
  parts.foldl (fun acc part =>
    match acc with
    | none   => none
    | some arr =>
        match part.toInt? with
        | none   => none
        | some n => some (arr.push n)) (some #[])

-- ─── Full CLI argument parser ─────────────────────────────────────────────────

structure ParsedArgs where
  board   : Board
  bag     : List CamelColor
  players : Nat
  scores  : Array Int
  leg     : Nat
  player  : Nat
  sims    : Nat

def defaultArgs : ParsedArgs :=
  { board   := Board.empty
    bag     := CamelColor.all
    players := 2
    scores  := #[0, 0]
    leg     := 0
    player  := 0
    sims    := 200 }

-- Walk argv looking for --flag value pairs.
private def findFlag (argv : List String) (flag : String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | [_] => none
    | f :: v :: rest => if f == flag then some v else go (v :: rest)
  go argv

def parseArgs (argv : List String) : Except String ParsedArgs := do
  let board ←
    match findFlag argv "--board" with
    | none   => pure Board.empty
    | some s =>
        match parseBoard s with
        | none   => throw s!"Could not parse --board \"{s}\""
        | some b => pure b
  let bag ←
    match findFlag argv "--bag" with
    | none   => pure CamelColor.all
    | some s =>
        match parseBag s with
        | none    => throw s!"Could not parse --bag \"{s}\""
        | some bs => pure bs
  let nPlayers ←
    match findFlag argv "--players" with
    | none   => pure 2
    | some s =>
        match s.toNat? with
        | none   => throw s!"--players must be a number, got \"{s}\""
        | some n => if n == 0 then throw "--players must be ≥ 1" else pure n
  let sims ←
    match findFlag argv "--sims" with
    | none   => pure 200
    | some s =>
        match s.toNat? with
        | none   => throw s!"--sims must be a number, got \"{s}\""
        | some n => pure (max 10 n)
  let leg :=
    match findFlag argv "--leg" with
    | none   => 0
    | some s => s.toNat?.getD 0
  let player :=
    match findFlag argv "--player" with
    | none   => 0
    | some s => s.toNat?.getD 0
  let scores ←
    match findFlag argv "--scores" with
    | none   => pure ((List.replicate nPlayers (0 : Int)).toArray)
    | some s =>
        match parseScores s with
        | none    => throw s!"Could not parse --scores \"{s}\""
        | some sc => pure sc
  pure { board, bag, players := nPlayers, scores, leg, player, sims }

/-- Build a GameState from ParsedArgs.  The modifiers and bet arrays start empty
    (the parser intentionally omits them for simplicity). -/
def argsToState (a : ParsedArgs) : GameState :=
  let n := max a.players 1
  let sc := if a.scores.size == n then a.scores
            else (List.replicate n (0 : Int)).toArray
  { board          := a.board
    diceBag        := a.bag
    legNo          := a.leg
    finishedCamels := []
    numPlayers     := n
    currentPlayer  := a.player % n
    scores         := sc
    legBetTiles    := initialLegBetTiles
    legBetsPlaced  := []
    raceBetsWin    := []
    raceBetsLose   := []
    modifiers      := (List.replicate numSquares (none : Option ModifierTile)).toArray
    gameOver       := false }

end CamelUp.Parser
