-- CamelUp.View.Basic
-- Minimal textual renderer for game states and simulation results.
import CamelUp.Model.Types
import CamelUp.Controller.Sim

namespace CamelUp.View

/-! ## Stack and board rendering -/

def stackToString (s : Stack) : String :=
  if s.isEmpty then "·"
  else "[" ++ String.intercalate "," (s.map toString) ++ "]"

def boardToString (board : Board) : String :=
  let pieces :=
    (List.range numSquares).filterMap (fun i =>
      let s := board.getStack i
      if s.isEmpty then none
      else some s!"{i}:{stackToString s}")
  if pieces.isEmpty then "(empty board)"
  else String.intercalate "  " pieces

/-! ## Score rendering -/

def scoresToString (scores : Array Int) : String :=
  let parts := (List.range scores.size).map (fun i =>
    s!"P{i}:{scores.getD i 0}")
  "[" ++ String.intercalate " " parts ++ "]"

/-! ## Full state rendering -/

def stateToString (gs : GameState) : String :=
  let bagStr :=
    if gs.diceBag.isEmpty then "∅"
    else "[" ++ String.intercalate "," (gs.diceBag.map toString) ++ "]"
  let overStr := if gs.gameOver then " [RACE OVER]" else ""
  s!"Leg {gs.legNo} | {boardToString gs.board} | bag:{bagStr}{overStr}"

def scoresLine (gs : GameState) : String :=
  s!"Scores: {scoresToString gs.scores} | turn: P{gs.currentPlayer}"

/-! ## Simulation result rendering -/

def winCountsToString (wc : CamelUp.Sim.WinCounts) (n : Nat) : String :=
  let lines := wc.map (fun (c, cnt) =>
    let pctNum := if n = 0 then 0 else (cnt * 1000 + n / 2) / n
    let whole  := pctNum / 10
    let frac   := pctNum % 10
    s!"  {c}: {cnt}/{n}  ({whole}.{frac}%)")
  String.intercalate "\n" lines

def leaderToString (gs : GameState) : String :=
  match gs.leader with
  | none   => "no leader yet"
  | some c => s!"current leader: {c}"

def raceWinnerToString (gs : GameState) : String :=
  match gs.raceWinner with
  | none   => "race in progress"
  | some c => s!"race winner: {c}"

end CamelUp.View
