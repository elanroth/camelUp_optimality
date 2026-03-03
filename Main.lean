-- Main.lean — Milestones 3-11 demo + CLI state analyzer
import CamelUp

open CamelUp CamelUp.Sim CamelUp.View CamelUp.EV CamelUp.Policy
     CamelUp.VarSeek CamelUp.Exact CamelUp.Parser

def exampleBoard : Board :=
  Board.empty
  |>.setStack 0 [.Black]
  |>.setStack 1 [.Yellow]
  |>.setStack 3 [.White, .Green]
  |>.setStack 5 [.Blue]

def exampleState : GameState := GameState.initial 2 exampleBoard

-- ─── M11: CLI analysis mode ──────────────────────────────────────────────────

/-- Print a full probability + EV analysis for an arbitrary GameState. -/
def runAnalysis (gs : GameState) (sims : Nat) : IO Unit := do
  IO.println s!"State  : {stateToString gs}"
  IO.println s!"{scoresLine gs}"
  IO.println s!"Leader : {leaderToString gs}"
  IO.println ""
  IO.println "--- Exact leg-win probabilities ---"
  IO.println (exactProbsToString gs)
  IO.println ""
  IO.println s!"--- Move rankings by EV ({sims} sims/move, seed=7) ---"
  let ranked := rankMoves gs 7 sims
  ranked.forM (fun me => IO.println (toString me))
  IO.println ""
  IO.println "--- mughBot recommendation ---"
  let rng : RNG := { seed := 7 }
  let (bestMove, _) := mughBot sims gs rng
  IO.println s!"  -> {bestMove}"

def runCLI (argv : List String) : IO Unit := do
  IO.println "=== Camel Up Analyzer (M11) ==="
  IO.println ""
  match parseArgs argv with
  | Except.error msg =>
      IO.eprintln s!"Parse error: {msg}"
      IO.eprintln "Usage: camelup [--board \"0:B 1:Y 3:WG 5:L\"] [--bag \"WBGYL\"]"
      IO.eprintln "               [--players 2] [--scores \"5,3\"] [--leg 0]"
      IO.eprintln "               [--player 0] [--sims 200]"
      IO.eprintln "Color letters: W=White B=Black G=Green Y=Yellow L=Blue"
  | Except.ok args =>
      let gs := argsToState args
      runAnalysis gs args.sims

-- ─── Demo (no CLI args) ──────────────────────────────────────────────────────

def runDemo : IO Unit := do
  let gs := exampleState
  IO.println "=== Camel Up Probability Tool  [Milestones 3-11] ==="
  IO.println ""
  IO.println s!"State  : {stateToString gs}"
  IO.println s!"{scoresLine gs}"
  IO.println s!"Leader : {leaderToString gs}"
  IO.println ""

  -- M5: per-move EV ranking
  let simsPerMove : Nat := 100
  IO.println s!"--- Move rankings by EV ({simsPerMove} sims/move, seed=7) ---"
  let ranked := rankMoves gs 7 simsPerMove
  ranked.forM (fun me => IO.println (toString me))
  IO.println ""

  -- M6: head-to-head tournament
  let nGames : Nat := 10
  IO.println s!"--- Tournament: mughBot vs randomPolicy ({nGames} games, seed=99) ---"
  let policies : Array Policy := #[mughBot 20, randomPolicy]
  let policyNames : Array String := #["mughBot (P0)", "random  (P1)"]
  let (result, wins) := runTournament gs policies 99 nGames
  IO.println (tournamentSummary "Results" result wins policyNames)
  IO.println ""
  IO.println "M6 complete."
  IO.println ""

  -- M7: varSeekBot vs mughBot vs random (3-player)
  IO.println s!"--- Tournament: varSeekBot vs mughBot vs random ({nGames} games, seed=77) ---"
  let gs3 := GameState.initial 3 exampleBoard
  let policies3 : Array Policy := #[varSeekBot 20, mughBot 20, randomPolicy]
  let names3    : Array String := #["varSeekBot", "mughBot   ", "random    "]
  let (res3, wins3) := runTournament gs3 policies3 77 nGames
  IO.println (tournamentSummary "M7 Results" res3 wins3 names3)
  IO.println ""
  IO.println "M7 complete."
  IO.println ""

  -- M8: modifier tile demo
  IO.println "--- M8: Modifier tile demo ---"
  let tileMove := Move.PlaceTile 2 true
  IO.println s!"P0 places: {tileMove}"
  match step gs tileMove with
  | none     => IO.println "  -> illegal!"
  | some gs1 =>
      IO.println s!"  -> {stateToString gs1}"
      let rollY := Move.Roll { camel := .Yellow, value := (0 : Fin 3) }
      IO.println s!"P1 rolls: {rollY}  (Yellow +1 → sq2, hits oasis, bounces to sq3)"
      match step gs1 rollY with
      | none     => IO.println "  -> illegal!"
      | some gs2 =>
          IO.println s!"  -> {stateToString gs2}"
          IO.println s!"  -> {scoresLine gs2}  (P0: tile coin; P1: roll coin)"
  IO.println ""
  IO.println "M8 complete."
  IO.println ""

  -- M9: exact enumeration
  IO.println "--- M9: Exact leg-win probabilities ---"
  IO.println (exactProbsToString gs)
  IO.println ""
  IO.println "M9 complete."
  IO.println ""

  -- M10: dominance lemma summary
  IO.println "M10: Dominance lemmas in CamelUp/Proofs/Dominance.lean (sorry-stubbed)"
  IO.println "     L1 insertDesc_head_ge  L2 rankMoves_sorted_desc"
  IO.println "     L3 rankMoves_roll_included  L4 mughBot_picks_max_EV"
  IO.println "     L5 mughBot_ge_roll_score  L6 evalDetMove_illegal_sentinel"
  IO.println ""
  IO.println "M10 complete."
  IO.println ""

  -- M11: illustrate the CLI parser on the example board
  IO.println "--- M11: State parser demo ---"
  IO.println "Parsing: --board \"0:B 1:Y 3:WG 5:L\" --bag \"WBGYL\" --players 2"
  let argv := ["--board", "0:B 1:Y 3:WG 5:L", "--bag", "WBGYL", "--players", "2"]
  match parseArgs argv with
  | Except.error e => IO.println s!"  Error: {e}"
  | Except.ok args =>
      let parsedGs := argsToState args
      IO.println s!"  Parsed state: {stateToString parsedGs}"
      IO.println s!"  Board matches original: {parsedGs.board == gs.board}"
  IO.println ""
  IO.println "M11 complete. Run with args to analyze a custom state:"
  IO.println "  camelup --board \"0:B 1:Y 3:WG 5:L\" --bag \"WBGYL\" --players 2 --sims 300"

def main (argv : List String) : IO Unit := do
  if argv.isEmpty then
    runDemo
  else
    runCLI argv
