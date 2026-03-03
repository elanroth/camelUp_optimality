/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f92d8fc5-ddf5-4d44-a540-0d31b7e3080b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem step_Roll_board_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.board.size = numSquares

- theorem step_Roll_camel_unique (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor,
      gs'.finishedCamels.count c +
      (List.range numSquares).foldl (fun acc i => acc + (gs'.board.getStack i).count c) 0 = 1

- theorem step_Roll_bag_sub (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c ∈ gs'.diceBag, c ∈ CamelColor.all

- theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1

- theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers

- theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5

- theorem step_Roll_mods_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.modifiers.size = numSquares

- theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers

- theorem step_BetLeg_tiles_size (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.legBetTiles.size = 5

- theorem step_BetLeg_scores_size (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.scores.size = gs'.numPlayers

- theorem step_BetLeg_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers

- theorem step_BetRaceWin_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetRaceWin c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers

- theorem step_BetRaceLose_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetRaceLose c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers

- theorem step_PlaceTile_board_unchanged (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_step : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.scores = gs.scores ∧
    gs'.legBetTiles = gs.legBetTiles

- theorem step_PlaceTile_mods_size (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.modifiers.size = numSquares

- theorem step_PlaceTile_player_valid (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
  HELPER LEMMAS FILE — for Aristotle (4th batch)
  ================================================

  TASK: Replace every `sorry` in this file with a real proof.
  The main theorem `step_preserves_valid` is already assembled in
  CamelUp/Proofs/Invariants.lean using these helpers — just fill them in here.

  ── CRITICAL BUG FIX FROM LAST BATCH ──────────────────────────────────────────
  In the previous Aristotle run (3ccc4914) almost every lemma failed with:
    "Function expected at `updateArr`" / "Function expected at `step`" /
    "Function expected at `ValidState`"
  This was caused by `updateArr` being `private` in CamelUp.Model.Step.
  DO NOT reference `updateArr` by name anywhere in this file.
  Instead use `updateArr_size` (the public theorem exported from Step.lean).

  Other env notes:
    • `step   : GameState → Move → Option GameState`  (use `simp only [step] at h_step`
      or `unfold step at h_step` to unfold it)
    • `ValidState` is a *structure* with fields accessed as `h_valid.board_size`,
      `h_valid.camel_unique`, `h_valid.bag_sub`, `h_valid.bag_each_once`,
      `h_valid.scores_size`, `h_valid.tiles_size`, `h_valid.player_valid`,
      `h_valid.mods_size`
    • `GameState` fields: `board`, `finishedCamels`, `diceBag`, `modifiers`,
      `legBetTiles`, `scores`, `numPlayers`, `currentPlayer`
    • `numSquares : Nat` is a constant (= 16)

  ── PRIORITY ORDER (easiest first) ────────────────────────────────────────────
  1. BetLeg helpers (tiles_size, scores_size, player_valid):
       BetLeg only (a) calls `updateArr gs.legBetTiles idx rest` on legBetTiles
       and (b) advances the player. Everything else is unchanged.
       For tiles_size: use `updateArr_size` + `h_valid.tiles_size`.
       For scores_size: scores are untouched, numPlayers unchanged, use `h_valid.scores_size`.
       For player_valid: `gs'.currentPlayer = advancePlayer gs.currentPlayer gs.numPlayers`;
         use `advancePlayer_bound` (proved below).

  2. BetRaceWin / BetRaceLose helpers (fields_unchanged, player_valid × 2):
       These branches only append one entry to `raceWinBets` / `raceLoseBets` and
       advance the player. Board, bag, scores, tiles, modifiers are all untouched.
       `unfold step at h_step; split_ifs at h_step; simp_all` should expose the
       field equalities.

  3. PlaceTile helpers (board_unchanged, mods_size, player_valid):
       PlaceTile only writes `updateArr gs.modifiers sq tile` — all other fields
       unchanged. For mods_size: `updateArr_size` + `h_valid.mods_size`.

  4. Roll helpers (hardest — last):
       Roll calls `applyDie` then conditionally `resolveLegBets`.
       Use already-proved lemmas:
         • `applyDie_preserves_boardSize`  → board_size
         • `applyDie_preserves_camelCount` → camel_unique (each colour count preserved)
         • `resolveLegBets_scores_size`    → scores_size
         • `h_valid.bag_each_once` + List.count_erase_le_one' → bag_each_once
         • `h_valid.bag_sub` + List.mem_erase_sub' → bag_sub
       The diceBag after Roll is either `gs.diceBag.erase outcome.camel`
       (mid-leg) or `CamelColor.all` (leg end, when bag becomes empty).
       `CamelColor.all` is a literal list of all five colours — membership and
       count-≤-1 both hold by `decide`.

  ── ALREADY PROVED (do not re-prove) ─────────────────────────────────────────
  From CamelUp/Proofs/Invariants.lean (available via import):
    • applyDie_preserves_boardSize, applyDie_preserves_totalCount,
      applyDie_preserves_camelCount
    • resolveLegBets_scores_size, resolveRaceWinBets_scores_size
    • setStack_size, totalCamelCount_setStack

  From CamelUp/Model/Step.lean (available via import):
    • updateArr_size   : (updateArr arr i v).size = arr.size
    • awardPlayer_size : (awardPlayer scores p delta).size = scores.size

  Proved in this file (keep these, use them in Roll helpers):
    • advancePlayer_bound
    • List.mem_erase_sub', List.count_erase_le', List.count_erase_le_one'
-/
import Mathlib
import CamelUp.Model.Types
import CamelUp.Model.Step


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

namespace CamelUp

open CamelUp

/-! ## Utility: advancePlayer stays in bounds -/

/-- `advancePlayer` always produces a valid player index. -/
theorem advancePlayer_bound (cur n : Nat) (h : 0 < n) :
    advancePlayer cur n < n := by
  unfold advancePlayer
  simp [Nat.pos_iff_ne_zero.mp h]
  exact Nat.mod_lt _ h

/-! ## Utility: List.erase preserves invariants needed for diceBag -/

/-- Every element remaining after erase was in the original list. -/
theorem List.mem_erase_sub {α} [BEq α] [LawfulBEq α] (l : List α) (a : α) :
    ∀ x ∈ l.erase a, x ∈ l := by
  intro x hx
  exact List.mem_of_mem_erase hx

/-- Erasing an element cannot increase count of any element. -/
theorem List.count_erase_le {α} [BEq α] [LawfulBEq α] (l : List α) (a b : α) :
    (l.erase a).count b ≤ l.count b := by
  induction l with
  | nil => simp
  | cons h t ih =>
      simp [List.erase]
      split_ifs with heq
      · simp [List.count_cons]
        omega
      · simp [List.count_cons]
        omega

/-- If `a` appears at most once in `l`, it appears at most once after erase. -/
theorem List.count_erase_le_one {α} [BEq α] [LawfulBEq α] (l : List α) (a b : α)
    (h : l.count b ≤ 1) : (l.erase a).count b ≤ 1 :=
  Nat.le_trans (List.count_erase_le l a b) h

/-! ## Roll branch: field-by-field preservation -/

/-- After a legal Roll, the board size is still numSquares. -/
theorem step_Roll_board_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.board.size = numSquares := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState.board_size ];
  split_ifs at h_step <;> simp_all +decide [ CamelUp.ValidState.board_size ];
  · rw [ ← h_step.2 ] ; simp +decide [ CamelUp.ValidState.board_size ] ;
    unfold CamelUp.applyDie; simp +decide [ List.foldl ] ;
    cases h : CamelUp.findCamelOnBoard gs.board outcome.camel <;> simp +decide [ h ] at * ; simp_all +decide [ CamelUp.ValidState.board_size ] ;
    rw [ ← h_valid.board_size ] ; simp +decide [ CamelUp.Board.setStack ] ;
    -- The length of the list after setting the stack is equal to the original length because we're just replacing an element, not adding or removing any.
    have h_length : ∀ (l : List CamelUp.Stack) (i : Nat) (s : CamelUp.Stack), (CamelUp.Board.setStack.setAt s l i).length = l.length := by
      intros l i s; induction' l with hd tl ih generalizing i s <;> simp +decide [ CamelUp.Board.setStack.setAt ] ;
      cases i <;> simp +decide [ *, CamelUp.Board.setStack.setAt ];
    grind;
  · have h_size : ∀ (board : Board) (mods : Array (Option ModifierTile)) (finished : List CamelColor) (outcome : DieOutcome), (CamelUp.applyDie board mods finished outcome).1.size = board.size := by
      intros board mods finished outcome
      simp [CamelUp.applyDie];
      cases h : CamelUp.findCamelOnBoard board outcome.camel <;> simp +decide [ h ];
      split_ifs <;> simp +decide [ CamelUp.Board.setStack ];
      · -- The length of the list after setAt is the same as the original list's length.
        have h_length : ∀ (l : List CamelUp.Stack) (i : Nat) (v : List CamelUp.CamelColor), (CamelUp.Board.setStack.setAt v l i).length = l.length := by
          intros l i v; induction' l with hd tl ih generalizing i v <;> simp +decide [ *, CamelUp.Board.setStack.setAt ] ;
          cases i <;> simp +decide [ *, CamelUp.Board.setStack.setAt ];
        exact h_length _ _ _;
      · simp_all +decide [ CamelUp.DieValue.toNat ];
      · exact absurd ‹ ( ‹ℕ × ℕ›.1 = 0 ∧ outcome.value.toNat = 0 ) ›.2 ( by linarith [ Fin.is_lt outcome.value, show outcome.value.toNat > 0 from Nat.succ_pos _ ] );
      · -- The length of the list after setting a stack is equal to the original size of the board because we're just replacing an existing element.
        have h_length : ∀ (l : List (List CamelColor)) (i : Nat) (s : List CamelColor), (CamelUp.Board.setStack.setAt s l i).length = l.length := by
          intros l i s; induction' l with hd tl ih generalizing i s <;> simp +decide [ CamelUp.Board.setStack.setAt ] ;
          cases i <;> simp +decide [ *, CamelUp.Board.setStack.setAt ];
        exact h_length _ _ _;
      · -- The length of the list after setting the stack is equal to the original board's size because we're just replacing an element, not adding or removing any.
        have h_length : ∀ (l : List CamelUp.Stack) (i : Nat) (s : CamelUp.Stack), (CamelUp.Board.setStack.setAt s l i).length = l.length := by
          intros l i s; induction' l with hd tl ih generalizing i <;> simp +decide [ *, CamelUp.Board.setStack.setAt ] ;
          cases i <;> simp +decide [ *, CamelUp.Board.setStack.setAt ];
        convert h_length _ _ _ using 1;
        convert h_length _ _ _ |> Eq.symm using 1;
    rw [ ← h_step.2, h_size ] ; exact h_valid.board_size;
  · -- Since `applyDie` does not change the size of the board, the new board's size is the same as the original board's size.
    have h_board_size : (CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome).1.size = gs.board.size := by
      unfold CamelUp.applyDie;
      rcases h : CamelUp.findCamelOnBoard gs.board outcome.camel with ( _ | ⟨ sq, idx ⟩ ) <;> simp +decide [ h ];
      unfold CamelUp.Board.setStack; simp +decide [ List.length ] ;
      -- The setAt function replaces an element in the list without changing the list's length.
      have h_setAt_length : ∀ (l : List (List CamelUp.CamelColor)) (i : Nat) (v : List CamelUp.CamelColor), List.length (CamelUp.Board.setStack.setAt v l i) = List.length l := by
        intros l i v; induction' l with hd tl ih generalizing i; aesop;
        cases i <;> simp +decide [ *, CamelUp.Board.setStack.setAt ];
      split_ifs <;> simp_all +decide [ List.length ];
    exact h_step.2 ▸ h_board_size.trans h_valid.board_size

/- After a legal Roll, every colour appears exactly once across board + finished. -/
noncomputable section AristotleLemmas

open CamelUp

/-- Helper: Count of a camel on the board. -/
def countBoard (b : Board) (c : CamelColor) : Nat :=
  (List.range numSquares).foldl (fun acc i => acc + (b.getStack i).count c) 0

/-- Helper: Total count of a camel (board + finished). -/
def totalCamelCount (b : Board) (finished : List CamelColor) (c : CamelColor) : Nat :=
  finished.count c + countBoard b c

open CamelUp

/-- Helper: getStack after setStack. -/
theorem getStack_setStack (b : Board) (sq : Nat) (s : Stack) (i : Nat)
    (h_size : b.size = numSquares) :
    (b.setStack sq s).getStack i = if i = sq ∧ sq < numSquares then s else b.getStack i := by
      unfold CamelUp.Board.setStack;
      -- By definition of `setAt`, we can split into cases based on whether `i` equals `sq`.
      have h_setAt : ∀ (l : List Stack) (sq : Nat) (s : Stack), ∀ i, (CamelUp.Board.setStack.setAt s l sq).get! i = if i = sq ∧ sq < l.length then s else l.get! i := by
        intros l sq s i; induction' l with hd tl ih generalizing sq s i; aesop;
        rcases sq with ( _ | sq ) <;> rcases i with ( _ | i ) <;> simp_all +decide [ CamelUp.Board.setStack.setAt ];
      -- Apply the hypothesis `h_setAt` to the list `b.toList`.
      specialize h_setAt b.toList sq s i;
      unfold CamelUp.Board.getStack; aesop;

open CamelUp

/-- Helper: countBoard update rule. -/
theorem countBoard_setStack (b : Board) (sq : Nat) (s : Stack) (c : CamelColor)
    (h_size : b.size = numSquares) (h_sq : sq < numSquares) :
    countBoard (b.setStack sq s) c = countBoard b c - (b.getStack sq).count c + s.count c := by
      -- By definition of `countBoard`, we can split the sum into the sum over `sq` and the sum over all other squares.
      have h_split_sum : ∀ (b : Board) (sq : Nat) (s : Stack) (c : CamelColor), b.size = numSquares → sq < numSquares → countBoard (b.setStack sq s) c = countBoard b c - (b.getStack sq).count c + s.count c := by
        intros b sq s c h_size h_sq
        have h_split_sum : countBoard (b.setStack sq s) c = ∑ i ∈ Finset.range numSquares, (if i = sq then s.count c else (b.getStack i).count c) := by
          unfold CamelUp.countBoard;
          have h_split_sum : ∀ (i : Nat), (b.setStack sq s).getStack i = if i = sq then s else b.getStack i := by
            intros i
            simp [getStack_setStack, h_size, h_sq];
          induction' CamelUp.numSquares with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
          split_ifs <;> rfl;
        simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq' ];
        rw [ add_comm, show CamelUp.countBoard b c = ∑ x ∈ Finset.range CamelUp.numSquares, List.count c ( b.getStack x ) from ?_ ];
        · rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_range.mpr h_sq ), add_tsub_cancel_right ];
        · unfold CamelUp.countBoard;
          induction' CamelUp.numSquares with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
      exact h_split_sum b sq s c h_size h_sq

open CamelUp

/-- Helper: setStack preserves board size. -/
theorem Board.setStack_size (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).size = b.size := by
      -- The length of the list after setAt is equal to the length of the original list because we're just replacing an element, not adding or removing any.
      have h_length : ∀ (l : List CamelUp.Stack) (i : Nat) (s : CamelUp.Stack), (CamelUp.Board.setStack.setAt s l i).length = l.length := by
        -- By induction on the list, we can show that the length of the list after setAt is equal to the original length.
        intros l i s
        induction' l with x l ih generalizing i
        all_goals generalize_proofs at *;
        · cases i <;> rfl;
        · cases i <;> simp_all +decide [ CamelUp.Board.setStack.setAt ]
      generalize_proofs at *;
      convert h_length _ _ _

open CamelUp

/-- Helper: The count of a camel on a specific square is less than or equal to the total count on the board. -/
theorem count_le_countBoard (b : Board) (sq : Nat) (c : CamelColor) (h : sq < numSquares) :
    (b.getStack sq).count c ≤ countBoard b c := by
      -- The sum over all squares includes the count at sq, so the count at sq is less than or equal to the total count.
      have h_sum : List.sum (List.map (fun i => List.count c (b.getStack i)) (List.range numSquares)) = countBoard b c := by
        -- The sum of the counts in each stack is equal to the total count because the sum of the counts in each stack is the same as the sum of the counts in each stack.
        simp [CamelUp.countBoard];
        rw [ List.sum_eq_foldl ];
        conv => rw [ List.foldl_map ] ;
      rw [ ← h_sum ];
      convert List.le_sum_of_mem _;
      · infer_instance;
      · exact List.mem_map.mpr ⟨ sq, List.mem_range.mpr h, rfl ⟩

open CamelUp

theorem findCamelOnBoard_bounds (b : Board) (c : CamelColor) (sq idx : Nat) :
    findCamelOnBoard b c = some (sq, idx) → sq < numSquares := by
      intro h
      unfold CamelUp.findCamelOnBoard at h
      generalize_proofs at *;
      -- Since `List.range CamelUp.numSquares` is a list of numbers from `0` to `CamelUp.numSquares - 1`, any element in this list is less than `CamelUp.numSquares`.
      have h_sq_lt_numSquares : ∀ x ∈ List.range CamelUp.numSquares, x < CamelUp.numSquares := by
        exact fun x hx => List.mem_range.mp hx;
      -- By definition of `searchSquares`, if it returns `some (sq, idx)`, then `sq` must be an element of `List.range numSquares`.
      have h_sq_in_range : ∀ {l : List ℕ}, CamelUp.findCamelOnBoard.searchSquares b c l = Option.some (sq, idx) → sq ∈ l := by
        intros l hl
        induction' l with sq' rest ih
        generalize_proofs at *;
        · cases hl;
        · unfold CamelUp.findCamelOnBoard.searchSquares at hl; aesop;
      exact h_sq_lt_numSquares _ ( h_sq_in_range h )

open CamelUp

theorem applyDie_preserves_totalCount (b : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome) (c : CamelColor)
    (h_size : b.size = numSquares) :
    let (b', f', _) := applyDie b mods finished outcome
    totalCamelCount b' f' c = totalCamelCount b finished c := by
      unfold CamelUp.applyDie;
      rcases h : CamelUp.findCamelOnBoard b outcome.camel with ( _ | ⟨ sq, idx ⟩ ) <;> simp +decide [ h ];
      split_ifs <;> simp +decide [ *, List.count_append ] at *;
      · unfold CamelUp.totalCamelCount; simp +decide [ *, List.count_append ] ;
        rw [ countBoard_setStack ];
        · have h_split : List.count c (b.getStack sq) = List.count c (List.take idx (b.getStack sq)) + List.count c (List.drop idx (b.getStack sq)) := by
            rw [ ← List.count_append, List.take_append_drop ];
          linarith [ Nat.sub_add_cancel ( show List.count c ( b.getStack sq ) ≤ CamelUp.countBoard b c from by simpa [ h_size ] using count_le_countBoard b sq c ( by linarith [ findCamelOnBoard_bounds b outcome.camel sq idx h ] ) ) ];
        · exact h_size;
        · exact?;
      · unfold CamelUp.numSquares at * ; simp_all +decide [ CamelUp.DieValue.toNat ];
      · exact absurd ‹sq = 0 ∧ outcome.value.toNat = 0›.2 ( by linarith [ Fin.is_lt outcome.value, show outcome.value.toNat > 0 from Nat.succ_pos _ ] );
      · unfold CamelUp.totalCamelCount; simp +decide [ *, List.count_append ] ;
        rw [ countBoard_setStack ];
        · linarith [ Nat.sub_add_cancel ( show List.count c ( b.getStack sq ) ≤ CamelUp.countBoard b c from by
                                            apply_rules [ count_le_countBoard ];
                                            linarith [ outcome.value.toNat ] ), show List.count c ( List.drop idx ( b.getStack sq ) ) + List.count c ( List.take idx ( b.getStack sq ) ) = List.count c ( b.getStack sq ) from by
                                                                                                                          rw [ add_comm, ← List.count_append, List.take_append_drop ] ];
        · exact h_size;
        · linarith;
      · -- Since the camel is just being moved from one stack to another, its count in the board should remain the same.
        have h_count : (b.getStack sq).count c = (List.take idx (b.getStack sq)).count c + (List.drop idx (b.getStack sq)).count c := by
          rw [ ← List.count_append, List.take_append_drop ];
        unfold CamelUp.totalCamelCount; simp +decide [ *, List.count_append ] ;
        -- Since the camel is just being moved from one stack to another, its count in the board should remain the same. Therefore, the total count of the camel in the board remains the same after the move.
        have h_count : countBoard b c = countBoard (b.setStack sq (List.take idx (b.getStack sq))) c + (b.getStack sq).count c - (List.take idx (b.getStack sq)).count c := by
          rw [ countBoard_setStack ];
          · rw [ tsub_add_eq_add_tsub ];
            · rw [ tsub_add_cancel_of_le ];
              · rw [ Nat.add_sub_cancel ];
              · exact le_add_of_le_of_nonneg ( count_le_countBoard b sq c ( by linarith ) ) ( Nat.zero_le _ );
            · apply count_le_countBoard;
              linarith [ show outcome.value.toNat > 0 from Nat.succ_pos _ ];
          · exact h_size;
          · linarith [ show outcome.value.toNat ≥ 1 from Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by cases outcome.value ; tauto ) ) ];
        rw [ countBoard_setStack ];
        · rw [ tsub_add_eq_add_tsub ];
          · grind;
          · apply count_le_countBoard;
            grind +ring;
        · rw [ ← h_size, Board.setStack_size ];
        · assumption

end AristotleLemmas

theorem step_Roll_camel_unique (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor,
      gs'.finishedCamels.count c +
      (List.range numSquares).foldl (fun acc i => acc + (gs'.board.getStack i).count c) 0 = 1 := by
  intro c
  have h_total : (gs'.finishedCamels.count c + (List.range numSquares).foldl (fun acc i => acc + (gs'.board.getStack i).count c) 0) = (gs.finishedCamels.count c + (List.range numSquares).foldl (fun acc i => acc + (gs.board.getStack i).count c) 0) := by
    have h_total : totalCamelCount gs'.board gs'.finishedCamels c = totalCamelCount gs.board gs.finishedCamels c := by
      convert applyDie_preserves_totalCount gs.board gs.modifiers gs.finishedCamels outcome c _;
      · unfold CamelUp.step at h_step; aesop;
      · unfold CamelUp.step at h_step; aesop;
      · exact h_valid.board_size;
    exact h_total;
  exact h_total.trans ( h_valid.camel_unique c )

/-- After a legal Roll, the remaining dice bag entries are all valid colours. -/
theorem step_Roll_bag_sub (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c ∈ gs'.diceBag, c ∈ CamelColor.all := by
  intro c hc
  -- gs'.diceBag = gs.diceBag.erase outcome.camel (mid-leg) or CamelColor.all (leg end)
  -- Both are subsets of CamelColor.all.
  rcases c with ( _ | _ | _ | _ | c ) <;> tauto;

/-- After a legal Roll, no colour appears twice in the remaining bag. -/
theorem step_Roll_bag_each_once (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor, gs'.diceBag.count c ≤ 1 := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; norm_num at h_step;
  split_ifs at h_step <;> simp_all +decide [ List.count ];
  · rintro c; rw [ ← h_step.2 ] ; simp +decide [ CamelUp.CamelColor.all ] ;
    rcases c with ( _ | _ | _ | _ | _ | c ) <;> trivial;
  · intro c; rw [ ← h_step.2 ] ;
    convert List.count_erase_le_one _ _ _ _;
    · refine' { .. };
      · exact fun { a } => by cases a <;> rfl;
      · exact fun { a b } h => by cases a <;> cases b <;> trivial;
    · exact h_valid.bag_each_once c;
  · aesop

/-- After a legal Roll, the scores array length is preserved. -/
theorem step_Roll_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  -- numPlayers is invariant; scores grow only via awardPlayer/resolveLegBets/etc.,
  -- all of which preserve size by awardPlayer_size / resolveLegBets_scores_size.
  -- By definition of ` awardPlayer`, the size of the scores array does not change.
  have h_scores_size : ∀ (scores : Array Int) (p : Nat) (delta : Int), (awardPlayer scores p delta).size = scores.size := by
    exact?;
  unfold CamelUp.step at h_step;
  unfold CamelUp.resolveLegBets at *;
  unfold CamelUp.resolveRaceWinBets at *; unfold CamelUp.resolveRaceLoseBets at *; simp_all +decide [ h_scores_size ] ;
  split_ifs at h_step <;> simp_all +decide [ h_scores_size ];
  · rw [ ← h_step.2.2 ];
    induction' gs.legBetsPlaced using List.reverseRecOn with bet bets ih <;> simp_all +decide [ h_scores_size ];
    cases h : ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 <;> simp_all +decide [ h_scores_size ];
    · exact h_valid.scores_size;
    · exact h_valid.scores_size;
  · cases h : ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 <;> simp_all +decide [ h_scores_size ];
    · have := h_valid.scores_size; aesop;
    · have := h_valid.scores_size; aesop;
  · rcases h_step with ⟨ h₁, h₂, rfl ⟩ ; simp +decide [ h₁, h₂, h_scores_size ] ;
    induction' gs.raceBetsLose using List.reverseRecOn with bet bets ih <;> simp +decide [ * ];
    · induction' gs.raceBetsWin using List.reverseRecOn with bet bets ih <;> simp +decide [ * ];
      · induction' gs.legBetsPlaced using List.reverseRecOn with bet bets ih <;> simp +decide [ * ];
        cases h : ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 <;> simp +decide [ * ];
        · exact h_valid.scores_size;
        · exact h_valid.scores_size;
      · grind +ring;
    · grind +ring

/-- After a legal Roll, legBetTiles still has 5 entries. -/
theorem step_Roll_tiles_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.legBetTiles.size = 5 := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide;
  split_ifs at h_step <;> simp_all +decide [ CamelUp.ValidState.scores_size ];
  · aesop;
  · exact h_step.2 ▸ h_valid.tiles_size;
  · rw [ ← h_step.2 ] ; exact h_valid.tiles_size

/-- After a legal Roll, modifiers array size is still numSquares. -/
theorem step_Roll_mods_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.modifiers.size = numSquares := by
  have := h_valid.mods_size;
  unfold CamelUp.step at h_step; aesop;

/-- After a legal Roll, currentPlayer is in range. -/
theorem step_Roll_player_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.Roll outcome) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  intro hn
  -- gs'.currentPlayer = advancePlayer gs.currentPlayer gs.numPlayers
  -- advancePlayer_bound gives the result.
  -- By definition of `advancePlayer`, if `gs'.numPlayers > 0`, then `advancePlayer gs(_.currentPlayer) gs'.numPlayers` is also less than `gs'.numPlayers`.
  have h_advance : ∀ (cur n : Nat), 0 < n → advancePlayer cur n < n := by
    exact?;
  unfold CamelUp.step at h_step ; aesop;

/-! ## BetLeg branch -/

/-- BetLeg does not touch the board, finished camels, bag, or modifiers. -/
theorem step_BetLeg_board_unchanged (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_step : step gs (Move.BetLeg c) = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.modifiers = gs.modifiers := by
  unfold step at h_step
  simp at h_step
  split_ifs at h_step with hgo htiles <;> simp_all
  · cases htiles
  · obtain ⟨_, rfl⟩ := Option.some.inj h_step
    simp

/-- After a legal BetLeg, legBetTiles still has 5 entries
    (updateArr does not change array size). -/
theorem step_BetLeg_tiles_size (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.legBetTiles.size = 5 := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide;
  rcases h : gs.legBetTiles[c.toIdx]?.getD [] with ( _ | ⟨ tileVal, rest ⟩ ) <;> simp_all +decide;
  convert h_valid.tiles_size using 1;
  rw [ ← h_step ] ; exact?;

/-- After a legal BetLeg, scores size is preserved (scores untouched). -/
theorem step_BetLeg_scores_size (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.scores.size = gs'.numPlayers := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState.scores_size ];
  cases h : gs.legBetTiles[c.toIdx]?.getD [] <;> simp_all +decide [ CamelUp.ValidState.scores_size ];
  exact h_step ▸ h_valid.scores_size

/-- After a legal BetLeg, currentPlayer is in range. -/
theorem step_BetLeg_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetLeg c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState ];
  intros h_pos;
  rcases h : gs.legBetTiles[c.toIdx]?.getD [] with ( _ | ⟨ tileVal, rest ⟩ ) <;> simp_all +decide;
  subst h_step;
  exact?

/-! ## BetRaceWin / BetRaceLose branches (symmetric) -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid projection: Expected a value whose type is a structure
  move
has type
  CamelUp.Move
Invalid projection: Expected a value whose type is a structure
  move
has type
  CamelUp.Move-/
/-- BetRaceWin / BetRaceLose only append to the bet lists; all other fields unchanged. -/
theorem step_BetRace_fields_unchanged (gs : GameState) (move : Move) (gs' : GameState)
    (h_move : move = Move.BetRaceWin move.1 ∨ move = Move.BetRaceLose move.1)
    (h_step : step gs move = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.modifiers = gs.modifiers ∧
    gs'.scores = gs.scores ∧ gs'.legBetTiles = gs.legBetTiles := by
  sorry

/-- After BetRaceWin, currentPlayer is in range. -/
theorem step_BetRaceWin_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetRaceWin c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState ];
  cases h : gs.numPlayers <;> simp_all +decide [ CamelUp.advancePlayer ];
  · cases h_valid ; aesop;
  · exact fun _ => by subst_vars; exact Nat.mod_lt _ ( Nat.succ_pos _ ) ;

/-- After BetRaceLose, currentPlayer is in range. -/
theorem step_BetRaceLose_player_valid (gs : GameState) (c : CamelColor) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.BetRaceLose c) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  unfold CamelUp.step at h_step;
  -- By definition of `advancePlayer`, if `n` is positive, then `(cur + 1) % n` is less than `n`.
  intros hn_pos
  have h_mod : (gs.currentPlayer + 1) % gs.numPlayers < gs.numPlayers := by
    exact Nat.mod_lt _ ( Nat.pos_of_ne_zero ( by aesop_cat ) );
  cases h : gs.numPlayers <;> aesop

/-! ## PlaceTile branch -/

/-- PlaceTile does not change the board stacks only the modifiers array. -/
theorem step_PlaceTile_board_unchanged (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_step : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.board = gs.board ∧ gs'.finishedCamels = gs.finishedCamels ∧
    gs'.diceBag = gs.diceBag ∧ gs'.scores = gs.scores ∧
    gs'.legBetTiles = gs.legBetTiles := by
  unfold CamelUp.step at h_step; aesop;

/-- After PlaceTile, modifiers array has size numSquares (updateArr preserves size). -/
theorem step_PlaceTile_mods_size (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.modifiers.size = numSquares := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState.mods_size ];
  rcases h_step with ⟨ _, _, _, _, rfl ⟩ ; exact (by
  exact h_valid.mods_size ▸ by exact?;)

/-- After PlaceTile, currentPlayer is in range. -/
theorem step_PlaceTile_player_valid (gs : GameState) (sq : Nat) (pos : Bool) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs (Move.PlaceTile sq pos) = some gs') :
    gs'.numPlayers > 0 → gs'.currentPlayer < gs'.numPlayers := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step ; simp_all +decide [ CamelUp.advancePlayer ];
  cases h : gs.numPlayers <;> simp_all +decide [ Nat.mod_eq_of_lt ];
  · cases h_valid ; aesop;
  · rw [ ← h_step.2.2.2.2 ] ; simp +decide [ Nat.mod_lt ]

/-! ## Main theorem — uses all helpers above -/

/-- Every legal step preserves all ValidState invariants. -/
theorem step_preserves_valid
    (gs : GameState) (move : Move) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs move = some gs') :
    ValidState gs' := by
  -- Case split on the move type, then apply per-field helpers.
  match move with
  | .Roll outcome => exact {
      board_size   := step_Roll_board_size   gs outcome gs' h_valid h_step
      camel_unique := step_Roll_camel_unique gs outcome gs' h_valid h_step
      bag_sub      := step_Roll_bag_sub      gs outcome gs' h_valid h_step
      bag_each_once:= step_Roll_bag_each_once gs outcome gs' h_valid h_step
      scores_size  := step_Roll_scores_size  gs outcome gs' h_valid h_step
      tiles_size   := step_Roll_tiles_size   gs outcome gs' h_valid h_step
      player_valid := step_Roll_player_valid gs outcome gs' h_valid h_step
      mods_size    := step_Roll_mods_size    gs outcome gs' h_valid h_step }
  | .BetLeg c => exact {
      board_size   := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.1, h_valid.board_size]
      camel_unique := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.1, this.2.1]; exact h_valid.camel_unique
      bag_sub      := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.2.2.1]; exact h_valid.bag_sub
      bag_each_once:= by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.2.2.1]; exact h_valid.bag_each_once
      scores_size  := step_BetLeg_scores_size gs c gs' h_valid h_step
      tiles_size   := step_BetLeg_tiles_size  gs c gs' h_valid h_step
      player_valid := step_BetLeg_player_valid gs c gs' h_valid h_step
      mods_size    := by have := step_BetLeg_board_unchanged gs c gs' h_step; simp [this.2.2.2]; exact h_valid.mods_size }
  | .BetRaceWin c => exact {
      board_size   := by simp [step] at h_step; simp_all; exact h_valid.board_size
      camel_unique := by simp [step] at h_step; simp_all; exact h_valid.camel_unique
      bag_sub      := by simp [step] at h_step; simp_all; exact h_valid.bag_sub
      bag_each_once:= by simp [step] at h_step; simp_all; exact h_valid.bag_each_once
      scores_size  := by simp [step] at h_step; simp_all; exact h_valid.scores_size
      tiles_size   := by simp [step] at h_step; simp_all; exact h_valid.tiles_size
      player_valid := step_BetRaceWin_player_valid gs c gs' h_valid h_step
      mods_size    := by simp [step] at h_step; simp_all; exact h_valid.mods_size }
  | .BetRaceLose c => exact {
      board_size   := by simp [step] at h_step; simp_all; exact h_valid.board_size
      camel_unique := by simp [step] at h_step; simp_all; exact h_valid.camel_unique
      bag_sub      := by simp [step] at h_step; simp_all; exact h_valid.bag_sub
      bag_each_once:= by simp [step] at h_step; simp_all; exact h_valid.bag_each_once
      scores_size  := by simp [step] at h_step; simp_all; exact h_valid.scores_size
      tiles_size   := by simp [step] at h_step; simp_all; exact h_valid.tiles_size
      player_valid := step_BetRaceLose_player_valid gs c gs' h_valid h_step
      mods_size    := by simp [step] at h_step; simp_all; exact h_valid.mods_size }
  | .PlaceTile sq pos => exact {
      board_size   := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.1, h_valid.board_size]
      camel_unique := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.1, this.2.1]; exact h_valid.camel_unique
      bag_sub      := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.1]; exact h_valid.bag_sub
      bag_each_once:= by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.1]; exact h_valid.bag_each_once
      scores_size  := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.2.1]; exact h_valid.scores_size
      tiles_size   := by have := step_PlaceTile_board_unchanged gs sq pos gs' h_step; simp [this.2.2.2.2]; exact h_valid.tiles_size
      player_valid := step_PlaceTile_player_valid gs sq pos gs' h_valid h_step
      mods_size    := step_PlaceTile_mods_size gs sq pos gs' h_valid h_step }

end CamelUp