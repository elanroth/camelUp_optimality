/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6adf4117-9966-430e-9fc7-29c91e408cb5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem step_preserves_valid
    (gs : GameState) (move : Move) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs move = some gs') :
    ValidState gs'

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

-- CamelUp.Proofs.Invariants
-- Lemma statements about GameState validity.
-- Aristotle batch dd3275b3 proved applyDie_preserves_totalCount and
-- applyDie_preserves_camelCount (plus all helper lemmas).
-- Remaining sorry: step_preserves_valid.
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

/-! ## Board.setStack preserves array size -/

theorem setStack_size (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).size = b.size := by
  have h_size : ∀ (arr : Array (List CamelColor)) (i : Nat) (v : List CamelColor),
      (arr.set! i v).size = arr.size := by aesop
  convert h_size b sq s using 1
  have h_setAt_eq : ∀ (arr : Array (List CamelColor)) (i : Nat) (v : List CamelColor),
      (arr.set! i v).toList = (CamelUp.Board.setStack.setAt v arr.toList i) := by
    intros arr i v
    simp [CamelUp.Board.setStack.setAt]
    induction arr.toList generalizing i; aesop
    cases i <;> aesop
  convert congr_arg Array.size (congr_arg Array.mk (h_setAt_eq b sq s)) using 1
  · unfold CamelUp.Board.setStack; aesop
  · rw [← h_setAt_eq]

/-! ## applyDie preserves invariants -/

/- Conservation of camels: total count (board + finished) unchanged by a roll. -/
noncomputable section AristotleLemmas

/-
Updating a list of lists at index `i` changes the sum of lengths. Specifically,
the new sum plus the old length at `i` equals the old sum plus the new length.
This formulation avoids natural number subtraction issues.
-/
theorem List.sum_map_length_set_add {α} (L : List (List α)) (i : Nat) (s : List α) (h : i < L.length) :
    ((L.set i s).map List.length).sum + (L.get ⟨i, h⟩).length = (L.map List.length).sum + s.length := by
  induction' L with hd tl ih generalizing i s <;> simp_all ( config := { decide := Bool.true } ) [ List.get ];
  · contradiction;
  · rcases i with ( _ | i ) <;> simp_all ( config := { decide := Bool.true } ) [ List.set ];
    · ring;
    · linarith [ ih i s ( by simpa using h ) ]

/-- `Board.setStack` is equivalent to `List.set` on the underlying list. -/
theorem setStack_eq_set (b : Board) (sq : Nat) (s : Stack) :
    (b.setStack sq s).toList = b.toList.set sq s := by
  unfold CamelUp.Board.setStack;
  induction' b.toList with l ih generalizing sq;
  · cases sq <;> aesop;
  · cases sq <;> simp_all +decide [ CamelUp.Board.setStack.setAt ]

/--
The sum of stack lengths on the board computed via `foldl` over indices is equal
to the sum of lengths of the list of stacks.
-/
theorem board_sum_eq_foldl (b : Board) :
    (List.range b.size).foldl (fun acc i => acc + (b.getStack i).length) 0 = (b.toList.map List.length).sum := by
  have h_eq : List.foldl (fun acc i => acc + List.length (b.getStack i)) 0 (List.range (Array.size b)) = List.sum (List.map (fun i => List.length (b.getStack i)) (List.range (Array.size b))) := by
    induction' ( List.range b.size ) using List.reverseRecOn with l ih <;> simp +decide [ * ];
  rw [ h_eq ];
  have h_sum_eq : List.map (fun i => List.length (b.getStack i)) (List.range (Array.size b)) = List.map (fun s => List.length s) b.toList := by
    refine' List.ext_get _ _ <;> simp +decide [ CamelUp.Board.getStack ];
    aesop;
  rw [h_sum_eq]

/-- Updating a stack on the board changes the total camel count by the difference in stack lengths. -/
theorem sum_setStack_helper (b : Board) (sq : Nat) (s : Stack) (h : sq < numSquares) (hb : b.size = numSquares) :
    ((b.setStack sq s).toList.map List.length).sum + (b.getStack sq).length = (b.toList.map List.length).sum + s.length := by
  rw [ CamelUp.setStack_eq_set ];
  convert List.sum_map_length_set_add b.toList sq s _ using 1;
  all_goals norm_num [ hb, h ];
  unfold CamelUp.Board.getStack; aesop;

end AristotleLemmas

theorem applyDie_preserves_totalCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (h : board.size = numSquares) :
    let (board', finished', _) := applyDie board mods finished outcome
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).length) 0
      + finished'.length =
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).length) 0
      + finished.length := by
  unfold CamelUp.applyDie;
  rcases h : CamelUp.findCamelOnBoard board outcome.camel with ( _ | ⟨ sq, idx ⟩ ) <;> simp +decide [ h ];
  split_ifs <;> simp +decide [ CamelUp.board_sum_eq_foldl ];
  · have h_sum_setStack : ((board.setStack sq (List.take idx (board.getStack sq))).toList.map List.length).sum + (board.getStack sq).length = (board.toList.map List.length).sum + (List.take idx (board.getStack sq)).length := by
      apply_rules [ CamelUp.sum_setStack_helper ];
      contrapose! h; simp_all +decide [ CamelUp.findCamelOnBoard ] ;
      have h_contra : ∀ {l : List ℕ}, (∀ sq ∈ l, sq < CamelUp.numSquares) → ∀ {c : CamelUp.CamelColor}, ∀ {acc : Option (ℕ × ℕ)}, CamelUp.findCamelOnBoard.searchSquares board c l = acc → acc = none ∨ ∃ sq' idx', acc = some (sq', idx') ∧ sq' < CamelUp.numSquares := by
        intros l hl c acc hacc; induction' l with sq l ih generalizing acc <;> simp_all +decide [ CamelUp.findCamelOnBoard.searchSquares ] ;
        cases h : CamelUp.findCamelOnBoard.searchSquares.searchStack c ( board.getStack sq ) 0 <;> aesop;
      grind;
    have h_sum_setStack : (List.foldl (fun acc i => acc + List.length ((board.setStack sq (List.take idx (board.getStack sq))).getStack i)) 0 (List.range CamelUp.numSquares)) = (List.map List.length (board.setStack sq (List.take idx (board.getStack sq))).toList).sum := by
      convert CamelUp.board_sum_eq_foldl _ using 1;
      rw [ ← ‹Array.size board = CamelUp.numSquares›, CamelUp.setStack_size ]
    have h_sum_setStack' : (List.foldl (fun acc i => acc + List.length (board.getStack i)) 0 (List.range CamelUp.numSquares)) = (List.map List.length board.toList).sum := by
      convert CamelUp.board_sum_eq_foldl board using 1 ; aesop;
    simp_all +decide [ add_assoc, add_tsub_cancel_of_le ] ;
    cases min_cases idx ( List.length ( board.getStack sq ) ) <;> simp_all +decide [ add_assoc, add_tsub_cancel_of_le ] ; linarith [ Nat.sub_add_cancel ( show idx ≤ List.length ( board.getStack sq ) from by
                                                                                                                                                          assumption ) ] ;
  · rcases outcome with ⟨ _ | _, _ | _ ⟩ <;> simp_all +decide [ CamelUp.DieValue.toNat ];
  · cases outcome.value ; simp_all +decide [ CamelUp.DieValue.toNat ];
  · have h_sum_setStack : ((board.setStack sq (List.take idx (board.getStack sq))).toList.map List.length).sum + (board.getStack sq).length = (board.toList.map List.length).sum + (List.take idx (board.getStack sq)).length := by
      apply CamelUp.sum_setStack_helper;
      · linarith [ outcome.value.toNat ];
      · assumption;
    have h_sum_setStack : ((board.setStack sq (List.take idx (board.getStack sq))).toList.map List.length).sum + List.length (List.drop idx (board.getStack sq)) = (board.toList.map List.length).sum := by
      linarith [ show List.length ( List.take idx ( board.getStack sq ) ) + List.length ( List.drop idx ( board.getStack sq ) ) = List.length ( board.getStack sq ) from by rw [ List.length_take, List.length_drop ] ; omega ];
    convert congr_arg ( · + finished.length ) h_sum_setStack using 1 <;> ring!;
    · rw [ show List.foldl ( fun acc i => acc + List.length ( ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ).getStack i ) ) 0 ( List.range CamelUp.numSquares ) = List.sum ( List.map List.length ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ).toList ) from ?_ ] ; ring!;
      · rw [ List.length_drop ];
      · convert CamelUp.board_sum_eq_foldl _ using 1;
        rw [ setStack_size ] ; aesop;
    · rw [ add_comm, ← CamelUp.board_sum_eq_foldl ];
      rw [ ‹Array.size board = CamelUp.numSquares› ];
  · have h_sum_setStack : ∀ (b : CamelUp.Board) (sq : Nat) (s : CamelUp.Stack),
        sq < CamelUp.numSquares → b.size = CamelUp.numSquares →
        (List.foldl (fun acc i => acc + (CamelUp.Board.getStack (CamelUp.Board.setStack b sq s) i).length) 0 (List.range CamelUp.numSquares)) +
        (CamelUp.Board.getStack b sq).length =
        (List.foldl (fun acc i => acc + (CamelUp.Board.getStack b i).length) 0 (List.range CamelUp.numSquares)) +
        s.length := by
          intros b sq s hsq hb; exact (by
          convert CamelUp.sum_setStack_helper b sq s hsq hb using 1;
          · rw [ ← CamelUp.board_sum_eq_foldl ];
            rw [ setStack_size, hb ];
          · rw [ ← CamelUp.board_sum_eq_foldl ];
            rw [ hb ]);
    have := h_sum_setStack board sq ( List.take idx ( board.getStack sq ) ) ( by linarith ) ‹_›; have := h_sum_setStack ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ) ( match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => sq + outcome.value.toNat | Option.some tile => if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1 ) ( ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ).getStack ( match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => sq + outcome.value.toNat | Option.some tile => if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1 ) ++ List.drop idx ( board.getStack sq ) ) ( by
      grind +ring ) ( by
      rw [ setStack_size ] ; aesop ) ; simp_all +decide [ add_assoc ] ;
    cases min_cases idx ( List.length ( board.getStack sq ) ) <;> simp_all +decide [ add_assoc ];
    · cases h : mods[sq + outcome.value.toNat]?.getD Option.none <;> simp_all +decide [ add_assoc ];
      · grind;
      · linarith [ Nat.sub_add_cancel ‹_› ];
    · convert this using 1;
      cases mods[sq + outcome.value.toNat]?.getD Option.none <;> simp +decide [ * ]

set_option maxHeartbeats 4000000 in
theorem applyDie_preserves_boardSize
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (h : board.size = numSquares) :
    (applyDie board mods finished outcome).1.size = numSquares := by
  have h_setStack_size : ∀ (b : Board) (sq : Nat) (s : Stack),
      (b.setStack sq s).size = b.size := setStack_size
  unfold CamelUp.applyDie; aesop

noncomputable section AristotleLemmas2

/-- Definition of the total count of a specific camel color on the board. -/
def totalCamelCount (b : Board) (c : CamelColor) : Nat :=
  (List.range numSquares).foldl (fun acc i => acc + (b.getStack i).count c) 0

/-- If `findCamelOnBoard` finds a camel at square `sq`, then `sq < numSquares`. -/
theorem findCamelOnBoard_bounds (b : Board) (c : CamelColor) (sq idx : Nat)
    (h : findCamelOnBoard b c = some (sq, idx)) : sq < numSquares := by
  have h_sq_valid : sq ∈ List.range numSquares := by
    have h_search : ∀ (squares : List Nat), findCamelOnBoard.searchSquares b c squares = Option.some (sq, idx) → sq ∈ squares := by
      intros squares hsquares
      induction' squares with squares_sq squares_sq ih generalizing sq idx
      all_goals generalize_proofs at *;
      · cases hsquares;
      · unfold findCamelOnBoard.searchSquares at hsquares; aesop;
    exact h_search _ h
  generalize_proofs at *; (
  exact List.mem_range.mp h_sq_valid |> Nat.lt_of_lt_of_le <| by decide;)

/-- Retrieving the stack at the index just set returns the new stack (index in bounds). -/
theorem getStack_setStack_eq (b : Board) (sq : Nat) (s : Stack) (h : sq < b.size) :
    (b.setStack sq s).getStack sq = s := by
  simp only [Board.getStack, Board.setStack] at *; simp [h, Array.getD];
  have h_setAt_sq : (Board.setStack.setAt s b.toList sq)[sq]?.getD [] = s := by
    have h_setAt_sq : ∀ (l : List Stack) (sq : Nat) (s : Stack), sq < l.length → (Board.setStack.setAt s l sq)[sq]?.getD [] = s := by
      intros l sq s h_sq_lt_l_len
      induction' l with l_head l_tail ih generalizing sq s
      all_goals generalize_proofs at *;
      · contradiction;
      · rcases sq with ( _ | sq ) <;> simp_all +arith +decide [ Board.setStack.setAt ];
    exact h_setAt_sq _ _ _ ( by simpa using h );
  aesop

/-- Setting a stack at `sq` does not change stacks at other squares. -/
theorem getStack_setStack_ne (b : Board) (sq i : Nat) (s : Stack) (h_ne : i ≠ sq) :
    (b.setStack sq s).getStack i = b.getStack i := by
  unfold Board.setStack Board.getStack;
  have h_setAt : ∀ (l : List Stack) (s : Stack) (sq : Nat) (i : Nat), i ≠ sq → (Board.setStack.setAt s l sq).getD i [] = l.getD i [] := by
    intros l s sq i hi;
    induction' l with l_head l_tail ih generalizing sq i;
    · exact?;
    · rcases sq with ( _ | sq ) <;> rcases i with ( _ | i ) <;> simp_all +decide [ Board.setStack.setAt ];
  aesop

/--
Updating a stack at `sq` changes the total camel count by `new_count - old_count`.
Expressed as an equality of sums to avoid subtraction issues.
-/
theorem totalCamelCount_setStack (b : Board) (sq : Nat) (s : Stack) (c : CamelColor)
    (h_size : b.size = numSquares) (h_sq : sq < numSquares) :
    totalCamelCount (b.setStack sq s) c + (b.getStack sq).count c =
    totalCamelCount b c + s.count c := by
  unfold totalCamelCount;
  have h_split : List.foldl (fun acc i => acc + List.count c ((b.setStack sq s).getStack i)) 0 (List.range CamelUp.numSquares) =
    List.foldl (fun acc i => acc + List.count c (b.getStack i)) 0 (List.range CamelUp.numSquares) +
    List.count c s - List.count c (b.getStack sq) := by
      have h_split : List.foldl (fun acc i => acc + List.count c ((b.setStack sq s).getStack i)) 0 (List.range CamelUp.numSquares) = ∑ i ∈ Finset.range CamelUp.numSquares, List.count c ((b.setStack sq s).getStack i) ∧ List.foldl (fun acc i => acc + List.count c (b.getStack i)) 0 (List.range CamelUp.numSquares) = ∑ i ∈ Finset.range CamelUp.numSquares, List.count c (b.getStack i) := by
        induction' CamelUp.numSquares with n ih <;> simp_all +decide [ Finset.sum_range_succ, List.range_succ ];
      rw [ h_split.left, h_split.right, tsub_eq_of_eq_add ];
      have h_split : ∑ i ∈ Finset.range CamelUp.numSquares, List.count c ((b.setStack sq s).getStack i) = ∑ i ∈ Finset.range CamelUp.numSquares, (if i = sq then List.count c s else List.count c (b.getStack i)) := by
        refine' Finset.sum_congr rfl fun i hi => _;
        split_ifs <;> simp_all +decide [ CamelUp.getStack_setStack_eq, CamelUp.getStack_setStack_ne ];
      simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
      rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_range.mpr h_sq ), add_comm ] ; ring;
  rw [ h_split, tsub_add_cancel_of_le ];
  refine' le_add_of_le_of_nonneg _ _;
  · have h_split : List.foldl (fun acc i => acc + List.count c (b.getStack i)) 0 (List.range CamelUp.numSquares) = List.sum (List.map (fun i => List.count c (b.getStack i)) (List.range CamelUp.numSquares)) := by
      rw [ List.sum_eq_foldl ];
      rw [ List.foldl_map ];
    exact h_split.symm ▸ List.le_sum_of_mem ( List.mem_map.mpr ⟨ sq, List.mem_range.mpr h_sq, rfl ⟩ );
  · exact Nat.zero_le _

end AristotleLemmas2

theorem applyDie_preserves_camelCount
    (board : Board) (mods : Array (Option ModifierTile))
    (finished : List CamelColor) (outcome : DieOutcome)
    (c : CamelColor) (h : board.size = numSquares) :
    let (board', finished', _) := applyDie board mods finished outcome
    finished'.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board'.getStack i).count c) 0 =
    finished.count c +
    (List.range numSquares).foldl (fun acc i => acc + (board.getStack i).count c) 0 := by
  by_cases h_find : findCamelOnBoard board outcome.camel = none;
  · unfold CamelUp.applyDie; aesop;
  · obtain ⟨sq, idx, h_sq, h_idx⟩ : ∃ sq idx, findCamelOnBoard board outcome.camel = some (sq, idx) ∧ sq < numSquares := by
      obtain ⟨ sq, idx ⟩ := Option.ne_none_iff_exists'.mp h_find;
      exact ⟨ sq.1, sq.2, idx, by have := CamelUp.findCamelOnBoard_bounds board outcome.camel sq.1 sq.2 idx; aesop ⟩;
    unfold CamelUp.applyDie;
    simp [h_sq] at *;
    split_ifs <;> simp_all +decide [ List.count_append ];
    · have h_totalCamelCount_setStack : CamelUp.totalCamelCount (board.setStack sq (List.take idx (board.getStack sq))) c + (board.getStack sq).count c = CamelUp.totalCamelCount board c + (List.take idx (board.getStack sq)).count c := by
        apply CamelUp.totalCamelCount_setStack board sq (List.take idx (board.getStack sq)) c h h_idx;
      have h_count_split : (board.getStack sq).count c = (List.take idx (board.getStack sq)).count c + (List.drop idx (board.getStack sq)).count c := by
        rw [ ← List.count_append, List.take_append_drop ];
      linarith!;
    · cases mods[0]?.getD Option.none <;> simp_all +decide [ CamelUp.DieValue.toNat ];
    · unfold CamelUp.DieValue.toNat at * ; aesop ( simp_config := { decide := true } ) ;
    · have h_totalCamelCount_setStack : CamelUp.totalCamelCount (board.setStack sq (List.take idx (board.getStack sq))) c + (board.getStack sq).count c = CamelUp.totalCamelCount board c + (List.take idx (board.getStack sq)).count c := by
        apply CamelUp.totalCamelCount_setStack; assumption; assumption;
      generalize_proofs at *; (
      have h_totalCamelCount_setStack : (List.drop idx (board.getStack sq)).count c + (List.take idx (board.getStack sq)).count c = (board.getStack sq).count c := by
        rw [ add_comm, ← List.count_append, List.take_append_drop ]
      generalize_proofs at *; (
      linarith! [ CamelUp.totalCamelCount ( board.setStack sq ( List.take idx ( board.getStack sq ) ) ) c ] ;));
    · have h_totalCamelCount_setStack : ∀ (b : CamelUp.Board) (sq : Nat) (s : CamelUp.Stack) (c : CamelUp.CamelColor), b.size = CamelUp.numSquares → sq < CamelUp.numSquares → (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack (b.setStack sq s) i)) 0 (List.range CamelUp.numSquares)) + List.count c (CamelUp.Board.getStack b sq) = (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack b i)) 0 (List.range CamelUp.numSquares)) + List.count c s := by
        intros b sq s c hb hsq;
        convert CamelUp.totalCamelCount_setStack b sq s c hb hsq using 1;
      have h_totalCamelCount_setStack : (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack ((board.setStack sq (List.take idx (board.getStack sq))).setStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1 ((board.setStack sq (List.take idx (board.getStack sq))).getStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1 ++ List.drop idx (board.getStack sq))) i)) 0 (List.range CamelUp.numSquares)) + List.count c ((board.setStack sq (List.take idx (board.getStack sq))).getStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1) = (List.foldl (fun acc i => acc + List.count c (CamelUp.Board.getStack (board.setStack sq (List.take idx (board.getStack sq))) i)) 0 (List.range CamelUp.numSquares)) + List.count c ((board.setStack sq (List.take idx (board.getStack sq))).getStack (match mods[sq + outcome.value.toNat]?.getD Option.none with | Option.none => (sq + outcome.value.toNat, Option.none) | Option.some tile => (if 0 < tile.effect then sq + outcome.value.toNat + 1 else sq + outcome.value.toNat - 1, Option.some tile.owner)).1 ++ List.drop idx (board.getStack sq)) := by
          apply_assumption
          generalize_proofs at *; (
          rw [ ← h, CamelUp.setStack_size ]);
          assumption
      generalize_proofs at *; (
      cases h : mods[sq + outcome.value.toNat]?.getD Option.none <;> simp_all +decide [ List.count_append ] ; ring!;
      · have h_totalCamelCount_setStack : List.count c (List.take idx (board.getStack sq)) + List.count c (List.drop idx (board.getStack sq)) = List.count c (board.getStack sq) := by
          rw [ ← List.count_append, List.take_append_drop ]
        generalize_proofs at *; (
        grind);
      · have h_totalCamelCount_setStack : List.count c (List.take idx (board.getStack sq)) + List.count c (List.drop idx (board.getStack sq)) = List.count c (board.getStack sq) := by
          rw [ ← List.count_append, List.take_append_drop ]
        generalize_proofs at *; (
        grind +ring))

/-! ## step preserves ValidState (all move types) -/

/- The central safety property: every legal step preserves all ValidState invariants.

    This covers all four move types: Roll, BetLeg, BetRaceWin, BetRaceLose.
    The Roll case is the hard one (requires applyDie_preserves_camelCount et al.).
    The bet cases are straightforward since they don't touch the board. -/
noncomputable section AristotleLemmas

/-
The function `resolveLegBets` updates scores but does not change the size of the scores array.
-/
open CamelUp

theorem resolveLegBets_size (scores : Array Int) (ranking : List CamelColor) (bets : List LegBetEntry) :
    (resolveLegBets scores ranking bets).size = scores.size := by
      induction' bets using List.reverseRecOn with bets ih;
      · rfl;
      · convert awardPlayer_size ( CamelUp.resolveLegBets scores ranking bets ) ih.player _ using 1;
        convert rfl;
        convert rfl;
        unfold CamelUp.resolveLegBets; simp +decide [ CamelUp.awardPlayer ] ;
        congr! 1;
        exact?

/-
The function `resolveRaceWinBets` updates scores but does not change the size of the scores array.
-/
open CamelUp

theorem resolveRaceWinBets_size (scores : Array Int) (winner : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceWinBets scores winner bets).size = scores.size := by
      -- By definition of `awardPlayer`, the size of the array remains the same after applying it.
      have h_awardPlayer_size (scores : Array ℤ) (p : Nat) (delta : Int) : (awardPlayer scores p delta).size = scores.size := by
        exact?;
      induction' bets using List.reverseRecOn with bets ih <;> simp_all ( config := { decide := Bool.true } ) [ CamelUp.resolveRaceWinBets ];
      grind

/-
The function `resolveRaceLoseBets` updates scores but does not change the size of the scores array.
-/
open CamelUp

theorem resolveRaceLoseBets_size (scores : Array Int) (loser : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceLoseBets scores loser bets).size = scores.size := by
      convert resolveRaceWinBets_size scores loser bets using 1

/-
`advancePlayer` returns a value strictly less than `n` (the number of players), provided `n > 0`.
-/
open CamelUp

theorem advancePlayer_lt (cur : Nat) (n : Nat) (h : n > 0) :
    advancePlayer cur n < n := by
      unfold CamelUp.advancePlayer;
      split_ifs <;> [ linarith; exact Nat.mod_lt _ h ]

/-
Each camel color appears at most once in `CamelColor.all`.
-/
open CamelUp

theorem CamelColor_all_count_le_one (c : CamelColor) :
    CamelColor.all.count c ≤ 1 := by
      rcases c with ( _ | _ | _ | _ | _ | c ) <;> trivial

/-
The size of `initialLegBetTiles` is 5.
-/
open CamelUp

theorem initialLegBetTiles_size : initialLegBetTiles.size = 5 := by
  rfl

/-
Removing an element from a list of valid camel colors preserves the property that all elements are valid camel colors.
-/
open CamelUp

theorem bag_sub_erase (bag : List CamelColor) (c : CamelColor) (h : ∀ x ∈ bag, x ∈ CamelColor.all) :
    ∀ x ∈ bag.erase c, x ∈ CamelColor.all := by
      exact fun x hx => h x <| List.mem_of_mem_erase hx

/-
Removing an element from a list where each element appears at most once preserves this property.
-/
open CamelUp

theorem bag_each_once_erase (bag : List CamelColor) (c : CamelColor) (h : ∀ x, bag.count x ≤ 1) :
    ∀ x, (bag.erase c).count x ≤ 1 := by
      intro x;
      specialize h x;
      rcases eq_or_ne x c with rfl | hx <;> simp_all +decide [ List.count ];
      · have h_countP_erase : ∀ {l : List CamelUp.CamelColor} {x : CamelUp.CamelColor}, List.countP (fun y => y == x) (List.erase l x) ≤ List.countP (fun y => y == x) l := by
          intros l x; induction' l with y l ih <;> simp_all +decide [ List.countP_cons ] ;
          by_cases hy : y == x <;> simp_all +decide [ List.erase_cons ];
        exact le_trans ( h_countP_erase ) h;
      · rw [ List.countP_eq_length_filter ] at *;
        refine' le_trans _ h;
        have h_erase : ∀ {l : List CamelColor}, (List.filter (fun y => y == x) (List.erase l c)).length ≤ (List.filter (fun y => y == x) l).length := by
          intros l; induction' l with y l ih <;> simp_all +decide [ List.filter_cons ] ;
          grind;
        apply h_erase

/-
The `Roll` move preserves the size of the scores array, which remains equal to `numPlayers`.
This holds because `awardPlayer` and the bet resolution functions (`resolveLegBets`, `resolveRaceWinBets`, `resolveRaceLoseBets`) all preserve the size of the scores array.
-/
open CamelUp

theorem step_roll_preserves_scores_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step : step gs (Move.Roll outcome) = some gs') :
    gs'.scores.size = gs.numPlayers := by
      unfold CamelUp.step at h_step;
      split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState.scores_size ];
      rcases h : ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 with ( _ | p ) <;> simp_all +decide [ CamelUp.awardPlayer_size ];
      · split_ifs at h_step <;> simp_all +decide [ CamelUp.ValidState.scores_size ];
        · rw [ ← h_step.2 ] ; simp +decide [ CamelUp.resolveLegBets_size, CamelUp.ValidState.scores_size ] ;
          rw [ CamelUp.awardPlayer_size, h_valid.scores_size ];
        · exact h_step.2 ▸ CamelUp.awardPlayer_size _ _ _ |> Eq.trans <| h_valid.scores_size;
        · rw [ ← h_step.2 ] ; simp +decide [ CamelUp.resolveRaceLoseBets_size, CamelUp.resolveRaceWinBets_size, CamelUp.resolveLegBets_size, CamelUp.awardPlayer_size, h_valid.scores_size ] ;
      · split_ifs at h_step <;> simp_all +decide [ CamelUp.ValidState.scores_size ];
        · rw [ ← h_step.2 ] ; simp +decide [ CamelUp.ValidState.scores_size ] ;
          convert CamelUp.resolveLegBets_size _ _ _ using 1;
          rw [ CamelUp.awardPlayer_size, CamelUp.awardPlayer_size, h_valid.scores_size ];
        · rw [ ← h_step.2 ] ; simp +decide [ CamelUp.awardPlayer_size ] ;
          exact h_valid.scores_size;
        · rw [ ← h_step.2 ] ; simp +decide [ CamelUp.ValidState.scores_size ] ;
          rw [ CamelUp.resolveRaceLoseBets_size, CamelUp.resolveRaceWinBets_size, CamelUp.resolveLegBets_size, CamelUp.awardPlayer_size, CamelUp.awardPlayer_size ] ; simp +decide [ h_valid.scores_size ]

/-
The `Roll` move preserves the board size.
Proof sketch:
1. Unfold `step`.
2. The board in `gs'` comes from `applyDie`.
3. Use `applyDie_preserves_boardSize` to show the new board has size `numSquares`.
-/
open CamelUp

theorem step_roll_preserves_board_size (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step : step gs (Move.Roll outcome) = some gs') :
    gs'.board.size = numSquares := by
      -- Apply the theorem that states the board size is preserved by the.Roll move.
      have h_applyDie_preserves_boardSize : (CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome).1.size = numSquares := by
        exact applyDie_preserves_boardSize _ _ _ _ h_valid.board_size;
      unfold CamelUp.step at h_step; aesop;

/-
The `Roll` move preserves the uniqueness of camels (each camel appears exactly once on the board or in the finished list).
This follows from `applyDie_preserves_camelCount` and the fact that the initial state satisfies `camel_unique`.
-/
open CamelUp

theorem step_roll_preserves_camel_unique (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step : step gs (Move.Roll outcome) = some gs') :
    ∀ c : CamelColor,
    gs'.finishedCamels.count c +
    (List.range numSquares).foldl (fun acc i => acc + (gs'.board.getStack i).count c) 0 = 1 := by
      intro c;
      convert applyDie_preserves_camelCount gs.board gs.modifiers gs.finishedCamels outcome c h_valid.board_size using 1;
      · unfold CamelUp.step at h_step; aesop;
      · rw [ ← h_valid.camel_unique c ]

/-
The `Roll` move preserves the `ValidState` invariants.
Proof uses helper lemmas for board size, camel uniqueness, scores size, and bag properties.
Case analysis on the three possible outcomes of a roll (Race Over, Leg Ends, Normal Step).
-/
open CamelUp

theorem step_roll_preserves_valid (gs : GameState) (outcome : DieOutcome) (gs' : GameState)
  (h_valid : ValidState gs)
  (h_step : step gs (Move.Roll outcome) = some gs') :
  ValidState gs' := by
    unfold CamelUp.step at h_step;
    split_ifs at h_step ; simp_all +decide [ CamelUp.ValidState ];
    split_ifs at h_step <;> simp_all +decide [ CamelUp.ValidState ];
    · constructor;
      all_goals rw [ ← h_step.2 ] ; simp +decide [ CamelUp.ValidState.mods_size ];
      any_goals rw [ ← h_valid.mods_size ];
      · rw [ show gs.modifiers.size = numSquares from ?_ ];
        · convert applyDie_preserves_boardSize gs.board gs.modifiers gs.finishedCamels outcome h_valid.board_size using 1;
        · exact h_valid.mods_size;
      · intro c;
        have := h_valid.camel_unique c;
        convert this using 1;
        convert applyDie_preserves_camelCount gs.board gs.modifiers gs.finishedCamels outcome c h_valid.board_size using 1;
        rw [ h_valid.mods_size ] ; aesop;
      · exact?;
      · convert resolveLegBets_size _ _ _ using 1;
        cases ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 <;> simp +decide [ *, awardPlayer_size ];
        · exact h_valid.scores_size.symm;
        · exact h_valid.scores_size.symm;
      · exact?;
    · rcases h_step.2.symm with rfl; exact ⟨ by
        apply applyDie_preserves_boardSize; exact h_valid.board_size;, by
        intro c
        generalize_proofs at *;
        convert h_valid.camel_unique c using 1;
        convert applyDie_preserves_camelCount gs.board gs.modifiers gs.finishedCamels outcome c h_valid.board_size using 1;
        grind +ring, by
        exact fun c hc => h_valid.bag_sub c <| List.mem_of_mem_erase hc, by
        exact bag_each_once_erase _ _ h_valid.bag_each_once, by
        field_simp;
        cases ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 <;> simp +decide [ *, awardPlayer_size ];
        · exact h_valid.scores_size;
        · exact h_valid.scores_size, by
        exact h_valid.tiles_size, by
        rcases h : ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 with ( _ | p ) <;> simp_all +decide [ CamelUp.awardPlayer ];
        · exact?;
        · exact?, by
        exact h_valid.mods_size ⟩ ;
    · rw [ ← h_step.2 ] at *; simp_all +decide [ CamelUp.ValidState ] ;
      constructor <;> simp +decide [ * ];
      any_goals linarith [ h_valid.scores_size, h_valid.tiles_size, h_valid.mods_size ];
      · convert applyDie_preserves_boardSize gs.board gs.modifiers gs.finishedCamels outcome h_valid.board_size using 1;
      · intro c; exact (by
        convert applyDie_preserves_camelCount gs.board gs.modifiers gs.finishedCamels outcome c h_valid.board_size using 1;
        exact Eq.symm ( h_valid.camel_unique c ));
      · convert h_valid.scores_size using 1;
        rw [ resolveRaceLoseBets_size, resolveRaceWinBets_size, resolveLegBets_size ];
        cases ( CamelUp.applyDie gs.board gs.modifiers gs.finishedCamels outcome ).2.2 <;> simp +decide [ CamelUp.awardPlayer_size ];
      · exact?

end AristotleLemmas

theorem step_preserves_valid
    (gs : GameState) (move : Move) (gs' : GameState)
    (h_valid : ValidState gs)
    (h_step  : step gs move = some gs') :
    ValidState gs' := by
  unfold CamelUp.step at h_step;
  split_ifs at h_step;
  rcases move with ( _ | _ | _ | _ | _ ) <;> simp +decide at h_step ⊢;
  · convert step_roll_preserves_valid gs _ gs' h_valid _ using 1;
    exact?;
    unfold CamelUp.step; aesop;
  · cases h : gs.legBetTiles[‹CamelColor›.toIdx]?.getD [] <;> simp_all +decide [ CamelUp.ValidState ];
    constructor;
    all_goals subst h_step; simp_all +decide [ CamelUp.ValidState ] ;
    exact h_valid.board_size;
    exact h_valid.camel_unique;
    exact h_valid.bag_sub;
    · exact h_valid.bag_each_once;
    · exact h_valid.scores_size;
    · exact h_valid.tiles_size ▸ updateArr_size _ _ _;
    · exact?;
    · exact h_valid.mods_size;
  · subst h_step;
    constructor;
    all_goals norm_num [ h_valid.board_size, h_valid.camel_unique, h_valid.bag_sub, h_valid.bag_each_once, h_valid.scores_size, h_valid.tiles_size, h_valid.player_valid, h_valid.mods_size ];
    · exact h_valid.bag_sub;
    · exact?;
  · rw [ ← h_step ] ; exact ⟨ by
      exact h_valid.board_size, by
      exact h_valid.camel_unique, by
      exact h_valid.bag_sub, by
      exact h_valid.bag_each_once, by
      exact h_valid.scores_size, by
      exact h_valid.tiles_size, by
      intro h; exact?;, by
      exact h_valid.mods_size ⟩ ;
  · constructor;
    all_goals rcases h_step with ⟨ h₁, h₂, h₃, h₄, rfl ⟩ ; simp_all +decide [ CamelUp.ValidState ];
    all_goals try { exact h_valid.board_size };
    any_goals exact h_valid.camel_unique;
    any_goals exact h_valid.scores_size;
    · exact h_valid.bag_sub;
    · exact h_valid.bag_each_once;
    · exact h_valid.tiles_size;
    · exact?;
    · convert h_valid.mods_size using 1;
      exact?

/-! ## Bet resolution corollaries -/

/-- resolveLegBets does not change array length. -/
theorem resolveLegBets_scores_size
    (scores : Array Int) (ranking : List CamelColor) (bets : List LegBetEntry) :
    (resolveLegBets scores ranking bets).size = scores.size := by
  unfold resolveLegBets
  induction bets generalizing scores with
  | nil => simp
  | cons bet rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact awardPlayer_size _ _ _

-- Helper lemmas for resolveRaceWinBets_scores_size

/-- resolveRaceWinBets does not change array length. -/
theorem resolveRaceWinBets_scores_size
    (scores : Array Int) (winner : CamelColor) (bets : List RaceBetEntry) :
    (resolveRaceWinBets scores winner bets).size = scores.size := by
  unfold resolveRaceWinBets
  have h : ∀ (bs : List RaceBetEntry) (sc : Array Int) (idx : Nat),
      (List.foldl (fun (pair : Array Int × Nat) (bet : RaceBetEntry) =>
        let (s, i) := pair
        if bet.camel == winner
        then (awardPlayer s bet.player (racePayoutAt i), i + 1)
        else (awardPlayer s bet.player (-1), i))
        (sc, idx) bs).1.size = sc.size := by
    intro bs
    induction bs with
    | nil => simp
    | cons bet rest ih =>
        intro sc idx
        simp only [List.foldl_cons]
        split_ifs <;> simp [awardPlayer_size, ih]
  exact h _ _ _

/-! ## Useful corollaries -/

theorem valid_bag_sub (gs : GameState) (h : ValidState gs) :
    ∀ c ∈ gs.diceBag, c ∈ CamelColor.all :=
  h.bag_sub

theorem valid_board_size (gs : GameState) (h : ValidState gs) :
    gs.board.size = numSquares :=
  h.board_size

theorem valid_scores_size (gs : GameState) (h : ValidState gs) :
    gs.scores.size = gs.numPlayers :=
  h.scores_size

end CamelUp