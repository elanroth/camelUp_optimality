/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: a5fc1040-7e14-4966-b39e-5ee91cd57d6f

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN

- theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _)

- theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

-- Aristotle Batch: CamelUp.Proofs.Dominance — next round
--
-- Batch 516ee802 proved:
--   ✅ evalDetMove_no_nan
--   ✅ rankMoves_roll_included  (+ helpers: evalRollAction_label, insertByEV_mem_iff,
--                                           foldl_insertByEV_mem_iff_gen)
--
-- Batch 516ee802 negated evalRollAction_no_nan (false without ¬baseline.isNaN guard).
-- Fixed statement is below.
--
-- Remaining targets this batch:
--   • evalState_no_nan
--   • evalRollAction_no_nan   (fixed: add h_baseline : ¬baseline.isNaN)
--   • rankMoves_no_nan
--   • insertDesc_head_ge
--   • rankMoves_sorted_desc
--   • mughBot_picks_max_EV
--   • mughBot_ge_roll_score

import CamelUp.Model.Types
import CamelUp.Model.Step
import CamelUp.Controller.Sim
import CamelUp.Controller.EV
import CamelUp.Controller.Policy


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

namespace CamelUp.Dominance

open CamelUp CamelUp.Sim CamelUp.EV CamelUp.Policy

-- Already proved (use freely):

theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN := by
  unfold CamelUp.EV.evalDetMove
  cases h : CamelUp.step gs move <;> simp (config := { decide := true }) [*]
  · native_decide +revert
  · have := evalState_no_nan ‹_› gs.currentPlayer rng n; aesop

theorem evalRollAction_label (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
    (evalRollAction gs baseline rng n).1.label = "Roll" := by
  unfold CamelUp.EV.evalRollAction; aesop

theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  unfold CamelUp.EV.rankMoves
  rw [List.any_eq_true]
  use (evalRollAction gs (evalState gs gs.currentPlayer { seed } n).1
                         (evalState gs gs.currentPlayer { seed } n).2 n).1
  constructor
  · rw [if_neg h]
    simp +zetaDelta
  · rw [CamelUp.EV.evalRollAction]; aesop

/- Aristotle failed to find a proof. -/
-- =============================================
-- Prove these:
-- =============================================

/-- evalState never produces NaN.
    Structure: n=0 → returns 0.0; n>0 → total/n.toFloat where total is finite sum of intToFloat.
    intToFloat never returns NaN (it's just Nat.toFloat or its negation).
    n.toFloat ≠ 0 when n > 0.  Division of finite / nonzero-finite = finite. -/
theorem evalState_no_nan (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
  sorry

/- Aristotle failed to find a proof. -/
/-- evalRollAction never produces NaN, given the baseline is not NaN.
    (Statement corrected from 516ee802: without this precondition the theorem is false —
     if legalDieOutcomes is empty, output.meanScore = baseline, which could be NaN.)
    With ¬baseline.isNaN:
    • empty outcomes → returns baseline → not NaN by h_baseline
    • nonempty outcomes → average of evalDetMove results → not NaN by evalDetMove_no_nan -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) (h_baseline : ¬baseline.isNaN) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/- Every MoveEval in rankMoves output has non-NaN meanScore.
    All entries come from evalDetMove (non-NaN) and evalRollAction (non-NaN when
    baseline = evalState result, which is non-NaN by evalState_no_nan). -/
noncomputable section AristotleLemmas

theorem evalState_no_nan_aux (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
      convert evalState_no_nan gs player rng n using 1

theorem evalRollAction_no_nan_aux (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) (h_baseline : ¬baseline.isNaN) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
      convert evalRollAction_no_nan gs baseline rng n h_baseline using 1

def insertSorted_aux (me : MoveEval) (l : List MoveEval) : List MoveEval :=
  match l with
  | [] => [me]
  | h :: t => if me.ev >= h.ev then me :: h :: t else h :: insertSorted_aux me t

theorem insertSorted_aux_mem (me : MoveEval) (l : List MoveEval) :
    ∀ x ∈ insertSorted_aux me l, x = me ∨ x ∈ l := by
      induction l <;> simp_all +decide [ CamelUp.Dominance.insertSorted_aux ];
      grind +ring

theorem insertSorted_preserves_pred (P : CamelUp.EV.MoveEval → Prop) (me : CamelUp.EV.MoveEval) (l : List CamelUp.EV.MoveEval)
    (h_me : P me) (h_l : ∀ x ∈ l, P x) :
    ∀ x ∈ insertSorted_aux me l, P x := by
      intro x hx; have := insertSorted_aux_mem me l x hx; aesop;

theorem fold_insertSorted_preserves_pred (P : CamelUp.EV.MoveEval → Prop) (l : List CamelUp.EV.MoveEval) (acc : List CamelUp.EV.MoveEval)
    (h_l : ∀ x ∈ l, P x) (h_acc : ∀ x ∈ acc, P x) :
    ∀ x ∈ l.foldl (fun acc me => insertSorted_aux me acc) acc, P x := by
      -- Apply the induction hypothesis to conclude the proof.
      have ih_step : ∀ (acc : List CamelUp.EV.MoveEval), (∀ x ∈ acc, P x) → ∀ (me : CamelUp.EV.MoveEval), P me → ∀ x ∈ CamelUp.Dominance.insertSorted_aux me acc, P x := by
        intros acc h_acc me h_me
        apply CamelUp.Dominance.insertSorted_preserves_pred P me acc h_me h_acc
        all_goals generalize_proofs at *; aesop;
      induction l using List.reverseRecOn <;> aesop

theorem fold_evals_prop (gs : GameState) (baseline : Float) (n : Nat)
    (f : CamelColor → Move)
    (cond : CamelColor → Bool)
    (l : List CamelColor)
    (acc : List MoveEval × RNG)
    (h_acc : ∀ x ∈ acc.1, ¬x.meanScore.isNaN) :
    ∀ x ∈ (l.foldl (fun (acc : List MoveEval × RNG) c =>
      if cond c then
        let (evals, rng) := acc
        let m := f c
        let (me, rng') := evalDetMove gs m baseline rng n
        (evals ++ [me], rng')
      else acc) acc).1, ¬x.meanScore.isNaN := by
        -- Apply the induction hypothesis to the list l.
        apply Classical.byContradiction
        intro h_contra;
        push_neg at h_contra;
        obtain ⟨ x, hx₁, hx₂ ⟩ := h_contra; induction l using List.reverseRecOn <;> simp_all +decide ;
        split_ifs at hx₁ <;> simp_all +decide [ List.mem_append, List.mem_singleton ];
        exact absurd hx₂ ( by exact? )

end AristotleLemmas

theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN := by
  unfold CamelUp.EV.rankMoves;
  split_ifs ; simp_all +decide [ CamelUp.EV.rankMoves.ins ];
  convert CamelUp.Dominance.fold_insertSorted_preserves_pred _ _ _ _ _ using 1;
  congr! 1;
  congr! 1;
  congr! 1;
  · funext sorted me; exact (by
    induction sorted <;> simp +decide [ *, CamelUp.EV.rankMoves.ins ];
    · rfl;
    · exact?);
  · intro x hx; simp_all +decide [ List.foldl_append ] ;
    rcases hx with ( rfl | hx | hx | hx );
    · convert CamelUp.Dominance.evalRollAction_no_nan_aux gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.2 ) n _ using 1;
      · grind;
      · exact?;
    · have := CamelUp.Dominance.fold_evals_prop gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) n ( fun c => CamelUp.Move.BetLeg c ) ( fun c => ¬ ( gs.legBetTiles[c.toIdx]?.getD [] = [] ) ) CamelUp.CamelColor.all ( [ ], ( CamelUp.EV.evalRollAction gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.2 ) n |>.2 ) ) ; aesop;
    · have := CamelUp.Dominance.fold_evals_prop gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 n ( fun c => CamelUp.Move.BetRaceWin c ) ( fun c => Bool.true ) CamelUp.CamelColor.all ( [ ], ( List.foldl ( fun ( acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG ) ( c : CamelUp.CamelColor ) => if gs.legBetTiles[c.toIdx]?.getD [] = [] then acc else ( acc.1 ++ [ ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 acc.2 n ).1 ], ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 acc.2 n ).2 ) ) ( [ ], ( CamelUp.EV.evalRollAction gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).2 n ).2 ) CamelUp.CamelColor.all ).2 ) ; aesop;
    · have := CamelUp.Dominance.fold_evals_prop gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) n ( fun c => CamelUp.Move.BetRaceLose c ) ( fun c => Bool.true ) CamelUp.CamelColor.all ( [ ], ( List.foldl ( fun ( acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG ) ( c : CamelUp.CamelColor ) => ( acc.1 ++ [ ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetRaceWin c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.1 ) ], ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetRaceWin c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.2 ) ) ) ( [ ], ( List.foldl ( fun ( acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG ) ( c : CamelUp.CamelColor ) => if gs.legBetTiles[c.toIdx]?.getD [] = [] then acc else ( acc.1 ++ [ ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.1 ) ], ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.2 ) ) ) ( [ ], ( CamelUp.EV.evalRollAction gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.2 ) n |>.2 ) ) CamelUp.CamelColor.all ).2 ) CamelUp.CamelColor.all ).2 ) ; aesop;
  · aesop

private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc t x

/- Aristotle failed to find a proof. -/
/-- Head of insertion-sorted list (descending, NaN-free) is ≥ every element.
    Proof: induction on lst.
    Base: [x] — head = x, need x ≥ x. Use Float.le_refl (ok since ¬isNaN makes ≥ reflexive).
    Step h::t:
      if x ≥ h: head = x. x ≥ x (refl), x ≥ h (if-cond), x ≥ t (trans via h_sorted).
      else h > x: head = h. h ≥ h (refl), h ≥ x (from else + NaN-free total order),
                  h ≥ t (h_sorted), h ≥ IH-inserted (IH gives new head ≥ all, but head stays h). -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_no_nan_x   : ¬x.meanScore.isNaN)
    (h_no_nan_lst : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/- Aristotle failed to find a proof. -/
/-- rankMoves output is sorted descending: head ≥ every element.
    Use rankMoves_no_nan + insertDesc_head_ge via induction on how rankMoves builds via foldl. -/
theorem rankMoves_sorted_desc (gs : GameState) (seed : UInt64) (n : Nat) :
    let ranked := rankMoves gs seed n
    ∀ me ∈ ranked, ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/- mughBot picks the head of rankMoves when the top entry is not Roll.
    Hint: unfold mughBot; when head = some me and ¬(me.label == "Roll"),
    it returns me.move directly. Use obtain from h_topIsBet. -/
noncomputable section AristotleLemmas

/-
Helper lemma: evalDetMove preserves the non-Roll nature of the move and its label is not "Roll".
-/
theorem evalDetMove_properties (gs : GameState) (move : Move) (baseline : Float) (rng : RNG) (n : Nat)
    (h_not_roll : ∀ o, move ≠ Move.Roll o) :
    (evalDetMove gs move baseline rng n).1.label ≠ "Roll" ∧
    ∀ o, (evalDetMove gs move baseline rng n).1.move ≠ Move.Roll o := by
      unfold CamelUp.EV.evalDetMove;
      cases h : CamelUp.step gs move <;> simp_all +decide;
      · rcases move with ( _ | _ | _ | _ | _ ) <;> norm_num [ ToString.toString ];
        · tauto;
        · rename_i c; rcases c with ( _ | _ | _ | _ | _ ) <;> trivial;
        · rename_i c; rcases c with ( _ | _ | _ | _ | _ ) <;> tauto;
        · rename_i c; rcases c with ( _ | _ | _ | _ | _ ) <;> trivial;
        · cases ‹Bool› <;> simp +decide [ * ];
          · simp +decide [ String.ext_iff ];
          · simp +decide [ String.ext_iff ];
      · cases move <;> simp_all +decide [ ToString.toString ];
        · rename_i c; rcases c with ( _ | _ | _ | _ | _ | c ) <;> trivial;
        · rename_i c; rcases c with ( _ | _ | _ | _ | _ | c ) <;> tauto;
        · rename_i c; rcases c with ( _ | _ | _ | _ | _ | c ) <;> trivial;
        · cases ‹Bool› <;> simp +decide [ String.ext_iff ]

/-
Helper lemma: evalRollAction always produces a result with label "Roll" and a Move.Roll move.
-/
theorem evalRollAction_properties (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
    (evalRollAction gs baseline rng n).1.label = "Roll" ∧
    ∃ o, (evalRollAction gs baseline rng n).1.move = Move.Roll o := by
      unfold CamelUp.EV.evalRollAction; aesop;

/-
Helper definition and lemma: insertSorted_aux preserves membership.
-/
def insertSorted_aux (me : MoveEval) (sorted : List MoveEval) : List MoveEval :=
  match sorted with
  | []        => [me]
  | x :: rest => if me.ev >= x.ev then me :: x :: rest else x :: insertSorted_aux me rest

theorem insertSorted_aux_mem (me : MoveEval) (sorted : List MoveEval) :
    ∀ x, x ∈ insertSorted_aux me sorted ↔ x = me ∨ x ∈ sorted := by
      induction sorted <;> intros <;> simp_all +decide [ CamelUp.Dominance.insertSorted_aux ];
      split_ifs <;> aesop;

/-
Helper lemma: foldl of insertSorted_aux preserves membership (union of list and accumulator).
-/
theorem foldl_insertSorted_aux_mem (l : List MoveEval) (sorted : List MoveEval) :
    ∀ x, x ∈ l.foldl (fun acc me => insertSorted_aux me acc) sorted ↔ x ∈ l ∨ x ∈ sorted := by
      -- By definition of `insertSorted_aux`, we know that `insertSorted_aux me sorted` is the list sorted with `me` inserted in the correct position.
      have h_insert : ∀ (me : CamelUp.EV.MoveEval) (sorted : List CamelUp.EV.MoveEval), ∀ x, x ∈ CamelUp.Dominance.insertSorted_aux me sorted ↔ x = me ∨ x ∈ sorted := by
        exact?;
      induction l using List.reverseRecOn <;> simp_all +decide [ List.foldl ];
      grind +ring

/-
Helper lemma: All moves generated by the leg-bet loop in rankMoves are non-Roll moves.
-/
open CamelUp CamelUp.Sim CamelUp.EV

theorem legEvals_properties (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
  ∀ me ∈ (CamelColor.all.foldl (fun (acc : List MoveEval × RNG) c =>
        let (evals, rng) := acc
        if (gs.legBetTiles.getD (CamelColor.toIdx c) []).isEmpty then (evals, rng)
        else
          let m := Move.BetLeg c
          let (me, rng') := evalDetMove gs m baseline rng n
          (evals ++ [me], rng'))
      ([], rng)).1,
  me.label ≠ "Roll" ∧ ∀ o, me.move ≠ Move.Roll o := by
    -- By definition of `CamelColor.all`, we can split the proof into cases based on each color.
    have h_cases : ∀ (cs : List CamelUp.CamelColor), ∀ (acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG), (∀ x ∈ acc.1, x.label ≠ "Roll" ∧ ∀ o : CamelUp.DieOutcome, x.move ≠ CamelUp.Move.Roll o) → ∀ (me : CamelUp.EV.MoveEval), me ∈ (List.foldl (fun (acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG) (c : CamelUp.CamelColor) =>
      match acc with
      | (evals, rng) =>
        if (gs.legBetTiles.getD c.toIdx []).isEmpty = Bool.true then (evals, rng)
        else
          let m : CamelUp.Move := CamelUp.Move.BetLeg c;
          match CamelUp.EV.evalDetMove gs m baseline rng n with
          | (me, rng') => (evals ++ [me], rng')
    ) acc cs).1 → me.label ≠ "Roll" ∧ ∀ o : CamelUp.DieOutcome, me.move ≠ CamelUp.Move.Roll o := by
      intro cs acc hacc me hme; induction cs using List.reverseRecOn <;> simp_all +decide ;
      split_ifs at hme <;> simp_all +decide [ List.mem_append, List.mem_singleton ] ;
      rcases hme with ( hme | rfl ) <;> [ exact ‹me ∈ _ → _› hme; exact evalDetMove_properties _ _ _ _ _ ( by tauto ) ] ;
    generalize_proofs at *; (
    exact h_cases _ _ fun x hx => by contradiction;)

/-
Helper lemma: All moves generated by the win-bet loop in rankMoves are non-Roll moves.
-/
open CamelUp CamelUp.Sim CamelUp.EV

theorem winEvals_properties (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
  ∀ me ∈ (CamelColor.all.foldl (fun (acc : List MoveEval × RNG) c =>
        let (evals, rng) := acc
        let m := Move.BetRaceWin c
        let (me, rng') := evalDetMove gs m baseline rng n
        (evals ++ [me], rng'))
      ([], rng)).1,
  me.label ≠ "Roll" ∧ ∀ o, me.move ≠ Move.Roll o := by
    intros me hypers;unfold CamelUp.CamelColor.all at hypers;simp at hypers; (
    rcases hypers with ( rfl | rfl | rfl | rfl | rfl ) <;> simp +decide [ evalDetMove_properties ]);

/-
Helper lemma: All moves generated by the lose-bet loop in rankMoves are non-Roll moves.
-/
open CamelUp CamelUp.Sim CamelUp.EV

theorem loseEvals_properties (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
  ∀ me ∈ (CamelColor.all.foldl (fun (acc : List MoveEval × RNG) c =>
        let (evals, rng) := acc
        let m := Move.BetRaceLose c
        let (me, rng') := evalDetMove gs m baseline rng n
        (evals ++ [me], rng'))
      ([], rng)).1,
  me.label ≠ "Roll" ∧ ∀ o, me.move ≠ Move.Roll o := by
    convert evalDetMove_properties _ _ _ _ _ _ using 1;
    rotate_left;
    exact?;
    exact Move.BetRaceLose CamelColor.White;
    exact?;
    exact?;
    exact n;
    · exact fun o => by rintro ⟨ ⟩ ;
    · constructor <;> intro h <;> simp_all +decide [ CamelUp.CamelColor.all ];
      exact ⟨ evalDetMove_properties _ _ _ _ _ ( by tauto ), evalDetMove_properties _ _ _ _ _ ( by tauto ), evalDetMove_properties _ _ _ _ _ ( by tauto ), evalDetMove_properties _ _ _ _ _ ( by tauto ) ⟩

/-
Helper lemma: For every move in rankMoves, the label is "Roll" iff the move is a Roll move.
-/
open CamelUp CamelUp.Sim CamelUp.EV

theorem rankMoves_consistent (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, (me.label = "Roll" ↔ ∃ o, me.move = Move.Roll o) := by
      unfold CamelUp.EV.rankMoves;
      -- By definition of `rankMoves`, the list of moves is constructed by folding over the legEvals, winEvals, and loseEvals.
      simp [CamelUp.EV.rankMoves.ins] at *;
      intro me hme;
      have h_foldl : ∀ (l : List CamelUp.EV.MoveEval) (sorted : List CamelUp.EV.MoveEval), me ∈ List.foldl (fun sorted me => CamelUp.EV.rankMoves.ins me sorted) sorted l ↔ me ∈ l ∨ me ∈ sorted := by
        intros l sorted;
        have h_foldl : ∀ (l : List MoveEval) (sorted : List MoveEval), ∀ x, x ∈ List.foldl (fun sorted me => CamelUp.EV.rankMoves.ins me sorted) sorted l ↔ x ∈ l ∨ x ∈ sorted := by
          intros l sorted x; exact (by
          convert foldl_insertSorted_aux_mem l sorted x using 1;
          congr! 2;
          funext sorted me; exact (by
          induction sorted <;> simp +decide [ *, CamelUp.EV.rankMoves.ins ];
          · rfl;
          · exact?));
        exact h_foldl l sorted me;
      simp_all +decide [ List.foldl_append, List.foldl_cons ];
      intro hme';
      rcases hme' with ( h | h | h | h );
      · have := loseEvals_properties gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( List.foldl ( fun ( acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG ) ( c : CamelUp.CamelColor ) => ( acc.1 ++ [ ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetRaceWin c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.1 ) ], ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetRaceWin c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.2 ) ) ) ( [ ], ( List.foldl ( fun ( acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG ) ( c : CamelUp.CamelColor ) => if gs.legBetTiles[c.toIdx]?.getD [] = [] then acc else ( acc.1 ++ [ ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.1 ) ], ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) acc.2 n |>.2 ) ) ) ( [ ], ( CamelUp.EV.evalRollAction gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.2 ) n |>.2 ) ) CamelUp.CamelColor.all |>.2 ) ) CamelUp.CamelColor.all |>.2 ) n;
        grind +ring;
      · have := winEvals_properties gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 ( List.foldl ( fun ( acc : List CamelUp.EV.MoveEval × CamelUp.Sim.RNG ) ( c : CamelUp.CamelColor ) => if gs.legBetTiles[c.toIdx]?.getD [] = [] then acc else ( acc.1 ++ [ ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 acc.2 n ).1 ], ( CamelUp.EV.evalDetMove gs ( CamelUp.Move.BetLeg c ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 acc.2 n ).2 ) ) ( [ ], ( CamelUp.EV.evalRollAction gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).1 ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n ).2 n ).2 ) CamelUp.CamelColor.all ).2 n; aesop;
      · have := legEvals_properties gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalRollAction gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.2 ) n |>.2 ) n; aesop;
      · have := evalRollAction_properties gs ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.1 ) ( CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n |>.2 ) n; aesop;

end AristotleLemmas

theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _) := mughBot sims gs rng
    ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧ move = me.move := by
  obtain ⟨me, hme⟩ := h_topIsBet
  have h_me_not_roll : ¬(∃ o, me.move = Move.Roll o) := by
    have := rankMoves_consistent gs rng.seed sims;
    specialize this me (by
    exact List.mem_of_mem_head? hme.1) ; aesop;
  unfold CamelUp.Policy.mughBot; aesop;

/-- mughBot's score ≥ Roll's score in the ranked list. Follows from sorted + roll_included. -/
theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked := rankMoves gs seed sims
    match ranked.head?, ranked.find? (fun me => me.label == "Roll") with
    | some top, some rollMe => top.meanScore ≥ rollMe.meanScore
    | _, _                  => True := by
  -- Since the list is sorted in descending order, the head's mean score is the greatest.
  have h_head_greatest : ∀ me ∈ rankMoves gs seed sims, (rankMoves gs seed sims).head?.map (·.meanScore) ≥ some me.meanScore := by
    convert rankMoves_sorted_desc gs seed sims using 1;
  grind

end CamelUp.Dominance