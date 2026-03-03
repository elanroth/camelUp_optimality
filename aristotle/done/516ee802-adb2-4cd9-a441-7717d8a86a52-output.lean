/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 516ee802-adb2-4cd9-a441-7717d8a86a52

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN

- theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true

The following was negated by Aristotle:

- theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```



At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

-- Aristotle Batch: CamelUp.Proofs.Dominance remaining sorries
--
-- All 9 theorems below are sorry-stubbed.  Prove as many as possible.
--
-- Dependency order:
--   NaN-freedom (evalState_no_nan / evalDetMove_no_nan /
--                evalRollAction_no_nan / rankMoves_no_nan)
--     ↓
--   L1: insertDesc_head_ge
--     ↓
--   L2: rankMoves_sorted_desc    (needs NaN + L1)
--   L3: rankMoves_roll_included  (needs NaN; structural)
--     ↓
--   L4: mughBot_picks_max_EV     (needs L2 + L3; structural)
--   L5: mughBot_ge_roll_score    (needs L2 + L3; corollary)
--
-- Key definitions (from CamelUp.Controller.EV):
--
--   def evalState (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) : Float × RNG
--     -- n Monte-Carlo roll-outs; mean final score for `player`
--     -- body: foldl over List.range n, accumulates (sum, rng), divides by n
--     -- all individual scores come from gs'.scores.getD, shifted via intToFloat
--
--   def evalDetMove (gs : GameState) (move : Move) (baseline : Float)
--                   (rng : RNG) (n : Nat) : MoveEval × RNG
--     -- if step gs move = none → MoveEval with meanScore = -999.0 (proved: evalDetMove_illegal_sentinel)
--     -- otherwise → applies move, calls evalState on resulting state, returns MoveEval
--
--   def evalRollAction (gs : GameState) (baseline : Float)
--                      (rng : RNG) (n : Nat) : MoveEval × RNG
--     -- average over legalDieOutcomes of evalDetMove results
--
--   def rankMoves (gs : GameState) (seed : UInt64) (simsPerMove : Nat) : List MoveEval
--     -- builds list of MoveEval by calling evalDetMove / evalRollAction
--     -- inserts into descending-sorted list via insertDesc
--
--   private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval
--     -- defined locally in Dominance.lean (re-stated below for Aristotle):
--     -- | []     => [x]
--     -- | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
--     --             else h :: insertDesc t x
--
-- Float / NaN notes:
--   • Float in Lean follows IEEE 754:  NaN.isNaN = true, and for all finite f,
--     f.isNaN = false.
--   • Int.toNat.toFloat and intToFloat (defined in EV.lean) never produce NaN.
--   • Arithmetic on non-NaN values may produce NaN only via 0/0 or ∞−∞;
--     since all inputs are bounded, all results are finite.
--   • The guard `if n = 0 then 0.0 else total / n.toFloat` avoids 0/0.

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

/-! ## NaN-freedom lemmas -/

/- Aristotle failed to find a proof. -/
/-- `evalState` never produces a NaN mean score.
    Hint: unfold evalState; the result is `0.0` when n=0 (literal, not NaN),
    or `total / n.toFloat` where `total` is a finite sum of `intToFloat` values.
    Try: `unfold evalState; split_ifs; simp [Float.isNaN]` -/
theorem evalState_no_nan (gs : GameState) (player : Nat) (rng : RNG) (n : Nat) :
    ¬(evalState gs player rng n).1.isNaN := by
  sorry

/-- `evalDetMove` never produces a NaN mean score.
    Hint: unfold evalDetMove; case split on `step gs move`.
    • none branch  → meanScore = -999.0, not NaN. `simp [Float.isNaN]`
    • some branch  → meanScore comes from evalState; use evalState_no_nan.
    Try: `unfold evalDetMove; split_ifs; simp [Float.isNaN]` and
         `exact evalState_no_nan ...` -/
theorem evalDetMove_no_nan (gs : GameState) (move : Move) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalDetMove gs move baseline rng n).1.meanScore.isNaN := by
  unfold CamelUp.EV.evalDetMove;
  cases h : CamelUp.step gs move <;> simp ( config := { decide := Bool.true } ) [ * ];
  · native_decide +revert;
  · have := evalState_no_nan ‹_› gs.currentPlayer rng n; aesop;

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

open CamelUp CamelUp.Sim CamelUp.EV

/-- If there are no legal outcomes, evalRollAction returns the baseline. -/
lemma CamelUp.Dominance.evalRollAction_eq_baseline_of_empty (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat)
    (h : (legalDieOutcomes gs).isEmpty) :
    (evalRollAction gs baseline rng n).1.meanScore = baseline := by
      unfold CamelUp.EV.evalRollAction; aesop;

open CamelUp CamelUp.Sim CamelUp.EV

theorem evalRollAction_counterexample : ∃ gs baseline rng n, (evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  let gs := GameState.initial 1 Board.empty
  let gs' := { gs with gameOver := true }
  use gs', (0.0 / 0.0), { seed := 0 }, 0
  unfold evalRollAction
  simp [legalDieOutcomes]
  native_decide

end AristotleLemmas

/-
`evalRollAction` never produces a NaN mean score.
    Hint: similar to evalDetMove_no_nan; unfold evalRollAction,
    the result is an average of evalDetMove meanScores (all non-NaN by
    evalDetMove_no_nan).
-/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the counterexample to derive a contradiction.
  apply evalRollAction_counterexample

-/
/-- `evalRollAction` never produces a NaN mean score.
    Hint: similar to evalDetMove_no_nan; unfold evalRollAction,
    the result is an average of evalDetMove meanScores (all non-NaN by
    evalDetMove_no_nan). -/
theorem evalRollAction_no_nan (gs : GameState) (baseline : Float)
    (rng : RNG) (n : Nat) :
    ¬(evalRollAction gs baseline rng n).1.meanScore.isNaN := by
  sorry

/- Aristotle failed to find a proof. -/
/-- Every `MoveEval` in the output of `rankMoves` has a non-NaN mean score.
    Hint: unfold rankMoves; all entries come from evalDetMove or evalRollAction,
    both proved non-NaN above.  Use `List.mem_*` lemmas + the above. -/
theorem rankMoves_no_nan (gs : GameState) (seed : UInt64) (n : Nat) :
    ∀ me ∈ rankMoves gs seed n, ¬me.meanScore.isNaN := by
  sorry

/-! ## L1 — Insertion sort preserves the head-is-maximum invariant -/

-- (Same local definition as in Dominance.lean; stated here so Aristotle can
-- reason about it without unfolding the actual rankMoves internals.)
private def insertDesc' (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc' t x

/- Aristotle failed to find a proof. -/
/-- After inserting `x` into a descending-sorted list (all non-NaN),
    the head of the result is ≥ every element in the result.
    Hint: induction on `lst`.
    • Base (lst = []): result = [x]; head = x; x.meanScore >= x.meanScore
      follows from Float.ge_iff_le + le_refl (valid because ¬x.meanScore.isNaN).
    • Step (lst = h::t):
      – if x.meanScore >= h.meanScore: result = x::h::t; head = x.
        Need x >= x (by NaN freedom), x >= h (hypothesis), x >= everything in t
        (by h_sorted transitivity: x >= h >= t).
      – else (h.meanScore > x.meanScore, since both non-NaN):
        result = h :: insertDesc' t x; head = h.
        Need h >= x (from the else branch + NaN-total-order),
        h >= everything in t (h_sorted on t), and h >= inserted position
        (inductive hypothesis gives insertDesc' head >= new head, but head doesn't
        change here since h stays at front). -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_no_nan_x   : ¬x.meanScore.isNaN)
    (h_no_nan_lst : ∀ me ∈ lst, ¬me.meanScore.isNaN)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc' lst x,
      (insertDesc' lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-! ## L2 — rankMoves output is sorted descending by meanScore -/

/- Aristotle failed to find a proof. -/
theorem rankMoves_sorted_desc (gs : GameState) (seed : UInt64) (n : Nat) :
    let ranked := rankMoves gs seed n
    ∀ me ∈ ranked,
      ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
  -- Ingredients: rankMoves_no_nan + insertDesc_head_ge
  sorry

/-! ## L3 — Roll always appears in rankMoves when game not over -/

/- When the game is not over there is at least one legal die outcome,
    so `evalRollAction` is called and its result is inserted into the ranked list.
    Hint: unfold rankMoves; `h : ¬gs.gameOver` means `gs.diceBag` is nonempty
    (or legalDieOutcomes is nonempty).  The Roll entry always gets a label "Roll"
    from evalRollAction.  Use List.any_iff_exists + List.mem_*. -/
noncomputable section AristotleLemmas

/-
Defines `insertByEV` (mimicking the local `insertSorted` in `rankMoves`) and proves that inserting an element `y` into a list `lst` results in a list containing exactly `y` and the elements of `lst`.
-/
open CamelUp CamelUp.Sim CamelUp.EV

def insertByEV (me : MoveEval) (sorted : List MoveEval) : List MoveEval :=
  match sorted with
  | []        => [me]
  | x :: rest => if me.ev >= x.ev then me :: x :: rest else x :: insertByEV me rest

theorem insertByEV_mem_iff (lst : List MoveEval) (x y : MoveEval) :
    x ∈ insertByEV y lst ↔ x = y ∨ x ∈ lst := by
      unfold CamelUp.Dominance.insertByEV;
      cases lst <;> simp ( config := { decide := Bool.true } ) [ * ];
      split_ifs <;> simp ( config := { decide := Bool.true } ) [ * ];
      induction ‹List CamelUp.EV.MoveEval› <;> simp ( config := { decide := Bool.true } ) [ *, CamelUp.Dominance.insertByEV ];
      · grind +ring;
      · grind

/-
Generalization of `foldl_insertByEV_mem_iff`: folding `insertByEV` over a list `l` starting with accumulator `acc` results in a list containing exactly the elements of `l` and `acc`.
Proof strategy: Induction on `l`.
Base case: `l = []`. `foldl` returns `acc`. `x ∈ [] ∨ x ∈ acc ↔ x ∈ acc`. Correct.
Step case: `l = h :: t`.
`foldl f (h :: t) acc = foldl f t (f acc h)`.
Here `f acc y = insertByEV y acc`.
So `foldl ... = foldl ... t (insertByEV h acc)`.
IH: `x ∈ foldl ... t acc' ↔ x ∈ t ∨ x ∈ acc'`.
So `x ∈ result ↔ x ∈ t ∨ x ∈ insertByEV h acc`.
By `insertByEV_mem_iff`: `x ∈ insertByEV h acc ↔ x = h ∨ x ∈ acc`.
So `x ∈ result ↔ x ∈ t ∨ x = h ∨ x ∈ acc`.
RHS: `x ∈ h :: t ∨ x ∈ acc ↔ (x = h ∨ x ∈ t) ∨ x ∈ acc`.
Equivalent.
-/
open CamelUp CamelUp.Sim CamelUp.EV

theorem foldl_insertByEV_mem_iff_gen (l : List MoveEval) (acc : List MoveEval) (x : MoveEval) :
    x ∈ l.foldl (fun acc y => insertByEV y acc) acc ↔ x ∈ l ∨ x ∈ acc := by
      have h_insertByEV_mem_iff : ∀ (x y : CamelUp.EV.MoveEval) (l : List CamelUp.EV.MoveEval), x ∈ insertByEV y l ↔ x = y ∨ x ∈ l := by
        exact?
      generalize_proofs at *; (
      induction l using List.reverseRecOn <;> aesop;)

/-
Proves that `evalRollAction` always returns a `MoveEval` with the label "Roll".
Proof: Unfold `evalRollAction`. It has an if-then-else on `outcomes.isEmpty`.
Both branches return a structure where `label := "Roll"`.
So it is true by definition.
-/
open CamelUp CamelUp.Sim CamelUp.EV

theorem evalRollAction_label (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
    (evalRollAction gs baseline rng n).1.label = "Roll" := by
      unfold CamelUp.EV.evalRollAction; aesop;

end AristotleLemmas

theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  unfold CamelUp.EV.rankMoves;
  rw [ List.any_eq_true ];
  use (CamelUp.EV.evalRollAction gs (CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n).1 (CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n).2 n).1;
  constructor;
  · rw [ if_neg h ];
    convert foldl_insertByEV_mem_iff_gen _ _ _ |>.2 _ using 1;
    congr! 1;
    · funext sorted me; exact (by
      induction sorted <;> simp +decide [ *, CamelUp.EV.rankMoves.ins ];
      · rfl;
      · exact?);
    · simp +zetaDelta at *;
  · rw [ CamelUp.EV.evalRollAction ] ; aesop

/-! ## L4 — mughBot selects the head of rankMoves -/

/- Aristotle ran out of time. -/
theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _) := mughBot sims gs rng
    ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧ move = me.move := by
  -- Hint: unfold mughBot; the implementation takes head of rankMoves and
  -- checks if label == "Roll". When head is a bet (h_topIsBet), it returns
  -- head.move directly. Use obtain from h_topIsBet to name the head me,
  -- then unfold mughBot and simp with me's properties.
  sorry

/- Aristotle ran out of time. -/
/-! ## L5 — mughBot's meanScore ≥ Roll's meanScore -/

/- Aristotle ran out of time. -/
theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked := rankMoves gs seed sims
    match ranked.head?, ranked.find? (fun me => me.label == "Roll") with
    | some top, some rollMe => top.meanScore ≥ rollMe.meanScore
    | _, _                  => True := by
  -- Hint: by rankMoves_sorted_desc, head >= every element.
  -- By rankMoves_roll_included, Roll is in the list.
  -- List.find? returns some iff List.any = true; then head >= that element.
  -- Use: rankMoves_sorted_desc, rankMoves_roll_included,
  --      List.find?_some (or List.mem_of_find?_eq_some),
  --      to get rollMe ∈ ranked, then apply sorted_desc to rollMe.
  simp only []
  have hsorted := rankMoves_sorted_desc gs seed sims
  have hroll   := rankMoves_roll_included gs seed sims h
  -- rankMoves_roll_included gives List.any = true, which means
  -- ∃ me ∈ ranked, me.label == "Roll"
  rw [List.any_eq_true] at hroll
  obtain ⟨rollMe, hmem, hlabel⟩ := hroll
  have hge := hsorted rollMe hmem
  -- Now: (rankMoves gs seed sims).head?.map ... ≥ some rollMe.meanScore
  -- and find? (fun me => me.label == "Roll") finds at least rollMe
  cases h1 : (rankMoves gs seed sims).head? with
  | none => trivial
  | some top =>
    cases h2 : (rankMoves gs seed sims).find? (fun me => me.label == "Roll") with
    | none =>
      exfalso
      rw [List.find?_eq_none] at h2
      exact h2 rollMe hmem hlabel
    | some foundMe =>
      -- hge: some top.meanScore ≥ some rollMe.meanScore
      simp [h1] at hge
      -- foundMe might differ from rollMe but both satisfy ¬isNaN and have the same bound
      have hfoundMem := List.mem_of_find?_eq_some h2
      have hge2 := hsorted foundMe hfoundMem
      simp [h1] at hge2
      -- We want top.meanScore ≥ foundMe.meanScore; hge2 gives exactly that
      exact hge2

/- Aristotle ran out of time. -/
end CamelUp.Dominance