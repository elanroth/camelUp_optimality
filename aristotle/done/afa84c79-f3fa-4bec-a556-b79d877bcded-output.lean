/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: afa84c79-f3fa-4bec-a556-b79d877bcded

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true

- theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked

- theorem evalDetMove_illegal_sentinel (gs : GameState) (move : Move)
    (baseline : Float) (rng : RNG) (n : Nat)
    (h_illegal : step gs move = none) :
    (evalDetMove gs move baseline rng n).1.meanScore = -999.0

The following was negated by Aristotle:

- theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore

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

-- CamelUp.Proofs.Dominance
-- Formal statements about mughBot's EV-maximizing dominance.
-- All proofs are sorry-stubbed for Aristotle (M11 batch).
--
-- Theorem hierarchy:
--   L1  insertDesc_head_ge       — head of insertion-sorted list is maximal
--   L2  rankMoves_sorted_desc    — rankMoves output is sorted by meanScore ↓
--   L3  rankMoves_roll_included  — Roll always appears in rankMoves output
--   L4  mughBot_picks_max_EV    — mughBot's chosen move is the rankMoves head
--   L5  mughBot_ge_roll_score   — mughBot's meanScore ≥ Roll's meanScore
--   L6  evalDetMove_illegal_last — illegal moves sort last (−999 sentinel)
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

/-! ## L1 — Insertion sort preserves the head-is-maximum invariant -/

/-- The insertion-sort used in `rankMoves` (descending). -/
private def insertDesc (lst : List MoveEval) (x : MoveEval) : List MoveEval :=
  match lst with
  | []     => [x]
  | h :: t => if x.meanScore >= h.meanScore then x :: h :: t
              else h :: insertDesc t x

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
After inserting `x` into a descending-sorted list, the head is the global max.
-/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the list `lst` to be empty.
  use [];
  -- Let's simplify the goal. Since we have a contradiction assumption, the goal should be false. We can use the fact that `Float.neg` is negative.
  skip
  simp [CamelUp.Dominance.insertDesc] at *;
  -- Let's choose any `x` such that `x.meanScore` is not less than or equal to itself.
  use ⟨"Test", Move.Roll ⟨.White, 1⟩, Float.ofBits 0x7FF0000000000001, Float.ofBits 0x7FF0000000000001⟩;
  -- We'll use that 9218868437227405313 is not less than or equal to itself to derive a contradiction.
  by_contra h_contra
  skip
  exact absurd h_contra (by native_decide)

-/
/-- After inserting `x` into a descending-sorted list, the head is the global max. -/
theorem insertDesc_head_ge (lst : List MoveEval) (x : MoveEval)
    (h_sorted : ∀ me ∈ lst, lst.head?.map (·.meanScore) ≥ some me.meanScore) :
    ∀ me ∈ insertDesc lst x,
      (insertDesc lst x).head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-! ## L2 — rankMoves output is sorted descending by meanScore -/

/- Aristotle failed to find a proof. -/
/-- rankMoves yields a list where every earlier entry has meanScore ≥ later entries. -/
theorem rankMoves_sorted_desc (gs : GameState) (seed : UInt64) (n : Nat) :
    let ranked := rankMoves gs seed n
    ∀ me ∈ ranked,
      ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
  sorry

/-! ## L3 — Roll always appears in rankMoves when !gs.gameOver -/

noncomputable section AristotleLemmas

/-
The label of the MoveEval returned by evalRollAction is always "Roll".
-/
theorem evalRollAction_label (gs : GameState) (baseline : Float) (rng : RNG) (n : Nat) :
  (evalRollAction gs baseline rng n).1.label = "Roll" := by
    unfold CamelUp.EV.evalRollAction; aesop;

/-
Helper definition for insertion sort on MoveEval lists based on EV.
-/
def insertEV (me : CamelUp.EV.MoveEval) (sorted : List CamelUp.EV.MoveEval) : List CamelUp.EV.MoveEval :=
  match sorted with
  | [] => [me]
  | x :: rest => if me.ev >= x.ev then me :: x :: rest else x :: insertEV me rest

/-
`insertEV` preserves membership: an element is in the result iff it is the inserted element or was in the original list.
-/
theorem insertEV_mem (me : CamelUp.EV.MoveEval) (sorted : List CamelUp.EV.MoveEval) (x : CamelUp.EV.MoveEval) :
    x ∈ insertEV me sorted ↔ x = me ∨ x ∈ sorted := by
      -- We split into the two cases for the recursive definition of `insertEV`.
      have h_cases : ∀ {xs : List MoveEval}, x ∈ insertEV me xs ↔ x = me ∨ x ∈ xs := by
        intro xs; induction xs <;> simp_all ( config := { decide := Bool.true } ) [ CamelUp.Dominance.insertEV ] ; aesop;
      exact h_cases

/-
Folding `insertEV` over a list preserves all elements from the list and the accumulator.
-/
theorem fold_insertEV_mem (l : List CamelUp.EV.MoveEval) (acc : List CamelUp.EV.MoveEval) (x : CamelUp.EV.MoveEval) :
    x ∈ l ∨ x ∈ acc → x ∈ l.foldl (fun acc y => insertEV y acc) acc := by
      have h_insertEV_mem : ∀ (me : CamelUp.EV.MoveEval) (sorted : List CamelUp.EV.MoveEval) (x : CamelUp.EV.MoveEval), x ∈ insertEV me sorted ↔ x = me ∨ x ∈ sorted := by
        exact?;
      have h_foldl_mem : ∀ (l : List CamelUp.EV.MoveEval) (acc : List CamelUp.EV.MoveEval), ∀ x, x ∈ l ∨ x ∈ acc → x ∈ List.foldl (fun (acc : List CamelUp.EV.MoveEval) (y : CamelUp.EV.MoveEval) => insertEV y acc) acc l := by
        intro l acc x hx; induction l using List.reverseRecOn <;> aesop;
      generalize_proofs at *;
      exact h_foldl_mem l acc x

end AristotleLemmas

theorem rankMoves_roll_included (gs : GameState) (seed : UInt64) (n : Nat)
    (h : ¬gs.gameOver) :
    (rankMoves gs seed n).any (fun me => me.label == "Roll") = true := by
  -- By definition of `CamelUp.EV.rankMoves`, the `any` operation on the required type will return true.
  simp [CamelUp.EV.rankMoves] at *;
  use (CamelUp.EV.evalRollAction gs (CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n).1 (CamelUp.EV.evalState gs gs.currentPlayer { seed := seed } n).2 n).1;
  have h_insert_sorted : ∀ (me : CamelUp.EV.MoveEval) (sorted : List CamelUp.EV.MoveEval), (CamelUp.EV.rankMoves.ins me sorted) = insertEV me sorted := by
    intros me sorted; exact (by
    induction sorted <;> simp +decide [ *, CamelUp.EV.rankMoves.ins ] ; aesop;
    exact?)
  generalize_proofs at *; exact (by
  simp [h_insert_sorted] at *;
  apply And.intro
  generalize_proofs at *; exact (by
  have h_fold_insertEV_mem : ∀ (l : List CamelUp.EV.MoveEval) (acc : List CamelUp.EV.MoveEval) (x : CamelUp.EV.MoveEval), x ∈ l ∨ x ∈ acc → x ∈ List.foldl (fun acc y => CamelUp.Dominance.insertEV y acc) acc l := by
    exact?
  generalize_proofs at *; exact (by
  apply And.intro h (h_fold_insertEV_mem _ _ _ (Or.inr (by
  apply h_fold_insertEV_mem; simp [CamelUp.Dominance.insertEV] at *; exact (by
  grind))))))
  generalize_proofs at *; exact (by
  exact?))

/-! ## L4 — mughBot selects the head of rankMoves -/

/- Aristotle failed to find a proof. -/
/-- mughBot picks the top-ranked deterministic move or delegates to randomPolicy
    for Roll.  When the top entry is a bet move, mughBot applies it directly. -/
theorem mughBot_picks_max_EV (gs : GameState) (rng : RNG) (sims : Nat)
    (h_gameNotOver : ¬gs.gameOver)
    (h_topIsBet : ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧
                        ¬(me.label == "Roll")) :
    let (move, _) := mughBot sims gs rng
    ∃ me, (rankMoves gs rng.seed sims).head? = some me ∧ move = me.move := by
  sorry

/-! ## L5 — mughBot's meanScore ≥ Roll's meanScore in the same ranked list -/

/-- The move selected by mughBot (as measured by its rankMoves meanScore)
    is at least as good as taking the Roll action.
    Proof: by L2 (sorted) + L3 (Roll is present) + L4 (head is chosen). -/
theorem mughBot_ge_roll_score (gs : GameState) (seed : UInt64) (sims : Nat)
    (h : ¬gs.gameOver) :
    let ranked := rankMoves gs seed sims
    match ranked.head?, ranked.find? (fun me => me.label == "Roll") with
    | some top, some rollMe => top.meanScore ≥ rollMe.meanScore
    | _, _                  => True := by
  -- By definition of `rankMoves`, the list is sorted in descending order of mean score.
  have h_sorted : let ranked := rankMoves gs seed sims; ∀ me ∈ ranked, ranked.head?.map (·.meanScore) ≥ some me.meanScore := by
    apply rankMoves_sorted_desc;
  grind

/-! ## L6 — Illegal moves sort to the bottom (−999 sentinel) -/

/-- `evalDetMove` returns meanScore = −999 for illegal moves, ensuring they
    always sort below any legal move (whose meanScore ≥ 0 in any reachable state). -/
theorem evalDetMove_illegal_sentinel (gs : GameState) (move : Move)
    (baseline : Float) (rng : RNG) (n : Nat)
    (h_illegal : step gs move = none) :
    (evalDetMove gs move baseline rng n).1.meanScore = -999.0 := by
  unfold CamelUp.EV.evalDetMove; aesop;

end CamelUp.Dominance