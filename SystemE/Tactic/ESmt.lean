import Lean

import Smt.Tactic.Smt
import SystemE.Tactic.EQuery
import SystemE.Tactic.Attr
import SystemE.Tactic.Translate
import Qq

namespace Smt

open Qq
open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util


#check prepareSmtQuery

def prepareSmtQuery' (oldExprs : List Expr) (initialState : QueryBuilderM.State := { : QueryBuilderM.State }) (hs : List Expr) (goalType : Expr) (fvNames : Std.HashMap FVarId String) : MetaM (List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g => do
    Query.generateQuery' oldExprs initialState g hs fvNames

/- Unsound axiom we use to admit results from the solvers
   Dangerous!
 -/
universe u

axiom SMT_VERIF (α : Sort u) (synthetic := false) : α


def mkSMT_VERIF (type : Expr) (synthetic : Bool) : MetaM Expr := do
  let u ← Meta.getLevel type
  return mkApp2 (mkConst ``SMT_VERIF [u]) type (toExpr synthetic)


#check Meta.mkSorry


def esmt (oldExprs : List Expr) (st : QueryBuilderM.State) (mv : MVarId) (ac : List Command) (hs : List Expr) (timeout' : Option Nat := none) : MetaM (List MVarId) := mv.withContext do
  let mv₁ := (← Meta.mkFreshExprMVar (← mv.getType)).mvarId!
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv₁ hs fun mv₂ hs => mv₂.withContext do
  -- let (hs, mv₂) ← Preprocess.elimIff mv₂ hs
  mv₂.withContext do
  let goalType : Q(Prop) ← mv₂.getType
  -- 2. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  -- let (st, _) ← prepareSmtQuery' as (← mv.getType) fvNames₁
  let cmds ← prepareSmtQuery' oldExprs st hs (← mv₂.getType) fvNames₁
  let cmds := .setLogic "ALL" :: cmds
  trace[smt] "goal: {goalType}"
  trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- parse the commands
  let time1 ← IO.monoMsNow
  let query := Command.cmdsAsQuery cmds
  let time2 ← IO.monoMsNow
  dbg_trace f!"parsing time: {time2 - time1}"
  -- 3. Run the solver.
  let res ← solve query (some 1)
  let time3 ← IO.monoMsNow
  dbg_trace f!"solving time: {time3 - time2}"
  -- 4. Print the result.
  -- trace[smt] "\nresult: {res}"
  match res with
  | .error e =>
    -- 4a. Print error reason.
    trace[smt] "\nerror reason:\n{repr e}\n"
    throwError "unable to prove goal, either it is false or you need to define more symbols with `smt [foo, bar]`"
  | .ok pf =>
    -- 4b. Reconstruct proof.
    let goalType ← mv.getType
    let lsorry ← mkSMT_VERIF goalType (synthetic := true)
    mv.assign lsorry
    return []
    -- let ctx := { userNames := fvNames₂ }
    -- let (_, ps, p, hp, mvs) ← reconstructProof pf ctx
    -- let mv₂ ← mv₂.assert (← mkFreshId) p hp
    -- let ⟨_, mv₂⟩ ← mv₂.intro1
    -- let mut gs ← mv₂.apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ps.dropLast q(Prop), goalType])
    -- mv₂.withContext (gs.forM (·.assumption))
    -- mv.assign (.mvar mv₁)
    -- return mvs

-- open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

namespace Tactic

syntax (name := esmt) "esmt" smtHints : tactic

#check Tactic.evalRunTac
#check Tactic.evalTactic
#check Tactic.elabTerm

/-
  if no hints are given the entire local context is used
-/
@[tactic esmt]
def evalESmt : Tactic := fun stx => withMainContext do
  -- evalTactic (← `(tactic | dsimp at *))

  let ⟨st, oldGoals, cmds⟩ := euclidExtension.getState (← getEnv)

  let axioms := euclidExtension.getState (← getEnv)
  let userHints ← elabHints ⟨stx[1]⟩

  let mvs ← Smt.esmt oldGoals st (← Tactic.getMainGoal) [] (userHints) none
  Tactic.replaceMainGoal mvs
