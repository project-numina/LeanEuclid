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



def prepareSmtQuery' (hs : List Expr) (goalType : Expr) (fvNames : Std.HashMap FVarId String) (initialState : QueryBuilderM.State := { : QueryBuilderM.State }) : MetaM (QueryBuilderM.State × List Command) := do
  let goalId ← Lean.mkFreshMVarId
  Lean.Meta.withLocalDeclD goalId.name (mkNot goalType) fun g => do
    (Query.generateQuery' g hs fvNames initialState)

/- Unsound axiom we use to admit results from the solvers
   Dangerous!
 -/
universe u

#check Meta.mkSorry

def esmt (mv : MVarId) (ac : List Command) (ax : List Expr) (hs : List Expr) (timeout' : Option Nat := none) : MetaM (List MVarId) := mv.withContext do
  -- 1. Process the hints passed to the tactic.
  withProcessedHints mv hs fun mv hs => mv.withContext do
  let (hs, mv) ← Preprocess.elimIff mv hs
  mv.withContext do
  let goalType : Q(Prop) ← mv.getType
  -- 2. Generate the SMT query.
  let (fvNames₁, fvNames₂) ← genUniqueFVarNames
  -- let (st, _) ← prepareSmtQuery' as (← mv.getType) fvNames₁
  let cmds ← prepareSmtQuery hs (← mv.getType) fvNames₁
  let cmds := .setLogic "ALL" :: ac ++ cmds
  trace[smt] "goal: {goalType}"
  trace[smt] "\nquery:\n{Command.cmdsAsQuery (cmds ++ [.checkSat])}"
  -- parse the commands
  let time1 ← IO.monoMsNow
  let query := Command.cmdsAsQuery cmds
  let time2 ← IO.monoMsNow
  dbg_trace f!"parsing time: {time2 - time1}"
  -- 3. Run the solver.
  let res ← solve query timeout'
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
    let (p, hp, mvs) ← reconstructProof pf fvNames₂
    let mv ← mv.assert (← mkFreshId) p hp
    let ⟨_, mv⟩ ← mv.intro1
    let ts ← (ax ++ hs).mapM Meta.inferType
    let mut gs ← mv.apply (← Meta.mkAppOptM ``Prop.implies_of_not_and #[listExpr ts q(Prop), goalType])
    mv.withContext (gs.forM (·.assumption))
    return mvs

-- open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

namespace Tactic

syntax (name := esmt) "esmt" smtHints smtTimeout : tactic

#check Tactic.evalRunTac
#check Tactic.evalTactic
#check Tactic.elabTerm

/-
  if no hints are given the entire local context is used
-/
@[tactic esmt]
def evalESmt : Tactic := fun stx => withMainContext do
  let axioms := euclidExtension.getState (← getEnv)
  -- let axiomExprs : List Expr := (← axioms.toList.mapM (fun x => do
  --   let e ← `(show _ from $(mkIdent x))
  --   elabTerm e none
  -- ))
  let axiomCommands : Array (Smt.Translate.Command) := euclidSorts.toArray ++ axioms.1.map (·.2)
  let axiomExprs1 ← axioms.1.mapM fun ⟨x, _⟩ => do
        let ll ← `(show _ from $(mkIdent x))
        return ← elabTerm ll none
  let axiomExprs2 ← axioms.2.mapM fun x => do
        let ll ← `(show _ from $(mkIdent x))
        return ← elabTerm ll none
  let userHints ← parseHints ⟨stx[1]⟩

  for ⟨x, _⟩ in axioms.1 do
    evalTactic (← `(tactic| have := $(mkIdent x)))

  -- If hints are empty, fall back to all local declarations
  let hints ← if userHints.isEmpty then
    let lctx ← getLCtx
    lctx.foldlM (init := []) fun acc decl =>
      if decl.isImplementationDetail || decl.isAuxDecl then
        pure acc
      else do
        let type ← instantiateMVars decl.type
        if ← Meta.isProp type then
          pure (acc.concat <| ← instantiateMVars decl.toExpr)
        else
          pure acc
  else
    pure userHints

  let mvs ← Smt.esmt (← Tactic.getMainGoal) axiomCommands.toList axiomExprs1.toList (axiomExprs2.toList ++ hints) (← parseTimeout ⟨stx[2]⟩)
  Tactic.replaceMainGoal mvs
