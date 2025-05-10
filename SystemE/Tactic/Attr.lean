import Lean
import Smt.Translate
import Smt.Real
import Smt.Translate.Commands
import Smt

open Lean Meta Elab Command

initialize diagExtension : LabelExtension ← registerLabelAttr `diag "System E diagrammatic inference axiom"
initialize metricExtension : LabelExtension ← registerLabelAttr `metric "System E metric inference axiom"
initialize superExtension : LabelExtension ← registerLabelAttr `super "System E superposition inference axiom"
initialize transferExtension : LabelExtension ← registerLabelAttr `transfer "System E transfer inference axiom"

abbrev EuclidExtension := SimpleScopedEnvExtension (Name × Smt.Translate.Command) (Array (Name × Smt.Translate.Command))

instance : Inhabited Smt.Translate.Command :=
  ⟨Smt.Translate.Command.exit⟩

#check ConstantInfo.levelParams
#check getConstInfo
#check ConstantInfo.type
#check Smt.Translator.applyTranslators!
#check IO.processCommands
#check registerSimpAttr


def registerEuclidAttr (attrName : Name) (attrDescr : String)
  (ref : Name := by exact decl_name%) : IO EuclidExtension := do
  let ext : EuclidExtension ← registerSimpleScopedEnvExtension {
    name     := ref
    initial  := {}
    addEntry := fun d e => d.push e
  }
  registerBuiltinAttribute {
    ref   := ref
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add   := fun declName stx attrKind => do
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        let reducedType ← reduce info.type
        let (declCmd, _) ← (Smt.Translator.applyTranslators! reducedType).run {}
        ext.add <| ⟨declName, Smt.Translate.Command.assert declCmd⟩
      discard <| go.run {} {}
    erase := fun declName => do
      let s := ext.getState (← getEnv)
      modifyEnv fun env => ext.modifyState env fun _ => s.filter (declName = ·.1)
  }
  return ext

initialize euclidExtension : EuclidExtension ← registerEuclidAttr `euclid "euclidean geometry inference rules"

def getEuclidTheorems : CoreM (Array Smt.Translate.Command) := do
  pure <| (euclidExtension.getState (← getEnv)).map (·.2)

elab "#euclid_post" : command => do
  liftTermElabM do
    IO.println "=== post simp theorems ==="
    for thm in  ← getEuclidTheorems do
      IO.println thm
