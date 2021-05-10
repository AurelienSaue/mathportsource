/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Gabriel Ebner
-/
import MathPort.Util
import MathPort.Basic
import MathPort.ActionItem
import MathPort.Rules
import MathPort.Translate
import MathPort.OldRecursor
import MathPort.PrintSource
import Lean

namespace MathPort

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Std

def shouldGenCodeFor (d : Declaration) : Bool :=
  -- TODO: sadly, noncomputable comes after the definition
  -- (so if this isn't good enough, we will need to refactor)
  match d with
  | Declaration.defnDecl _ => true
  | _                      => false

def addDeclLoud (n : Name) (d : Declaration) : PortM Unit := do
  let path := (← read).path
  println! "[addDecl] START {path.mrpath.path} {n}"
  if n == `module.End.eigenvectors_linear_independent then
    match d with
    | Declaration.thmDecl d => println! "[fail] {d.type} \n\n\n\n{d.value}"
    | _ => pure ()
  addDecl d
  println! "[addDecl] END   {path.mrpath.path} {n}"
  if shouldGenCodeFor d then
    match (← getEnv).compileDecl {} d with
    | Except.ok env    => println! "[compile] {n} SUCCESS!"
                          setEnv env
    | Except.error err => let msg ← err.toMessageData (← getOptions)
                          let msg ← msg.toString
                          println! "[compile] {n} {msg}"

def setAttr (attr : Attribute) (declName : Name) : PortM Unit := do
  let env ← getEnv
  match getAttributeImpl env attr.name with
  | Except.error errMsg => throwError errMsg
  | Except.ok attrImpl  => liftMetaM $ attrImpl.add declName attr.stx attr.kind

def processMixfix (kind : MixfixKind) (n : Name) (prec : Nat) (tok : String) : PortM Unit := do
  -- For now, we avoid the `=` `=` clash by making all Mathlib notations
  -- lower priority than the Lean4 ones.
  let prio : Nat := (← liftMacroM <| evalOptPrio none).pred

  let stxPrec  : Option Syntax := Syntax.mkNumLit (toString prec)
  let stxName  : Option Syntax := none
  let stxPrio  : Option Syntax := quote prio
  let stxOp    : Syntax := Syntax.mkStrLit tok
  let stxFun   : Syntax := Syntax.ident SourceInfo.none n.toString.toSubstring n []

  let stx ←
    match kind with
    | MixfixKind.infixl =>
      `(infixl $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.infixr =>
      `(infixr $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.prefix =>
      `(prefix $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.postfix =>
      `(postfix $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    | MixfixKind.singleton =>
      let correctPrec : Option Syntax := Syntax.mkNumLit (toString Parser.maxPrec)
      `(notation $[: $correctPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)

  let nextIdx : Nat ← (← get).nNotations
  modify λ s => { s with nNotations := nextIdx + 1 }
  let ns : Syntax := mkIdent $ s!"{(← read).path.mrpath.toUnderscorePath}_{nextIdx}"
  let stx ← `(namespace $ns:ident $stx end $ns:ident)
  elabCommand stx

def maybeRegisterEquation (n : Name) : PortM Unit := do
  -- example: list.nth.equations._eqn_1
  -- def insertWith (m : HashMap α β) (merge : β → β → β) (a : α) (b : β) : HashMap α β :=
  let n₁ : Name := n.getPrefix
  if n₁.isStr && n₁.getString! == "equations" then
    modify λ s => { s with name2equations := s.name2equations.insertWith (· ++ ·) n₁.getPrefix [n] }

def tryAddSimpLemma (n : Name) (prio : Nat) : PortM Unit :=
  try
    liftMetaM $ addSimpLemma n False AttributeKind.global prio
    println! "[simp] {n} {prio}"
  catch ex => warn ex

def isBadSUnfold (n : Name) : PortM Bool := do
  if !n.isStr then return false
  if n.getString! != "_sunfold" then return false
  match (← getEnv).find? (n.getPrefix ++ `_main) with
  | some cinfo =>
    match cinfo.value? with
    -- bad means the original function isn't actually recursive
    | some v => Option.isNone $ v.find? fun e => e.isConst && e.constName!.isStr && e.constName!.getString! == "brec_on"
    | _ => throwError "should have value"
  | _ => return false /- this can happen when e.g. `nat.add._main -> Nat.add` (which may be needed due to eqn lemmas) -/

def processActionItem (actionItem : ActionItem) : PortM Unit := do
  modify λ s => { s with decl := actionItem.toDecl }
  let s ← get
  let f n := translateName s (← getEnv) n

  match actionItem with
  | ActionItem.export d => do
    println! "[export] {d.currNs} {d.ns} {d.nsAs} {d.hadExplicit}, renames={d.renames}, excepts={d.exceptNames}"
    -- we use the variable names of elabExport
    if not d.exceptNames.isEmpty then
      warnStr s!"export of {d.ns} with exceptions is ignored"
    else if d.nsAs != Name.anonymous then
      warnStr s!"export of {d.ns} with 'nsAs' is ignored"
    else if ¬ d.hadExplicit then
      warnStr s!"export of {d.ns} with no explicits is ignored"
    else
      let mut env ← getEnv
      for (n1, n2) in d.renames do
        println! "[alias] {f n1} short for {f n2}"
        env := addAlias env (f n1) (f n2)
      setEnv env

  | ActionItem.mixfix kind n prec tok =>
    println! "[mixfix] {kind} {tok} {prec} {n}"
    processMixfix kind (f n) prec tok

  | ActionItem.simp n prio => do
    tryAddSimpLemma (f n) prio
    for eqn in (← get).name2equations.findD n [] do
      tryAddSimpLemma (f eqn) prio

  | ActionItem.reducibility n kind => do
    -- (note: this will fail if it declares reducible in a new module)
    println! "reducibility {n} {repr kind}"
    try setAttr { name := reducibilityToName kind } (f n)
    catch ex => warn ex

  | ActionItem.projection proj => do
    println! "[projection] {reprStr proj}"
    setEnv $ addProjectionFnInfo (← getEnv) (f proj.projName) (f proj.ctorName) proj.nParams proj.index proj.fromClass

  | ActionItem.class n => do
    let env ← getEnv
    if s.ignored.contains n then return ()
    -- for meta classes, Lean4 won't know about the decl
    match addClass env (f n) with
    | Except.error msg => warnStr msg
    | Except.ok env    => setEnv env

  | ActionItem.instance nc ni prio => do
    -- for meta instances, Lean4 won't know about the decl
    -- note: we use `prio.pred` so that the Lean4 builtin instances get priority
    -- this is currently needed because Decidable instances aren't getting compiled!
    match (← get).noInsts.find? ni with
    | some _ => println! "[skipInstance] {ni}"
    | none   => try liftMetaM $ addInstance (f ni) AttributeKind.global prio
                    setAttr { name := `inferTCGoalsRL } (f ni)
                catch ex => warn ex

  | ActionItem.private _ _ => pure ()
  | ActionItem.protected n =>
    -- TODO: have the semantics changed here?
    -- When we mark `nat.has_one` as `Protected`, the kernel
    -- fails to find it when typechecking definitions (but not theorems)
    -- setEnv $ addProtected (← getEnv) (f n)
    pure ()

  | ActionItem.position n line col => do
      println! "[POSITION] {n}"
      let n ← f n
      let range ← DeclarationRanges.mk
            { pos := { line := line, column := col }, 
              charUtf16 := col, 
              endPos := { line := line, column := col }, 
              endCharUtf16 := col }
            { pos := { line := line, column := col },
              charUtf16 := col,
              endPos := { line := line, column := col },
              endCharUtf16 := col} 
      Lean.addDeclarationRanges n range

  | ActionItem.decl d => do
    match d with
    | Declaration.axiomDecl ax => do
      let name := f ax.name
      let type ← translate ax.type

      if s.ignored.contains ax.name then return ()
      maybeRegisterEquation ax.name

      addDeclLoud ax.name $ Declaration.axiomDecl {
        ax with
          name := name,
          type := type
      }

    | Declaration.thmDecl thm => do
      let name := f thm.name
      let type ← translate thm.type

      if s.ignored.contains thm.name then return ()
      maybeRegisterEquation thm.name

      if s.sorries.contains thm.name ∨ (¬ (← read).proofs ∧ ¬ s.neverSorries.contains thm.name) then
        addDeclLoud thm.name $ Declaration.axiomDecl {
          thm with
            name     := name,
            type     := type,
            isUnsafe := false -- TODO: what to put here?
        }
      else
        let value ← translate thm.value
        addDeclLoud thm.name $ Declaration.thmDecl {
          thm with
            name  := name,
            type  := type,
            value := value
        }

    | Declaration.defnDecl defn => do
      let name := f defn.name
      let type ← translate defn.type

      if s.ignored.contains defn.name then return ()
      if ← isBadSUnfold name then return ()

      let value ← translate defn.value
      let env ← getEnv
      addDeclLoud defn.name $ Declaration.defnDecl {
        defn with
          name  := name,
          type  := type,
          value := value,
          hints := defn.hints
      }

    | Declaration.inductDecl lps nps [ind] iu => do
      let name := f ind.name
      let type ← translate ind.type

      if not (s.ignored.contains ind.name) then
        -- TODO: why do I need this nested do? Because of the scope?
        let ctors ← ind.ctors.mapM fun (ctor : Constructor) => do
          let cname := f ctor.name
          let ctype ← translate ctor.type
          pure { ctor with name := cname, type := ctype }
        addDeclLoud ind.name $ Declaration.inductDecl lps nps
          [{ ind with name := name, type := type, ctors := ctors }] iu

        try
          -- these may fail for the invalid inductive types currently being accepted
          -- by the temporary patch https://github.com/dselsam/lean4/commit/1bef1cb3498cf81f93095bda16ed8bc65af42535
          mkRecOn name
          mkCasesOn name
          mkNoConfusion name
          mkBelow name -- already there
          mkIBelow name
          mkBRecOn name
          mkBInductionOn name
        catch _ => pure ()

      let oldRecName := mkOldRecName (f ind.name)
      let oldRec ← liftMetaM $ mkOldRecursor (f ind.name) oldRecName
      match oldRec with
      | some oldRec => do
        addDeclLoud oldRecName oldRec
        setAttr { name := `reducible } oldRecName
      | none => pure ()

    | _ => throwError (toString d.names)

def addInfo (n : Name) (info : String) (pos : Nat := 0) : PortM Unit := do
  let h ← (← get).name2info
  let h ← 
    match h.find? n with 
      | some i => 
        match info with 
        | "position"      => h.insert n {i with position := pos}
        | "autoGenerated" => h.insert n {i with autoGenerated := true}
        | "instance"      => h.insert n {i with «instance» := true}
        | "class"         => h.insert n {i with «class» := true}
        | "protected"     => h.insert n {i with «protected» := true}
        | "private"       => h.insert n {i with «private» := true}
        | "simp"          => h.insert n {i with simp := true}
        | _ => 
          println! "invalid argument info"
          h
      | none => 
        match info with 
        | "position"      => h.insert n {position := pos}
        | "autoGenerated" => h.insert n {autoGenerated := true}
        | "instance"      => h.insert n {«instance» := true}
        | "class"         => h.insert n {«class» := true}
        | "protected"     => h.insert n {«protected» := true}
        | "private"       => h.insert n {«private» := true}
        | "simp"          => h.insert n {simp := true}
        | _ => 
          println! "invalid argument info"
          h
  modify $ λ s => { s with name2info := h }


def fillDeclInfo (actionItem : ActionItem) : PortM Unit := do
  let s ← get
  let f n := translateName s (← getEnv) n
  match actionItem with
  | ActionItem.simp n prio         => addInfo (f n) "simp"
  | ActionItem.class n             => addInfo (f n) "class"
  | ActionItem.instance nc ni prio => addInfo (f ni) "instance"
  | ActionItem.private pretty real => addInfo (f real) "private"
  | ActionItem.protected n         => addInfo (f n) "protected"
  | ActionItem.position n line col => addInfo (f n) "position" line
  | ActionItem.decl d => do
    let name ← f $ 
      match d with
      | Declaration.axiomDecl ax => ax.name
      | Declaration.thmDecl thm => thm.name
      | Declaration.defnDecl defn => defn.name
      | Declaration.inductDecl lps nps [ind] iu => ind.name
      | _ => arbitrary
    if not $ (← get).name2info.contains name then
      modify $ λ s => { s with name2info := s.name2info.insert name {} }
  | _ => ()

def fillUniverses (actionItem : ActionItem) : PortM Unit := do
  let s ← get
  let f n := translateName s (← getEnv) n
  match actionItem with
  | ActionItem.decl d => do
    let lps ← 
      match d with
      | Declaration.axiomDecl ax => ax.levelParams
      | Declaration.thmDecl thm => thm.levelParams
      | Declaration.defnDecl defn => defn.levelParams
      | Declaration.inductDecl lps nps [ind] iu => lps
      | _ => arbitrary
    for lp in lps do
      if not $ (← get).universes.contains lp then
        modify $ λ s => { s with «universes» := s.universes.push lp }
  | _ => ()

def findAutoGenerated : PortM Unit := do
  let mut positionMap : HashMap Nat (List Name) := mkHashMap
  let h ← (← get).name2info
  for (n,di) in h.toList do 
    positionMap := positionMap.insertWith (· ++ ·)  di.position [n] 
  for (line, l) in positionMap.toList do
    println! "ligne {line}"
    let mut shortest := l.head!
    for n in l.tail! do 
      println! "{n}: {((← get).name2info.find! n).autoGenerated}"
      if n.getNumParts < shortest.getNumParts then
        addInfo shortest "autoGenerated"
        println! "{n} < {shortest}"
        shortest := n
      else 
        addInfo n "autoGenerated"
        println! "{shortest} < {n}"
    
    if line = 0 then 
      println! "deleted {shortest}"
      addInfo shortest "autoGenerated"
    else 
      println! "chose {shortest}"
      println! "{shortest}: {((← get).name2info.find! shortest).autoGenerated}"
  
  let s ← get
  let h ← (← get).name2info
  for (n,di) in h.toList do 
    println! "{n} : {di.autoGenerated}"

def findFirstLine : PortM Nat := do
  let mut res := 0
  let h ← (← get).name2info
  for (n,di) in h.toList do 
    if di.position > 0 && (res = 0 || di.position < res) then 
      res := di.position
  return res

def newPos (actionItem : ActionItem) : PortM Nat := do
  let s ← get
  let name2info ← s.name2info
  let f n := translateName s (← getEnv) n
  match actionItem with
  | ActionItem.decl d => do
    match d with
    | Declaration.axiomDecl ax => do
      let name := f ax.name
      return (name2info.find! name).position
    | Declaration.thmDecl thm => do
      let name := f thm.name
      return (name2info.find! name).position
    | Declaration.defnDecl defn => do
      let name := f defn.name
      return (name2info.find! name).position
    | Declaration.inductDecl lps nps [ind] iu => do
      let name := f ind.name
      return (name2info.find! name).position
    | _ => throwError (toString d.names)
  | _ => return s.currLine
def actionItemToSource (actionItem : ActionItem) : PortM String := do
  modify λ s => { s with decl := actionItem.toDecl }
  let s ← get
  let f n := translateName s (← getEnv) n

  match actionItem with
  | ActionItem.export d => ""
    -- println! "[export] {d.currNs} {d.ns} {d.nsAs} {d.hadExplicit}, renames={d.renames}, excepts={d.exceptNames}"
    -- -- we use the variable names of elabExport
    -- if not d.exceptNames.isEmpty then
    --   warnStr s!"export of {d.ns} with exceptions is ignored"
    -- else if d.nsAs != Name.anonymous then
    --   warnStr s!"export of {d.ns} with 'nsAs' is ignored"
    -- else if ¬ d.hadExplicit then
    --   warnStr s!"export of {d.ns} with no explicits is ignored"
    -- else
    --   let mut env ← getEnv
    --   for (n1, n2) in d.renames do
    --     println! "[alias] {f n1} short for {f n2}"
    --     env := addAlias env (f n1) (f n2)
    --   setEnv env

  | ActionItem.mixfix kind n prec tok => do
    -- println! "[mixfix] {kind} {tok} {prec} {n}"
    -- processMixfix kind (f n) prec tok
    let n ← f n

    let prio : Nat := (← liftMacroM <| evalOptPrio none).pred

    let stxPrec  : Option Syntax := Syntax.mkNumLit (toString prec)
    let stxName  : Option Syntax := none
    let stxPrio  : Option Syntax := quote prio
    let stxOp    : Syntax := Syntax.mkStrLit tok
    let stxFun   : Syntax := Syntax.ident SourceInfo.none n.toString.toSubstring n []

    let stx ←
      match kind with
      | MixfixKind.infixl =>
        `(infixl $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
      | MixfixKind.infixr =>
        `(infixr $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
      | MixfixKind.prefix =>
        `(prefix $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
      | MixfixKind.postfix =>
        `(postfix $[: $stxPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
      | MixfixKind.singleton =>
        let correctPrec : Option Syntax := Syntax.mkNumLit (toString Parser.maxPrec)
        `(notation $[: $correctPrec]? $[(name := $stxName)]? $[(priority := $stxPrio)]? $stxOp => $stxFun)
    let str ←
      match kind with
      | MixfixKind.infixl =>
        s!"infixl:{prec} \"{tok}\" => {n}"
      | MixfixKind.infixr =>
        s!"infixr:{prec} \"{tok}\" => {n}"
      | MixfixKind.prefix =>
        s!"prefix:{prec} \"{tok}\" => {n}"
      | MixfixKind.postfix =>
        s!"postfix:{prec} \"{tok}\" => {n}"
      | MixfixKind.singleton =>
        let correctPrec := Parser.maxPrec
        s!"notation:{correctPrec} \"{tok}\" => {n}"

    let nextIdx : Nat ← (← get).nNotations
    modify λ s => { s with nNotations := nextIdx + 1 }
    let ns : Syntax := mkIdent $ s!"{(← read).path.mrpath.toUnderscorePath}_{nextIdx}"
    let stx ← `(namespace $ns:ident $stx end $ns:ident)
    println! "NOTATION {str}"
    
    return s!"{str}\n\n"

  | ActionItem.simp n prio => ""
    -- tryAddSimpLemma (f n) prio
    -- for eqn in (← get).name2equations.findD n [] do
    --   tryAddSimpLemma (f eqn) prio

  | ActionItem.reducibility n kind => ""
    -- -- (note: this will fail if it declares reducible in a new module)
    -- println! "reducibility {n} {repr kind}"
    -- try setAttr { name := reducibilityToName kind } (f n)
    -- catch ex => warn ex

  | ActionItem.projection proj => ""
    -- println! "[projection] {reprStr proj}"
    -- setEnv $ addProjectionFnInfo (← getEnv) (f proj.projName) (f proj.ctorName) proj.nParams proj.index proj.fromClass

  | ActionItem.class n => ""
    -- if s.ignored.contains n then return ""
    -- -- for meta classes, Lean4 won't know about the decl
    -- match addClass env (f n) with
    -- | Except.error msg => warnStr msg
    -- | Except.ok env    => setEnv env

  | ActionItem.instance nc ni prio => ""
    -- -- for meta instances, Lean4 won't know about the decl
    -- -- note: we use `prio.pred` so that the Lean4 builtin instances get priority
    -- -- this is currently needed because Decidable instances aren't getting compiled!
    -- match (← get).noInsts.find? ni with
    -- | some _ => println! "[skipInstance] {ni}"
    -- | none   => try liftMetaM $ addInstance (f ni) AttributeKind.global prio
    --                 setAttr { name := `inferTCGoalsRL } (f ni)
    --             catch ex => warn ex

  | ActionItem.private _ _ => pure ""
  | ActionItem.protected n =>
    -- TODO: have the semantics changed here?
    -- When we mark `nat.has_one` as `Protected`, the kernel
    -- fails to find it when typechecking definitions (but not theorems)
    -- setEnv $ addProtected (← getEnv) (f n)
    pure ""

  | ActionItem.position n line col => ""
      -- println! "[POSITION] {n}"
      -- let n ← f n
      -- let range ← DeclarationRanges.mk
      --       { pos := { line := line, column := col }, 
      --         charUtf16 := col, 
      --         endPos := { line := line, column := col }, 
      --         endCharUtf16 := col }
      --       { pos := { line := line, column := col },
      --         charUtf16 := col,
      --         endPos := { line := line, column := col },
      --         endCharUtf16 := col} 
      -- Lean.addDeclarationRanges n range

  | ActionItem.decl d => do
    match d with
    | Declaration.axiomDecl ax => do
      let name := 
        if s.ignored.contains ax.name then `Mathlib ++ ax.name
        else f ax.name
      let type ← translate ax.type

      if not printIgnored && s.ignored.contains ax.name then 
        println! "ignored {name}"
        return ""
      
      if (s.name2info.find! name).autoGenerated then
        println! "autogenerated {name}"
        return ""
      
      println! " PRINTING axiom {name}"
      
      return (← printAxiomLike "axiom" name ax.levelParams type s.currNamespace ax.isUnsafe)


    | Declaration.thmDecl thm => do
      let name := 
        if s.ignored.contains thm.name then `Mathlib ++ thm.name
        else f thm.name
      let type ← translate thm.type

      if not printIgnored && s.ignored.contains thm.name then 
        println! "ignored {name}"
        return ""
      if (s.name2info.find! name).autoGenerated then
        println! "autogenerated {name}"
        return ""
      -- maybeRegisterEquation thm.name
      println! " PRINTING thm {name}"

      if s.sorries.contains thm.name ∨ (¬ (← read).proofs ∧ ¬ s.neverSorries.contains thm.name) then
        -- addDeclLoud thm.name $ Declaration.axiomDecl {
        --   thm with
        --     name     := name,
        --     type     := type,
        --     isUnsafe := false -- TODO: what to put here?
        -- }
        return (← printDefLike "theorem" name thm.levelParams type arbitrary s.currNamespace)
      else
        -- let value ← translate thm.value
        -- addDeclLoud thm.name $ Declaration.thmDecl {
        --   thm with
        --     name  := name,
        --     type  := type,
        --     value := value
        -- }
        return (← printDefLike "theorem" name thm.levelParams type arbitrary s.currNamespace)

    | Declaration.defnDecl defn => do
      let name := 
        if s.ignored.contains defn.name then `Mathlib ++ defn.name
        else f defn.name
      let type ← translate defn.type

      if not printIgnored && s.ignored.contains defn.name then 
        println! "ignored {name}"
        return ""
      if ← isBadSUnfold name then 
        println! "bad unfold {name}"
        return ""
      if (s.name2info.find! name).autoGenerated then
        println! "autogenerated {name}"
        return ""


      println! " PRINTING def {name}"

      let value ← translate defn.value
      -- let env ← getEnv
      -- addDeclLoud defn.name $ Declaration.defnDecl {
      --   defn with
      --     name  := name,
      --     type  := type,
      --     value := value,
      --     hints := defn.hints
      -- }
      return (← printDefLike "def" name defn.levelParams type arbitrary s.currNamespace defn.safety)

    | Declaration.inductDecl lps nps [ind] iu => do
      let name := f ind.name

      if not printIgnored && s.ignored.contains ind.name then 
        println! "ignored {name}"
        return ""

      if (s.name2info.find! name).autoGenerated  then
        println! "autogenerated {name}"
        return ""
      
      return (← constantToString name s.currNamespace "")

      

    | _ => throwError (toString d.names)
end MathPort
