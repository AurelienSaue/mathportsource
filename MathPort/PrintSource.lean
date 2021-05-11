import Lean
import MathPort.Basic

open Lean

open MathPort
-- Options

def useSorry := true
def doFilter := true
def declareUniverses := true
def importPostport := true
def printIgnored := true

-- Utils

def MathlibPrefix : Name := `Mathlib

def removeMathlibPrefix : Name → Name 
  | n@(Name.str p s _) => if (n == MathlibPrefix) then Name.anonymous 
                          else Name.mkStr (removeMathlibPrefix p) s
  | Name.num p n _     => Name.mkNum (removeMathlibPrefix p) n
  | Name.anonymous     => Name.anonymous

def startsWithAux : (s : List Char) → (subStr : List Char) → Bool 
  | _, [] => true
  | [], _ => false 
  | c₁::t₁, c₂::t₂ => c₁ = c₂ && startsWithAux t₁ t₂

def String.startsWith (s : String) (start : String) : Bool :=
  startsWithAux s.data start.data

def removeStartAux : (s : List Char) → (subStr : List Char) → List Char 
  | l, [] => l
  | [], l => []
  | c₁::t₁, c₂::t₂ => removeStartAux t₁ t₂

def String.removeStart (s : String) (start : String) : String :=
  ⟨removeStartAux s.data start.data⟩

def String.endsWith (s : String) (ending : String) : Bool :=
  startsWithAux s.data.reverse ending.data.reverse 

def containsStrAux : (s : List Char) →  (subStr : List Char) → Bool 
  | [], [] => true
  | [], _ => false 
  | _, [] => true
  | c₁::t₁, c₂::t₂ =>
    if c₁ = c₂ then (startsWithAux t₁ t₂) || (containsStrAux t₁ (c₂::t₂))
    else (containsStrAux t₁ (c₂::t₂))

def String.containsStr (s : String) (subStr : String) : Bool :=
  containsStrAux s.data subStr.data

def Lean.Name.last : Name → String
| Name.str _ s _  => s
| Name.num _ n _  => toString n
| Name.anonymous  => "[anonymous]"

def Lean.Name.removeSuffix : Name → Name → Name
  | n, Name.anonymous                  => n
  | Name.str p₁ s₁ _, Name.str p₂ s₂ _ => removeSuffix p₁ p₂
  | Name.num p₁ n₁ _, Name.num p₂ n₂ _ => removeSuffix p₁ p₂
  | _,           _                     => arbitrary

def Lean.Name.removePrefix (n : Name) (pfx : Name) : IO Name :=
  if n.beq pfx then Name.anonymous 
  else 
    match n with
    | Name.anonymous => do 
      println! "Invalid prefix {pfx} for {n}"
      Name.anonymous
    | Name.str p s _ => do Name.mkStr (← removePrefix p pfx) s
    | Name.num p n _ => do Name.mkNum (← removePrefix p pfx) n

def listMetaM {α : Type _} (l : List (MetaM α)) : MetaM (List α) :=
  match l with 
  | [] => []
  | x::t => do (← x)::(← listMetaM t)

def arrayMetaM {α : Type _} (array : Array (MetaM α)) : MetaM (Array α) := do
  return ⟨← listMetaM array.data⟩ 


def Lean.Expr.forallDepth (prevnames : List Name) : (type : Expr) → Nat
  | Expr.forallE n _ e _ => do 
    if n.beq `ᾰ || prevnames.contains n then 0
    else forallDepth (n :: prevnames) e + 1
  | _ =>  0

def Lean.Expr.forallRoot : (type : Expr) → Expr
  | Expr.forallE _ _ e _ => forallRoot e
  | e => e

-- Printing

def printExpr (e : Expr) (currNamespace : Name) : MetaM String := do toString (← PrettyPrinter.ppExpr currNamespace [] e)

def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | []    => ""
  | u::us => do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ u
    return m ++ "}"


def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) (safety : DefinitionSafety) (numParams : Option Nat := none): PortM String := do
  let info ← (← get).name2info.find! id
  let m : MessageData :=
    if info.simp then "@[simp] " else ""
  let m := m ++
    match safety with
    | DefinitionSafety.unsafe  => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe    => ""
  let m := if info.protected then m ++ "protected " else m
  let (m, shortid) : MessageData × IO Name := do 
    match privateToUserName? (removeMathlibPrefix id) with
      | some shid => (m ++ "private ", shid)
      | none    => do 
        return (m, id.removePrefix currNamespace)

  let kind := if info.instance then "instance" else kind

  let m := m ++ kind ++ " " ++ (← shortid)
  if declareUniverses then 
    let m := m ++ levelParamsToMessageData levelParams
  let m := m ++ " " 
  
  let numParams ← 
    if numParams.isNone then some $ type.forallDepth []
    else numParams

  let formatType (args : Array Expr) (resType : Expr) : MetaM String := do 
    let mut s := ""
    for arg in args do
      let argType ← Meta.inferType arg
      let localDecl ← Meta.getFVarLocalDecl arg
      match localDecl.binderInfo with
      | BinderInfo.default        => s := s ++ "(" ++ (← printExpr arg currNamespace) ++ " : " ++ (← printExpr argType currNamespace) ++ ") "
      | BinderInfo.implicit       => s := s ++ "{" ++ (← printExpr arg currNamespace) ++ " : " ++ (← printExpr argType currNamespace) ++ "} "
      | BinderInfo.strictImplicit => s := s ++ "⦃" ++ (← printExpr arg currNamespace) ++ " : " ++ (← printExpr argType currNamespace) ++ "⦄ "
      | BinderInfo.instImplicit   => do
          let str ← printExpr arg currNamespace
          if str.startsWith "_" then
            s := s ++ "[" ++ (← printExpr argType currNamespace) ++ "] "
          else 
            s := s ++ "[" ++ (← printExpr arg currNamespace) ++ " : " ++ (← printExpr argType currNamespace) ++ "] "
      | BinderInfo.auxDecl        => println! "ERROR: argument {arg} is auxDecl"
    match resType with
    | Expr.sort _ _ => ()
    | _ =>
    s := s ++ ": " ++ toString (← PrettyPrinter.ppExpr currNamespace [] resType)
    s
  let stype : String ← liftMetaM (@Meta.forallBoundedTelescope MetaM _ _ _ type numParams formatType)
  
  return (← m.toString) ++ stype


def printDefLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (value : Expr) (currNamespace : Name) (safety := DefinitionSafety.safe) : PortM String := do
  let mut m : String := (← mkHeader kind id levelParams type currNamespace safety)
  if useSorry then
    m := m ++ " := sorry\n\n"
  else
    m := m ++ " :=\n" ++ (toString (← liftMetaM $ PrettyPrinter.ppExpr currNamespace [] value))
  pure m

def mkHeader' (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool) (currNamespace : Name) (numParams : Option Nat := none): PortM String :=
  mkHeader kind id levelParams type currNamespace (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe) numParams

def printAxiomLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) (isUnsafe := false) : PortM String := do
  mkHeader' kind id levelParams type isUnsafe currNamespace

def printQuot (kind : QuotKind) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) : PortM String := do
  printAxiomLike "Quotient primitive" id levelParams type currNamespace

def findExtensions (id : Name) : PortM (Array Expr) := do 

  let getResType (fields : Array Expr) (resType : Expr) : MetaM Expr := do 
      println! "rt"
      println! "resType: {(← printExpr resType Name.anonymous)}"
      resType

  println! "looking for extensions"
  let mut res := #[]
  let s ← get 
  let extensionsPrefix : String := id.toString ++ ".to_"
  println! "prefix: {extensionsPrefix}"
  let pos := (s.name2info.find! id).position
  for (name, info) in s.name2info.toArray do 
    if name.toString.startsWith extensionsPrefix && info.position = pos then 
      println! "candidate : {name}"
      res := res.push info.type.forallRoot
     
  return res

def extractStructureName (e : Expr) : Name := do
  match e with 
  | Expr.app e1 e2 _ => extractStructureName e1
  | Expr.const n _ _ => n
  | _ => panic! "WRONG STRUCT FORMAT"

def findFields (id : Name) : MetaM (List Name) := do 

  let findFieldsAux (numParams : Nat) (fields : Array Expr) (resType : Expr) : MetaM (List Name) := do 
      let mut res := []
      let mut i := 0
      let ctx ← getLCtx
      for field in fields do
        if i >= numParams then
          let fieldName ← (ctx.getFVar! field).userName
          println! "field {fieldName}"
          println! "numParams: {numParams}"
          res := fieldName :: res
        i := i + 1
      return res
    
    


  match (← getEnv).find? (`Mathlib ++ id) with
  | ConstantInfo.inductInfo { levelParams := us, numParams := np, numIndices := numIndices, type := t, ctors := ctors, isUnsafe := u, .. } =>
    if ctors.length != 1 then 
      panic! "{id} is not a struct (too many constructors)"
    else 
      println! "real num params {np}"
      let cinfo ← getConstInfo ctors.head!
      return ← Meta.forallBoundedTelescope cinfo.type none (findFieldsAux np)
  | _ => panic! "{id} is not a struct (not inductive type)"

def printInduct (id : Name) (levelParams : List Name) (numParams : Nat) (numIndices : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) (currNamespace : Name) (keyword : String): PortM String := do
  let info ← (← get).name2info.find! id

  let mut struct := false
  if ctors.length = 1 then 
    let ctor ← ctors.head!

    let name2info ← (← get).name2info

    let checkFields (fields : Array Expr) (resType : Expr) : MetaM Bool := do 
      let mut res := true
      let mut i := 0
      let ctx ← getLCtx
      for field in fields do
        if i >= numParams then
          let fieldName ← (ctx.getFVar! field).userName
          println! "field {field}: {id ++ fieldName}"
          let isDefined ← name2info.contains $ id ++ fieldName
          let autoGenerated ← fieldName.toString.startsWith "_"
          println! "the field is defined:{isDefined} the field is autogen:{autoGenerated}"
          res := res && (isDefined || autoGenerated)
        i := i + 1
      res
    
    let cinfo ← getConstInfo ctor

    
    struct := (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type none checkFields)




  if struct then
    let kind ← do 
      if info.class then "class"
      else "structure"
    println! "STRUCTURE kind: {kind} numParams: {numParams} numIndices: {numIndices}"
    let mut m ← mkHeader' kind id levelParams type isUnsafe currNamespace numParams
    
    let extensions ← findExtensions id
    println! "extensions: {extensions}"
    

    let ctor ← ctors.head!
    println! "constructor: {ctor}"

    let formatFields (fields : Array Expr) (resType : Expr) : MetaM String := do 
      let mut s := ""
      let mut fields2Ignore := []
      if extensions != #[] then 
        s := s ++ "\nextends "
        println! "fields"
        for field in fields do
          println! "{field} aka {(← printExpr field currNamespace)}"
        
        let mut i := 0
        for extension in extensions do 
          let extension ← extension.liftLooseBVars 0 (fields.size - numParams - 1)
          
          println! "instanciating {extension}"

          let extension ← (extension.instantiateRev fields)
          println! "=> {(← printExpr extension Name.anonymous)}"

          if i > 0 then
            s := s ++ ", "
          s := s ++ toString (← printExpr extension currNamespace)

          i := i + 1
          
          let extensionName ← extractStructureName extension
          println! "struct name {(extractStructureName extension)}"
          let extensionFields : List Name ← findFields extensionName
          fields2Ignore := fields2Ignore.append extensionFields

      s := s ++ "\nwhere"
      let mut i := 0
      let ctx ← getLCtx

      for field in fields do
        let fieldName ← (ctx.getFVar! field).userName
        if i >= numParams then
          if fields2Ignore.contains fieldName|| fieldName.toString.startsWith "_" then 
            println! "ignored field {fieldName}"
          else
          let fieldType ← Meta.inferType field
          s := s ++ "\n  " ++ (← printExpr field currNamespace) ++ " : " ++ (← printExpr fieldType currNamespace)
        i := i + 1
      s

    let formatFieldsCustomCtor (fields : Array Expr) (resType : Expr) : MetaM String := do 
      let mut s := ""
      if extensions != #[] then 
        s := s ++ "\nextends "
        for extension in extensions do 
          s := s ++ toString (← printExpr (extension.instantiateRev fields) currNamespace)
      s := s ++ "\nwhere"
      let mut i := 0
      for field in fields do
        if i >= numParams then
          let fieldType ← Meta.inferType field
          s := s ++ " (" ++ (← printExpr field currNamespace) ++ " : " ++ (← printExpr fieldType currNamespace) ++ ")"
        i := i + 1
      s
    
    let cinfo ← getConstInfo ctor

    if ctor.last = "mk" then 
      m := m ++ (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type none formatFields)
    else 
      m := m ++ "\n  " ++ ctor.last ++ " ::" ++ (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type none formatFieldsCustomCtor)
    return m ++ "\n\n"
  else
    let kind ← do 
      if info.class then "class inductive"
      else "inductive"
    println! "INDUCTIVE {id} kind: {kind} numParams: {numParams} numIndices: {numIndices}"

    let mut m ← mkHeader' kind id levelParams type isUnsafe currNamespace numParams
    m := m ++ "\nwhere"

    let formatCtorType (args : Array Expr) (resType : Expr) : MetaM String := do 
      let mut s := ""
      let mut explicit := false
      for arg in args do
        let localDecl ← Meta.getFVarLocalDecl arg
        match localDecl.binderInfo with
        | BinderInfo.default => explicit := true
        | _                  => ()
      if explicit then s := s ++ " {} "
      s := s ++ " : " ++ (← printExpr resType currNamespace)
      s

    for ctor in ctors do
      let cinfo ← getConstInfo ctor
      m := m ++ "\n| " ++ (← ctor.removePrefix id).toString
      m := m ++ (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type (some numParams) formatCtorType)
    return m ++ "\n\n"

def printStruct (id : Name) (levelParams : List Name) (numParams : Nat) (numIndices : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) (currNamespace : Name) : PortM String := do
  let mut m ← mkHeader' "structure" id levelParams type isUnsafe currNamespace
  m := m ++ "\nwhere"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ "\n| " ++ (← ctor.removePrefix id).toString ++ " : " ++ (toString (← liftMetaM $ PrettyPrinter.ppExpr currNamespace [] cinfo.type))
  return m



def constantToString (id : Name) (currNamespace : Name) (keyword : String): PortM String := do
  match (← getEnv).find? id with
  | ConstantInfo.defnInfo  { levelParams := us, type := t, value := v, safety := s, .. } => printDefLike "def" id us t v currNamespace s 
  | ConstantInfo.thmInfo  { levelParams := us, type := t, value := v, .. } => printDefLike "theorem" id us t v currNamespace
  | ConstantInfo.axiomInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "axiom" id us t currNamespace u
  | ConstantInfo.opaqueInfo  { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "constant" id us t currNamespace u
  | ConstantInfo.quotInfo  { kind := kind, levelParams := us, type := t, .. } => printQuot kind id us t currNamespace
  | ConstantInfo.ctorInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "constructor" id us t currNamespace u
  | ConstantInfo.recInfo { levelParams := us, type := t, isUnsafe := u, .. } => printAxiomLike "recursor" id us t currNamespace u
  | ConstantInfo.inductInfo { levelParams := us, numParams := numParams, numIndices := numIndices, type := t, ctors := ctors, isUnsafe := u, .. } =>
    printInduct id us numParams numIndices t ctors u currNamespace keyword
  | _ => "not found"

