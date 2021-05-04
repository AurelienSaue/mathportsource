import Lean
import MathPort.Basic

open Lean

open MathPort
-- Options

def useSorry := true
def doFilter := true
def declareUniverses := true
def importPostport := false


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
      println! "Invalid suffix {pfx} for {n}"
      arbitrary
    | Name.str p s _ => do Name.mkStr (← removePrefix p pfx) s
    | Name.num p n _ => do Name.mkNum (← removePrefix p pfx) n

def listMetaM {α : Type _} (l : List (MetaM α)) : MetaM (List α) :=
  match l with 
  | [] => []
  | x::t => do (← x)::(← listMetaM t)

def arrayMetaM {α : Type _} (array : Array (MetaM α)) : MetaM (Array α) := do
  return ⟨← listMetaM array.data⟩ 


def forallDepth (prevnames : List Name) : (type : Expr) → Nat
  | Expr.forallE n _ e _ => do 
    if n.beq `ᾰ || prevnames.contains n then 0
    else forallDepth (n :: prevnames) e + 1
  | _ =>  0

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


def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) (safety : DefinitionSafety) (numParams : Option Nat := none): MetaM String := do
  let simpNames ← (← Meta.getSimpLemmas).lemmaNames
  let m : MessageData :=
    if simpNames.contains id then "@[simp] " else ""
  let m := m ++
    match safety with
    | DefinitionSafety.unsafe  => "unsafe "
    | DefinitionSafety.partial => "partial "
    | DefinitionSafety.safe    => ""
  let m := if isProtected (← getEnv) id then m ++ "protected " else m

  let (m, shortid) : MessageData × IO Name := do 
    match privateToUserName? (removeMathlibPrefix id) with
      | some shid => (m ++ "private ", shid)
      | none    => do 
        return (m, id.removePrefix currNamespace)

  let env ← (← getEnv)
  let kind := if Meta.isGlobalInstance env id then "instance" else kind

  let m := m ++ kind ++ " " ++ (← shortid)
  if declareUniverses then 
    let m := m ++ levelParamsToMessageData levelParams
  let m := m ++ " " 
  
  let numParams ← 
    if numParams.isNone then some $ forallDepth [] type
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

    s := s ++ ": " ++ toString (← PrettyPrinter.ppExpr currNamespace [] resType)
    s
  let stype : MetaM String:= Meta.forallBoundedTelescope type numParams formatType
  
  return (← m.toString) ++ (← stype)


def printDefLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (value : Expr) (currNamespace : Name) (safety := DefinitionSafety.safe) : MetaM String := do
  let mut m : String := (← mkHeader kind id levelParams type currNamespace safety)
  if useSorry then
    m := m ++ " := sorry\n\n"
  else
    m := m ++ " :=\n" ++ (toString (← PrettyPrinter.ppExpr currNamespace [] value))
  pure m

def mkHeader' (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool) (currNamespace : Name) (numParams : Option Nat := none): MetaM String :=
  mkHeader kind id levelParams type currNamespace (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe) numParams

def printAxiomLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) (isUnsafe := false) : MetaM String := do
  mkHeader' kind id levelParams type isUnsafe currNamespace

def printQuot (kind : QuotKind) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) : MetaM String := do
  printAxiomLike "Quotient primitive" id levelParams type currNamespace

def printInduct (id : Name) (levelParams : List Name) (numParams : Nat) (numIndices : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) (currNamespace : Name) (keyword : String): MetaM String := do
  let env ← getEnv

  if ctors.length = 1 && keyword = "structure" then
    let kind ← do 
      if isClass env id then "class"
      else "structure"
    println! "STRUCTURE kind: {kind} numParams: {numParams} numIndices: {numIndices}"
    let mut m ← mkHeader' kind id levelParams type isUnsafe currNamespace numParams
    m := m ++ "\nwhere"

    let ctor ← ctors.head!
    println! "constructor: {ctor}"

    let formatFields (fields : Array Expr) (resType : Expr) : MetaM String := do 
      let mut s := ""
      let mut i := 0
      for field in fields do
        if i >= numParams then
          let fieldType ← Meta.inferType field
          s := s ++ "\n  " ++ (← printExpr field currNamespace) ++ " : " ++ (← printExpr fieldType currNamespace)
        i := i + 1
      s

    let formatFieldsCustomCtor (fields : Array Expr) (resType : Expr) : MetaM String := do 
      let mut s := ""
      let mut i := 0
      for field in fields do
        if i >= numParams then
          let fieldType ← Meta.inferType field
          s := s ++ " (" ++ (← printExpr field currNamespace) ++ " : " ++ (← printExpr fieldType currNamespace) ++ ")"
        i := i + 1
      s
    
    let cinfo ← getConstInfo ctor

    if ctor.last = "mk" then 
      m := m ++ (← Meta.forallBoundedTelescope cinfo.type none formatFields)
    else 
      m := m ++ "\n  " ++ ctor.last ++ " ::" ++ (← Meta.forallBoundedTelescope cinfo.type none formatFieldsCustomCtor)
    return m
  else
    let kind ← do 
      if isClass env id then "class inductive"
      else "inductive"
    println! "INDUCTIVE kind: {kind} numParams: {numParams} numIndices: {numIndices}"

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
      m := m ++ (← Meta.forallBoundedTelescope cinfo.type (some numParams) formatCtorType)
    return m

def printStruct (id : Name) (levelParams : List Name) (numParams : Nat) (numIndices : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) (currNamespace : Name) : MetaM String := do
  let mut m ← mkHeader' "structure" id levelParams type isUnsafe currNamespace
  m := m ++ "\nwhere"
  for ctor in ctors do
    let cinfo ← getConstInfo ctor
    m := m ++ "\n| " ++ (← ctor.removePrefix id).toString ++ " : " ++ (toString (← PrettyPrinter.ppExpr currNamespace [] cinfo.type))
  return m



def constantToString (id : Name) (currNamespace : Name) (keyword : String): MetaM String := do
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

