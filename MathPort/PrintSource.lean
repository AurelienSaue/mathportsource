import Lean
import MathPort.Basic

open Lean

open MathPort
-- Options

def useSorry := false
def doFilter := true
def declareUniverses := true
def importPostport := false
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

def replaceAux (c : Char) (toInsert : String) (prev : List Char): List Char → List Char 
  | c₁::t => if c₁ = c then (replaceAux c toInsert (prev ++ toInsert.data) t) else (replaceAux c toInsert (prev ++ [c₁]) t)
  | [] => prev

def String.replace (s : String) (c : Char) (toInsert : String) : String :=
  ⟨replaceAux c toInsert [] s.data⟩

def countAux (c : Char) : List Char → Nat
  | c₁::t => if c₁ = c then Nat.succ (countAux c t) else countAux c t
  | [] => 0

def String.count (s : String) (c : Char) : Nat:=
  (countAux c s.data)

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




def rip : (Std.Format) → String
  | Std.Format.nil  => "nil"
  | Std.Format.line => "line"
  | Std.Format.text s  => s!"text \"{s}\""
  | Std.Format.append f₁ f₂ => s!"{(rip f₁)}\n{(rip f₂)}"
  | Std.Format.nest x f => s!"nest {x}\n| {(rip f).replace '\n' "\n| "}"
  | Std.Format.group f Std.Format.FlattenBehavior.allOrNone => s!"group aon\n| {(rip f).replace '\n' "\n| "}"
  | Std.Format.group f Std.Format.FlattenBehavior.fill => s!"fill\n| {(rip f).replace '\n' "\n| "}"

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

-- Copy of private definitions from Lean/Meta/Basic.lean
private def getDefInfoTemp (info : ConstantInfo) : MetaM (Option ConstantInfo) := do
  match (← Lean.Meta.getTransparency) with
  | Lean.Meta.TransparencyMode.all => return some info
  | Lean.Meta.TransparencyMode.default => return some info
  | _ =>
    if (← isReducible info.name) then
      return some info
    else
      return none
private def getConstTemp? (constName : Name) : MetaM (Option ConstantInfo) := do
  let env ← getEnv
  match env.find? constName with
  | some (info@(ConstantInfo.thmInfo _))  => Lean.Meta.getTheoremInfo info
  | some (info@(ConstantInfo.defnInfo _)) => getDefInfoTemp info
  | some info                             => pure (some info)
  | none                                  => throwUnknownConstant constName

private def isClassQuickConst? (constName : Name) : MetaM (LOption Name) := do
  let env ← getEnv
  if isClass env constName then
    pure (LOption.some constName)
  else
    match (← getConstTemp? constName) with
    | some _ => pure LOption.undef
    | none   => pure LOption.none
private partial def isClassQuick? : Expr → MetaM (LOption Name)
  | Expr.bvar ..         => pure LOption.none
  | Expr.lit ..          => pure LOption.none
  | Expr.fvar ..         => pure LOption.none
  | Expr.sort ..         => pure LOption.none
  | Expr.lam ..          => pure LOption.none
  | Expr.letE ..         => pure LOption.undef
  | Expr.proj ..         => pure LOption.undef
  | Expr.forallE _ _ b _ => isClassQuick? b
  | Expr.mdata _ e _     => isClassQuick? e
  | Expr.const n _ _     => isClassQuickConst? n
  | Expr.mvar mvarId _   => do
    match (← Lean.Meta.getExprMVarAssignment? mvarId) with
    | some val => isClassQuick? val
    | none     => pure LOption.none
  | Expr.app f _ _       =>
    match f.getAppFn with
    | Expr.const n .. => isClassQuickConst? n
    | Expr.lam ..     => pure LOption.undef
    | _              => pure LOption.none
private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
  match maxFVars? with
  | some maxFVars => fvars.size < maxFVars
  | none          => true
mutual
  /--
    `withNewLocalInstances isClassExpensive fvars j k` updates the vector or local instances
    using free variables `fvars[j] ... fvars.back`, and execute `k`.

    - `isClassExpensive` is defined later.
    - The type class chache is reset whenever a new local instance is found.
    - `isClassExpensive` uses `whnf` which depends (indirectly) on the set of local instances.
      Thus, each new local instance requires a new `resettingSynthInstanceCache`. -/
  private partial def withNewLocalInstancesImp
      (fvars : Array Expr) (i : Nat) (k : MetaM α) : MetaM α := do
    if h : i < fvars.size then
      let fvar := fvars.get ⟨i, h⟩
      let decl ← Lean.Meta.getFVarLocalDecl fvar
      match (← isClassQuick? decl.type) with
      | LOption.none   => withNewLocalInstancesImp fvars (i+1) k
      | LOption.undef  =>
        match (← isClassExpensive? decl.type) with
        | none   => withNewLocalInstancesImp fvars (i+1) k
        | some c => Lean.Meta.withNewLocalInstance c fvar <| withNewLocalInstancesImp fvars (i+1) k
      | LOption.some c => Lean.Meta.withNewLocalInstance c fvar <| withNewLocalInstancesImp fvars (i+1) k
    else
      k
  private partial def lambdaTelescopeReducingAuxAux
      (reducing          : Bool) (maxFVars? : Option Nat)
      (type              : Expr)
      (k                 : Array Expr → Expr → MetaM α) : MetaM α := do
    let rec process (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (type : Expr) : MetaM α := do
      match type with
      | Expr.lam n d b c =>
        if fvarsSizeLtMaxFVars fvars maxFVars? then
          let d     := d.instantiateRevRange j fvars.size fvars
          let fvarId ← mkFreshId
          let lctx  := lctx.mkLocalDecl fvarId n d c.binderInfo
          let fvar  := mkFVar fvarId
          let fvars := fvars.push fvar
          process lctx fvars j b
        else
          let type := type.instantiateRevRange j fvars.size fvars;
          withReader (fun ctx => { ctx with lctx := lctx }) do
            withNewLocalInstancesImp fvars j do
              k fvars type
      | _ =>
        let type := type.instantiateRevRange j fvars.size fvars;
        withReader (fun ctx => { ctx with lctx := lctx }) do
          withNewLocalInstancesImp fvars j do
            if reducing && fvarsSizeLtMaxFVars fvars maxFVars? then
              let newType ← Lean.Meta.whnf type
              if newType.isLambda then
                process lctx fvars fvars.size newType
              else
                k fvars type
            else
              k fvars type
    process (← getLCtx) #[] 0 type

  private partial def lambdaTelescopeReducingAux (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
    match maxFVars? with
    | some 0 => k #[] type
    | _ => do
      let newType ← Lean.Meta.whnf type
      if newType.isLambda then
        lambdaTelescopeReducingAuxAux true maxFVars? newType k
      else
        k #[] type
  
  private partial def isClassExpensive? : Expr → MetaM (Option Name)
    | type => Lean.Meta.withReducible <| -- when testing whether a type is a type class, we only unfold reducible constants.
      lambdaTelescopeReducingAux type none fun xs type => do
        let env ← getEnv
        match type.getAppFn with
        | Expr.const c _ _ => do
          if isClass env c then
            return some c
          else
            -- make sure abbreviations are unfolded
            match (← Lean.Meta.whnf type).getAppFn with
            | Expr.const c _ _ => return if isClass env c then some c else none
            | _ => return none
        | _ => return none

  private partial def isClassImp? (type : Expr) : MetaM (Option Name) := do
    match (← isClassQuick? type) with
    | LOption.none   => pure none
    | LOption.some c => pure (some c)
    | LOption.undef  => isClassExpensive? type

end

variable [MonadControlT MetaM n] [Monad n]


private partial def lambdaBoundedTelescopeImp (e : Expr) (consumeLet : Bool) (k : Array Expr → Expr → MetaM α) (maxDepth : Nat): MetaM α := do
  let rec process (consumeLet : Bool) (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (e : Expr) (maxDepth : Nat): MetaM α := do
    match maxDepth, consumeLet, e with
    | 0, _, _ =>
      let e := e.instantiateRevRange j fvars.size fvars
      withReader (fun ctx => { ctx with lctx := lctx }) do
        withNewLocalInstancesImp fvars j do
          k fvars e
    | _, _, Expr.lam n d b c =>
      let d := d.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshId
      let lctx := lctx.mkLocalDecl fvarId n d c.binderInfo
      let fvar := mkFVar fvarId
      process consumeLet lctx (fvars.push fvar) j b (maxDepth - 1)
    | _, true, Expr.letE n t v b _ => do
      let t := t.instantiateRevRange j fvars.size fvars
      let v := v.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshId
      let lctx := lctx.mkLetDecl fvarId n t v
      let fvar := mkFVar fvarId
      process true lctx (fvars.push fvar) j b (maxDepth - 1)
    | _, _, e =>
      let e := e.instantiateRevRange j fvars.size fvars
      withReader (fun ctx => { ctx with lctx := lctx }) do
        withNewLocalInstancesImp fvars j do
          k fvars e
  process consumeLet (← getLCtx) #[] 0 e maxDepth

/-- Similar to `forallTelescope` but for lambda expressions. -/
def lambdaBoundedTelescope (type : Expr) (k : Array Expr → Expr → n α) (maxDepth : Nat): n α :=
  Lean.Meta.map2MetaM (fun k => lambdaBoundedTelescopeImp type false k maxDepth) k

-- Printing

def printExpr (e : Expr) (currNamespace : Name) : MetaM Format := do PrettyPrinter.ppExpr currNamespace [] e

def levelParamsToMessageData (levelParams : List Name) : MessageData :=
  match levelParams with
  | []    => ""
  | u::us => do
    let mut m := m!".\{{u}"
    for u in us do
      m := m ++ ", " ++ u
    return m ++ "}"


def mkHeader (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) (safety : DefinitionSafety) (numParams : Option Nat := none): PortM Format := do
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
  
  let numParams ← 
    if numParams.isNone then some $ type.forallDepth []
    else numParams

  let formatType (args : Array Expr) (resType : Expr) : MetaM Format := do 
    let mut s : Format := (← m.toString)
    for arg in args do
      let argType ← Meta.inferType arg
      let localDecl ← Meta.getFVarLocalDecl arg
      -- println! "RIP arg\n{rip (← printExpr arg currNamespace)}"
      -- println!  "RIP argtype\n{rip (← printExpr argType currNamespace)}"
      match localDecl.binderInfo with
      | BinderInfo.default        => s := s ++ Format.line ++ Format.fill (Format.nest 2 ("(" ++ (← printExpr arg currNamespace) ++ " :" ++ Format.line ++ (← printExpr argType currNamespace) ++ ")"))
      | BinderInfo.implicit       => s := s ++ Format.line ++ Format.fill (Format.nest 2 ("{" ++ (← printExpr arg currNamespace) ++ " :" ++ Format.line ++ (← printExpr argType currNamespace) ++ "}"))
      | BinderInfo.strictImplicit => s := s ++ Format.line ++ Format.fill (Format.nest 2 ("⦃" ++ (← printExpr arg currNamespace) ++ " :" ++ Format.line ++ (← printExpr argType currNamespace) ++ "⦄"))
      | BinderInfo.instImplicit   => do
          let str ← printExpr arg currNamespace
          if (toString str).startsWith "_" then
            s := s ++ Format.line ++ Format.fill (Format.nest 2 ("[" ++ (← printExpr argType currNamespace) ++ "]"))
          else 
            s := s ++ Format.line ++ Format.fill (Format.nest 2 ("[" ++ (← printExpr arg currNamespace) ++ " :" ++ Format.line ++ (← printExpr argType currNamespace) ++ "]"))
      | BinderInfo.auxDecl        => println! "ERROR: argument {arg} is auxDecl"
    match resType with
    | Expr.sort _ _ => ()
    | _ =>
      s := s ++ " :" ++ Format.line ++ Format.fill (Format.nest 2 ((← PrettyPrinter.ppExpr currNamespace [] resType)))
    Format.fill (Format.nest 2 s)

  let ftype : Format ← liftMetaM (@Meta.forallBoundedTelescope MetaM _ _ _ type numParams formatType)

  return ftype


def sorryTerm := mkApp (mkApp (mkConst `sorryAx []) (mkConst `Nat)) (mkConst `Bool.false)
def containsAutoGenerated (value : Expr) : PortM Bool := do 
    match value with
    | Expr.forallE _ d b _   => (← containsAutoGenerated d) || (← containsAutoGenerated b)
    | Expr.lam _ d b _       => (← containsAutoGenerated d) || (← containsAutoGenerated b)
    | Expr.mdata _ e _       => (← containsAutoGenerated e)
    | Expr.letE _ t v b _    => (← containsAutoGenerated t) || (← containsAutoGenerated v) || (← containsAutoGenerated b)
    | Expr.app f a _         => (← containsAutoGenerated f) || (← containsAutoGenerated a)
    | Expr.proj _ _ e _      => (← containsAutoGenerated e)
    | Expr.const n _ _       => do
      println! "found constant {n}"
      let s ← get 
      println! "  -> {(s.name2info.findD n {}).autoGenerated} {n.isInternal}"
      return (s.name2info.findD n {}).autoGenerated || n.isInternal
    | e                      => false

def replaceAutoGenerated (id : Name) (value : Expr) : PortM Expr := do 
    match value with
    | Expr.forallE n d b dt  => Expr.forallE n (← replaceAutoGenerated id d) (← replaceAutoGenerated id b) dt
    | Expr.lam n d b dt      => Expr.lam n (← replaceAutoGenerated id d) (← replaceAutoGenerated id b) dt
    | Expr.mdata m e d       => Expr.mdata m (← replaceAutoGenerated id e) d
    | Expr.letE n t v b d    => Expr.letE n (← replaceAutoGenerated id t) (← replaceAutoGenerated id v) (← replaceAutoGenerated id b) d
    | Expr.app f a d         => 
      match (← replaceAutoGenerated id f) with 
      | Expr.app (Expr.app (Expr.const `sorryAx _ _) _ _) _ _ => sorryTerm
      | e => Expr.app e (← replaceAutoGenerated id a) d
    | Expr.proj n x e d      => Expr.proj n x (← replaceAutoGenerated id e) d
    | e@(Expr.const n _ _)   => do
      let s ← get 
      if id.isPrefixOf n then
        return sorryTerm 
      else 
        return e
    | e                      => e

def printDefLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (value : Expr) (currNamespace : Name) (safety := DefinitionSafety.safe) : PortM Format := do
  let mut m : Format := (← mkHeader kind id levelParams type currNamespace safety)
  if useSorry then
    m := m ++ " :=" ++ Format.line ++ "sorry"
  else
    -- println! "printing value {value}"
    let numParams ← type.forallDepth []
    println! "depth: {numParams}"
    let value ← replaceAutoGenerated id value
    let formatValue (args : Array Expr) (resValue : Expr) : MetaM Format := do 
      (← PrettyPrinter.ppExpr currNamespace [] resValue)
      
    let fvalue : Format ← liftMetaM (@lambdaBoundedTelescope MetaM _ _ _ value formatValue numParams)
    
    let svalue := toString fvalue
    if svalue.length > 1000 then
      m := m ++ " :=" ++ Format.line ++ "sorry"
    else
      if (kind = "theorem" && svalue.count '\n' > 2) then 
        m := m ++ " :=" ++ Format.line ++ "sorry"
      else
        m := m ++ " :=" ++ Format.line ++ fvalue
  -- println! "RIPdeflike\n{rip (Format.fill m)}"
  pure $ Format.fill $ Format.nest 2 $ m

def mkHeader' (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (isUnsafe : Bool) (currNamespace : Name) (numParams : Option Nat := none): PortM Format :=
  mkHeader kind id levelParams type currNamespace (if isUnsafe then DefinitionSafety.unsafe else DefinitionSafety.safe) numParams

def printAxiomLike (kind : String) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) (isUnsafe := false) : PortM Format := do
  mkHeader' kind id levelParams type isUnsafe currNamespace

def printQuot (kind : QuotKind) (id : Name) (levelParams : List Name) (type : Expr) (currNamespace : Name) : PortM Format := do
  printAxiomLike "Quotient primitive" id levelParams type currNamespace

def findExtensions (id : Name) : PortM (Array Expr) := do 
  -- TODO : Would be more clever to use the constructor
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
    if name.toString.startsWith extensionsPrefix && not (name.toString = (extensionsPrefix ++ "fun")) && info.position = pos then 
      println! "candidate : {name} of type {info.type}"
      res := res.push info.type.forallRoot
     
  return res

def extractStructureName (e : Expr) : Name := do
  match e with 
  | Expr.app e1 e2 _ => extractStructureName e1
  | Expr.const n _ _ => n
  | _ => panic! s!"WRONG STRUCT FORMAT in {e}"

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
    
    


  match (← getEnv).find? (id) with
  | ConstantInfo.inductInfo { levelParams := us, numParams := np, numIndices := numIndices, type := t, ctors := ctors, isUnsafe := u, .. } =>
    if ctors.length != 1 then 
      panic! s!"{id} is not a struct (too many constructors)"
    else 
      println! "real num params {np}"
      let cinfo ← getConstInfo ctors.head!
      return ← Meta.forallBoundedTelescope cinfo.type none (findFieldsAux np)
  | _ => panic! s!"{id} is not a struct (not inductive type)"

def printInduct (id : Name) (levelParams : List Name) (numParams : Nat) (numIndices : Nat) (type : Expr)
    (ctors : List Name) (isUnsafe : Bool) (currNamespace : Name) (keyword : String): PortM Format := do
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
    let header ← mkHeader' kind id levelParams type isUnsafe currNamespace numParams
    
    let extensions ← findExtensions id
    println! "extensions: {extensions}"
    

    let ctor ← ctors.head!
    println! "constructor: {ctor}"

    let formatFields (fields : Array Expr) (resType : Expr) : MetaM Format := do 
      let mut f : Format := header
      let mut fields2Ignore := [] -- TODO : This list is useless (the fields of the extended structures are not in the constructor)
      if extensions != #[] then 
        let mut fextensions : Format := "extends" ++ Format.line
        println! "fields"
        for field in fields do
          println! "{field} aka {(← printExpr field currNamespace)}"
        
        let mut i := 0
        for extension in extensions do 
          println! "instanciating {extension}"
          let extension ← extension.liftLooseBVars 0 (fields.size - numParams - 1)
          
          println! "instanciating {extension}"

          let extension ← (extension.instantiateRev fields)
          println! "=> {(← printExpr extension Name.anonymous)}"

          if i > 0 then
            fextensions := fextensions ++ "," ++ Format.line
          fextensions := fextensions ++ (← printExpr extension currNamespace)

          i := i + 1
          
          let extensionName ← extractStructureName extension
          println! "struct name {(extractStructureName extension)}"
          let extensionFields : List Name ← findFields extensionName
          fields2Ignore := fields2Ignore.append extensionFields
        fextensions := Format.fill (Format.nest 2 fextensions)
        f := Format.fill (Format.nest 2 (f ++ Format.nest 2 (Format.line ++ fextensions ++ Format.line ++ "where")))
      else 
        f := Format.fill (Format.nest 2 (f ++ Format.nest 2 (Format.line ++ "where")))
      f := Format.fill f
      let mut i := 0
      let ctx ← getLCtx

      let mut ffields := Format.nil
      for field in fields do
        let fieldName ← (ctx.getFVar! field).userName
        if i >= numParams then
          if fields2Ignore.contains fieldName|| fieldName.toString.startsWith "_" then 
            println! "ignored field {fieldName}"
          else
          let fieldType ← Meta.inferType field
          ffields := ffields ++ Format.line ++ Format.fill (Format.nest 2 ((← printExpr field currNamespace) ++ " :" ++ Format.line ++ (← printExpr fieldType currNamespace)))
        i := i + 1
      return f ++ (Format.nest 2 ffields)

    let formatFieldsCustomCtor (ctorname : Name) (fields : Array Expr) (resType : Expr) : MetaM Format := do 
      let mut f : Format := header
      let mut fields2Ignore := []
      if extensions != #[] then 
        let mut fextensions : Format := "extends" ++ Format.line
        println! "fields"
        for field in fields do
          println! "{field} aka {(← printExpr field currNamespace)}"
        
        let mut i := 0
        for extension in extensions do 
          println! "instanciating {extension}"
          let extension ← extension.liftLooseBVars 0 (fields.size - numParams - 1)
          
          println! "instanciating {extension}"

          let extension ← (extension.instantiateRev fields)
          println! "=> {(← printExpr extension Name.anonymous)}"

          if i > 0 then
            fextensions := fextensions ++ "," ++ Format.line
          fextensions := fextensions ++ (← printExpr extension currNamespace)

          i := i + 1
          
          let extensionName ← extractStructureName extension
          println! "struct name {(extractStructureName extension)}"
          let extensionFields : List Name ← findFields extensionName
          fields2Ignore := fields2Ignore.append extensionFields
        fextensions := Format.fill (Format.nest 2 fextensions)
        f := Format.fill (Format.nest 2 (f ++ Format.nest 2 (Format.line ++ fextensions ++ Format.line ++ "where")))
      else 
        f := Format.fill (Format.nest 2 (f ++ Format.nest 2 (Format.line ++ "where")))
      f := Format.fill f
      let mut i := 0
      let ctx ← getLCtx

      let mut ffields := Format.nil
      for field in fields do
        let fieldName ← (ctx.getFVar! field).userName
        if i >= numParams then
          if fields2Ignore.contains fieldName|| fieldName.toString.startsWith "_" then 
            println! "ignored field {fieldName}"
          else
          let fieldType ← Meta.inferType field
          ffields := ffields ++ Format.line ++ Format.fill (Format.nest 2 ("(" ++ (← printExpr field currNamespace) ++ " :" ++ Format.line ++ (← printExpr fieldType currNamespace) ++ ")"))
        i := i + 1
      return f ++ Format.nest 2 (Format.line ++ Format.group (Format.nest 2 (ctorname.toString ++ " ::" ++ ffields)))
    
    let cinfo ← getConstInfo ctor
    
    if ctor.last = "mk" then 
      return (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type none formatFields)
    else 
      return (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type none (formatFieldsCustomCtor ctor.last))

  else
    let kind ← do 
      if info.class then "class inductive"
      else "inductive"
    println! "INDUCTIVE {id} kind: {kind} numParams: {numParams} numIndices: {numIndices}"

    let mut m ← mkHeader' kind id levelParams type isUnsafe currNamespace numParams
    m := Format.fill ( Format.nest 2 (m ++ Format.nest 2 (Format.line ++ "where")))

    let formatCtorType (args : Array Expr) (resType : Expr) : MetaM Format := do 
      let mut s : Format := ""
      let mut explicit := false
      for arg in args do
        let localDecl ← Meta.getFVarLocalDecl arg
        match localDecl.binderInfo with
        | BinderInfo.default => explicit := true
        | _                  => ()
      if explicit then s := s ++ " {}"
      s := s ++ " :" ++ Format.line ++ (← printExpr resType currNamespace)
      return Format.fill (Format.nest 4 s)

    for ctor in ctors do
      let cinfo ← getConstInfo ctor
      m := m ++ Format.line ++ "| " ++ (← ctor.removePrefix id).toString
      m := m ++ (← liftMetaM $ Meta.forallBoundedTelescope cinfo.type (some numParams) formatCtorType)
    return m



def constantToString (id : Name) (currNamespace : Name) (keyword : String): PortM Format := do
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

