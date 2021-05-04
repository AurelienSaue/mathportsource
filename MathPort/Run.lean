/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import MathPort.Basic
import MathPort.Rules
import MathPort.ParseExport
import MathPort.ProcessActionItem
import MathPort.Path

import Lean
import Std.Data.HashMap
import Std.Data.HashSet

open Lean Lean.Meta
open Std (HashMap HashSet)

namespace MathPort
namespace Run -- TODO: better name. runAll? schedule?

abbrev Job := Task (Except IO.Error Unit)

instance : Inhabited Job := ⟨⟨pure ()⟩⟩

structure Context where
  proofs    : Bool
  source    : Bool

structure State where
  path2task : HashMap String Job := {}

abbrev RunM := ReaderT Context (StateRefT State IO)

-- TODO: weave
def rulesFilename := "rules.txt"

def parseTLeanImports (target : Path34) : IO (List Path34) := do
  let line ← IO.FS.withFile target.toTLean IO.FS.Mode.read fun h => h.getLine
  let tokens := line.trim.splitOn " " |>.toArray
  let nImports := tokens[1].toNat!
  let mut paths := #[]
  for i in [:nImports] do
    if tokens[2+2*i+1] ≠ "-1" then throw $ IO.userError "found relative import!"
    let dotPath : DotPath := ⟨tokens[2+2*i]⟩
    paths := paths.push $ ← resolveDotPath dotPath
  return paths.toList

def bindTasks (tasks : List Job) (k : Unit → IO Job) : IO Job :=
  match tasks with
  | []          => k ()
  | task::tasks => IO.bindTask task λ
    | Except.ok _ => bindTasks tasks k
    | Except.error err => throw err

@[implementedBy withImportModules]
constant withImportModulesConst {α : Type} (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) (x : Environment → IO α) : IO α :=
  throw $ IO.userError "NYI"

def genOLeanFor (proofs : Bool) (source : Bool) (target : Path34) : IO Unit := do
  println! s!"[genOLeanFor] START {target.mrpath.path}"
  createDirectoriesIfNotExists target.toLean4olean

  let imports : List Import := [{ module := `Init : Import }, { module := `PrePort : Import }]
    ++ (← parseTLeanImports target).map fun path => { module := parseName path.toLean4dot }

  -- NEW
  let hsource3 : IO.FS.Handle ← IO.FS.Handle.mk target.toLean3Source IO.FS.Mode.read false
  let hsource4 : IO.FS.Handle ← IO.FS.Handle.mk target.toLean4autolean IO.FS.Mode.write false

  

  -- if source then
  --   println! "Processing imports"
  --   for import in imports do
  --     hsource4.putStr "import "
  --     hsource4.putStrLn $ toString import.module
  --     println! "IMPORT {modPathToFilePath import.module}"
  --   -- if importPostport then
  --   --   hsource4.putStrLn "import PostPort"
  --   hsource4.putStr "\n"

  withImportModulesConst imports (opts := {}) (trustLevel := 0) $ λ env₀ => do
    let env₀ := env₀.setMainModule target.mrpath.toDotPath.path
    let _ ← PortM.toIO (ctx := { proofs := proofs, source := source, path := target }) (env := env₀) do
      parseRules rulesFilename
      IO.FS.withFile target.toTLean IO.FS.Mode.read fun h => do
       let _ ← h.getLine -- discard imports
       let mut actionItems := #[]
       while (not (← h.isEof)) do
         let line := (← h.getLine).dropRightWhile λ c => c == '\n'
         if line == "" then continue
         actionItems := actionItems.append (← processLine line).toArray

       let mut isIrreducible : Bool := false
       let mut comment := false
       let mut doneImports := false

       for actionItem in actionItems do
         processActionItem actionItem

         if source then
          let sourceStr ← actionItemToSource actionItem
          
          for i in [(← get).prevLine : (← get).currLine] do 
            let line ← hsource3.getLine 

            if line.startsWith "--" then 
              println! "comment '{line}'"
              hsource4.putStr line

            if comment || line.startsWith "/-" then 
              println! "comment '{line}'"
              comment := true
              hsource4.putStr line
            
            if not doneImports && not comment && line.length > 0 then
              println! "Processing imports"
              for import in imports do
                hsource4.putStr "import "
                hsource4.putStrLn $ toString import.module
                println! "IMPORT {modPathToFilePath import.module}"
              -- if importPostport then
              --   hsource4.putStrLn "import PostPort"
              hsource4.putStr "\n"
              doneImports := true

              println! "Processing levelParams"
              -- if declareUniverses then
              --   let allLevelParams ← findAllLevelParams constants
              --   if not allLevelParams.isEmpty then
              --     hsource4.putStr "universes "
              --     for u in allLevelParams do 
              --       hsource4.putStr $ toString u ++ " "
              --     hsource4.putStr "\n\n"
              
              hsource4.putStr "namespace Mathlib\n\n"
              
            if comment && line.endsWith "-/\n" then 
              println! "end of comment"
              comment := false
              hsource4.putStr "\n"
              
            
            
            if line.startsWith "namespace" then 
              match line.splitOn " " with 
              | ["namespace", name] => do 
                modify λ s => { s with currNamespace := s.currNamespace.append name.toName}
                hsource4.putStr $ "namespace " ++ name ++ "\n\n"
              | _ => println! "Unrecognized namespace pattern: {line}"
            
            if line.startsWith "end" then 
              match line.splitOn " " with 
              | ["end", name] => do 
                if name.toName.isSuffixOf (← get).currNamespace then 
                  modify λ s => { s with currNamespace := s.currNamespace.removeSuffix name.toName}
                  hsource4.putStr $ "end " ++ name ++ "\n\n"
              | _ => ()
          
          modify λ s => { s with prevLine := s.currLine}
          hsource4.putStr sourceStr
      let env ← getEnv
      writeModule env target.toLean4olean
      println! s!"[genOLeanFor] END   {target.mrpath.path}"
    pure ()

partial def visit (depth : Nat) (target : Path34) : RunM Job := do
  match (← get).path2task.find? target.toTLean with
  | some task => pure task
  | none      => do
    if (← IO.fileExists target.toLean4olean) && depth > 0 then
      IO.asTask (pure ())
    else
      let paths ← parseTLeanImports target
      let cjobs ← paths.mapM (visit (depth + 1))
      let job : Job ← bindTasks cjobs λ _ => IO.asTask $ genOLeanFor (← read).proofs (← read).source target
      modify λ s => { s with path2task := s.path2task.insert target.toTLean job }
      pure job


end Run

open Run

unsafe def run (proofs : Bool) (source : Bool) (target : Path34) : IO Unit := do
  initSearchPath s!"{Lean4LibPath}:{Lib4Path}"
  let job ← (visit 0 target) { proofs := proofs, source := source } |>.run' (s := {})
  let result ← IO.wait job
  match result with
  | Except.ok _ => pure ()
  | Except.error err => throw err


end MathPort
