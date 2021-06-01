structure A where 
  a : Nat
  b : Nat

#print A

structure B extends A where
  x : Nat

#print B


structure C (a b : Prop) : Prop where
  intro :: 
    (mp : a → b) 
    (mpr : b → a)

#print C


inductive loc 
where
| wildcard : loc
| ns : List (Option Nat) → loc