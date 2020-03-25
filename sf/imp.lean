
-- Inspired by Software Foundations Vol. 1: Imp chapter

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Data definitions
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

-- Arithmetic unary operations
inductive AUOp
| inc : AUOp
| dec : AUOp

-- Arithmetic binary operations
inductive ABOp
| add : ABOp
| sub : ABOp
| mul : ABOp

-- Arithmetic expressions
inductive AExp
| num : Nat → AExp
| var : String → AExp
| uop : AUOp → AExp → AExp
| bop : ABOp → AExp → AExp → AExp

-- Boolean-returning arithmetic binary operations
inductive BBOp
| eq  : BBOp
| le  : BBOp

-- Boolean expressions
inductive BExp
| bool : Bool → BExp
| bop  : BBOp → AExp → AExp → BExp
| not  : BExp → BExp
| and  : BExp → BExp → BExp
| or   : BExp → BExp → BExp

-- Commands
inductive Com
| skip  : Com
| set   : String → AExp → Com
| seq   : Com → Com → Com
| cond  : BExp → Com → Com → Com
| while : BExp → Com → Com

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Evaluation Functions
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --


def State : Type := String → Nat

def init_state : State := λ _ => 0

namespace AUOp
open Nat

def eval : AUOp → Nat → Nat
| inc, n => n + 1
| dec, 0 => 0
| dec, (succ n) => n

end AUOp

namespace ABOp

def eval : ABOp → Nat → Nat → Nat
| add, x, y => x + y
| sub, x, y => x - y
| mul, x, y => x * y

end ABOp

namespace AExp

def eval : State → AExp → Nat
| _, num n => n
| ρ, var x => ρ x
| ρ, uop op e => op.eval (e.eval ρ)
| ρ, bop op e₁ e₂ => op.eval (e₁.eval ρ) (e₂.eval ρ)

namespace Tests
open AUOp ABOp
#eval (num 42).eval init_state == 42
#eval (var "x").eval init_state == 0
#eval ((uop inc) (var "x")).eval init_state == 1
#eval ((uop dec) (num 42)).eval init_state == 41
#eval ((bop add) (num 42) ((uop inc) (num 1))).eval init_state == 44
end Tests

end AExp



namespace BBOp

def eval : BBOp → Nat → Nat  → Bool
| eq, n₁, n₂ => n₁ == n₂
| le, n₁, n₂ => n₁ <= n₂

end BBOp


namespace BExp
open BBOp

def eval : State → BExp → Bool
| _, bool b => b
| ρ, bop op e₁ e₂ => op.eval (e₁.eval ρ) (e₂.eval ρ)
| ρ, not e₁ => ¬ e₁.eval ρ
| ρ, and e₁ e₂ => e₁.eval ρ && e₂.eval ρ
| ρ, or e₁ e₂ => e₁.eval ρ || e₂.eval ρ

namespace Tests
open AExp AUOp ABOp
#eval (bool true).eval init_state == true
#eval (bop eq (num 1) (num 1)).eval init_state == true
#eval (bop le (num 1) (num 1)).eval init_state == true
#eval (bop le (num 1) (num 2)).eval init_state == true
#eval (bop le (num 2) (num 1)).eval init_state == false
#eval (not (bool true)).eval init_state == false
#eval (and (bool true) (bool false)).eval init_state == false
#eval (or (bool false) (bool true)).eval init_state == true
end Tests

end BExp

-- Environment extension
def ext (p : String × Nat) (ρ : State) : State :=
λ y => if p.fst == y then p.snd else ρ y

-- Single-step reduction relation
inductive Step : State → Com → State → Prop
| skip (ρ:State) : 
  Step ρ Com.skip ρ
| set (ρ:State) (e:AExp) (n:Nat) (x:String) : 
  e.eval ρ = n 
  → Step ρ (Com.set x e) (ext (x,n) ρ)
| seq (ρ₁ ρ₂ ρ₃:State) (c₁ c₂:Com) :
  Step ρ₁ c₁ ρ₂
  → Step ρ₂ c₂ ρ₃
  → Step ρ₁ (Com.seq c₁ c₂) ρ₃
| if_true (ρ₁ ρ₂:State) (e:BExp) (c₁ c₂:Com) :
  e.eval ρ₁ = true
  → Step ρ₁ c₁ ρ₂
  → Step ρ₁ (Com.cond e c₁ c₂) ρ₂
| if_false (ρ₁ ρ₂:State) (e:BExp) (c₁ c₂:Com) :
  e.eval ρ₁ = false
  → Step ρ₁ c₂ ρ₂
  → Step ρ₁ (Com.cond e c₁ c₂) ρ₂
| while_false (e:BExp) (ρ:State) (c:Com) :
  e.eval ρ = false
  → Step ρ (Com.while e c) ρ



-- def eval : Nat → Com → State → State 

--def aeval : AExp → Nat
--| num n => n
--| 


