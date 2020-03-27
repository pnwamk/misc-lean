-- Some simple programming language modeling, using lean4
-- commit 4296e1d83e734b18b4787329e4195569c0518325 
-- from Fri Mar 20 18:32:04 2020 -0700
import Init.Data.String

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Data definitions
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

def Var := String

-- Arithmetic unary operations
inductive Ty : Type
| int : Ty
| bool : Ty
--|sum : Ty → Ty → Ty

-- Arithmetic binary operations
inductive Const : Type
| int : Int → Const
| bool : Bool → Const
--|left : Const → Ty → Const
--|right : Ty → Const → Const

instance intToConst : HasCoe Int Const := ⟨Const.int⟩
instance boolToConst : HasCoe Bool Const := ⟨Const.bool⟩

inductive UOp : Type
| inc
| dec
| neg
| zero?
| not

inductive BOp : Type
| add
| sub
| mul
  

-- Arithmetic expressions
inductive Exp : Type
| var    : Var → Exp
| const  : Const → Exp
| uop    : UOp → Exp → Exp
| bop    : BOp → Exp → Exp → Exp
| cond   : Exp → Exp → Exp → Exp
| letvar : Var → Exp → Exp → Exp
--|left  : Exp → Ty → Exp
--|right : Ty → Exp → Exp
--|elim  : Exp → Ty → Ty → Var


namespace Exp
open UOp BOp Const

private def ci := λ n => const $ int n
private def cb := λ b => const $ bool b

def ex1 : Exp := (ci 42)
def ex2 : Exp := (cb true)
def ex3 : Exp := (uop inc (ci 41))
def ex4 : Exp := (uop dec (const (int 43)))
def ex5 : Exp := (uop neg (bop sub (ci 0) (ci 42)))
def ex6 : Exp := (uop zero? (ci 0))
def ex7 : Exp := (bop add (ci 41) (ci 1))
def ex8 : Exp := (bop sub (ci 43) (ci 1))
def ex9 : Exp := (bop mul (ci 21) (ci 2))
def ex10 : Exp := (uop not (uop zero? (ci 1)))
def ex11 : Exp := (cond (uop not (uop zero? (ci 42))) (ci 42) (ci 0))
def ex12 : Exp := (cond (uop not (uop zero? (ci 0))) (ci 0) (ci 42))
def ex13 : Exp := (letvar "x" (cb true)
                    (cond (var "x") (ci 42) (ci 0)))
def ex14 : Exp := (letvar "x" (uop inc (ci 41))
                    (cond (cb true) (var "x") (ci 0)))
def ex15 : Exp := (letvar "x" (uop inc (ci 39))
                    (letvar "x" (uop inc (var "x"))
                      (uop inc (var "x"))))

end Exp

def Env : Type := Var → Option Const

namespace Env

def empty : Env := λ _ => none
def extend (ρ : Env) (x : Var) (c:Const) : Env :=
  λ y => if x == y then some c else (ρ y)

end Env

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Interpreter
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

namespace UOp

def interp : UOp → Const → Option Const
| inc,   (Const.int n)  => some $ Const.int $ n + 1
| dec,   (Const.int n)  => some $ Const.int $ n - 1
| neg,   (Const.int n)  => some $ Const.int $ 0 - n
| zero?, (Const.int n)  => some $ Const.bool $ n == 0
| not,   (Const.bool b) => some $ Const.bool $ ¬ b
| _,_ => none

end UOp

namespace BOp

def interp : BOp → Const → Const → Option Const
| add, (Const.int x), (Const.int y)  => some $ Const.int $ x + y
| sub, (Const.int x), (Const.int y)  => some $ Const.int $ x - y
| mul, (Const.int x), (Const.int y)  => some $ Const.int $ x * y
| _,_,_ => none

end BOp


namespace Exp

def interp : Env → Exp → Option Const
| ρ, var x => ρ x
| ρ, const c => c
| ρ, uop op e => do
  v ← interp ρ e;
  UOp.interp op v
| ρ, bop op e₁ e₂ => do
  v₁ ← interp ρ e₁;
  v₂ ← interp ρ e₂;
  BOp.interp op v₁ v₂
| ρ, cond e₁ e₂ e₃ =>
  match interp ρ e₁ with
  | some (Const.bool true) => interp ρ e₂
  | some (Const.bool false) => interp ρ e₃
  | _ => none
| ρ, letvar x e₁ e₂ => do
  v₁ ← interp ρ e₁;
  let ρ' := Env.extend ρ x v₁;
  interp ρ' e₂

end Exp


def TyEnv : Type := Var → Option Ty

namespace TyEnv

def empty : TyEnv := λ _ => none
def extend (Γ : TyEnv) (x : Var) (t:Ty) : TyEnv :=
  λ y => if x == y then some t else (Γ y)

end TyEnv


namespace Const

def typeof : Const → Ty
| int _ => Ty.int
| bool _ => Ty.bool

end Const


namespace UOp

def typeof : UOp → (Ty × Ty)
| inc   => (Ty.int, Ty.int)
| dec   => (Ty.int, Ty.int)
| neg   => (Ty.int, Ty.int)
| zero? => (Ty.int, Ty.bool)
| not   => (Ty.bool, Ty.bool)
end UOp


namespace BOp

def typeof : BOp → (Ty × Ty × Ty)
| add   => (Ty.int, Ty.int, Ty.int)
| sub   => (Ty.int, Ty.int, Ty.int)
| mul   => (Ty.int, Ty.int, Ty.int)

end BOp


inductive TypeOf : TyEnv → Exp → Ty → Prop
| var (Γ:TyEnv) x t :
  (Γ x) = (some t)
  → TypeOf Γ (Exp.var x) t
| const Γ c t :
  Const.typeof c = t
  → TypeOf Γ (Exp.const c) t
| uop Γ op e t t' :
  TypeOf Γ e t
  → UOp.typeof op = (t, t')
  → TypeOf Γ (Exp.uop op e) t'
| bop Γ op e₁ e₂ t₁ t₂ t₃ :
  TypeOf Γ e₁ t₁
  → TypeOf Γ e₂ t₂
  → BOp.typeof op = (t₁, t₂, t₃)
  → TypeOf Γ (Exp.bop op e₁ e₂) t₃
| cond Γ e₁ e₂ e₃ t :
  TypeOf Γ e₁ Ty.bool
  → TypeOf Γ e₂ t
  → TypeOf Γ e₃ t
  → TypeOf Γ (Exp.cond e₁ e₂ e₃) t
| letvar Γ x e₁ e₂ t₁ t₂ :
  TypeOf Γ e₁ t₁
  → TypeOf (TyEnv.extend Γ x t₁) e₂ t₂
  → TypeOf Γ (Exp.letvar x e₁ e₂) t₂

-- In the given expression, substitute
-- the constant for the variable.
def subst : Exp → Const → Var → Exp
| Exp.var y, c, x => 
  if x == y then (Exp.const c) else Exp.var y
| Exp.const c, _, _ => 
  Exp.const c
| Exp.uop op e, c, x => 
  Exp.uop op (subst e c x)
| Exp.bop op e₁ e₂, c, x => 
  Exp.bop op (subst e₁ c x) (subst e₂ c x)
| Exp.cond e₁ e₂ e₃, c, x => 
  Exp.cond (subst e₁ c x) (subst e₂ c x) (subst e₃ c x)
| Exp.letvar y e₁ e₂, c, x => 
  let e₁' := (subst e₁ c x);
  if x == y then
    Exp.letvar y e₁' e₂
  else
    Exp.letvar y e₁' (subst e₂ c x)

-- A single reduction step.
inductive Step : Exp → Exp → Prop 
| uop_red op c₁ c₂ :
  UOp.interp op c₁ = some c₂
  → Step (Exp.uop op (Exp.const c₁)) (Exp.const c₂)
| bop_red op c₁ c₂ c₃ :
  BOp.interp op c₁ c₂ = some c₃
  → Step (Exp.bop op (Exp.const c₁) (Exp.const c₂)) (Exp.const c₃)
| cond_congr e₁ e₁' e₂ e₃ :
  Step e₁ e₁'
  → Step (Exp.cond e₁ e₂ e₃) (Exp.cond e₁' e₂ e₃)
| cond_red e₁ e₂ :
  Step (Exp.cond (Exp.const true) e₁ e₂) e₁
| letvar_congr x e₁ e₁' e₂ :
  Step e₁ e₁'
  → Step (Exp.letvar x e₁ e₂) (Exp.letvar x e₁' e₂)
| letvar_red x c e :
  Step (Exp.letvar x (Exp.const c) e) (subst e c x)


-- | Zero or more steps of reduction.
inductive Steps : Exp → Exp → Prop
| nil e : 
  Steps e e
| cons e₁ e₂ e₃ : 
  Step e₁ e₂
  → Steps e₂ e₃
  → Steps e₁ e₃



def env_sat (Γ:TyEnv) (ρ:Env) : Prop := forall x t, 
   (Γ x) = some t 
   → Exists (λ c => (ρ x) = some c ∧ Const.typeof c = t)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Theorems (N.B., seems like tactics have to
-- come after `new_frontend`... need to look
-- more into what it entails.)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --



new_frontend

macro try t:tactic : tactic => `($t <|> skip)

syntax "repeat" tactic : tactic
macro_rules
| `(tactic| repeat $t) => `(tactic| try ($t; repeat $t))

-- TODO there's got to be a way to just apply all
-- the known constructors for a type, right?
-- oooh, check out src/Init/Lean/Meta/Tactic
macro constr_TypeOf : tactic => 
`((apply TypeOf.var) <|>
  (apply TypeOf.const) <|>
  (apply TypeOf.uop) <|>
  (apply TypeOf.bop) <|>
  (apply TypeOf.cond) <|>
  (apply TypeOf.letvar))

macro typecheck : tactic =>
 `(repeat (constr_TypeOf <|> (exact rfl)))
  


open Exp

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Example evaluation tests
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

def test_eval : Exp → Option Const := interp Env.empty

private theorem test_ex1 : 
 test_eval ex1 = some (Const.int 42) := 
Eq.refl (some (Const.int 42))

private theorem test_ex2 :
 test_eval ex2 = some (Const.bool true) :=
Eq.refl (some (Const.bool true))

private theorem test_ex3 :
 test_eval ex3 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex4 :
 test_eval ex4 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex5 :
 test_eval ex5 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex6 :
 test_eval ex6 = some (Const.bool true) :=
Eq.refl (some (Const.bool true))

private theorem test_ex7 :
 test_eval ex7 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex8 :
 test_eval ex8 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex8 :
 test_eval ex8 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex9 :
 test_eval ex9 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex10 :
 test_eval ex10 = some (Const.bool true) :=
Eq.refl (some (Const.bool true))

private theorem test_ex11 :
 test_eval ex11 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex12 :
 test_eval ex12 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex13 :
 test_eval ex13 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

private theorem test_ex14 :
 test_eval ex14 = some (Const.int 42) :=
Eq.refl (some (Const.int 42))

theorem test_ex15 : 
 test_eval ex15 = some (Const.int 42) :=
begin
  exact rfl
end

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Example type checking tests
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

namespace Exp
open UOp BOp Const


theorem test_ex1 : 
 TypeOf TyEnv.empty ex1 Ty.int :=
begin
  typecheck
end

theorem test_ex2 : 
 TypeOf TyEnv.empty ex2 Ty.bool :=
begin
  typecheck
end

theorem test_ex3 : 
 TypeOf TyEnv.empty ex3 Ty.int :=
begin
  typecheck
end

theorem test_ex4 : 
 TypeOf TyEnv.empty ex4 Ty.int :=
begin
  typecheck
end

theorem test_ex5 : 
 TypeOf TyEnv.empty ex5 Ty.int :=
begin
  typecheck
end

theorem test_ex6 : 
 TypeOf TyEnv.empty ex6 Ty.bool :=
begin
  typecheck
end

theorem test_ex7 : 
 TypeOf TyEnv.empty ex7 Ty.int :=
begin
  typecheck
end

theorem test_ex8 : 
 TypeOf TyEnv.empty ex8 Ty.int :=
begin
  typecheck
end

theorem test_ex9 : 
 TypeOf TyEnv.empty ex9 Ty.int :=
begin
  typecheck
end

theorem test_ex10 : 
 TypeOf TyEnv.empty ex10 Ty.bool :=
begin
  typecheck
end

theorem test_ex11 : 
 TypeOf TyEnv.empty ex11 Ty.int :=
begin
  typecheck
end

theorem test_ex12 : 
 TypeOf TyEnv.empty ex12 Ty.int :=
begin
  typecheck
end

theorem test_ex13 : 
 TypeOf TyEnv.empty ex13 Ty.int :=
begin
  typecheck
end

theorem test_ex14 : 
 TypeOf TyEnv.empty ex14 Ty.int :=
begin
  typecheck
end

theorem test_ex15 : 
 TypeOf TyEnv.empty ex15 Ty.int :=
begin
  typecheck
end


end Exp


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Type safety theorems
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

namespace UOp
open Const

def interp_safe : forall op t₁ t₂ c,
 typeof op = (t₁, t₂)
 → Const.typeof c = t₁
 → Exists (λ c' => interp op c = some c' ∧ Const.typeof c' = t₂) :=
begin
  intros op t₁ t₂ c Hop Hc;
  cases op; cases c;
  apply (Exists.intro (Const.int $ a + 1));
  apply And.intro;
  exact rfl;
end

end UOp


-- UOp.interp is type safe
-- BOp.interp is type safe
-- BOp.interp is type safe

