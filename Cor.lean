-- This module serves as the root of the `Cor` library.
-- Import modules here that should be built as part of the library.
import Cor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Algebraic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

-- Define Basic Recurrence structure
/-
  BR has the following structure:
  f = {φ₀,⊙,f₁}
  where φ₀ is a constant, ⬝ is either + or ⋆ and f₁ is a function over ℕ
-/
section BR

inductive BinOp
| Add
| Mul
deriving DecidableEq

@[simp]
def evalBinOp : BinOp → ℝ → ℝ → ℝ
| BinOp.Add => (· + ·)
| BinOp.Mul => (· * ·)

structure BR :=
  (r0 : ℝ)
  (bop : BinOp)
  (f : ℕ → ℝ)

def evalBR (br : BR) (n : ℕ) : ℝ :=
  match br with
  | ⟨r0, binop, f⟩ =>
    let vals : List ℝ := List.map f (List.range n)
    List.foldl (evalBinOp binop) r0 vals

@[simp]
lemma evalBR_zero (br : BR) :
  evalBR br 0 = br.r0 := by
  rfl

lemma evalBR_one (r0 : ℝ) (f1 : ℕ → ℝ) :
  evalBR { r0 := r0, bop := BinOp.Add, f := f1} 1 = r0 + f1 0 := by
  simp [evalBR]
  simp [List.map]

@[simp]
lemma evalBR_succ (br : BR) (n : ℕ) :
  evalBR br (n+1) = evalBinOp br.bop (evalBR br (n)) (br.f (n)) := by
  cases br with
  | mk r0 bop f =>
    induction n with
    | zero =>
      simp
      rw [evalBR]
      simp
      rw [List.range_succ]
      rw [List.map_append]
      simp
    | succ n ih =>
      simp
      cases bop
      case Add =>
        simp [evalBinOp]
        rw [ih]
        simp
        rw [evalBR]
        simp
        rw [List.range_succ]
        rw [List.map_append]
        simp [List.foldl]
        rw [evalBR]
        simp
        rw [List.range_succ]
        rw [List.map_append]
        simp
      case Mul =>
        simp [evalBinOp]
        rw [ih]
        simp
        rw [evalBR]
        simp
        rw [List.range_succ]
        rw [List.map_append]
        simp [List.foldl]
        rw [evalBR]
        simp
        rw [List.range_succ]
        rw [List.map_append]
        simp



lemma evalBR_add_equals_sum_f (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := x, bop := BinOp.Add, f := f1} n =
  x + ∑ i in Finset.range (n), f1 i := by
  induction n with
  | zero =>
    rw [evalBR]
    simp
  | succ n ih =>
    rw [evalBR_succ]
    simp
    rw [ih]
    rw [add_assoc]
    congr
    rw [Finset.sum_range_succ]


lemma evalBR_mul_equals_prd_f (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := x, bop := BinOp.Mul, f := f1} n =
  x * ∏ i in Finset.range n, f1 i := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih  =>
    rw [evalBR_succ]
    simp
    rw [ih]
    rw [Finset.prod_range_succ]
    rw [mul_assoc]

-- this is lemma 2.6 in the paper
lemma add_constant_to_BR (c : ℝ) (φ : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  c + evalBR {r0 := φ, bop := BinOp.Add, f := f1} n =
  evalBR {r0 := c + φ, bop := BinOp.Add, f := f1} n := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp [evalBinOp]
    rw [← add_assoc]
    rw [ih]

-- lemma 2.7
lemma mul_constant_to_BR (c : ℝ) (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  c * evalBR {r0 := x, bop := BinOp.Add, f := f1} n =
  evalBR {r0 := c * x, bop := BinOp.Add, f := λ n => c * f1 n} n := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [mul_add]
    rw [ih]

-- lemma 2.8 TODO: replace Ring with Reals somehow? or replace real with Ring R everywhere
-- TODO: this required adding c > 0 after using rpow_add and ih
lemma exp_with_add_BR (c : ℝ) (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) (h : 0 < c) :
 c ^ (evalBR {r0 := x, bop := BinOp.Add, f := f1} n) =
  evalBR {r0 := c ^ x, bop := BinOp.Mul, f := λ n => c ^ f1 n} n := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [Real.rpow_add]
    simp
    rw [ih]
    simp
    exact h

-- lemma 2.9
lemma mul_constant_to_mul_BR (c : ℝ) (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  c * evalBR {r0 := x, bop := BinOp.Mul, f := f1} n =
  evalBR {r0 := c * x, bop := BinOp.Mul, f := f1} n := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [← mul_assoc]
    rw [ih]

-- lemma 2.10
lemma br_pow_const (c : ℝ) (x : ℝ) (f1 : ℕ → ℝ)
 (n : ℕ) (h : 0 < c) :
  (evalBR {r0 := x, bop := BinOp.Mul, f := f1} n) ^ c = evalBR {r0 := x ^ c, bop := BinOp.Mul, f := f1 ^ c} n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [Real.mul_rpow]
    rw [ih]
    sorry -- have to use ring here also
    sorry


-- lemma 2.11
lemma log_br (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) (h1 : f1 (n) != 0 ∧ (evalBR {r0 := x, bop := BinOp.Mul, f := f1} n) != 0) :
  Real.log (evalBR {r0 := x, bop := BinOp.Mul, f := f1} n) = evalBR {r0 := Real.log x, bop := BinOp.Add, f := λ n => Real.log (f1 n)} n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [Real.log_mul]
    simp
    rw [ih]
    sorry
    sorry
    sorry




-- lemma 3.12 - this should be doable a lot better - why can simp not finish this after distributive? does it not work well over Finset and ℝ?
lemma add_add_BR_add_BR (x : ℝ) (y : ℝ) (f1 : ℕ → ℝ) (g1: ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := x, bop := BinOp.Add, f := f1} n + evalBR {r0 := y, bop := BinOp.Add, f := g1} n = evalBR {r0 := x + y, bop := BinOp.Add, f := λ n => f1 n + g1 n} n := by
  rw [evalBR_add_equals_sum_f]
  rw [evalBR_add_equals_sum_f]
  rw [evalBR_add_equals_sum_f]
  rw [add_assoc]
  rw [← add_assoc]
  rw [Finset.sum_add_distrib]
  rw [← add_assoc]
  rw [add_comm (x + _)]
  rw [add_assoc y]
  rw [add_assoc x]
  rw [add_comm x y]
  rw [add_assoc y]


open Finset
open BinOp
-- lemma 3.13
lemma mul_BR_mul_BR (φ0 ψ0 : ℝ) (f1 g1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := φ0, bop := BinOp.Add, f := f1} n *
  evalBR {r0 := ψ0, bop := BinOp.Add, f := g1} n =
  evalBR {r0 := φ0 * ψ0, bop := Add, f := λ n => (g1 n * evalBR {r0 := φ0, bop := Add, f := f1} (n) +
                 f1 n * evalBR {r0 := ψ0, bop := Add, f := g1} (n)) + f1 n * g1 n } (n) := by
    simp [evalBR_add_equals_sum_f]
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ]
      rw [sum_range_succ]
      rw [← add_assoc]
      rw [← add_assoc]
      rw [add_mul]
      rw [mul_add]
      rw [ih]
      rw [sum_range_succ]
      rw [mul_add]
      ring

-- lemma 3.14
lemma mul_br_mul_mul_BR (φ0 ψ0 : ℝ) (f1 g1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := φ0, bop := Mul, f := f1} n * evalBR {r0 := ψ0, bop := Mul, f := g1} n =
  evalBR {r0 := φ0 * ψ0, bop := Mul, f := λ n => (g1 * f1) n} n := by
  simp [evalBR_mul_equals_prd_f]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp [prod_range_succ]
    calc
      φ0 * ((∏ i ∈ range n, f1 i) * f1 n) * (ψ0 * ((∏ i ∈ range n, g1 i) * g1 n))
     _ = (φ0 * ∏ i ∈ range n, f1 i) * f1 n * (ψ0 * ∏ i ∈ range n, g1 i) * g1 n := by ring
     _ = (φ0 * ∏ i ∈ range n, f1 i) * (ψ0 * ∏ i ∈ range n, g1 i) * (f1 n * g1 n) := by ring
     _ = (φ0 * ψ0 * ∏ i ∈ range n, g1 i * f1 i) * (f1 n * g1 n) := by rw [ih]
    ring





end BR
open BinOp

/-
example:
  f1(i : ℕ) = (1 + i^2)

  x = 1;
  for (int i = 0; i < 4; i++) {
    x += f(i)
  }
-/
def f1 (n : ℕ) : ℝ := 1 + n^2


def ex1 (acc : ℝ) (n : ℕ) : ℝ :=
  (List.range n).foldl (λ acc i => acc + f1 i) acc

def myBR : BR :=
  BR.mk 1 BinOp.Add f1

#eval evalBR myBR 4
#eval ex1 1 4

section CR

inductive CR
| liftBRToCR : BR → CR
| recurCR : ℝ → BinOp → CR → CR


inductive PureCR (bop : BinOp)
| PureBR : ℝ → ℝ → PureCR bop
| recurPureCR : ℝ → PureCR bop → PureCR bop

open BR
open CR
open PureCR

def CR_to_BR : CR → BR
| (liftBRToCR br) => br
| (recurCR r0 bop cr') =>
  let br' := CR_to_BR cr'
  BR.mk r0 bop (λ n => evalBR br' n)


def evalCR (cr : CR) (n : ℕ) : ℝ :=
  evalBR (CR_to_BR cr) n



def PureCR_to_CR (bop : BinOp) (pcr : PureCR bop) : CR :=
match pcr with
| PureBR c0 _ => liftBRToCR (BR.mk c0 bop (λ c1 => c1))
| recurPureCR c0 pcr' => recurCR c0 bop (PureCR_to_CR bop pcr')


@[simp]
lemma evalBR_eq_evalCR_of_CR_to_BR (cr : CR) (n : ℕ) :
  evalBR (CR_to_BR cr) n = evalCR cr n := by
  rfl

@[simp]
lemma evalCR_zero (cr' : CR) (r : ℝ) (bop : BinOp) :
  evalCR (recurCR r bop cr') 0 = r := by
  unfold evalCR
  simp [evalBR]
  unfold CR_to_BR
  simp

lemma evalCR_succ (cr' : CR) (r : ℝ) (bop : BinOp) (n : ℕ):
  evalCR (recurCR r bop cr') (n+1)  = evalBinOp bop (evalCR (recurCR r bop cr') (n)) (evalBR (CR_to_BR cr') (n)) := by
  induction n with
  | zero =>
    simp
    rw [evalCR]
    rw [evalBR_succ]
    rw [evalBR_zero]
    dsimp [CR_to_BR] at *
    rw [evalCR]
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_eq_evalCR_of_CR_to_BR]
    rw [ih]
    rw [evalCR]
    rw [evalBR_succ]
    dsimp [CR_to_BR] at *
    simp
    congr




-- lemma 3.16
lemma add_const_to_CR (r c0 : ℝ) (cr : CR) (n : ℕ) :
  r + (evalCR (recurCR c0 Add cr) n) = evalCR (recurCR (c0 + r) Add cr) n := by
  induction n with
  | zero =>
    rw [evalCR]
    rw [← evalBR_eq_evalCR_of_CR_to_BR]
    unfold evalBR
    simp
    unfold CR_to_BR
    simp
    rw [add_comm]
  | succ n ih =>
    rw [evalCR_succ]
    simp
    rw [evalCR_succ]
    rw [evalBR_eq_evalCR_of_CR_to_BR]
    conv =>
      lhs
      rw [← add_assoc]
    simp
    rw [ih]

-- lemma 17
lemma mul_const_to_CR (r c0 : ℝ) (cr : CR) (n : ℕ) :
  r * (evalCR (recurCR c0 Mul cr) n) = evalCR (recurCR (c0 * r) Mul cr) n := by
  induction n with
  | zero =>
    simp
    ring
  | succ n ih =>
    simp [evalCR_succ]
    rw [← mul_assoc]
    rw [ih]

def evalPureCR (bop : BinOp) (pcr' : PureCR bop) (n : ℕ) :=
  evalCR (PureCR_to_CR bop pcr') n

lemma pureCR_zero (bop : BinOp) (x : ℝ) (pcr' : PureCR bop):
  evalPureCR bop (recurPureCR x pcr') 0 = x := by
  rfl

lemma pureCR_succ (bop : BinOp) (x : ℝ) (pcr' : PureCR bop):
  evalPureCR bop (recurPureCR x pcr') (n+1) = evalBinOp bop (evalPureCR bop (recurPureCR x pcr') n) (evalPureCR bop pcr' n) := by
  rw [evalPureCR]
  rw [evalPureCR]
  rw [evalPureCR]
  rw [PureCR_to_CR]
  rw [evalCR_succ]
  simp

def CR_size : CR → ℕ
| (liftBRToCR _) => 0
| (recurCR _ _ cr') => 1 + CR_size cr'

def PureCR_size {bop : BinOp} : PureCR bop → ℕ
| (PureBR _ _) => 0
| (recurPureCR _ pcr') => 1 + PureCR_size pcr'

-- lemma 1


-- algorithm CRMake
inductive Expr
| Const  : ℝ → Expr  -- Constant value
| Var    : String → Expr  -- Variable (e.g., "x")
| Add    : Expr → Expr → Expr  -- Addition
| Mul    : Expr → Expr → Expr  -- Multiplication
| Exp    : Expr → ℕ → Expr  -- Exponentiation
| Fact   : Expr → Expr  -- Factorial



def CRMake : ℕ → (ℕ → ℝ) → CR
| 0, f => CR.liftBRToCR ⟨f 0, Add, f⟩
| (n + 1), f =>
  let prevCR := CRMake n (λ i => f (i + 1) - f i) -- Compute difference
  CR.recurCR (f 0) Add prevCR


def ff1 (n : ℕ) : ℝ :=  n * (n + 1) * 0.5

def parseCR (expr : ℕ → ℝ) (n : ℕ) : CR :=
  CRMake n expr

#eval evalCR (parseCR ff1 3) 3

end CR
