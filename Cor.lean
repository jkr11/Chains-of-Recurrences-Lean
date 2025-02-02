-- This module serves as the root of the `Cor` library.
-- Import modules here that should be built as part of the library.
import Cor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Define BR structure
/-
  BR has the following structure:
  f = {φ₀,⊙,f₁}
-/
section BR
structure BR :=
  (r0 : ℝ)
  (bop : ℝ → ℝ → ℝ)
  (f : ℕ → ℝ)

def evalBR (br : BR) (n : ℕ) : ℝ :=
  match br with
  | ⟨r0, binop, f⟩ =>
    let vals : List ℝ := List.map f (List.range n)
    List.foldl binop r0 vals

lemma evalBR_succ (br : BR) (n : ℕ) :
  evalBR br (n+1) = br.bop (evalBR br n) (br.f n) := by
  cases br with
  | mk r0 bop f =>
    simp [evalBR]
    rw [List.range_succ]
    rw [List.map_append]
    rw [List.foldl_append]
    simp[List.foldl]

#check evalBR_succ

-- this is lemma 2.6 in the paper
lemma add_constant_to_BR (c : ℝ) (φ : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  c + evalBR {r0 := φ, bop := (· + ·), f := f1} n =
  evalBR {r0 := c + φ, bop := (· + ·), f := f1} n := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    rw [← add_assoc]
    rw [ih]

-- lemma 2.7
lemma mul_constant_to_BR (c : ℝ) (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  c * evalBR {r0 := x, bop := (· + ·), f := f1} n =
  evalBR {r0 := c * x, bop := (· + ·), f := λ n => c * f1 n} n := by
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
 c ^ (evalBR {r0 := x, bop := (· + ·), f := f1} n) =
  evalBR {r0 := c ^ x, bop := (· * ·), f := λ n => c ^ f1 n} n := by
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
  c * evalBR {r0 := x, bop := (· * ·), f := f1} n =
  evalBR {r0 := c * x, bop := (· * ·), f := f1} n := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [← mul_assoc]
    rw [ih]

end BR
/-
def h : ℝ := 1.0
def z : ℝ := 1.0

def f1 (_j : ℕ) : ℝ := 3 * h

def myBR : BR :=
  BR.mk (3 * z + 1) (· * ·) f1

#eval 3 * evalBR myBR 0
#eval evalBR myBR 1
#eval evalBR myBR 2
-/
section CR

inductive CR
| liftBRToCR : BR → CR
| recurCR : ℝ → (ℝ → ℝ → ℝ) → CR → CR

open BR
open CR

def CR_to_BR : CR → BR
| (liftBRToCR br) => br
| (recurCR r0 bop cr') =>
  let br' := CR_to_BR cr'
  BR.mk r0 bop (λ n => (br'.f n))

def evalCR (cr : CR) (n : ℕ) : ℝ :=
  evalBR (CR_to_BR cr) n

lemma evalBR_eq_evalCR_of_CR_to_BR (cr : CR) (n : ℕ) :
  evalBR (CR_to_BR cr) n = evalCR cr n := by
  rfl

#check evalBR_eq_evalCR_of_CR_to_BR




end CR
