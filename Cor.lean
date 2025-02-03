-- This module serves as the root of the `Cor` library.
-- Import modules here that should be built as part of the library.
import Cor.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- Define Basic Recurrence structure
/-
  BR has the following structure:
  f = {φ₀,⊙,f₁}
  where φ₀ is a constant, ⬝ is either + or ⋆ and f₁ is a function over ℕ
-/
section BR

structure BR :=
  (r0 : ℝ)
  (bop : ℝ → ℝ → ℝ)
  (f : ℕ → ℝ)

def evalBR (br : BR) (n : ℕ) : ℝ :=
  match br with
  | ⟨r0, binop, f⟩ =>
    let vals : List ℝ := List.map f (List.range' 1 n)
    List.foldl binop r0 vals

@[simp]
lemma evalBR_zero (br : BR) :
  evalBR br 0 = br.r0 := by
  rfl

@[simp]
lemma evalBR_succ (br : BR) (n : ℕ) :
  evalBR br (n+1) = br.bop (evalBR br n) (br.f (n+1)) := by
  cases br with
  | mk r0 bop f =>
    induction n with
    | zero =>
      simp
      rfl
    | succ n ih =>
      simp
      unfold evalBR
      rw [List.range'_eq_map_range 1 (n + 1 + 1)]
      rw [List.range_succ]
      rw [List.map_append]
      rw [List.range_succ]
      rw [List.map_append]
      simp [List.foldl]
      congr
      rw [List.range'_eq_map_range 2 n]
      simp [List.map]
      sorry



lemma evalBR_add_equals_sum_f (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := x, bop := (· + ·), f := f1} n =
  x + ∑ i in Finset.range (n), f1  i := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [evalBR_succ]
    simp
    rw [Finset.sum_range_succ]
    simp [ih]
    rw [add_assoc]

lemma evalBR_mul_equals_prd_f (x : ℝ) (f1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := x, bop := (· * ·), f := f1} n =
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

-- lemma 3.12 - this should be doable a lot better - why can simp not finish this after distributive? does it not work well over Finset and ℝ?
lemma add_add_BR_add_BR (x : ℝ) (y : ℝ) (f1 : ℕ → ℝ) (g1: ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := x, bop := (· + ·), f := f1} n + evalBR {r0 := y, bop := (· + ·), f := g1} n = evalBR {r0 := x + y, bop := (· + ·), f := λ n => f1 n + g1 n} n := by
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

-- lemma 3.13
lemma mul_BR_mul_BR (φ0 ψ0 : ℝ) (f1 g1 : ℕ → ℝ) (n : ℕ) :
  evalBR {r0 := φ0, bop := (· + ·), f := f1} n *
  evalBR {r0 := ψ0, bop := (· + ·), f := g1} n =
  evalBR {r0 := φ0 * ψ0, bop := (· + ·), f := λ n => g1 n * evalBR {r0 := φ0, bop := (· + ·), f := f1} n +
                 f1 n * evalBR {r0 := ψ0, bop := (· + ·), f := g1} n } n := by
  rw [evalBR_add_equals_sum_f]
  rw [evalBR_add_equals_sum_f]
  rw [right_distrib, left_distrib, mul_add]
  rw [Finset.sum_mul_sum]
  sorry


end BR

def h : ℚ := 1.0
def z : ℝ := 1.0

def f1 (_j : ℕ) : ℝ := 3 * h

def myBR : BR :=
  BR.mk (3 * z + 1) (· * ·) f1

#eval 3 * evalBR myBR 0
#eval evalBR myBR 1
#eval evalBR myBR 2


section CR

inductive CR
| liftBRToCR : BR → CR
| recurCR : ℝ → (ℝ → ℝ → ℝ) → CR → CR

inductive PureCR (bop : ℝ → ℝ → ℝ)
| PureBR : ℝ → ℝ → PureCR bop
| recurPureCR : ℝ → PureCR bop → PureCR bop

open BR
open CR
open PureCR

def CR_to_BR : CR → BR
| (liftBRToCR br) => br
| (recurCR r0 bop cr') =>
  let br' := CR_to_BR cr'
  BR.mk r0 bop (λ n => (br'.f n))

def evalCR (cr : CR) (n : ℕ) : ℝ :=
  evalBR (CR_to_BR cr) n

def PureCR_to_CR (bop : ℝ → ℝ → ℝ) (pcr : PureCR bop) : CR :=
match pcr with
| PureBR c0 c1 => liftBRToCR (BR.mk c0 bop (λ c1 => c1))
| recurPureCR c0 pcr' => recurCR c0 bop (PureCR_to_CR bop pcr')

@[simp]
lemma evalBR_eq_evalCR_of_CR_to_BR (cr : CR) (n : ℕ) :
  evalBR (CR_to_BR cr) n = evalCR cr n := by
  rfl

@[simp]
lemma evalCR_zero (cr' : CR) (r : ℝ) (bop : ℝ → ℝ → ℝ) :
  evalCR (recurCR r bop cr') 0 = r := by
  unfold evalCR
  simp [evalBR]
  unfold CR_to_BR
  simp

class LoopVariant (A : Type) (R : Type) where
  evalAtIx : A → ℕ → R

instance loopVariantCR : LoopVariant CR ℝ where
  evalAtIx cr n := evalCR cr n

open loopVariantCR
#check LoopVariant.evalAtIx


variable {bop : ℝ → ℝ → ℝ} (h_comm : ∀ x y : ℝ, bop x y = bop y x)

lemma evalCR_succ (cr' : CR) (r : ℝ) (bop : ℝ → ℝ → ℝ) (n : ℕ) (h_comm : ∀ x y : ℝ, bop x y = bop y x) :
  evalCR (recurCR r bop cr') (n+1)  = bop (evalCR (recurCR r bop cr') n) (evalBR (CR_to_BR cr') (n+1)) := by
  simp
  rw [← evalBR_eq_evalCR_of_CR_to_BR]
  rw [evalBR_succ]
  congr
  unfold CR_to_BR
  simp
  cases cr'
  case liftBRToCR br =>
    rw [CR_to_BR]
    unfold evalCR
    unfold CR_to_BR
    rw [CR_to_BR]
    simp
    congr









-- lemma 3.16
lemma add_const_to_CR (r c0 : ℝ) (cr : CR) (n : ℕ) :
  r + (evalCR (recurCR c0 (· + ·) cr) n) = evalCR (recurCR (c0 + r) (· + ·) cr) n := by
  induction n with
  | zero =>
    rw [evalCR]
    rw [← evalBR_eq_evalCR_of_CR_to_BR]
    unfold evalBR
    simp
    unfold CR_to_BR
    simp
    rw [add_comm]
  | succ ih n =>
    rw [evalCR]
    rw [evalBR_succ]
    sorry

-- lemma 17
lemma mul_const_to_CR (r c0 : ℝ) (cr : CR) (n : ℕ) :
  r * (evalCR (recurCR c0 (· * ·) cr) n) = evalCR (recurCR (c0 * r) (· * ·) cr) n := by
  sorry

--lemma add_const_to_pure_add_CR (r c0 : ℝ) (cr : CR) (n : ℕ) :
--  r * (evalCR (recurPureCR)) =

end CR
