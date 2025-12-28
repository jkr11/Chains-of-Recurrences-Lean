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

-- lemma 2.10 (only for f > 0 (f n >= 0), we should maybe just generalize to CommRing?)
lemma br_pow_const (c : ℝ) (x : ℝ) (f1 : ℕ → ℝ)
  (n : ℕ) (hx : x ≥ 0) (hf : ∀x : ℕ, f1 x ≥ 0) :
  (evalBR {r0 := x, bop := BinOp.Mul, f := f1} n) ^ c =
    evalBR {r0 := x ^ c, bop := BinOp.Mul, f := f1 ^ c} n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [evalBR_succ]
    rw [evalBR_succ]
    simp
    rw [Real.mul_rpow]
    · rw [ih]
    . rw [evalBR_mul_equals_prd_f]; apply mul_nonneg hx;
      apply Finset.prod_nonneg
      intro i _; exact hf i
    . simp [hf]

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
    . simp; sorry
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
lemma mul_BR_add_BR (φ0 ψ0 : ℝ) (f1 g1 : ℕ → ℝ) (n : ℕ) :
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


def factorial : ℕ → ℝ
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

def falling_factorial (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (x - k) * falling_factorial x k

def PureCR_to_CR (bop : BinOp) (pcr : PureCR bop) : CR :=
match pcr with
| PureBR c0 c1 => liftBRToCR (BR.mk c0 bop (λ _ => c1))
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

lemma evalCR_zero_ (phi : CR):
  evalCR (phi) 0 = (CR_to_BR phi).r0 := by
  unfold evalCR
  simp [evalBR]


lemma evalCR_succ (cr' : CR) (r : ℝ) (bop : BinOp) (n : ℕ):
  evalCR (recurCR r bop cr') (n+1)  = evalBinOp bop (evalCR (recurCR r bop cr') (n)) (evalBR (CR_to_BR cr') (n)) := by
  induction n with
  | zero =>
    simp
    rw [evalCR,evalBR_succ,evalBR_zero]
    dsimp [CR_to_BR] at *
    rfl
  | succ n ih =>
    rw [evalBR_eq_evalCR_of_CR_to_BR]
    rw [evalCR] at *
    rw [evalCR] at *
    rw [ih]
    rw [evalBR_succ]
    dsimp [CR_to_BR] at *
    rw [ih]

lemma evalCR_succ_gen (phi : CR) (n : ℕ) :
  evalCR phi (n + 1) = evalBinOp (CR_to_BR phi).bop (evalCR phi n) ((CR_to_BR phi).f n) := by
  rw [evalCR]
  simp [evalBR_succ]

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

def PureCR_to_BR (bop : BinOp) (pcr : PureCR bop) : BR :=
  CR_to_BR (PureCR_to_CR bop pcr)

lemma evalPureCR_zero (bop : BinOp) (x : ℝ) (pcr' : PureCR bop):
  evalPureCR bop (recurPureCR x pcr') 0 = x := by
  rw [evalPureCR, PureCR_to_CR]
  simp

lemma evalPureCR_succ (bop : BinOp) (x : ℝ) (pcr' : PureCR bop):
  evalPureCR bop (recurPureCR x pcr') (n+1) = evalBinOp bop (evalPureCR bop (recurPureCR x pcr') n) (evalPureCR bop pcr' n) := by
  simp [evalPureCR]
  rw [PureCR_to_CR]
  rw [evalCR_succ]
  simp

lemma evalPureCR_succ_ (bop : BinOp) (pcr : PureCR bop) (n : ℕ) :
  evalPureCR bop pcr (n + 1) =
  match pcr with
  | .PureBR _ x => evalBinOp bop (evalPureCR bop pcr n) x
  | .recurPureCR _ pcr' => evalBinOp bop (evalPureCR bop pcr n) (evalPureCR bop pcr' n) := by
  cases pcr
  . simp; cases bop
    . simp
      rw [evalPureCR]
      simp [evalCR_succ_gen]
      rw [evalPureCR]
      rw [PureCR_to_CR]
      rename_i d1 d2
      rw [evalCR]
      rw [CR_to_BR]
    . simp [evalPureCR]
      rw [PureCR_to_CR
      ,evalCR_succ_gen
      ,CR_to_BR
      ,evalCR
      ,evalBinOp]
  . simp[evalPureCR_succ]


def PureCR.size {bop : BinOp} : PureCR bop → ℕ
| (PureBR _ _) => 1
| (recurPureCR _ pcr') => 1 + pcr'.size

@[simp]
lemma PureCR.size_pos {bop : BinOp} (p : PureCR bop) : 0 < p.size := by
  induction p <;> simp [PureCR.size]

def pureCR_mul_scalar (c : ℝ) : PureCR Add → PureCR Add
| PureBR c0 x => PureBR (c * c0) (c * x)
| recurPureCR r pcr' => recurPureCR (c * r) (pureCR_mul_scalar c pcr')

-- lemma 18
lemma add_const_to_pure_sum_CR (c : ℝ) (phi : PureCR Add) :
  ∀ n, c * evalPureCR Add phi n = evalPureCR Add (pureCR_mul_scalar c phi) n := by
  induction phi with
  | PureBR c0 x =>
    intro n
    dsimp[evalPureCR, pureCR_mul_scalar, PureCR_to_CR]
    rw [evalCR] at *
    rw [evalCR] at *
    rw [CR_to_BR] at *
    rw [CR_to_BR] at *
    rw [mul_constant_to_BR]
  | recurPureCR r pcr' ih =>
    intro n
    induction n with
    | zero =>
      simp [evalPureCR, PureCR_to_CR, evalCR_zero]
    | succ n n_ih =>
      rw [evalPureCR_succ]
      dsimp [pureCR_mul_scalar]
      rw [evalPureCR_succ]
      rw [evalBinOp]
      rw [mul_add]
      rw [n_ih]
      simp
      rw [ih]
      rw [← pureCR_mul_scalar]


def pure_zip {bop : BinOp} (f : ℝ → ℝ → ℝ) : PureCR bop → PureCR bop → PureCR bop
  | PureBR r1 r2, PureBR s1 s2 =>
      PureBR (f r1 s1) (f r2 s2)
  | recurPureCR r pcr_r, recurPureCR s pcr_s =>
      recurPureCR (f r s) (pure_zip f pcr_r pcr_s)
  | a, _ => a

def pure_zip_eq {bop : BinOp} (f : ℝ → ℝ → ℝ) : (phi psi : PureCR bop) → phi.size = psi.size → PureCR bop
  | PureBR r1 r2, PureBR s1 s2, _ =>
      PureBR (f r1 s1) (f r2 s2)
  | recurPureCR r phi', recurPureCR s psi', h =>
    let h_next : phi'.size = psi'.size := by
      simp [PureCR.size] at h
      exact h
    recurPureCR (f r s) (pure_zip_eq f phi' psi' h_next)
  | PureBR _ _, recurPureCR _ psi', h => by
    simp [PureCR.size] at h
    trivial
  | recurPureCR _ _, PureBR _ _, h => by
    rw [PureCR.size] at h
    trivial


-- Prop2.22
lemma add_PureCR_sum (phi psi : PureCR Add) (h : phi.size = psi.size) (n : ℕ) :
  evalPureCR Add phi n + evalPureCR Add psi n = evalPureCR Add (pure_zip_eq (· + ·) phi psi h) n := by
  revert psi h n
  induction phi with
  | PureBR r1 r2 =>
    intro psi h n
    match psi, h with
    | PureBR s1 s2, _ =>
      simp [pure_zip_eq, evalPureCR]
      simp [PureCR_to_CR]
      rw [evalCR, evalCR, evalCR]
      simp [CR_to_BR]
      rw [add_add_BR_add_BR]
    | recurPureCR _ psi', h_size =>
      simp [PureCR.size] at h_size
      have pos := psi'.size_pos
      rw [← h_size] at pos
      simp at pos
  | recurPureCR r phi' ih_phi =>
    intro psi h n
    match psi, h with
    | PureBR _ _, h_size =>
      simp [PureCR.size] at h_size
      have pos := phi'.size_pos
      rw [h_size] at pos
      simp at pos
    | recurPureCR s psi', h_size =>
      simp [pure_zip_eq]
      induction n with
      | zero =>
        simp [evalPureCR, PureCR_to_CR]
      | succ n n_ih =>
        simp [evalPureCR_succ, evalBinOp, evalPureCR, PureCR_to_CR]
        simp [evalCR_succ]
        simp [evalPureCR, PureCR_to_CR] at n_ih
        conv_lhs =>
          arg 1
          rw [add_comm]
        rw [add_assoc]
        conv_lhs =>
          arg 2
          rw [← add_assoc]
          rw [n_ih]
        rw [← add_assoc]
        rw [add_comm]
        rw [← add_assoc]
        simp [evalPureCR] at ih_phi
        conv_lhs =>
          arg 1
          rw [add_comm]
        rw [ih_phi]
        ring

def pure_add (phi psi : PureCR Add) (h : phi.size = psi.size) : PureCR Add :=
  pure_zip_eq (· + ·) phi psi h


def pure_mul_scalar (c : ℝ) : PureCR Add → PureCR Add
  | PureBR c0 x => PureBR (c * c0) (c * x)
  | recurPureCR r pcr' => recurPureCR (c * r) (pure_mul_scalar c pcr')

def CRProd : (phi psi : PureCR Add) → PureCR Add
  | .PureBR φ0 φ1, .PureBR ψ0 ψ1 =>
      PureBR (φ0 * ψ0) (φ1 * ψ0 + φ0 * ψ1)
  | phi, .PureBR ψ0 _ =>
      pure_mul_scalar ψ0 phi
  | .PureBR φ0 _, psi =>
      pure_mul_scalar φ0 psi
  | .recurPureCR φ0 f1, .recurPureCR ψ0 g1 =>
      -- P2: Prepare recursive calls, are we just allowd to flip these? Would certainly be easier
      let psi_prime := pure_add (recurPureCR ψ0 g1) (recurPureCR 0 g1) (by simp [PureCR.size])

      let xi_prime := CRProd (recurPureCR φ0 f1) g1
      let xi_double_prime := CRProd f1 psi_prime
      recurPureCR (φ0 * ψ0) (pure_add xi_prime xi_double_prime (by sorry))


noncomputable def factorial_poly_sum (phi : PureCR Add) (i : ℕ) : ℝ :=
  let rec loop : PureCR Add → ℕ → ℝ
    | .PureBR c0 x, j =>
      (c0 / factorial j) * falling_factorial i j +
      (x / factorial (j + 1)) * falling_factorial i (j + 1)
    | .recurPureCR r pcr', j =>
      (r / factorial j) * falling_factorial i j + loop pcr' (j + 1)
  loop phi 0

@[simp]
lemma ff_0 (x : ℝ) :
  falling_factorial x 0 = 1 := by simp [falling_factorial]

@[simp]
lemma zero_ff {i : ℕ} (h : i > 0):
  falling_factorial 0 i = 0 := by
  induction i with
  | zero =>
    exact (Nat.not_lt_zero 0 h).elim
  | succ i ih =>
    unfold falling_factorial
    cases i with
    | zero =>
      simp [falling_factorial]
    | succ i =>
      -- Case where i+1 > 1, so i > 0
      rw [ih (Nat.succ_pos i)]
      ring

-- Todo: do we even need the sum expr?
lemma factorial_poly_sum_loop_zero {phi : PureCR BinOp.Add} {j : ℕ} (hj : j > 0) :
  factorial_poly_sum.loop 0 phi j = 0 := by
  induction phi generalizing j with
  | PureBR c0 x =>
    unfold factorial_poly_sum.loop
    simp
    ring
    rw [zero_ff]
    simp
    exact hj
  | recurPureCR r pcr' ih =>
    unfold factorial_poly_sum.loop
    simp
    rw [zero_ff]
    . simp
      rw [ih]
      simp [hj]
    . exact hj

lemma lemma_1_ (phi : PureCR Add) (i : ℕ) :
  evalPureCR Add phi i = factorial_poly_sum phi i := by
  simp [factorial_poly_sum, factorial_poly_sum.loop]
  induction phi with
  | PureBR c0 x =>
    simp [evalPureCR, PureCR_to_CR]
    rw [evalCR, CR_to_BR]
    unfold factorial_poly_sum.loop
    rw [evalBR_add_equals_sum_f]
    simp
    simp [factorial, falling_factorial]
    ring
  | recurPureCR r pcr' ih =>
    induction i with
    | zero =>
      simp [factorial_poly_sum, factorial_poly_sum.loop]
      simp [evalPureCR, PureCR_to_CR, factorial]
      unfold factorial_poly_sum.loop
      simp
      split
      . next c0 x j =>
        simp
      . next r pcr' j =>
        simp
        sorry
    | succ i ihh =>
      rw [evalPureCR_succ, evalBinOp]
      simp
      rw [ihh]
      unfold factorial_poly_sum.loop
      simp
      simp [factorial]
      sorry
      sorry

lemma lemma_1 (phi : PureCR Add) (i : ℕ) :
  evalPureCR Add phi i = factorial_poly_sum phi i := by
  induction i generalizing phi with
  | zero =>
    simp [factorial_poly_sum, factorial_poly_sum.loop, evalPureCR, evalCR_zero_]
    unfold factorial_poly_sum.loop
    cases phi
    . simp
      rw [factorial]
      rename_i r0 r1
      unfold CR_to_BR
      simp
      unfold PureCR_to_CR
      simp

    . simp
      simp [factorial]
      unfold CR_to_BR
      unfold PureCR_to_CR
      simp
      rw [factorial_poly_sum_loop_zero]
      simp
  | succ i ih =>
    simp [evalPureCR_succ_]
    rw [ih]
    cases phi
    . simp
      unfold factorial_poly_sum
      unfold factorial_poly_sum.loop
      simp [zero_ff, ff_0, factorial]
      rename_i a1 a2
      unfold falling_factorial
      simp [zero_ff]
      ring
    . simp
      rename_i a1 a2
      rw [ih]
      unfold factorial_poly_sum
      sorry

def f11 (i : ℕ) : ℝ := 1 + i^2
def br1 : BR := BR.mk 1 BinOp.Add f11
def cr1 : CR := liftBRToCR br1

#eval evalBR br1 4
#eval evalCR cr1 4

def cr2 := recurCR 10 BinOp.Add cr1
#eval evalCR cr2 1


noncomputable def cos_seq (x0 h : ℝ) (i : ℕ) : ℝ :=
  Real.cos (20 * (x0 + i * h))

noncomputable def br_cos (x0 h : ℝ) : BR :=
  BR.mk 1 BinOp.Mul (cos_seq x0 h)

noncomputable def cr_cos (x0 h : ℝ) : CR :=
  liftBRToCR (br_cos x0 h)

noncomputable def f0 (x0 h : ℝ) (i : ℕ) : ℝ := Real.exp (x0^2)
noncomputable def f111 (x0 h : ℝ) (i : ℕ) : ℝ := Real.exp (2 * h * x0 * i + h^2 * i)
noncomputable def f2 (x0 h : ℝ) (i : ℕ) : ℝ := Real.exp (2 * h^2 * i)

noncomputable def br_f0 (x0 h : ℝ) : BR := BR.mk 1 BinOp.Mul (f0 x0 h)
noncomputable def br_f1 (x0 h : ℝ) : BR := BR.mk 1 BinOp.Mul (f111 x0 h)
noncomputable def br_f2 (x0 h : ℝ) : BR := BR.mk 1 BinOp.Mul (f2 x0 h)


noncomputable def cr_f0 (x0 h : ℝ) : CR := liftBRToCR (br_f0 x0 h)
noncomputable def cr_f1 (x0 h : ℝ) : CR := liftBRToCR (br_f1 x0 h)
noncomputable def cr_f2 (x0 h : ℝ) : CR := liftBRToCR (br_f2 x0 h)

inductive CRExpression
| constant : ℝ → CRExpression
| cr_node  : ℝ → BinOp → CRExpression → CRExpression
| func     : (List ℝ → ℝ) → List CRExpression → CRExpression

inductive GExpr
| var                          -- Represents the variable 'x'
| constant (r : ℝ)             -- Represents a constant c
| add (g1 g2 : GExpr)          -- g1 + g2
| mul (g1 g2 : GExpr)          -- g1 * g2
| pow (g1 : GExpr) (n : ℕ)     -- g1^n
| factorial (g1 : GExpr)       -- g1!
| cr (phi : CRExpression)      -- An already constructed CR


def CRMake (x0 h : ℝ) : GExpr → CRExpression
| .constant c => .constant c
| .cr phi => phi
| .var =>
    .cr_node x0 .Add (.constant h)
| _ => sorry

--| .add g1 g2 =>
--    -- S2: Apply recursively to arguments
--    let phi1 := CRMake x0 h g1
--    let phi2 := CRMake x0 h g2
--    -- S4.1: {φ0, +, f1} + {ψ0, +, g1} return {φ0 + ψ0, +, CRMake(f1 + g1)}
--    match phi1, phi2 with
--    | .cr_node r1 .Add f1, .cr_node r2 .Add g1 =>
--        .cr_node (r1 + r2) .Add (CRMake_from_CRE (f1) (g1) .Add)
--    | _, _ => .func (λ l => l.get! 0 + l.get! 1) [phi1, phi2]
--
--| .mul g1 g2 =>
--    let phi1 := CRMake x0 h g1
--    let phi2 := CRMake x0 h g2
--    -- S4.3: If simple pure-sum CRs, return CRProd
--    -- (Assuming a check for 'simple pure-sum' exists)
--    match is_pure_sum phi1, is_pure_sum phi2 with
--    | true, true => CRProd phi1 phi2
--    | _, _ => .func (λ l => l.get! 0 * l.get! 1) [phi1, phi2]
--
--| .factorial g1 =>
--    -- S5: Check for factorial case
--    let phi := CRMake x0 h g1
--    match phi with
--    | .cr_node r0 .Add (.constant r1) =>
--        if r1 > 0 then
--            -- return {φ0!, *, CRMake(Π {φ0+l, +, φ1})}
--            let prod_term := build_factorial_prod r0 r1
--            .cr_node (factorial_real r0) .Mul (CRMake x0 h prod_term)
--        else
--            -- handle r1 < 0 case
--            .constant 0 -- Simplified placeholder
--    | _ => .func (λ l => factorial_real (l.get! 0)) [phi]
--
--| .pow g1 n =>
--    -- S4.5: G ≡ Φ^n return CRMake(Φ * Φ^{n-1})
--    if n = 0 then .constant 1
--    else CRMake x0 h (.mul g1 (.pow g1 (n-1)))


inductive Expr
| Const  : ℝ → Expr
| Var    : String → Expr
| Add    : Expr → Expr → Expr
| Mul    : Expr → Expr → Expr
| Exp    : Expr → ℕ → Expr
| Fact   : Expr → Expr


def CRMake_  : ℕ → (ℕ → ℝ) → CR
| 0, f => CR.liftBRToCR ⟨f 0, Add, f⟩
| (n + 1), f =>
  let prevCR := CRMake_ n (λ i => f (i + 1) - f i) -- Compute difference
  CR.recurCR (f 0) Add prevCR

def ff1 (n : ℕ) : ℝ :=  n * (n + 1) * 0.5

def parseCR (expr : ℕ → ℝ) (n : ℕ) : CR :=
  CRMake_ n expr

#eval evalCR (parseCR ff1 3) 3

end CR
