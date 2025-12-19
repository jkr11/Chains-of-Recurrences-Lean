import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
open BigOperators

section BRGeneral

variable {R : Type*} [CommRing R]

inductive BinOp
| Add
| Mul
deriving DecidableEq

@[simp]
def evalBinOp : BinOp → R → R → R
| BinOp.Add => (· + ·)
| BinOp.Mul => (· * ·)

structure BR (R : Type*) [CommRing R] :=
  (r0 : R)
  (bop : BinOp)
  (f : ℕ → R)

def BR_Add (R : Type*) [CommRing R] := { br : BR R // br.bop = BinOp.Add }

def BR_mul (R : Type*) [CommRing R] := { br : BR R // br.bop = BinOp.Mul }

@[ext]
lemma BR.ext {R : Type*} [CommRing R] (a b : BR R) :
  a.r0 = b.r0 → a.bop = b.bop → a.f = b.f → a = b :=
by
  intros; cases a; cases b; simp_all

lemma BR_Add_bop_eq {R : Type*} [CommRing R] (a b : BR_Add R):
  a.val.bop = b.val.bop := by sorry

@[ext]
lemma BR_Add.ext {R : Type*} [CommRing R] (a b : BR_Add R) :
  a.val.r0 = b.val.r0 → a.val.f = b.val.f → a = b :=
  by sorry
  -- fun hr0 hf => Subtype.ext (BR.ext _ _ _ _) sorry



def evalBR {R : Type*} [CommRing R] (br : BR R) (n : ℕ) : R :=
  match br with
  | ⟨r0, binop, f⟩ =>
    let vals : List R := List.map f (List.range n)
    List.foldl (evalBinOp binop) r0 vals

@[simp]
lemma evalBR_zero {R : Type*} [CommRing R] (br : BR R) :
  evalBR br 0 = br.r0 := by
  rfl

@[simp]
lemma evalBR_succ {R : Type*} [CommRing R] (br : BR R) (n : ℕ) :
  evalBR br (n+1) = evalBinOp br.bop (evalBR br n) (br.f n) := by
  cases br with
  | mk r0 bop f =>
    induction n with
    | zero =>
      simp [evalBR]
      rw [List.range_succ, List.map_append]
      simp
    | succ n ih =>
      simp [evalBR]
      rw [List.range_succ, List.map_append]
      simp [List.foldl]

lemma evalBR_add_equals_sum_f {R : Type*} [CommRing R] [DecidableEq R] (x : R) (f1 : ℕ → R) (n : ℕ) :
  evalBR {r0 := x, bop := BinOp.Add, f := f1} n =
  x + ∑ i in Finset.range n, f1 i := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih =>
    rw [evalBR_succ]
    simp [evalBinOp]
    rw [ih]
    rw [add_assoc]
    congr
    rw [Finset.sum_range_succ]

lemma evalBR_mul_equals_prd_f (x : R) (f1 : ℕ → R) (n : ℕ) :
  evalBR {r0 := x, bop := BinOp.Mul, f := f1} n =
  x * ∏ i in Finset.range n, f1 i := by
  induction n with
  | zero =>
    simp [evalBR]
  | succ n ih  =>
    rw [evalBR_succ]
    simp [evalBinOp]
    rw [ih]
    rw [Finset.prod_range_succ]
    rw [mul_assoc]

lemma add_constant_to_BR (c x : R) (f1 : ℕ → R) (n : ℕ) :
  evalBR {r0 := c + x, bop := BinOp.Add, f := f1} n =
    c + evalBR {r0 := x, bop := BinOp.Add, f := f1} n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [evalBR_succ, evalBinOp]
    rw [ih, add_assoc]

lemma mul_constant_to_mul_BR (c x : R) (f1 : ℕ → R) (n : ℕ) :
  evalBR {r0 := c * x, bop := BinOp.Mul, f := f1} n =
    c * evalBR {r0 := x, bop := BinOp.Mul, f := f1} n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [evalBR_succ, evalBinOp]
    rw [ih, mul_assoc]

lemma evalBR_add (x y : R) (f1 g1 : ℕ → R) (n : ℕ) :
  evalBR {r0 := x, bop := BinOp.Add, f := f1} n +
    evalBR {r0 := y, bop := BinOp.Add, f := g1} n =
    evalBR {r0 := x + y, bop := BinOp.Add, f := λ n => f1 n + g1 n} n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [evalBR_succ, evalBinOp]
    calc
      (evalBR {r0 := x, bop := BinOp.Add, f := f1} n + f1 n) +
        (evalBR {r0 := y, bop := BinOp.Add, f := g1} n + g1 n)
        = (evalBR {r0 := x, bop := BinOp.Add, f := f1} n + evalBR {r0 := y, bop := BinOp.Add, f := g1} n) + (f1 n + g1 n) := by rw [add_assoc, add_assoc, add_left_comm (f1 n)]
      _ = evalBR {r0 := x + y, bop := BinOp.Add, f := fun n => f1 n + g1 n} n + (f1 n + g1 n) := by rw [ih]
      _ = evalBR {r0 := x + y, bop := BinOp.Add, f := fun n => f1 n + g1 n} (n + 1) := by simp [evalBR_succ, evalBinOp]
    simp

lemma mul_evalBR_add (c x : R) (f1 : ℕ → R) (n : ℕ) :
  c * evalBR {r0 := x, bop := BinOp.Add, f := f1} n =
    evalBR {r0 := c * x, bop := BinOp.Add, f := λ n => c * f1 n} n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [evalBR_succ, evalBinOp]
    rw [mul_add, ih]

end BRGeneral


namespace BRAdd

variable {R : Type*} [CommRing R]

@[simp]
def add (br₁ br₂ : BR R) : BR R :=
  { r0 := br₁.r0 + br₂.r0,
    bop := BinOp.Add,
    f := λ n => br₁.f n + br₂.f n }


def zero : BR R :=
  { r0 := 0,
    bop := BinOp.Add,
    f := λ _ => 0 }



instance : Add (BR R) := ⟨add⟩
instance : Zero (BR R) := ⟨zero⟩

@[simp] lemma add_def (a b : BR R) : a + b = add a b := rfl

@[simp] lemma zero_def : (0 : BR R) = zero := rfl

lemma add_assoc' (a b c : BR R) : a + b + c = a + (b + c) := by
  ext
  · rw [add_def, add_def]
    rw [add, add]
    simp [add_assoc]
  . rw [add_def, add_def]
    rw [add, add]
    simp
  · simp [add_def, add, BinOp, add_assoc]


instance : AddCommMonoid (BR R) where
  add := (· + ·)
  zero := 0
  add_assoc := by
    intros a b c
    apply add_assoc'
  zero_add := by
    intros a
    ext
    · simp [add_def, add, zero]
    simp

  add_zero := by
    intros a
    ext
    · simp [add, zero, BinOp]
    · simp [add, zero, BinOp]
  add_comm := by
    intros a b
    ext
    · simp [add, zero, BinOp]
      apply add_comm
    · simp [add, zero, BinOp]
      funext n; apply add_comm
    · simp [add, zero, BinOp]; apply add_comm
    · simp [add, zero, BinOp]; funext n; apply add_comm
  nsmul := fun n br =>
    { r0 := n • br.r0,
      bop := BinOp.Add,
      f := fun k => n • br.f k }

instance : SMul R (BR R) where
  smul c br := { r0 := c * br.r0, bop := BinOp.Add, f := λ n => c * br.f n }

instance : Module R (BR R) where
  one_smul := by intros; ext <;> simp [SMul.smul, BinOp]
  mul_smul := by intros; ext <;> simp [SMul.smul, BinOp]; ring
  smul_add := by intros; ext <;> simp [SMul.smul, add, BinOp]; ring
  smul_zero := by intros; ext <;> simp [SMul.smul, zero, BinOp]
  add_smul := by intros; ext <;> simp [SMul.smul, BinOp]; ring
  zero_smul := by intros; ext <;> simp [SMul.smul, zero, BinOp]

end BRAdd
