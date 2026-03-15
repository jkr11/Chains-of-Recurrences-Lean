import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.List.Basic
import Mathlib.RingTheory.Algebraic

variable {α : Type*} [CommRing α]

open scoped Finset

inductive BinOp
| Add
| Mul
deriving DecidableEq

@[simp]
def evalBinOp : BinOp → (α → α → α)
| BinOp.Add => (· + ·)
| BinOp.Mul => (· * ·)

section BR

/- A BR has the following structure: `{φ₀,⊙,f₁}` where `φ₀ ∈ α` is a constant, `⬝` is either `+` or `⋆` and `f₁` is a function `ℕ → α` -/
structure BR (α : Type*) :=
  (r : α)
  (bop : BinOp)
  (f : ℕ → α)

notation "⟪" r "," op "," f "⟫" => BR.mk r op f

def evalBR (br : BR α) : ℕ → α
| 0     => br.r
| n + 1 => evalBinOp br.bop (evalBR br n) (br.f n)

#eval evalBR ⟪(6:ℤ), BinOp.Add, λ (i:ℕ) ↦ (i ^ 10:ℤ)⟫ 3

@[simp]
lemma evalBR_zero (br : BR α) :
  evalBR br 0 = br.r := rfl

lemma evalBR_one (r : α) (f : ℕ → α) :
  evalBR { r := r, bop := BinOp.Add, f := f } 1 = r + f 0 := rfl

@[simp]
lemma evalBR_succ (br : BR α) (n : ℕ) :
  evalBR br (n + 1) = evalBinOp br.bop (evalBR br n) (br.f n) := rfl

lemma evalBR_add_equals_sum_f (x : α) (f : ℕ → α) (n : ℕ) :
  evalBR {r := x, bop := BinOp.Add, f := f} n = x + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [evalBR_succ, ih, Finset.sum_range_succ, evalBinOp, add_assoc]

lemma evalBR_mul_equals_prod_f (x : α) (f : ℕ → α) (n : ℕ) :
  evalBR {r := x, bop := BinOp.Mul, f := f} n = x * ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [evalBR_succ, ih, Finset.prod_range_succ, evalBinOp, mul_assoc];

-- lemma 2.6
lemma BR_add_add_const (c : α) (φ : α) (f : ℕ → α) (n : ℕ) :
  c + evalBR {r := φ, bop := BinOp.Add, f := f} n =
  evalBR {r := c + φ, bop := BinOp.Add, f := f} n := by
  induction n with
  | zero => simp [evalBR]
  | succ n ih => simp_rw [evalBR_succ, evalBinOp, ← add_assoc, ih]

-- lemma 2.7
lemma BR_add_smul (c : α) (x : α) (f1 : ℕ → α) (n : ℕ) :
  c * evalBR {r := x, bop := BinOp.Add, f := f1} n =
  evalBR {r := c * x, bop := BinOp.Add, f := λ n => c * f1 n} n := by
  induction n with
  | zero => simp [evalBR]
  | succ n ih => simp_rw [evalBR_succ, evalBinOp, mul_add, ih]

-- lemma 2.8 we cant really get pow α α here. Maybe we can restrict this to a Module?
--lemma pow_evalBR_add [Field α] (c : α) (x : α) (f : ℕ → α) (n : ℕ) :
--  c ^ (evalBR {r := x, bop := BinOp.Add, f := f} n) =
--    evalBR {r := c ^ x, bop := BinOp.Mul, f := fun i => c ^ f i} n := by

-- lemma 2.9
lemma BR_mul_smul (c : α) (x : α) (f : ℕ → α) (n : ℕ) :
  c * evalBR {r := x, bop := BinOp.Mul, f := f} n =
  evalBR {r := c * x, bop := BinOp.Mul, f := f} n := by
  induction n with
  | zero => simp [evalBR]
  | succ n ih => simp_rw [evalBR_succ, evalBinOp, ← mul_assoc, ih]

-- lemma 2.12
lemma add_add_BR_add_BR (x y : α) (f g : ℕ → α) (n : ℕ) :
  evalBR {r := x, bop := BinOp.Add, f := f} n + evalBR {r := y, bop := BinOp.Add, f := g} n =
  evalBR {r := x + y, bop := BinOp.Add, f := λ n ↦ f n + g n} n := by
  simp_rw [evalBR_add_equals_sum_f, Finset.sum_add_distrib]
  ring

-- lemma 3.13
lemma mul_BR_add_BR (x y: α) (f g : ℕ → α) (n : ℕ) :
  evalBR {r := x, bop := BinOp.Add, f := f} n *
  evalBR {r := y, bop := BinOp.Add, f := g} n =
  evalBR {r := x * y, bop := BinOp.Add, f := λ n => (g n * evalBR {r := x, bop := BinOp.Add, f := f} n + f n * evalBR {r := y, bop := BinOp.Add, f := g} n) + f n * g n } n := by
  simp [evalBR_add_equals_sum_f]
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Finset.sum_range_succ, ← add_assoc]
    rw [add_mul, mul_add, ih]
    ring

end BR

section CR

inductive CR (α : Type*)
  | const (f : ℕ → α) : CR α
  | recur (r0 : α) (op : BinOp) (next : CR α) : CR α

def evalCR : CR α → ℕ → α
| .const f, i           => f i
| .recur φ _ _, 0       => φ
| .recur φ op Δ, i + 1  =>
    let current := evalCR (.recur φ op Δ) i
    let step    := evalCR Δ i
    evalBinOp op current step

/-- We can view every CR as a function `ℕ → α` through `evalCR`-/
instance {α : Type*} [CommRing α] : CoeFun (CR α) (fun _ => ℕ → α) where
  coe := evalCR

variable (n : ℕ)

def G (x : ℕ) : ℚ :=
  ((Nat.factorial x) ^ 2) / Nat.factorial (n - x)

def GEx : CR ℚ :=
  .recur (1 / (Nat.factorial n : ℚ)) .Mul (
    .recur (n : ℚ) .Add (
      .recur (3*n - 4 : ℚ) .Add (
        .recur (2*n - 10 : ℚ) .Add (
          .const (fun _ => -6)
        )
      )
    )
  )

#eval (G (n:=7)) 7
#eval (GEx (n:=7)) 7

@[simp]
lemma evalCR_zero (φ : α) (op : BinOp) (Δ : CR α) :
  evalCR (.recur φ op Δ) 0 = φ := by
  rfl

lemma evalCR_const_zero (f : ℕ → α) :
  evalCR (.const f) 0 = f 0 :=
  rfl

@[simp]
lemma evalCR_succ (φ : α) (op : BinOp) (Δ : CR α) (n : ℕ) :
  evalCR (.recur φ op Δ) (n + 1) =
    evalBinOp op (evalCR (.recur φ op Δ) n) (evalCR Δ n) := by
  rfl

def CR.isPureOp (op : BinOp) : CR α → Prop
  | .const _ => True
  | .recur _ bop next => bop = op ∧ next.isPureOp op

def CR.isSimple : CR α → Prop
| .const f => ∃ c, ∀ i, f i = c
| .recur _ _ Δ => Δ.isSimple

def CR.length : CR α → ℕ
| .const _ => 0
| .recur _ _ Δ => 1 + Δ.length

-- TODO: unsure if these should be represented as such.
def CR.add_const {α : Type*} [Add α] (c : α) : CR α → CR α
| .const f      => .const (fun i => c + f i)
| .recur φ op Δ => .recur (c + φ) op Δ

theorem evalCR_add_const_add (c : α) (r : α) (next : CR α) (n : ℕ) :
  evalCR (CR.add_const c (CR.recur r BinOp.Add next)) n = c + evalCR (CR.recur r BinOp.Add next) n := by
  induction n with
  | zero =>
      simp [evalCR, CR.add_const]
  | succ n ih =>
      simp [evalCR, evalBinOp, CR.add_const]
      simp [CR.add_const] at ih
      rw [ih]
      ring

--lemma 17
theorem CR_mul_first (c : α) (r : α) (next : CR α) (n : ℕ):
  c * (CR.recur r BinOp.Mul next) n = (CR.recur (c*r) BinOp.Mul next) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [evalBinOp, ← mul_assoc, ih]

def CR.smul (c : α) : CR α → CR α
| .const f => .const (fun i => c * f i)
| .recur φ BinOp.Add Δ => .recur (c * φ) .Add (Δ.smul c)
| .recur φ .Mul Δ => .recur (c * φ) .Mul Δ

lemma CR_smul (Φ : CR α) (n : ℕ) :
  c * Φ n = (Φ.smul c) n := by
  induction Φ generalizing n with
  | const f =>
    rw [CR.smul]
    simp_rw [evalCR]
  | recur r op next ih =>
    induction n with
    | zero =>
      simp [evalCR];
      cases op
      . simp [CR.smul]
      . simp [CR.smul]
    | succ n ihh =>
      simp [evalCR]
      cases op
      . simp [CR.smul] at *
        rw [mul_add]
        simp_rw [ih]
        simp [ihh]
      . simp [CR.smul] at *
        rw [← mul_assoc, ihh]

inductive CRExpr (α : Type*)
| const (f : ℕ → α) : CRExpr α
| cr (φ : α) (op : BinOp) (next : CRExpr α) : CRExpr α
| func (F : List α → α) (args : List (CRExpr α)) : CRExpr α
