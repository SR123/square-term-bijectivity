import SquareGroups
import Cycle372Collision

/-! The syntax of the reduced signature and the exact triple produced by the compiler.
All primitive tables are shared between all occurrences. -/
namespace SquareBijection
open DisequalityDispersion Function

abbrev Triple (A : Type) := A × A × A

inductive Expr where
  | x | y | z | o
  | D (i j : Expr) | G (i j : Expr) | H (i j : Expr)
  deriving Repr, DecidableEq

structure Tables (A : Type) where
  o : A
  D : A → A → A
  G : A → A → A
  H : A → A → A

variable {A : Type}

def eval (I : Tables A) (p : Triple A) : Expr → A
  | .x => p.1
  | .y => p.2.1
  | .z => p.2.2
  | .o => I.o
  | .D a b => I.D (eval I p a) (eval I p b)
  | .G a b => I.G (eval I p a) (eval I p b)
  | .H a b => I.H (eval I p a) (eval I p b)

def run (I : Tables A) (s : Triple Expr) (p : Triple A) : Triple A :=
  (eval I p s.1, eval I p s.2.1, eval I p s.2.2)

def subst (s : Triple Expr) : Expr → Expr
  | .x => s.1
  | .y => s.2.1
  | .z => s.2.2
  | .o => .o
  | .D a b => .D (subst s a) (subst s b)
  | .G a b => .G (subst s a) (subst s b)
  | .H a b => .H (subst s a) (subst s b)

theorem eval_subst (I : Tables A) (p : Triple A) (s : Triple Expr) (a : Expr) :
    eval I p (subst s a) = eval I (run I s p) a := by
  induction a <;> simp_all [eval, subst, run]

/-- Apply the input triple first, then the remaining triples. -/
def chain : List (Triple Expr) → Triple Expr
  | [] => (.x, .y, .z)
  | s :: ss =>
    let t := chain ss
    (subst s t.1, subst s t.2.1, subst s t.2.2)

theorem run_chain_cons (I : Tables A) (s : Triple Expr) (ss : List (Triple Expr)) :
    run I (chain (s :: ss)) = run I (chain ss) ∘ run I s := by
  funext p
  simp only [chain, run, eval_subst, Function.comp_apply]

theorem bijective_comp_iff {B : Type} [Finite B] (g f : B → B) :
    Bijective (g ∘ f) ↔ Bijective g ∧ Bijective f := by
  constructor
  · intro h
    have hi : Injective f := fun _ _ he => h.1 (congrArg g he)
    have hs : Surjective g := fun y => by
      obtain ⟨x, hx⟩ := h.2 y
      exact ⟨f x, hx⟩
    exact ⟨hs.bijective_of_finite, hi.bijective_of_finite⟩
  · rintro ⟨hg,hf⟩
    exact hg.comp hf

theorem chain_iff [Finite A] (I : Tables A) (ss : List (Triple Expr)) :
    Bijective (run I (chain ss)) ↔ ∀ s ∈ ss, Bijective (run I s) := by
  induction ss with
  | nil => exact ⟨by simp, fun _ => Function.bijective_id⟩
  | cons s ss ih =>
    rw [run_chain_cons, bijective_comp_iff, ih, List.forall_mem_cons, and_comm]

abbrev Word (m : ℕ) := List (Letter (Fin m))

def tagIndex {m : ℕ} (l : Letter (Fin m)) : ℕ :=
  (if l.2 then l.1.val else m + l.1.val) + 1

def tag : ℕ → Expr
  | 0 => .o
  | n+1 => .H .o (tag n)

def tagVal (o : A) (h : A → A → A) : ℕ → A
  | 0 => o
  | n+1 => h o (tagVal o h n)

@[simp] theorem eval_tag (I : Tables A) (p : Triple A) (n : ℕ) :
    eval I p (tag n) = tagVal I.o I.H n := by
  induction n <;> simp_all [tag, eval, tagVal]

def letterMap {m : ℕ} (I : Tables A) (l : Letter (Fin m)) : A → A :=
  I.H (tagVal I.o I.H (tagIndex l))

def wordExpr {m : ℕ} : Word m → Expr → Expr
  | [], a => a
  | l :: w, a => .H (tag (tagIndex l)) (wordExpr w a)

@[simp] theorem eval_wordExpr {m : ℕ} (I : Tables A) (p : Triple A) (w : Word m) (a : Expr) :
    eval I p (wordExpr w a) = evalWord (letterMap I) w (eval I p a) := by
  induction w <;> simp_all [wordExpr, eval, evalWord, letterMap]

/-- All inverse words and all relators, preceded by the empty (diagonal) word. -/
def laws {m : ℕ} (rels : List (Word m)) : List (Word m) :=
  [[]] ++ (List.finRange m).map (fun i => [(i,true),(i,false)]) ++
  (List.finRange m).map (fun i => [(i,false),(i,true)]) ++ rels

def column : Triple Expr := (.y, .D .x .y, .z)

def marker : Triple Expr :=
  let L (i j t : Expr) := Expr.D i (.G j t)
  let b := L .x .o .o
  let middle := L .x .z (L .x .z b)
  let U (t : Expr) := L .y .o t
  (.x,U (U middle),U (U (L .y .z middle)))

def row {m : ℕ} (r : Word m) : Triple Expr :=
  (.x, .G (.D (wordExpr r .x) .x) .y, .z)

def separator {m : ℕ} (w : Word m) : Triple Expr :=
  (.D (.G .o .x) .y, .D (.G (wordExpr w .o) .x) .y, .z)

/-- This value is three finite trees over a fixed signature on exactly three variables. -/
def compile {m : ℕ} (rels : List (Word m)) (w : Word m) : Triple Expr :=
  chain ([column,marker] ++ (laws rels).map row ++ [separator w])

theorem compile_iff [Finite A] {m : ℕ} (I : Tables A) (rels : List (Word m)) (w : Word m) :
    Bijective (run I (compile rels w)) ↔
    Bijective (run I column) ∧ Bijective (run I marker) ∧
    (∀ r ∈ laws rels, Bijective (run I (row r))) ∧ Bijective (run I (separator w)) := by
  simp only [compile, chain_iff, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, and_assoc]

theorem run_marker (I : Tables A) (p : Triple A) :
    run I marker p = (p.1, Cycle372.data I.D I.G I.o p.1 p.2.1 p.2.2) := rfl

theorem run_row {m : ℕ} (I : Tables A) (r : Word m) (p : Triple A) :
    run I (row r) p = (p.1, I.G (I.D (evalWord (letterMap I) r p.1) p.1) p.2.1,p.2.2) := by
  simp [run,row,eval,eval_wordExpr]

theorem run_separator {m : ℕ} (I : Tables A) (w : Word m) (p : Triple A) :
    run I (separator w) p =
      (I.D (I.G I.o p.1) p.2.1,
       I.D (I.G (evalWord (letterMap I) w I.o) p.1) p.2.1, p.2.2) := by
  simp [run,separator,eval,eval_wordExpr]

end SquareBijection
