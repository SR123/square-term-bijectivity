import SquareReduction

/-! The original three-coordinate construction of §§1–3 of the 18 November note,
with separate F, G, D, the signed unary operations, and the ternary word test. -/
namespace SquareBijection.PaperTriple
open Function DisequalityDispersion
variable {m : ℕ} {A : Type}

inductive Term (m : ℕ) where
  | x | y | z | o
  | F (a b : Term m) | G (a b : Term m) | D (a b : Term m)
  | letter (l : Letter (Fin m)) (a : Term m)
  | Q (c v t : Term m)
  deriving Repr, DecidableEq

structure Ops (m : ℕ) (A : Type) where
  o : A
  F : A → A → A
  G : A → A → A
  D : A → A → A
  letter : Letter (Fin m) → A → A
  Q : A → A → A → A

def eval (I : Ops m A) (p : Triple A) : Term m → A
  | .x => p.1 | .y => p.2.1 | .z => p.2.2 | .o => I.o
  | .F a b => I.F (eval I p a) (eval I p b)
  | .G a b => I.G (eval I p a) (eval I p b)
  | .D a b => I.D (eval I p a) (eval I p b)
  | .letter l a => I.letter l (eval I p a)
  | .Q c v t => I.Q (eval I p c) (eval I p v) (eval I p t)

def run (I : Ops m A) (s : Triple (Term m)) (p : Triple A) : Triple A :=
  (eval I p s.1, eval I p s.2.1, eval I p s.2.2)

def subst (s : Triple (Term m)) : Term m → Term m
  | .x => s.1 | .y => s.2.1 | .z => s.2.2 | .o => .o
  | .F a b => .F (subst s a) (subst s b)
  | .G a b => .G (subst s a) (subst s b)
  | .D a b => .D (subst s a) (subst s b)
  | .letter l a => .letter l (subst s a)
  | .Q c v t => .Q (subst s c) (subst s v) (subst s t)

theorem eval_subst (I : Ops m A) (p : Triple A) (s : Triple (Term m)) (a : Term m) :
    eval I p (subst s a) = eval I (run I s p) a := by
  induction a <;> simp_all [eval, subst, run]

def chain : List (Triple (Term m)) → Triple (Term m)
  | [] => (.x,.y,.z)
  | s :: ss =>
    let t := chain ss
    (subst s t.1, subst s t.2.1, subst s t.2.2)

theorem run_cons (I : Ops m A) (s : Triple (Term m)) (ss : List (Triple (Term m))) :
    run I (chain (s :: ss)) = run I (chain ss) ∘ run I s := by
  funext p
  simp only [chain, run, eval_subst, comp_apply]

theorem chain_iff [Finite A] (I : Ops m A) (ss : List (Triple (Term m))) :
    Bijective (run I (chain ss)) ↔ ∀ s ∈ ss, Bijective (run I s) := by
  induction ss with
  | nil => exact ⟨by simp, fun _ => bijective_id⟩
  | cons s ss ih => rw [run_cons,bijective_comp_iff,ih,List.forall_mem_cons,and_comm]

def word : Word m → Term m → Term m
  | [], a => a
  | l :: v, a => .letter l (word v a)

theorem eval_word (I : Ops m A) (p : Triple A) (v : Word m) (a : Term m) :
    eval I p (word v a) = evalWord I.letter v (eval I p a) := by
  induction v <;> simp_all [word,eval,evalWord]

def columnF : Triple (Term m) := (.y,.F .x .y,.z)
def columnD : Triple (Term m) := (.y,.D .x .y,.z)
def marker : Triple (Term m) :=
  let L (i j t : Term m) := Term.F i (.G j t)
  let b := L .x .o .o
  let middle := L .x .z (L .x .z b)
  let U (t : Term m) := L .y .o t
  (.x,U (U middle),U (U (L .y .z middle)))
def row (v : Word m) : Triple (Term m) := (.x,.G (.D (word v .x) .x) .y,.z)
def separator (w : Word m) : Triple (Term m) := (.Q .o .x .y,.Q (word w .o) .x .y,.z)

def compile (rels : List (Word m)) (w : Word m) : Triple (Term m) :=
  chain ([columnF,marker,columnD] ++ (laws rels).map row ++ [separator w])

theorem compile_iff [Finite A] (I : Ops m A) (rels : List (Word m)) (w : Word m) :
    Bijective (run I (compile rels w)) ↔
      Bijective (run I columnF) ∧ Bijective (run I marker) ∧ Bijective (run I columnD) ∧
      (∀ r ∈ laws rels, Bijective (run I (row r))) ∧ Bijective (run I (separator w)) := by
  simp only [compile,chain_iff,List.forall_mem_append,List.forall_mem_map,List.forall_mem_cons,
    List.not_mem_nil,false_implies,implies_true,and_true,and_assoc]

theorem run_row (I : Ops m A) (r : Word m) (p : Triple A) :
    run I (row r) p = (p.1,I.G (I.D (evalWord I.letter r p.1) p.1) p.2.1,p.2.2) := by
  simp [run,row,eval,eval_word]

theorem run_sep (I : Ops m A) (w : Word m) (p : Triple A) :
    run I (separator w) p =
    (I.Q I.o p.1 p.2.1,I.Q (evalWord I.letter w I.o) p.1 p.2.1,p.2.2) := by
  simp [run,separator,eval,eval_word]

theorem sound [Fintype A] [Nontrivial A] (I : Ops m A) (rels : List (Word m))
    (w : Word m) (h : Bijective (run I (compile rels w))) : HasFiniteGroupWitness rels w := by
  obtain ⟨hf,hm,hd,hr,hs⟩ := (compile_iff I rels w).mp h
  have col (j k : A) : ∃ i, I.F i j = k := by
    obtain ⟨⟨a,b,c⟩, he⟩ := hf.2 (j,k,I.o)
    change (b,I.F a b,c) = (j,k,I.o) at he
    obtain ⟨rfl,hp⟩ := Prod.mk.inj he
    exact ⟨a,(Prod.mk.inj hp).1⟩
  have sep (a u z v t : A)
      (e : Cycle372.data I.F I.G I.o a u z = Cycle372.data I.F I.G I.o a v t) : z=t := by
    have he := hm.1 (show run I marker (a,u,z) = run I marker (a,v,t)
      from congrArg (fun q : A × A => (a,q)) e)
    exact congrArg (fun q : Triple A => q.2.2) he
  have dcol (x i j : A) (e : I.D i x = I.D j x) : i=j := by
    have he := hd.1 (show run I columnD (i,x,I.o) = run I columnD (j,x,I.o)
      from congrArg (fun a : A => (x,a,I.o)) e)
    exact congrArg Prod.fst he
  have rows (r : Word m) (hmemb : r ∈ laws rels) (x k : A) :
      ∃ v, I.G (I.D (evalWord I.letter r x) x) v = k := by
    obtain ⟨⟨a,b,c⟩, he⟩ := (hr r hmemb).2 (x,k,I.o)
    rw [run_row] at he
    obtain ⟨rfl,hp⟩ := Prod.mk.inj he
    exact ⟨b,(Prod.mk.inj hp).1⟩
  apply group_witness_of_action I.letter I.o rels w
  · intro r hmemb x
    exact Cycle372.compile_identity I.F I.G I.o I.D (evalWord I.letter r)
      col sep dcol (rows [] (by simp [laws])) (rows r hmemb) x
  · intro heq
    obtain ⟨b,hb⟩ := exists_ne I.o
    obtain ⟨v,hv⟩ := hs.2 (I.o,b,I.o)
    rw [run_sep,heq] at hv
    exact hb (((Prod.mk.inj (Prod.mk.inj hv).2).1).symm.trans (Prod.mk.inj hv).1)

/-- Every passer for the compressed triple is also a passer for the literal
paper triple on its same carrier, using definable tables for the extra symbols. -/
def expand (I : Tables A) : Ops m A where
  o := I.o
  F := I.D
  G := I.G
  D := I.D
  letter := letterMap I
  Q a v t := I.D (I.G a v) t

theorem expand_pass [Finite A] (I : Tables A) (rels : List (Word m)) (w : Word m)
    (h : Bijective (SquareBijection.run I (SquareBijection.compile rels w))) :
    Bijective (run (expand I) (compile rels w)) := by
  obtain ⟨hc,hm,hr,hs⟩ := (SquareBijection.compile_iff I rels w).mp h
  apply (compile_iff _ _ _).mpr
  refine ⟨hc,hm,hc,?_,?_⟩
  · intro r hmem
    have eq : run (expand I) (row r) = SquareBijection.run I (SquareBijection.row r) := by
      funext p
      rw [run_row,SquareBijection.run_row]
      rfl
    exact eq.symm ▸ hr r hmem
  · have eq : run (expand I) (separator w) = SquareBijection.run I (SquareBijection.separator w) := by
      funext p
      rw [run_sep,SquareBijection.run_separator]
      rfl
    exact eq.symm ▸ hs

/-- Sections 1–3, for the exact original signature with arbitrary primitive tables. -/
theorem originalTriple_iff_finiteQuotient (rels : List (Word m)) (w : Word m) :
    (∃ (A : Type) (_ : Fintype A) (_ : Nontrivial A) (I : Ops m A),
      Bijective (run I (compile rels w))) ↔ HasFiniteQuotient rels w := by
  constructor
  · rintro ⟨A,hA,hn,I,h⟩
    letI := hA
    letI := hn
    exact (finite_model_iff_quotient rels w).mp (sound I rels w h)
  · intro h
    obtain ⟨A,hA,hn,I,hi⟩ := (arbitraryFiniteCarrier_iff_finiteQuotient rels w).mpr h
    letI := hA
    exact ⟨A,hA,hn,expand I,expand_pass I rels w hi⟩

/-- On the paper signature a finite group witness works at its own cardinality.
The cyclic arithmetic supplies the guard tables. The group supplies the unary
tables via its regular action. Their algebraic structures need not coincide. -/
noncomputable def regularOps {Q : Type} [Group Q] {n : ℕ} [NeZero n]
    (e : Q ≃ Fin n) (g : Fin m → Q) : Ops m (Fin n) where
  o := 0
  F a b := a+b
  G := Cycle372.reset
  D a b := a-b
  letter l a := e (groupLetter g l * e.symm a)
  Q c v t := if c = 0 then v else t

theorem regular_word {Q : Type} [Group Q] {n : ℕ} [NeZero n]
    (e : Q ≃ Fin n) (g : Fin m → Q) (v : Word m) (x : Q) :
    evalWord (regularOps e g).letter v (e x) = e (groupWord g v * x) := by
  induction v with
  | nil => simp [evalWord,groupWord]
  | cons l v ih =>
    rw [evalWord,ih]
    simp [regularOps,groupWord,mul_assoc]

theorem finiteHom_passes_at_its_order {Q : Type} [Group Q] [Fintype Q]
    (rels : List (Word m)) (w : Word m) (φ : WordPresentation rels →* Q)
    (hw : φ (presentedWord rels w) ≠ 1) :
    ∃ I : Ops m (Fin (Fintype.card Q)), Bijective (run I (compile rels w)) := by
  classical
  let n := Fintype.card Q
  letI : NeZero n := ⟨Nat.ne_of_gt Fintype.card_pos⟩
  let e₀ : Q ≃ Fin n := Fintype.equivFin Q
  let e := e₀.trans (Equiv.swap (e₀ 1) (0 : Fin n))
  have he : e 1 = 0 := by simp [e]
  let g (i : Fin m) : Q := φ (PresentedGroup.of i)
  have hg (v : Word m) : φ (presentedWord rels v) = groupWord g v := by
    rw [presentedWord_eq,groupWord_map]
  have hr : ∀ r ∈ rels, groupWord g r = 1 := by
    intro r hmemb
    rw [← hg,presented_relator rels r hmemb,map_one]
  have live : evalWord (regularOps e g).letter w 0 ≠ 0 := by
    rw [← he,regular_word,mul_one]
    intro h
    exact hw ((hg w).trans (e.injective h))
  refine ⟨regularOps e g,(compile_iff _ _ _).mpr ⟨?_,?_,?_,?_,?_⟩⟩
  · apply Surjective.bijective_of_finite
    rintro ⟨a,b,c⟩
    exact ⟨(b-a,a,c),by simp [run,columnF,eval,regularOps]⟩
  · apply Surjective.bijective_of_finite
    rintro ⟨a,X,Y⟩
    let q := Cycle372.decoder a (X,Y)
    refine ⟨(a,q),?_⟩
    exact congrArg (fun pair : Fin n × Fin n => (a,pair)) (Cycle372.decoder_right a X Y)
  · apply Surjective.bijective_of_finite
    rintro ⟨a,b,c⟩
    exact ⟨(b+a,a,c),by simp [run,columnD,eval,regularOps]⟩
  · intro r hmemb
    apply Surjective.bijective_of_finite
    rintro ⟨a,b,c⟩
    obtain ⟨x,rfl⟩ := e.surjective a
    refine ⟨(e x,b,c),?_⟩
    rw [run_row]
    change (e x, Cycle372.reset (evalWord (regularOps e g).letter r (e x) - e x) b, c) = _
    rw [regular_word,all_group_laws g rels hr r hmemb,one_mul,sub_self]
    simp [Cycle372.reset]
  · apply Surjective.bijective_of_finite
    rintro ⟨a,b,c⟩
    refine ⟨(a,b,c),?_⟩
    rw [run_sep]
    change ((if (0 : Fin n) = 0 then a else b),
      (if evalWord (regularOps e g).letter w 0 = 0 then a else b),c) = _
    simp [live]

#print axioms finiteHom_passes_at_its_order

#print axioms originalTriple_iff_finiteQuotient
end SquareBijection.PaperTriple
