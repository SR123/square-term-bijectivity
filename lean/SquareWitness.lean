import SquareTerms
import Mathlib.Tactic.Abel

namespace SquareBijection
open Function DisequalityDispersion
variable {n m : ℕ} [NeZero n]

def cyclic (H : Fin n → Fin n → Fin n) : Tables (Fin n) where
  o := 0
  D i j := i-j
  G z t := -(Cycle372.reset z t)
  H := H

theorem cyclic_mark (H : Fin n → Fin n → Fin n) (a u z : Fin n) :
    Cycle372.data (cyclic H).D (cyclic H).G 0 a u z =
      Cycle372.data (· + ·) Cycle372.reset 0 a u z := by
  have h : Cycle372.L (cyclic H).D (cyclic H).G =
      Cycle372.L (· + ·) (@Cycle372.reset n _) := by
    funext i j t
    simp [Cycle372.L,cyclic]
  simp only [Cycle372.data,h]

theorem cyclic_pass (H : Fin n → Fin n → Fin n) (rels : List (Word m)) (w : Word m)
    (hr : ∀ r ∈ laws rels, ∀ x, evalWord (letterMap (cyclic H)) r x = x)
    (hw : evalWord (letterMap (cyclic H)) w 0 ≠ 0) :
    Bijective (run (cyclic H) (compile rels w)) := by
  apply (compile_iff _ _ _).mpr
  refine ⟨?_,?_,?_,?_⟩
  · apply Surjective.bijective_of_finite
    rintro ⟨a,b,c⟩
    exact ⟨(b+a,a,c),by simp [run,column,eval,cyclic]⟩
  · apply Surjective.bijective_of_finite
    rintro ⟨a,X,Y⟩
    let q := Cycle372.decoder a (X,Y)
    refine ⟨(a,q),?_⟩
    rw [run_marker]
    apply congrArg (fun pair : Fin n × Fin n => (a, pair))
    change Cycle372.data (cyclic H).D (cyclic H).G 0 a q.1 q.2 = (X,Y)
    rw [cyclic_mark]
    exact Cycle372.decoder_right a X Y
  · intro r hm
    apply Surjective.bijective_of_finite
    rintro ⟨a,b,c⟩
    refine ⟨(a,-b,c),?_⟩
    rw [run_row]
    change (a, (cyclic H).G ((cyclic H).D (evalWord (letterMap (cyclic H)) r a) a) (-b), c) = _
    rw [hr r hm a]
    simp [cyclic, Cycle372.reset]
  · apply Surjective.bijective_of_finite
    rintro ⟨X,Y,Z⟩
    let d := evalWord (letterMap (cyclic H)) w 0
    let t := -d-Y
    refine ⟨(-X-t,t,Z),?_⟩
    rw [run_separator]
    change ((-(Cycle372.reset 0 (-X-t)))-t, (-(Cycle372.reset d (-X-t)))-t,Z) = (X,Y,Z)
    have hd : d ≠ 0 := hw
    simp only [Cycle372.reset,if_neg hd,Prod.mk.injEq,and_true]
    constructor <;> dsimp [t] <;> abel

theorem tagIndex_pos {m : ℕ} (l : Letter (Fin m)) : 0 < tagIndex l := by
  simp [tagIndex]

theorem tagIndex_le {m : ℕ} (l : Letter (Fin m)) : tagIndex l ≤ 2*m := by
  rcases l with ⟨i,b⟩
  have hi := i.isLt
  cases b <;> simp [tagIndex] <;> omega

theorem tagIndex_inj {m : ℕ} : Injective (@tagIndex m) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have hi := i.isLt
  have hj := j.isLt
  apply Prod.ext
  · apply Fin.ext
    cases b <;> cases c <;> simp [tagIndex] at h <;> omega
  · cases b <;> cases c <;> simp_all [tagIndex] <;> omega

abbrev Carrier (Q : Type) (m : ℕ) := Q × Fin (2*m+1)

def base {Q : Type} [Group Q] (m : ℕ) : Carrier Q m := (1,0)

def slot (m j : ℕ) : Fin (2*m+1) :=
  ⟨min j (2*m), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The distinguished row walks along the tags. Every signed-generator row
acts by left multiplication on the first coordinate, leaving the tag fixed. -/
noncomputable def taggedH {Q : Type} [Group Q] (g : Fin m → Q)
    (c a : Carrier Q m) : Carrier Q m := by
  classical
  exact if c = base m then (1,slot m (a.2.val+1)) else
    if hex : ∃ l : Letter (Fin m), tagIndex l = c.2.val then
      (groupLetter g (Classical.choose hex) * a.1,a.2)
    else a

theorem tag_value {Q : Type} [Group Q] (g : Fin m → Q) (j : ℕ) (hj : j ≤ 2*m) :
    tagVal (base m) (taggedH g) j = (1,slot m j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hv : j ≤ 2*m := by omega
    rw [tagVal,ih hv]
    simp [taggedH,slot,Nat.min_eq_left hv]

theorem tagged_letter {Q : Type} [Group Q] (g : Fin m → Q) (l : Letter (Fin m))
    (a : Carrier Q m) :
    taggedH g (tagVal (base m) (taggedH g) (tagIndex l)) a =
      (groupLetter g l * a.1,a.2) := by
  classical
  rw [tag_value g _ (tagIndex_le l)]
  have hv : (slot m (tagIndex l)).val = tagIndex l := Nat.min_eq_left (tagIndex_le l)
  have hn : ((1,slot m (tagIndex l)) : Carrier Q m) ≠ base m := by
    intro h
    have he := congrArg (fun x : Carrier Q m => x.2.val) h
    change (slot m (tagIndex l)).val = 0 at he
    rw [hv] at he
    exact (Nat.ne_of_gt (tagIndex_pos l)) he
  have hex : ∃ t : Letter (Fin m), tagIndex t = (slot m (tagIndex l)).val := ⟨l,hv.symm⟩
  have hwhich : Classical.choose hex = l := tagIndex_inj ((Classical.choose_spec hex).trans hv)
  simp only [taggedH, if_neg hn, dif_pos hex, hwhich]

def transportH {A B : Type} (e : A ≃ B) (h : A → A → A) (c a : B) : B :=
  e (h (e.symm c) (e.symm a))

theorem tag_transport {A B : Type} (e : A ≃ B) (h : A → A → A) (o : A) (j : ℕ) :
    tagVal (e o) (transportH e h) j = e (tagVal o h j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [tagVal,ih,transportH]

theorem transported_word {Q : Type} [Group Q] (g : Fin m → Q)
    (e : Carrier Q m ≃ Fin n) (he : e (base m) = 0) (v : Word m) (a : Carrier Q m) :
    evalWord (letterMap (cyclic (transportH e (taggedH g)))) v (e a) =
      e (groupWord g v * a.1,a.2) := by
  have hl (l : Letter (Fin m)) (b : Carrier Q m) :
      letterMap (cyclic (transportH e (taggedH g))) l (e b) =
        e (groupLetter g l * b.1,b.2) := by
    change transportH e (taggedH g) (tagVal 0 (transportH e (taggedH g)) (tagIndex l)) (e b) = _
    rw [← he,tag_transport]
    simp [transportH,tagged_letter]
  induction v with
  | nil => simp [evalWord,groupWord]
  | cons l v ih => rw [evalWord,ih,hl]; simp [groupWord,mul_assoc]

theorem all_group_laws {Q : Type} [Group Q] (g : Fin m → Q) (rels : List (Word m))
    (hr : ∀ r ∈ rels, groupWord g r = 1) :
    ∀ r ∈ laws rels, groupWord g r = 1 := by
  simp only [laws, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
  refine ⟨⟨⟨by simp [groupWord],?_⟩,?_⟩,hr⟩ <;>
    intro i _ <;> simp [groupWord,groupLetter]

def HasBijectiveInterpretation (s : Triple Expr) : Prop :=
  ∃ (n : ℕ), 2 ≤ n ∧ ∃ I : Tables (Fin n), Bijective (run I s)

theorem compile_complete (rels : List (Word m)) (w : Word m)
    (h : HasFiniteGroupWitness rels w) : HasBijectiveInterpretation (compile rels w) := by
  classical
  obtain ⟨Q,hgroup,hfin,g,hr,hw⟩ := h
  letI := hgroup
  letI := hfin
  letI : Nontrivial Q := ⟨groupWord g w,1,hw⟩
  let B := Carrier Q m
  let N := Fintype.card B
  have hn : 2 ≤ N := Fintype.one_lt_card
  letI : NeZero N := ⟨by omega⟩
  let e₀ : B ≃ Fin N := Fintype.equivFin B
  let e := e₀.trans (Equiv.swap (e₀ (base m)) (0 : Fin N))
  have he : e (base m) = 0 := by simp [e]
  let H := transportH e (taggedH g)
  refine ⟨N,hn,cyclic H,cyclic_pass H rels w ?_ ?_⟩
  · intro r hmem x
    obtain ⟨a,rfl⟩ := e.surjective x
    rw [transported_word g e he r a, all_group_laws g rels hr r hmem,one_mul]
  · intro hbad
    have eq := transported_word g e he w (base m)
    rw [he] at eq
    have ht := e.injective (eq.symm.trans (hbad.trans he.symm))
    exact hw (by simpa [base] using congrArg Prod.fst ht)

end SquareBijection
