import SquareTerms

namespace SquareBijection
open DisequalityDispersion Function
variable {A : Type} {m : ℕ}

/-- A successful row test hits every value in its chosen row, at every point. -/
theorem onto_row (I : Tables A) (r : Word m) (h : Surjective (run I (row r))) (x k : A) :
    ∃ v, I.G (I.D (evalWord (letterMap I) r x) x) v = k := by
  obtain ⟨⟨a,b,c⟩, he⟩ := h (x,k,I.o)
  rw [run_row] at he
  obtain ⟨rfl,hb⟩ := Prod.mk.inj he
  exact ⟨b, (Prod.mk.inj hb).1⟩

theorem forced_laws [Finite A] (I : Tables A) (rels : List (Word m)) (w : Word m)
    (h : Bijective (run I (compile rels w))) :
    (∀ r ∈ laws rels, ∀ x, evalWord (letterMap I) r x = x) ∧
    (Nontrivial A → evalWord (letterMap I) w I.o ≠ I.o) := by
  obtain ⟨hc, hm, hr, hs⟩ := (compile_iff I rels w).mp h
  have col (j k : A) : ∃ i, I.D i j = k := by
    obtain ⟨⟨i,j',z⟩, he⟩ := hc.2 (j,k,I.o)
    change (j',I.D i j',z) = (j,k,I.o) at he
    obtain ⟨rfl, hpair⟩ := Prod.mk.inj he
    exact ⟨i,(Prod.mk.inj hpair).1⟩
  have sep (a u z v j : A)
      (eq : Cycle372.data I.D I.G I.o a u z = Cycle372.data I.D I.G I.o a v j) : z = j := by
    have he := hm.1 (show run I marker (a,u,z) = run I marker (a,v,j)
      from congrArg (fun q : A × A => (a,q)) eq)
    exact congrArg (fun q : Triple A => q.2.2) he
  have dcol (x i j : A) (e : I.D i x = I.D j x) : i = j := by
    have he := hc.1 (show run I column (i,x,I.o) = run I column (j,x,I.o)
      from congrArg (fun k : A => (x,k,I.o)) e)
    exact congrArg Prod.fst he
  constructor
  · intro r hmem x
    exact Cycle372.compile_identity I.D I.G I.o I.D (evalWord (letterMap I) r)
      col sep dcol (onto_row I [] (hr [] (by simp [laws])).2) (onto_row I r (hr r hmem).2) x
  · intro hnt heq
    letI := hnt
    obtain ⟨b,hb⟩ := exists_ne I.o
    obtain ⟨p,hp⟩ := hs.2 (I.o,b,I.o)
    rw [run_separator, heq] at hp
    exact hb (((Prod.mk.inj (Prod.mk.inj hp).2).1).symm.trans (Prod.mk.inj hp).1)

theorem group_witness_of_action [Fintype A] (M : Letter (Fin m) → A → A) (o : A)
    (rels : List (Word m)) (w : Word m)
    (hl : ∀ r ∈ laws rels, ∀ x, evalWord M r x = x) (hw : evalWord M w o ≠ o) :
    HasFiniteGroupWitness rels w := by
  classical
  let p : Fin m → A → A := fun i => M (i,true)
  let b : Fin m → A → A := fun i => M (i,false)
  have pb (i : Fin m) (x : A) : p i (b i x) = x := by
    exact hl [(i,true),(i,false)] (by simp [laws]) x
  have bp (i : Fin m) (x : A) : b i (p i x) = x := by
    exact hl [(i,false),(i,true)] (by simp [laws]) x
  let g := generatorPerms p b pb bp
  have ht : M = fun l : Letter (Fin m) => ⇑(groupLetter g l) := by
    funext l
    rcases l with ⟨i,s⟩
    cases s <;> rfl
  have he (v : Word m) (x : A) : evalWord M v x = groupWord g v x := by
    rw [ht]
    exact evalWord_perm (groupLetter g) v x
  refine ⟨Equiv.Perm A, inferInstance, inferInstance, g, ?_, ?_⟩
  · intro r hr
    ext x
    exact (he r x).symm.trans (hl r (by simp [laws,hr]) x)
  · intro e
    apply hw
    rw [he,e]
    rfl

theorem compile_sound [Fintype A] [Nontrivial A] (I : Tables A)
    (rels : List (Word m)) (w : Word m) (h : Bijective (run I (compile rels w))) :
    HasFiniteGroupWitness rels w := by
  obtain ⟨hl, hw⟩ := forced_laws I rels w h
  exact group_witness_of_action (letterMap I) I.o rels w hl (hw inferInstance)

end SquareBijection
