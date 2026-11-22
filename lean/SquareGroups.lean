import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Fin.Basic

/-! The signed-word and presented-group bridge is drawn from Riis's earlier
term-coding formalisation, Core.lean and PresentationBridge.lean. This module
includes only the group-theoretic definitions and proofs. -/
namespace DisequalityDispersion
variable {A S : Type*}
def evalWord (f : S → A → A) : List S → A → A
  | [], x => x
  | a :: w, x => f a (evalWord f w x)

abbrev Letter (S : Type*) := S × Bool

def signedTables (p m : S → A → A) : Letter S → A → A :=
  fun l => if l.2 then p l.1 else m l.1

def groupLetter {Q : Type*} [Group Q] (g : S → Q) (l : Letter S) : Q :=
  if l.2 then g l.1 else (g l.1)⁻¹

def groupWord {Q : Type*} [Group Q] (g : S → Q) (w : List (Letter S)) : Q :=
  (w.map (groupLetter g)).prod

theorem evalWord_mul_left {Q : Type*} [Group Q] (f : S → Q) (w : List S) (x : Q) :
    evalWord (fun s x => f s * x) w x = (w.map f).prod * x := by
  induction w with
  | nil => simp [evalWord]
  | cons a w ih => simp [evalWord, ih, mul_assoc]

theorem evalWord_perm (f : S → Equiv.Perm A) (w : List S) (x : A) :
    evalWord (fun s => f s) w x = (w.map f).prod x := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [evalWord, List.map_cons, List.prod_cons] using congrArg (f a) ih

def generatorPerms (p m : S → A → A)
    (hpm : ∀ i x, p i (m i x) = x) (hmp : ∀ i x, m i (p i x) = x) :
    S → Equiv.Perm A := fun i =>
  { toFun := p i, invFun := m i, left_inv := hmp i, right_inv := hpm i }

theorem signedTables_perm (p m : S → A → A)
    (hpm : ∀ i x, p i (m i x) = x) (hmp : ∀ i x, m i (p i x) = x)
    (l : Letter S) :
    signedTables p m l = ⇑(groupLetter (generatorPerms p m hpm hmp) l) := by
  rcases l with ⟨i, b⟩
  cases b <;> rfl

def HasFiniteGroupWitness (rels : List (List (Letter S))) (w : List (Letter S)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Fintype Q) (g : S → Q),
    (∀ r ∈ rels, groupWord g r = 1) ∧ groupWord g w ≠ 1

variable {S Q R : Type} [Group Q] [Group R]

theorem groupWord_map (φ : Q →* R) (g : S → Q) (w : List (Letter S)) :
    φ (groupWord g w) = groupWord (fun i => φ (g i)) w := by
  induction w with
  | nil => simp [groupWord]
  | cons l w ih =>
      have hl : φ (groupLetter g l) = groupLetter (fun i => φ (g i)) l := by
        rcases l with ⟨i, b⟩
        cases b <;> simp [groupLetter]
      simpa only [groupWord, List.map_cons, List.prod_cons, map_mul, hl] using
        congrArg (fun q => groupLetter (fun i => φ (g i)) l * q) ih

def freeWord (w : List (Letter S)) : FreeGroup S := groupWord FreeGroup.of w

def presentationRels (rels : List (List (Letter S))) : Set (FreeGroup S) :=
  {r | ∃ v ∈ rels, freeWord v = r}

abbrev WordPresentation (rels : List (List (Letter S))) :=
  PresentedGroup (presentationRels rels)

def presentedWord (rels : List (List (Letter S))) (w : List (Letter S)) :
    WordPresentation rels := PresentedGroup.mk _ (freeWord w)

theorem lift_freeWord (g : S → Q) (w : List (Letter S)) :
    FreeGroup.lift g (freeWord w) = groupWord g w := by
  rw [freeWord, groupWord_map]
  congr 1
  funext i
  exact FreeGroup.lift_apply_of

theorem presentedWord_eq (rels : List (List (Letter S))) (w : List (Letter S)) :
    presentedWord rels w =
      groupWord (PresentedGroup.of : S → WordPresentation rels) w := by
  exact groupWord_map (PresentedGroup.mk _) FreeGroup.of w

theorem presented_relator (rels : List (List (Letter S)))
    (r : List (Letter S)) (hr : r ∈ rels) : presentedWord rels r = 1 := by
  exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩

def HasFinitePresentationHom (rels : List (List (Letter S)))
    (w : List (Letter S)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Fintype Q)
    (φ : WordPresentation rels →* Q), φ (presentedWord rels w) ≠ 1

def HasFiniteQuotient (rels : List (List (Letter S)))
    (w : List (Letter S)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Fintype Q)
    (φ : WordPresentation rels →* Q),
    Function.Surjective φ ∧ φ (presentedWord rels w) ≠ 1

theorem finite_model_iff_presentation_hom (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFiniteGroupWitness rels w ↔ HasFinitePresentationHom rels w := by
  constructor
  · rintro ⟨Q, hQ, hfin, g, hr, hw⟩
    letI := hQ
    letI := hfin
    have hl : ∀ r ∈ presentationRels rels, FreeGroup.lift g r = 1 := by
      rintro r ⟨v, hv, rfl⟩
      rw [lift_freeWord]
      exact hr v hv
    let φ : WordPresentation rels →* Q := PresentedGroup.toGroup hl
    have hφ (v : List (Letter S)) : φ (presentedWord rels v) = groupWord g v := by
      rw [presentedWord_eq, groupWord_map]
      congr 1
      funext i
      exact PresentedGroup.toGroup.of hl
    exact ⟨Q, hQ, hfin, φ, by simpa only [hφ] using hw⟩
  · rintro ⟨Q, hQ, hfin, φ, hw⟩
    letI := hQ
    letI := hfin
    let g : S → Q := fun i => φ (PresentedGroup.of i)
    have hφ (v : List (Letter S)) : φ (presentedWord rels v) = groupWord g v := by
      rw [presentedWord_eq, groupWord_map]
    refine ⟨Q, hQ, hfin, g, ?_, by simpa only [hφ] using hw⟩
    intro r hr
    rw [← hφ, presented_relator rels r hr, map_one]

theorem finite_hom_iff_quotient (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFinitePresentationHom rels w ↔ HasFiniteQuotient rels w := by
  classical
  constructor
  · rintro ⟨Q, hQ, hfin, φ, hw⟩
    letI := hQ
    letI := hfin
    refine ⟨φ.range, inferInstance, inferInstance, φ.rangeRestrict, ?_, ?_⟩
    · exact φ.rangeRestrict_surjective
    · intro h
      apply hw
      exact congrArg Subtype.val h
  · rintro ⟨Q, hQ, hfin, φ, _, hw⟩
    exact ⟨Q, hQ, hfin, φ, hw⟩

theorem finite_model_iff_quotient (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFiniteGroupWitness rels w ↔ HasFiniteQuotient rels w :=
  (finite_model_iff_presentation_hom rels w).trans (finite_hom_iff_quotient rels w)

end DisequalityDispersion
