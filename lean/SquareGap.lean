import SquareReduction
import Mathlib.Data.Finset.Lattice.Fold

/-! The hard padded threshold and the arithmetic step for the strict one-unit
threshold. The latter states its two inputs from the term-cut theorem explicitly. -/
namespace SquareBijection
open Function DisequalityDispersion

/-- A tuple reading the original inputs and k additional coordinates, with one
extra ignored input and one constant output. X represents the original triple. -/
def padded {X Y A : Type} (f : X → X) (o : A) (p : X × Y × A) : X × Y × A :=
  (f p.1, p.2.1, o)

theorem padded_card {X Y A : Type} [Fintype X] [Fintype Y] [Fintype A]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] (f : X → X) (o : A) :
    (Finset.univ.image (padded (Y := Y) f o)).card =
      (Finset.univ.image f).card * Fintype.card Y := by
  have eq : Finset.univ.image (padded (Y := Y) f o) =
      (Finset.univ.image f) ×ˢ ((Finset.univ : Finset Y) ×ˢ {o}) := by
    ext ⟨u,v,t⟩
    constructor
    · intro h
      obtain ⟨⟨a,b,c⟩, _, he⟩ := Finset.mem_image.mp h
      change (f a,b,o) = (u,v,t) at he
      cases he
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _,rfl⟩,
        Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_singleton_self _⟩⟩
    · intro h
      obtain ⟨hu,hvt⟩ := Finset.mem_product.mp h
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hu
      have ht : t = o := Finset.mem_singleton.mp (Finset.mem_product.mp hvt).2
      exact Finset.mem_image.mpr ⟨(a,v,o),Finset.mem_univ _,by simp [padded,ha,ht]⟩
  rw [eq]
  simp

theorem padded_threshold {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (I : Tables (Fin n)) (s : Triple Expr) :
    n^(3+k) ≤ (Finset.univ.image (padded (Y := Fin k → Fin n) (run I s) I.o)).card ↔
      Bijective (run I s) := by
  let f := run I s
  have cardX : (Finset.univ : Finset (Triple (Fin n))).card = n^3 := by
    simp [Triple, pow_succ, Nat.mul_assoc]
  have cardY : Fintype.card (Fin k → Fin n) = n^k := by simp
  have pos : 0 < n^k := pow_pos (by omega) _
  rw [padded_card, cardY, pow_add]
  constructor
  · intro h
    have hi : (Finset.univ.image f).card = (Finset.univ : Finset (Triple (Fin n))).card :=
      le_antisymm Finset.card_image_le (by rw [cardX]; exact Nat.le_of_mul_le_mul_right h pos)
    have inj : Injective f := by simpa using (Finset.card_image_iff.mp hi)
    exact inj.bijective_of_finite
  · intro h
    rw [Finset.card_image_of_injective _ h.1,cardX]

/-- Existence of an interpretation is equivalent to the usual maximum-image
threshold because there are finitely many tables on Fin n. -/
theorem padded_exact_iff_finiteQuotient {m : ℕ} (rels : List (Word m)) (w : Word m) (k : ℕ) :
    (∃ n : ℕ, 2 ≤ n ∧ ∃ I : Tables (Fin n),
      n^(3+k) ≤ (Finset.univ.image (padded (Y := Fin k → Fin n) (run I (compile rels w)) I.o)).card)
    ↔ HasFiniteQuotient rels w := by
  rw [← compiledTriple_iff_finiteQuotient]
  constructor
  · rintro ⟨n,hn,I,hi⟩
    exact ⟨n,hn,I,(padded_threshold hn k I _).mp hi⟩
  · rintro ⟨n,hn,I,hi⟩
    exact ⟨n,hn,I,(padded_threshold hn k I _).mpr hi⟩

/-- The positive constant in the routing lower bound is represented using an
integer denominator K. All that is used is the cut bound for EVERY n ≥ 2
and the routing estimate from some N onward. -/
theorem oneUnit_iff_cutExponent (delta : ℕ → ℕ) (rho d : ℕ)
    (cut : ∀ n, 2 ≤ n → delta n ≤ n^rho)
    (routing : ∃ K N : ℕ, ∀ n, N ≤ n → n^rho ≤ K * delta n) :
    (∃ n : ℕ, 2 ≤ n ∧ n^d + 1 ≤ delta n) ↔ d+1 ≤ rho := by
  constructor
  · rintro ⟨n, hn, h⟩
    by_contra! hr
    have he := Nat.pow_le_pow_right (by omega : 0 < n) (by omega : rho ≤ d)
    have hc := cut n hn
    omega
  · intro hr
    obtain ⟨K,N,hl⟩ := routing
    let n := max (max N (K+1)) 2
    have hN : N ≤ n := (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
    have hK : K < n := (Nat.le_max_right N (K+1)).trans (Nat.le_max_left _ _)
    have hn : 2 ≤ n := Nat.le_max_right _ _
    refine ⟨n,hn,?_⟩
    by_contra! hsmall
    have hu : delta n ≤ n^d := by omega
    have h₁ := Nat.pow_le_pow_right (by omega : 0 < n) hr
    rw [pow_succ, Nat.mul_comm (n^d) n] at h₁
    have h₂ := (h₁.trans (hl n hN)).trans (Nat.mul_le_mul_left K hu)
    have h₃ := Nat.mul_lt_mul_of_pos_right hK (pow_pos (by omega : 0 < n) d)
    omega

/-- Equality-only decoder systems. One equation is imposed per coordinate of
the input tuple, expressing that the decoder recovers that coordinate. -/
noncomputable def recovered {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Y) (g : Y → X) : Finset X :=
  Finset.univ.filter (fun x => g (f x) = x)

theorem decoder_injOn {X Y : Type} [Fintype X] [DecidableEq X]
    (f : X → Y) (g : Y → X) : Set.InjOn f ↑(recovered f g) := by
  intro x hx y hy h
  have h₁ := (Finset.mem_filter.mp hx).2
  have h₂ := (Finset.mem_filter.mp hy).2
  exact h₁.symm.trans ((congrArg g h).trans h₂)

theorem decoder_upper {X Y : Type} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (g : Y → X) :
    (recovered f g).card ≤ (Finset.univ.image f).card := by
  rw [← (Finset.card_image_iff.mpr (decoder_injOn f g))]
  exact Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ _))

theorem decoder_attains_image {X Y : Type} [Fintype X] [Nonempty X]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    ∃ g : Y → X, (recovered f g).card = (Finset.univ.image f).card := by
  classical
  let g (y : Y) := if h : ∃ x, f x = y then Classical.choose h else Classical.arbitrary X
  have section_on_image (x : X) : f (g (f x)) = f x := by
    have h : ∃ t, f t = f x := ⟨x,rfl⟩
    simpa only [g,dif_pos h] using Classical.choose_spec h
  refine ⟨g,le_antisymm (decoder_upper f g) ?_⟩
  rw [← (Finset.card_image_iff.mpr (decoder_injOn f g))]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨g (f x),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,section_on_image x⟩
  exact congrArg g (section_on_image x)

private def tableEncoding (A : Type) :
    Tables A ≃ A × (A → A → A) × (A → A → A) × (A → A → A) where
  toFun I := (I.o,I.D,I.G,I.H)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual maximum image size, over all common interpretations at each n. -/
noncomputable def paddedDispersion (n k : ℕ) (s : Triple Expr) : ℕ := by
  classical
  letI : Fintype (Tables (Fin n)) := Fintype.ofEquiv _ (tableEncoding (Fin n)).symm
  exact Finset.univ.sup fun I : Tables (Fin n) =>
    (Finset.univ.image (padded (Y := Fin k → Fin n) (run I s) I.o)).card

theorem max_threshold_iff {n k t : ℕ} (ht : 0 < t) (s : Triple Expr) :
    t ≤ paddedDispersion n k s ↔ ∃ I : Tables (Fin n),
      t ≤ (Finset.univ.image (padded (Y := Fin k → Fin n) (run I s) I.o)).card := by
  classical
  unfold paddedDispersion
  rw [Finset.le_sup_iff ht]
  simp

theorem exact_maximum_iff_finiteQuotient {m : ℕ} (rels : List (Word m)) (w : Word m) (k : ℕ) :
    (∃ n : ℕ, 2 ≤ n ∧ n^(3+k) ≤ paddedDispersion n k (compile rels w)) ↔ HasFiniteQuotient rels w := by
  rw [← padded_exact_iff_finiteQuotient rels w k]
  constructor
  · rintro ⟨n,hn,h⟩
    exact ⟨n,hn,(max_threshold_iff (pow_pos (by omega : 0<n) _) _).mp h⟩
  · rintro ⟨n,hn,h⟩
    exact ⟨n,hn,(max_threshold_iff (pow_pos (by omega : 0<n) _) _).mpr h⟩

#print axioms exact_maximum_iff_finiteQuotient
#print axioms decoder_attains_image
#print axioms padded_exact_iff_finiteQuotient
#print axioms oneUnit_iff_cutExponent
end SquareBijection
