import Std

/- The literal mixed square and the unrestricted soundness direction.
   No structure, finiteness, decidable equality, or special laws on A.
   Uses only the necessary surjectivity/injectivity parts of the tests. -/
namespace Cycle372

variable {A : Type} (F G : A → A → A)

def L (i j t : A) : A := F i (G j t)

def data (c a u z : A) : A × A :=
  let b := L F G a c c
  let y := L F G a z (L F G a z b)
  let U := L F G u c
  (U (U y), U (U (L F G u z y)))

theorem exclusive (c : A)
    (col : ∀ t w : A, ∃ i, F i t = w)
    (sep : ∀ a u z v t, data F G c a u z = data F G c a v t → z = t)
    (d b : A) (hit : G d b = G c c) : d = c := by
  obtain ⟨a, ha⟩ := col (G c c) b
  have hbase : L F G a c c = b := ha
  have hfix : L F G a d b = b := by
    change F a (G d b) = b
    rw [hit, ha]
  let w := L F G a c (L F G a c b)
  obtain ⟨v, hv⟩ := col (G c w) w
  have hstay : L F G v c w = w := hv
  have hd : data F G c a a d = (w,w) := by
    simp only [data, hbase, hfix]
    rfl
  have hc : data F G c a v c = (w,w) := by
    simp only [data, hbase]
    change (L F G v c (L F G v c w),
            L F G v c (L F G v c (L F G v c w))) = (w,w)
    simp only [hstay]
  exact sep a a d v c (hd.trans hc.symm)

def colSquare (v : A × A) := (v.2, F v.1 v.2)
def rowSquare (h : A → A) (v : A × A) := (v.1, G (h v.1) v.2)
def mainSquare (h : A → A) (i : (A × A) × (A × A)) :=
  (i.1, data F G (h i.1.1) i.1.2 i.2.1 i.2.2)

theorem constancy (h : A → A)
    (colOnto : ∀ out, ∃ i, colSquare F i = out)
    (rowOnto : ∀ out, ∃ i, rowSquare G h i = out)
    (mainInj : ∀ i j, mainSquare F G h i = mainSquare F G h j → i = j)
    (p q : A) : h p = h q := by
  have col : ∀ t w : A, ∃ i, F i t = w := by
    intro t w
    obtain ⟨⟨v,j⟩,hj⟩ := colOnto (t,w)
    obtain ⟨rfl, hw⟩ := Prod.mk.inj hj
    exact ⟨v, hw⟩
  have rows : ∀ q t : A, ∃ b, G (h q) b = t := by
    intro q t
    obtain ⟨⟨j,v⟩,hj⟩ := rowOnto (q,t)
    obtain ⟨rfl, ht⟩ := Prod.mk.inj hj
    exact ⟨v, ht⟩
  have sep : ∀ a u z v t, data F G (h p) a u z = data F G (h p) a v t → z = t := by
    intro a u z v t he
    have k := mainInj ((p,a),(u,z)) ((p,a),(v,t)) (congrArg (fun s => ((p,a),s)) he)
    exact congrArg (fun i => i.2.2) k
  obtain ⟨b,hb⟩ := rows q (G (h p) (h p))
  exact (exclusive F G (h p) col sep (h q) b hb).symm

#print axioms exclusive
#print axioms constancy

/-- The marker separation also compiles a unary identity, using only the
    necessary parts of the actual square tests for F, G, and D. -/
theorem compile_identity (o : A) (D : A → A → A) (t : A → A)
    (col : ∀ j w : A, ∃ i, F i j = w)
    (sep : ∀ a u z v j, data F G o a u z = data F G o a v j → z = j)
    (dcol : ∀ x i j, D i x = D j x → i = j)
    (diag : ∀ x k, ∃ b, G (D x x) b = k)
    (term : ∀ x k, ∃ b, G (D (t x) x) b = k)
    (x : A) : t x = x := by
  obtain ⟨b,hb⟩ := diag x (G o o)
  obtain ⟨e,he⟩ := term x (G o o)
  exact dcol x (t x) x ((exclusive F G o col sep _ e he).trans
                         (exclusive F G o col sep _ b hb).symm)

#print axioms compile_identity

section CyclicWitness
variable {n : Nat} [NeZero n]

def reset (z t : Fin n) := if z = 0 then t else z
def encoded (a u z : Fin n) : Fin n × Fin n :=
  if z = 0 then (2*u+3*a, 3*u+3*a) else (2*u+a+z, 3*u+z)
def residual (a X Y : Fin n) : Fin n := 3*X-2*Y-3*a
def decoder (a : Fin n) (q : Fin n × Fin n) : Fin n × Fin n :=
  let z := residual a q.1 q.2
  (if z = 0 then q.2-q.1 else q.2-q.1+a, z)

theorem literal_encoded (a u z : Fin n) :
    data (· + ·) reset 0 a u z = encoded a u z := by
  by_cases hz : z = 0
  · subst z
    apply Prod.ext <;> simp [data, L, reset, encoded] <;> grind
  · apply Prod.ext <;> simp [data, L, reset, encoded, hz] <;> grind

theorem residual_encoded (a u z : Fin n) :
    residual a (encoded a u z).1 (encoded a u z).2 = z := by
  by_cases hz : z = 0
  · subst z; simp [encoded, residual] <;> grind
  · simp [encoded, residual, hz] <;> grind

theorem decoder_left (a u z : Fin n) :
    decoder a (data (· + ·) reset 0 a u z) = (u,z) := by
  rw [literal_encoded]
  unfold decoder
  rw [residual_encoded]
  by_cases hz : z = 0
  · subst z; simp [encoded] <;> grind
  · simp [encoded, hz] <;> grind

theorem decoder_right (a X Y : Fin n) :
    data (· + ·) reset 0 a (decoder a (X,Y)).1 (decoder a (X,Y)).2 = (X,Y) := by
  rw [literal_encoded]
  by_cases hz : residual a X Y = 0
  · have he : 3*X-2*Y-3*a = 0 := hz
    apply Prod.ext <;> simp [decoder, encoded, hz] <;> grind
  · apply Prod.ext <;> simp [decoder, encoded, residual] at * <;> grind

#print axioms decoder_left
#print axioms decoder_right
end CyclicWitness
end Cycle372
