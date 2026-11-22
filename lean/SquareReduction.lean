import SquareSoundness
import SquareWitness

namespace SquareBijection
open Function DisequalityDispersion

private theorem fin_nontrivial_of_two_le {n : ℕ} (hn : 2 ≤ n) : Nontrivial (Fin n) := by
  refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩⟩
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h)

/-- The generated tuple of three terms is bijective for some interpretations of the
fixed signature on an alphabet of size at least two exactly when a surjective
homomorphism onto a finite group separates the input word from the identity. -/
theorem compiledTriple_iff_finiteQuotient {m : ℕ} (rels : List (Word m)) (w : Word m) :
    HasBijectiveInterpretation (compile rels w) ↔ HasFiniteQuotient rels w := by
  constructor
  · rintro ⟨n, hn, I, h⟩
    letI : Nontrivial (Fin n) := fin_nontrivial_of_two_le hn
    exact (finite_model_iff_quotient rels w).mp (compile_sound I rels w h)
  · intro h
    exact compile_complete rels w ((finite_model_iff_quotient rels w).mpr h)

/-- Equivalent version quantifying over all finite nontrivial carriers. -/
theorem arbitraryFiniteCarrier_iff_finiteQuotient {m : ℕ} (rels : List (Word m)) (w : Word m) :
    (∃ (A : Type) (_ : Fintype A) (_ : Nontrivial A) (I : Tables A),
       Bijective (run I (compile rels w))) ↔ HasFiniteQuotient rels w := by
  constructor
  · rintro ⟨A, hA, hN, I, h⟩
    letI := hA
    letI := hN
    exact (finite_model_iff_quotient rels w).mp (compile_sound I rels w h)
  · intro h
    obtain ⟨n, hn, I, hi⟩ := (compiledTriple_iff_finiteQuotient rels w).mpr h
    exact ⟨Fin n, inferInstance, fin_nontrivial_of_two_le hn, I, hi⟩

#print axioms compiledTriple_iff_finiteQuotient
#print axioms arbitraryFiniteCarrier_iff_finiteQuotient

end SquareBijection
