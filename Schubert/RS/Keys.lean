import Schubert.RS.Operators

/-!
# Keys and atoms by a terminating sorting recursion

At each strict ascent we choose the leftmost position and sort it. The reverse
sequence constructs the polynomial from a decreasing monomial. Agreement with
other reduced sorting sequences is a separate theorem, not an assumed input.
-/

namespace Schubert.RS

open FinPermutation

noncomputable section

variable {n : ℕ}

def compositionMonomial (a : Composition n) : Polynomial n :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1

/-- Key polynomial with a fixed leftmost-ascent convention. -/
def key (a : Composition n) : Polynomial n :=
  if h : (ascentSet a).Nonempty then
    isobaric (firstAscent a h) (key (swapComposition a (firstAscent a h)))
  else compositionMonomial a
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

/-- Demazure atom with the same sorting convention as `key`. -/
def atom (a : Composition n) : Polynomial n :=
  if h : (ascentSet a).Nonempty then
    atomOperator (firstAscent a h) (atom (swapComposition a (firstAscent a h)))
  else compositionMonomial a
termination_by sortingMeasure a
decreasing_by exact sortingMeasure_firstAscent a h

theorem key_ascent (a : Composition n) (h : (ascentSet a).Nonempty) :
    key a = isobaric (firstAscent a h) (key (swapComposition a (firstAscent a h))) := by
  rw [key, dif_pos h]

theorem atom_ascent (a : Composition n) (h : (ascentSet a).Nonempty) :
    atom a = atomOperator (firstAscent a h) (atom (swapComposition a (firstAscent a h))) := by
  rw [atom, dif_pos h]

theorem key_of_no_ascent (a : Composition n) (h : ¬(ascentSet a).Nonempty) :
    key a = compositionMonomial a := by
  rw [key, dif_neg h]

theorem atom_of_no_ascent (a : Composition n) (h : ¬(ascentSet a).Nonempty) :
    atom a = compositionMonomial a := by
  rw [atom, dif_neg h]

theorem no_ascent_of_antitone (a : Composition n) (h : Antitone a) :
    ¬(ascentSet a).Nonempty := by
  rintro ⟨j, hj⟩
  exact (not_lt_of_ge (h (adjacentPosition j).left_lt_right.le))
    (Finset.mem_filter.mp hj).2

theorem key_of_antitone (a : Composition n) (h : Antitone a) :
    key a = compositionMonomial a :=
  key_of_no_ascent a (no_ascent_of_antitone a h)

theorem atom_of_antitone (a : Composition n) (h : Antitone a) :
    atom a = compositionMonomial a :=
  atom_of_no_ascent a (no_ascent_of_antitone a h)

end
end Schubert.RS
