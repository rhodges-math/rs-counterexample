import RSCounterexample.Demazure.Keys
import RSCounterexample.Demazure.Laurent
import RSCounterexample.Paper.Keys
import RSCounterexample.Paper.Laurent

/-!
# The flag-variety library's keys and atoms are RS's

The flag-variety library uses the copy `Schubert.Demazure` of RS's standard-monomial layer. Its
key polynomials, Demazure atoms and Laurent embedding coincide with RS's: the non-recursive
definitions agree by unfolding, and the recursive ones (`key`, `atom`, by the leftmost-ascent
sorting recursion) by induction on the sorting measure.
-/

namespace Schubert.RS.Geometric

variable {n : ℕ}

theorem toLaurent_eq : @Demazure.toLaurent n = @Schubert.RS.toLaurent n :=
  rfl

theorem compositionMonomial_eq (a : Composition n) :
    Demazure.compositionMonomial a = Schubert.RS.compositionMonomial a :=
  rfl

/-- **The key polynomials of `Schubert.Demazure` are RS's.** -/
theorem key_eq (a : Composition n) : Demazure.key a = Schubert.RS.key a := by
  induction a using (measure Schubert.RS.sortingMeasure).wf.induction with
  | h a ih =>
    by_cases h : (Schubert.RS.ascentSet a).Nonempty
    · have hy := ih (Demazure.swapComposition a (Demazure.firstAscent a h))
        (Schubert.RS.sortingMeasure_firstAscent a h)
      rw [Demazure.key_ascent a h, Schubert.RS.key_ascent a h, hy]
      rfl
    · rw [Demazure.key_of_no_ascent a h, Schubert.RS.key_of_no_ascent a h]
      rfl

/-- **The Demazure atoms of `Schubert.Demazure` are RS's.** -/
theorem atom_eq (a : Composition n) : Demazure.atom a = Schubert.RS.atom a := by
  induction a using (measure Schubert.RS.sortingMeasure).wf.induction with
  | h a ih =>
    by_cases h : (Schubert.RS.ascentSet a).Nonempty
    · have hy := ih (Demazure.swapComposition a (Demazure.firstAscent a h))
        (Schubert.RS.sortingMeasure_firstAscent a h)
      rw [Demazure.atom_ascent a h, Schubert.RS.atom_ascent a h, hy]
      rfl
    · rw [Demazure.atom_of_no_ascent a h, Schubert.RS.atom_of_no_ascent a h]
      rfl

end Schubert.RS.Geometric
