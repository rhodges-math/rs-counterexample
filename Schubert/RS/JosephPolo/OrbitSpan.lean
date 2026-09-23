import Schubert.RS.JosephPolo.RootOrbit
import Schubert.RS.JosephPolo.PolynomialSpan
import Schubert.RS.Representation.CyclicGeneration

namespace Schubert.RS.Representation
noncomputable section

/-- A finite word of elementary upper-unipotent row actions. -/
def upperRowWord {n : ℕ} : List (PositiveRoot n × ℂ) → MatrixPolynomial n → MatrixPolynomial n
  | [], p => p
  | (r,t)::w, p => rowAction (1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) (upperRowWord w p)

def upperRowOrbitSpan {n : ℕ} (p : MatrixPolynomial n) : Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ (Set.range (fun w : List (PositiveRoot n × ℂ) => upperRowWord w p))

theorem upperRowOrbitSpan_seed {n : ℕ} (p : MatrixPolynomial n) : p ∈ upperRowOrbitSpan p :=
  Submodule.subset_span ⟨[],rfl⟩

theorem upperRowOrbitSpan_stable {n : ℕ} (p : MatrixPolynomial n) (r : PositiveRoot n)
    (t : ℂ) {q : MatrixPolynomial n} (hq : q ∈ upperRowOrbitSpan p) :
    rowAction (1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) q ∈ upperRowOrbitSpan p := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨w,rfl⟩ := hq
    exact Submodule.subset_span ⟨(r,t)::w,rfl⟩
  | zero => simpa only [map_zero] using (upperRowOrbitSpan p).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (upperRowOrbitSpan p).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (upperRowOrbitSpan p).smul_mem c ih

theorem root_derivation_mem_of_rowActions_mem {n : ℕ} (S : Submodule ℂ (MatrixPolynomial n))
    (r : PositiveRoot n) (p : MatrixPolynomial n)
    (h : ∀ t : ℂ, rowAction (1 + t • Matrix.single r.val.1 r.val.2 (1:ℂ)) p ∈ S) :
    matrixUnitDerivation r.val.1 r.val.2 p ∈ S := by
  letI : Infinite ℂ := Infinite.of_injective (fun k : ℕ => (k : ℂ)) Nat.cast_injective
  have hc : (rootSubstitution r.val.1 r.val.2 p).coeff 1 ∈ S :=
    polynomial_coeff_mem_of_eval_mem S _ (fun t => by
      change (rootSubstitution r.val.1 r.val.2 p).eval (MvPolynomial.C t) ∈ S
      rw [rootSubstitution_eval]
      exact h t) 1
  have he := rootSubstitution_coeff r.val.1 r.val.2 (ne_of_lt r.property) p 1
  have he' : (rootSubstitution r.val.1 r.val.2 p).coeff 1 =
      matrixUnitDerivation r.val.1 r.val.2 p := by
    simpa [derivationIter_succ] using he
  rwa [he'] at hc

theorem upperRowOrbitSpan_root_stable {n : ℕ} (p : MatrixPolynomial n) (r : PositiveRoot n)
    {q : MatrixPolynomial n} (hq : q ∈ upperRowOrbitSpan p) :
    matrixUnitDerivation r.val.1 r.val.2 q ∈ upperRowOrbitSpan p :=
  root_derivation_mem_of_rowActions_mem (upperRowOrbitSpan p) r q
    (fun t => upperRowOrbitSpan_stable p r t hq)

/-- Equality of the Lie-cyclic and elementary row-orbit models, for every
matrix polynomial, without JP, PBW, character formulas, or geometry. -/
theorem upperCyclic_eq_upperRowOrbitSpan {n : ℕ} (p : MatrixPolynomial n) :
    upperCyclic p = upperRowOrbitSpan p := by
  apply le_antisymm
  · exact upperCyclic_le_of_root_stable p _ (upperRowOrbitSpan_seed p)
      (fun r q hq => upperRowOrbitSpan_root_stable p r hq)
  · apply Submodule.span_le.mpr
    rintro q ⟨w,rfl⟩
    induction w with
    | nil => exact upperCyclic_seed p
    | cons z w ih => exact upperCyclic_rowAction_root_stable z.1 p _ ih z.2

theorem flagDemazure_eq_upperRowOrbitSpan {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) :
    flagDemazure m w = upperRowOrbitSpan (extremalFlag m w) :=
  upperCyclic_eq_upperRowOrbitSpan _

end
end Schubert.RS.Representation
