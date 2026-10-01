import Schubert.RS.GL.Main
import Schubert.RS.Quiver.Extraction
import Schubert.RS.Statements.GLCharacterMultiplicity

/-!
# Theorem 5.3 as a dimension of intertwining maps

For a quiver `Q` with dimension vector `d`, the Levi group `L = ∏_p GL(d_p, ℂ)` acts on the
coordinate ring `R_Q` of `⊕_{e : p → q} Hom(ℂ^{d_p}, ℂ^{d_q})`. For dominant weights `λ`, the
space `Hom_L(V^λ, R_Q)` is finite-dimensional
(`ForwardQuiver.finiteDimensional_intertwiningMap_coordRep`): only the graded pieces of
multidegree at most `degreeBound λ` receive nonzero maps. Given the statement
`GLCharacterMultiplicity`, its dimension is the quiver multiplicity, and Theorem 5.3 reads
`[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)` (`atomCoefficient_eq_finrank_hom`).

## Main results

* `Schubert.RS.Quiver.ForwardQuiver.finiteDimensional_intertwiningMap_coordRep`.
* `Schubert.RS.Quiver.ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl`.
* `Schubert.RS.Quiver.atomCoefficient_eq_finrank_hom`: Theorem 5.3 in the form of the paper.
-/

namespace Schubert.RS.Quiver

open Schubert.RS.GL

namespace ForwardQuiver

variable (Q : ForwardQuiver)

/-- **`Hom_L(V^λ, R_Q)` is finite-dimensional**: it splits over the graded pieces of multidegree
at most `degreeBound λ`, each finite-dimensional. -/
theorem finiteDimensional_intertwiningMap_coordRep
    (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p)) :
    FiniteDimensional ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap Q.coordRep) := by
  classical
  let S := Fintype.piFinset fun _ : Q.Arrow => Finset.range (Q.degreeBound (fun p => (lam p).1) + 1)
  have hS : ∀ ℓ ∉ S, ∀ f : (ratLeviIrrep Q.dim lam).IntertwiningMap
      (Q.coordPiece ℓ).toRepresentation, f = 0 := by
    intro ℓ hℓ f
    rw [Fintype.mem_piFinset] at hℓ
    push Not at hℓ
    obtain ⟨e, he⟩ := hℓ
    by_contra hf
    have hcut : ∀ p, ∑ i, (lam p).1 i = (Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p := by
      intro p
      by_contra hp
      exact hf (Q.intertwiningMap_coordPiece_eq_zero lam hp f)
    have := Q.le_degreeBound (lam := fun p => (lam p).1) hcut e
    simp only [Finset.mem_range, not_lt] at he
    omega
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℂ) (M := TensorProduct ℂ
    (PiTensorProduct ℂ fun p => Schubert.RS.Representation.flagOrbitSpan (polyShape (lam p))) ℂ)
  have hfin : ∀ ℓ : S, Module.Finite ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap
      (Q.coordPiece ℓ).toRepresentation) := fun ℓ =>
    Module.Finite.of_injective
      ({ toFun := fun f i => f (b i)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } :
        (ratLeviIrrep Q.dim lam).IntertwiningMap (Q.coordPiece ℓ).toRepresentation →ₗ[ℂ]
          (Fin m → (Q.coordPiece ℓ).toSubmodule))
      fun f f' h => _root_.Representation.IntertwiningMap.ext
        (LinearMap.ext_on_range hb fun i => congrFun h i)
  exact Module.Finite.equiv (Q.homDecomposition (ratLeviIrrep Q.dim lam) S hS).symm

/-- **`dim Hom_L(V^λ, R_Q)` is the multiplicity**, given `GLCharacterMultiplicity`. -/
theorem finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl (hgl : GLCharacterMultiplicity)
    (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p)) :
    (Module.finrank ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap Q.coordRep) : ℤ) =
      Q.multiplicity fun p => (lam p).1 :=
  Q.finrank_intertwiningMap_coordRep_eq_multiplicity_of hgl lam

end ForwardQuiver

variable {n : ℕ} {a b c : Composition n} {N : ℕ} {I : IntervalPartition n}

/-- The space `Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)` of Theorem 5.3 is finite-dimensional. -/
theorem finiteDimensional_quiverHom (h : IsQuiverPartition a b c N I) :
    FiniteDimensional ℂ ((ratLeviIrrep (quiverOf a b c N I).dim
      (leviDominantWeight h)).IntertwiningMap (quiverOf a b c N I).coordRep) :=
  (quiverOf a b c N I).finiteDimensional_intertwiningMap_coordRep _

/-- **Theorem 5.3** (`thm:quiver-coefficient`), given `GLCharacterMultiplicity`: for a quiver
partition `I` of `(a, b, c)`, `[𝒜_c](κ_a κ_b) = dim Hom_{L_I}(⊗_p V_p^{λ^{(p)}}, R_Q)`, where
`L_I = ∏_p GL(V_p)` acts on the coordinate ring `R_Q` of `⊕_{e : p → q} Hom(V_p, V_q)`. -/
theorem atomCoefficient_eq_finrank_hom (hgl : GLCharacterMultiplicity)
    (h : IsQuiverPartition a b c N I) :
    atomCoefficient (key a * key b) c =
      Module.finrank ℂ ((ratLeviIrrep (quiverOf a b c N I).dim
        (leviDominantWeight h)).IntertwiningMap (quiverOf a b c N I).coordRep) := by
  rw [atomCoefficient_eq_multiplicity h,
    (quiverOf a b c N I).finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl hgl]
  rfl

end Schubert.RS.Quiver
