import Schubert.Demazure.Representation.StringEndpoints

/-!
# Lowering saturations

`loweringSaturation a b M` is the span of the iterates of the lowering derivation `E_ba` on `M`; it
contains `M`. If the extremal weight of `w` increases from `a` to `b`, the extremal flag vector of
`w` lies in the lowering saturation of the flag module of `(a b) w`
(`extremalFlag_mem_loweringSaturation`), and likewise for composition flag generators.
-/

open Schubert

namespace Demazure.FlagModule
noncomputable section

/-- The actual linear span of repeated lowering-operator images. No module
stability or saturation equality is part of this definition. -/
def loweringSaturation {n : ℕ} (a b : Fin n) (M : Submodule ℂ (MatrixPolynomial n)) :
    Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ
      (Set.range (fun kp : ℕ × M => derivationIter (matrixUnitDerivation b a) kp.1 kp.2.val))

theorem loweringSaturation_iter_mem {n : ℕ} (a b : Fin n) (M : Submodule ℂ (MatrixPolynomial n))
    (d : ℕ) {p : MatrixPolynomial n} (hp : p ∈ M) :
    derivationIter (matrixUnitDerivation b a) d p ∈ loweringSaturation a b M :=
  Submodule.subset_span ⟨(d,⟨p,hp⟩),rfl⟩

theorem le_loweringSaturation {n : ℕ} (a b : Fin n) (M : Submodule ℂ (MatrixPolynomial n)) :
    M ≤ loweringSaturation a b M := by
  intro p hp
  exact loweringSaturation_iter_mem a b M 0 hp

theorem extremalFlag_mem_loweringSaturation {n : ℕ} (m : ColumnShape n)
    (w : Equiv.Perm (Fin n)) (a b : Fin n)
    (hu : extremalWeight m w a < extremalWeight m w b) :
    extremalFlag m w ∈ loweringSaturation a b (flagDemazure m (Equiv.swap a b * w)) := by
  obtain ⟨c, hc, he⟩ := extremalFlag_reverse_string m w a b hu
  rw [he]
  apply Submodule.smul_mem
  apply loweringSaturation_iter_mem
  have hs := upperCyclic_seed (extremalFlag m (Equiv.swap a b * w))
  change rowRename (Equiv.swap a b) (rowRename w (highestFlag m)) ∈ _
  rw [← rowRename_mul]
  exact hs

theorem compositionFlagGenerator_mem_loweringSaturation {n : ℕ} (u : Composition n)
    (a b : Fin n) (hu : u a < u b) :
    (compositionFlagGenerator u).val ∈ loweringSaturation a b
        (compositionFlag (u ∘ Equiv.swap a b)) := by
  rw [compositionFlag_swap_eq]
  apply extremalFlag_mem_loweringSaturation
  rwa [composition_extremalWeight]

end
end Demazure.FlagModule
