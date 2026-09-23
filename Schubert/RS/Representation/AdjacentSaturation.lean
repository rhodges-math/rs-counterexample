import Schubert.RS.Representation.AdjacentStability

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation

/-- Stability under the lowering operator follows directly from the definition
as a span of its iterates. -/
theorem loweringSaturation_lower_stable {n : ℕ} (a b : Fin n)
    (M : Submodule ℂ (MatrixPolynomial n)) {q : MatrixPolynomial n}
    (hq : q ∈ loweringSaturation a b M) :
    matrixUnitDerivation b a q ∈ loweringSaturation a b M := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨⟨d,p⟩,rfl⟩ := hq
    rw [← derivationIter_succ]
    exact loweringSaturation_iter_mem a b M (d+1) p.property
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [Derivation.map_smul_of_tower] using Submodule.smul_mem _ c ih

theorem loweringSaturation_diagonal_stable {n : ℕ} (a b : Fin n)
    (M : Submodule ℂ (MatrixPolynomial n))
    (hM : ∀ j, ∀ p ∈ M, matrixUnitDerivation j j p ∈ M)
    (j : Fin n) {q : MatrixPolynomial n} (hq : q ∈ loweringSaturation a b M) :
    matrixUnitDerivation j j q ∈ loweringSaturation a b M := by
  let S := loweringSaturation a b M
  have hi (d : ℕ) (p : M) : matrixUnitDerivation j j (derivationIter (matrixUnitDerivation b a) d p.val) ∈ S := by
    induction d with
    | zero => exact le_loweringSaturation a b M (hM j p.val p.property)
    | succ d ih =>
      rw [derivationIter_succ]
      have hf := loweringSaturation_lower_stable a b M ih
      have hqF : matrixUnitDerivation b a (derivationIter (matrixUnitDerivation b a) d p.val) ∈ S := by
        rw [← derivationIter_succ]
        exact loweringSaturation_iter_mem a b M (d+1) p.property
      have he := diagonal_matrixUnit_commutator j b a (derivationIter (matrixUnitDerivation b a) d p.val)
      rw [sub_eq_iff_eq_add] at he
      rw [he]
      apply S.add_mem
      · apply S.sub_mem <;> split_ifs <;> first | exact hqF | exact S.zero_mem
      · exact hf
  induction hq using Submodule.span_induction with
  | mem q hq => obtain ⟨⟨d,p⟩,rfl⟩ := hq; exact hi d p
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [Derivation.map_smul_of_tower] using Submodule.smul_mem _ c ih

theorem loweringSaturation_upper_stable {n : ℕ} (i : AdjacentPosition n)
    (M : Submodule ℂ (MatrixPolynomial n))
    (hroot : ∀ r : PositiveRoot n, ∀ p ∈ M, matrixUnitDerivation r.val.1 r.val.2 p ∈ M)
    (hdiag : ∀ j, ∀ p ∈ M, matrixUnitDerivation j j p ∈ M)
    (r : PositiveRoot n) {q : MatrixPolynomial n} (hq : q ∈ loweringSaturation i.left i.right M) :
    matrixUnitDerivation r.val.1 r.val.2 q ∈ loweringSaturation i.left i.right M := by
  let S := loweringSaturation i.left i.right M
  have hi (d : ℕ) (p : M) : ∀ s : PositiveRoot n,
      matrixUnitDerivation s.val.1 s.val.2 (derivationIter (matrixUnitDerivation i.right i.left) d p.val) ∈ S := by
    induction d with
    | zero => intro s; exact le_loweringSaturation i.left i.right M (hroot s p.val p.property)
    | succ d ih =>
      intro s
      rw [derivationIter_succ]
      have he := loweringSaturation_lower_stable i.left i.right M (ih s)
      have hc := adjacent_lower_upper_commutator_mem i s S
        (derivationIter (matrixUnitDerivation i.right i.left) d p.val) ih
        (fun j => loweringSaturation_diagonal_stable i.left i.right M hdiag j
          (loweringSaturation_iter_mem i.left i.right M d p.property))
      exact (S.sub_mem_iff_right he).mp hc
  induction hq using Submodule.span_induction with
  | mem q hq => obtain ⟨⟨d,p⟩,rfl⟩ := hq; exact hi d p r
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [Derivation.map_smul_of_tower] using Submodule.smul_mem _ c ih

theorem loweringSaturation_le_of_stable {n : ℕ} (a b : Fin n)
    (M N : Submodule ℂ (MatrixPolynomial n)) (hMN : M ≤ N)
    (hN : ∀ p ∈ N, matrixUnitDerivation b a p ∈ N) : loweringSaturation a b M ≤ N := by
  apply Submodule.span_le.mpr
  rintro q ⟨⟨d,p⟩,rfl⟩
  induction d with
  | zero => exact hMN p.property
  | succ d ih =>
    change derivationIter (matrixUnitDerivation b a) (d+1) p.val ∈ N
    rw [derivationIter_succ]
    exact hN _ ih

/-- Exact saturation equality for the actual composition-indexed polynomial
modules. It does not assert any character recursion or string filtration. -/
theorem compositionFlag_adjacent_saturation {n : ℕ} (u : Composition n) (i : AdjacentPosition n)
    (hu : u i.left < u i.right) :
    loweringSaturation i.left i.right (compositionFlag (swapComposition u i)) = compositionFlag u := by
  apply le_antisymm
  · apply loweringSaturation_le_of_stable _ _ _ _ (compositionFlag_adjacent_le u i hu)
    intro p hp
    apply adjacent_lowering_flagDemazure_stable _ _ i _ hp
    rwa [composition_extremalWeight]
  · apply upperCyclic_le_of_root_stable
    · exact compositionFlagGenerator_mem_loweringSaturation u i.left i.right hu
    · intro r p hp
      apply loweringSaturation_upper_stable i _ _ _ r hp
      · intro s q hq
        exact upperCyclic_root_stable _ s hq
      · intro j q hq
        exact diagonal_flagDemazure_stable _ _ j hq

end
end Schubert.RS.Representation

