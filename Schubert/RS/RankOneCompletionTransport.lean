import Schubert.RS.Representation.RankOneCompletion

namespace Schubert.RS.Representation
noncomputable section
universe u v

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]
  {M M' X : Type u} [AddCommGroup M] [Module ℂ M]
  [AddCommGroup M'] [Module ℂ M'] [AddCommGroup X] [Module ℂ X]
  [LieRingModule L X] [LieModule ℂ L X] [Module.Finite ℂ X]
  {e h : L} {E H : Module.End ℂ M} {ι : M →ₗ[ℂ] X}

/-- Change the coordinates on the source of an exhibited completion. -/
theorem IsRankOneCompletion.reparametrize (C : IsRankOneCompletion e h E H ι)
    (b : M' ≃ₗ[ℂ] M) (E' H' : Module.End ℂ M')
    (he : ∀ m, b (E' m)=E (b m)) (hh : ∀ m, b (H' m)=H (b m)) :
    IsRankOneCompletion e h E' H' (ι.comp b.toLinearMap) where
  injective := C.injective.comp b.injective
  map_e := by intro m; change ι (b (E' m))=_; rw [he,C.map_e]; rfl
  map_h := by intro m; change ι (b (H' m))=_; rw [hh,C.map_h]; rfl
  universal := by
    intro N _ _ _ _ _ g ge gh
    let g' := g.comp b.symm.toLinearMap
    have he' : ∀ m, b.symm (E m)=E' (b.symm m) := by
      intro m
      apply b.injective
      rw [b.apply_symm_apply,he,b.apply_symm_apply]
    have hh' : ∀ m, b.symm (H m)=H' (b.symm m) := by
      intro m
      apply b.injective
      rw [b.apply_symm_apply,hh,b.apply_symm_apply]
    have ge' : ∀ m, g' (E m)=⁅e,g' m⁆ := by
      intro m
      change g (b.symm (E m))=_
      rw [he',ge]
      rfl
    have gh' : ∀ m, g' (H m)=⁅h,g' m⁆ := by
      intro m
      change g (b.symm (H m))=_
      rw [hh',gh]
      rfl
    obtain ⟨Φ,hΦ,hu⟩ := C.universal N g' ge' gh'
    refine ⟨Φ,?_,?_⟩
    · intro m
      change Φ (ι (b m))=g m
      rw [hΦ]
      exact congrArg g (b.symm_apply_apply m)
    · intro Ψ hΨ
      apply hu
      intro m
      have hz := hΨ (b.symm m)
      simpa only [g',LinearMap.comp_apply,LinearEquiv.coe_coe,b.apply_symm_apply] using hz

end
end Schubert.RS.Representation
